import time
import requests
import math
import json
import hmac
import hashlib
import base64
import urllib.parse
from datetime import datetime
import ccxt
import pandas as pd
import numpy as np
import os
from typing import Dict, List, Tuple, Optional, Any, Union

# 使用FMZ平台的日志方式
class Logger:
    def info(self, message):
        Log(message)
    
    def warning(self, message):
        Log("[WARNING] " + message)
    
    def error(self, message):
        Log("[ERROR] " + message)

logger = Logger()

# 配置参数
class Config:
    # 交易所API配置
    API_KEYS = {
        "binance": {
            "apiKey": "",
            "secret": "",
            "enableRateLimit": True,
            "options": {"defaultType": "future"}
        },
        "okx": {
            "apiKey": "",
            "secret": "",
            "password": "",  # 欧易需要额外的密码
            "enableRateLimit": True
        },
        "bitget": {
            "apiKey": "",
            "secret": "",
            "password": "",
            "enableRateLimit": True,
            "options": {
                "": False  
            }
        },
        "bybit": {
            "apiKey": "",
            "secret": "",
            "enableRateLimit": True
        },
        "huobi": {
            "apiKey": "",
            "secret": "",
            "enableRateLimit": True,
         },
        "gate": {
            "apiKey": "",
            "secret": "",
            "enableRateLimit": True
        },
        "mexc": {
            "apiKey": "",
            "secret": "",
            "enableRateLimit": True
        },
        "coinex": {
            "apiKey": "",
            "secret": "",
            "enableRateLimit": True
        },
        "whitebit": {
            "apiKey": "",
            "secret": "",
            "enableRateLimit": True
        }
    }
    
    # 交易参数
    SYMBOLS = []  # 将由get_all_symbols函数动态填充
    FUNDING_RATE_THRESHOLD = 0.0005  # 资金费率差异阈值，超过此值视为套利机会
    PRICE_DIFF_THRESHOLD = 0.2  # 价格差异阈值，超过此值不执行套利
    POSITION_SIZE = 100  # 每个交易对的头寸大小(USDT)
    LEVERAGE = 5  # 杠杆倍数
    STOP_LOSS_RATIO = 0.05  # 止损比例
    TAKE_PROFIT_RATIO = 0.02  # 目标利润比例
    REFRESH_INTERVAL = 60  # 刷新间隔(秒)
    ENABLE_TRADING = True  # 是否启用实盘交易 - 确保设置为True进行实盘交易
    SAVE_TO_CSV = True  # 是否保存数据到CSV
    CSV_DIR = "./data"  # CSV文件保存目录
    
    # 套利类型
    ENABLE_SPOT_FUTURES_ARBITRAGE = True  # 启用现货-合约套利
    ENABLE_CROSS_EXCHANGE_ARBITRAGE = True  # 启用跨交易所套利
    
    # 交易所费率
    TRADING_FEES = {
        "binance": {"maker": 0.0002, "taker": 0.0004},
        "okx": {"maker": 0.0002, "taker": 0.0005},
        "bitget": {"maker": 0.0002, "taker": 0.0006},
        "bybit": {"maker": 0.0001, "taker": 0.0006},
        "huobi": {"maker": 0.0002, "taker": 0.0004},
        "gate": {"maker": 0.0002, "taker": 0.0005},
        "mexc": {"maker": 0.0002, "taker": 0.0006},
        "coinex": {"maker": 0.0002, "taker": 0.0006},
        "whitebit": {"maker": 0.0001, "taker": 0.0004}
    }
    
    # 最大获取币种数量
    MAX_SYMBOLS = 5000  # 限制处理的交易对数量，避免API请求过多
    
    # 最小账户余额要求
    MIN_BALANCE = 10  # 最小USDT余额要求，低于此值不执行交易
    
    # 持仓管理参数
    MAX_POSITIONS = 100  # 最大持仓数量
    MAX_POSITION_DURATION = 7 * 24 * 60 * 60  # 最大持仓时间（秒），默认7天
    TAKE_PROFIT_THRESHOLD = 0.05  # 止盈阈值，5%
    STOP_LOSS_THRESHOLD = -0.02  # 止损阈值，-2%
    RATE_DIFF_CLOSE_THRESHOLD = 0.001  # 资金费率差异平仓阈值，0.1%
    MAX_TOTAL_LOSS = -0.1  # 最大总亏损，-10%
    BATCH_SIZE = 20  # 每次处理的持仓数量

class MultiExchangeArbitrage:
    def __init__(self, config: Config):
        self.config = config
        self.exchanges = {}
        self.spot_exchanges = {}
        self.futures_exchanges = {}
        self.symbols_data = {}
        self.funding_rates = {}
        self.opportunities = []
        self.positions = []
        self.init_time = int(time.time())
        self.last_position_index = 0  # 记录上次处理的持仓索引
        self.last_error = None # 记录上次运行循环中的错误
        self.exchange_errors = {}  # 记录各交易所的错误信息
        
        # 交易对映射
        self.exchange_symbols = {}  # 每个交易所支持的交易对
        self.contract_mappings = {}  # 各交易所合约映射
        
        # 确保数据目录存在
        if not os.path.exists(config.CSV_DIR):
            os.makedirs(config.CSV_DIR)
        
        # 初始化交易所
        self.init_exchanges()
        
    def init_exchanges(self):
        """初始化所有交易所连接"""
        exchange_ids =["gate", "binance" , "okx",  "bitget", "bybit",  "whitebit"]
        
        for exchange_id in exchange_ids:
            if not self.config.API_KEYS[exchange_id]["apiKey"]:
                logger.warning(f"跳过 {exchange_id} 交易所，未配置API密钥")
                continue
                
            try:
                # 创建现货交易所实例
                spot_exchange = getattr(ccxt, exchange_id)(self.config.API_KEYS[exchange_id])
                spot_exchange.options["defaultType"] = "spot"
                
                # 为Bitget特别设置市价买单选项
                if exchange_id == "bitget":
                    spot_exchange.options["createMarketBuyOrderRequiresPrice"] = False
                
                self.spot_exchanges[exchange_id] = spot_exchange
                
                # 创建合约交易所实例
                futures_exchange = getattr(ccxt, exchange_id)(self.config.API_KEYS[exchange_id])
                if exchange_id == "binance":
                    futures_exchange.options["defaultType"] = "future"
                elif exchange_id in ["okx", "huobi", "gate", "bitget", "bybit", "mexc", "coinex", "whitebit"]:
                    futures_exchange.options["defaultType"] = "swap"
                
                # 为Bitget特别设置市价买单选项
                if exchange_id == "bitget":
                    futures_exchange.options["createMarketBuyOrderRequiresPrice"] = False
                
                self.futures_exchanges[exchange_id] = futures_exchange
                
                logger.info(f"成功初始化 {exchange_id} 交易所")
            except Exception as e:
                logger.error(f"初始化 {exchange_id} 交易所失败: {str(e)}")
                self.exchange_errors[exchange_id] = f"初始化失败: {str(e)}"
        
        # 合并所有交易所到一个字典
        self.exchanges = {**self.spot_exchanges, **self.futures_exchanges}
        
        if not self.spot_exchanges or not self.futures_exchanges:
            logger.error("没有成功初始化任何交易所，请检查API配置")
            raise ValueError("没有可用的交易所")
            
        logger.info(f"成功初始化 {len(self.spot_exchanges)} 个现货交易所和 {len(self.futures_exchanges)} 个合约交易所")
        
        # 创建合约映射
        self.create_contract_mappings()

    
    def create_contract_mappings(self):
        """创建各交易所的合约映射"""
        # 初始化合约映射字典
        for exchange_id in self.futures_exchanges:
            self.contract_mappings[exchange_id] = {}
        
        # 加载市场数据
        self.load_markets()
        
        # 创建各交易所的合约映射
        for exchange_id, exchange in self.futures_exchanges.items():
            try:
                if not hasattr(exchange, "markets") or exchange.markets is None:
                    continue
                
                # 获取该交易所的所有永续合约
                for symbol, market in exchange.markets.items():
                    if market.get("swap", False) and market.get("active", False):
                        # 标准化符号格式
                        standard_symbol = self.normalize_symbol(symbol)
                        if standard_symbol:
                            self.contract_mappings[exchange_id][standard_symbol] = symbol
                
                logger.info(f"已创建 {exchange_id} 交易所的合约映射，共 {len(self.contract_mappings[exchange_id])} 个合约")
            except Exception as e:
                logger.error(f"创建 {exchange_id} 交易所的合约映射失败: {str(e)}")
                self.exchange_errors[exchange_id] = f"创建合约映射失败: {str(e)}"
    
    def normalize_symbol(self, symbol):
        """标准化交易对符号"""
        try:
            # 移除特殊后缀
            if ":" in symbol:
                parts = symbol.split(":")
                base = parts[0].split("/")[0]
                quote = parts[1]
                return f"{base}/USDT"
            elif "USDT" in symbol:
                # 处理常规USDT交易对
                if "/" in symbol:
                    base = symbol.split("/")[0]
                    return f"{base}/USDT"
                else:
                    # 处理没有/的格式，如BTCUSDT
                    for quote in ["USDT", "USD", "BUSD"]:
                        if symbol.endswith(quote):
                            base = symbol[:-len(quote)]
                            return f"{base}/USDT"
            
            return None
        except Exception as e:
            logger.error(f"标准化符号 {symbol} 失败: {str(e)}")
            return None
    
    def get_contract_symbol(self, exchange_id, standard_symbol):
        """获取交易所特定的合约符号"""
        if exchange_id in self.contract_mappings and standard_symbol in self.contract_mappings[exchange_id]:
            return self.contract_mappings[exchange_id][standard_symbol]
        return None
    
    def check_balance(self, exchange_id, currency="USDT"):
        """检查账户余额是否足够"""
        try:
            exchange = self.spot_exchanges[exchange_id]
            balance = exchange.fetch_balance()
            
            if currency in balance["free"]:
                free_balance = balance["free"][currency]
                logger.info(f"{exchange_id} {currency} 可用余额: {free_balance}")
                return free_balance >= self.config.MIN_BALANCE
            else:
                logger.warning(f"{exchange_id} 没有 {currency} 余额")
                return False
        except Exception as e:
            logger.error(f"获取 {exchange_id} 余额失败: {str(e)}")
            self.exchange_errors[exchange_id] = f"获取余额失败: {str(e)}"
            return False
    
    def load_markets(self):
        """加载所有交易所的市场数据"""
        for exchange_id, exchange in self.exchanges.items():
            try:
                exchange.load_markets()
                logger.info(f"成功加载 {exchange_id} 交易所的市场数据")
            except Exception as e:
                logger.error(f"加载 {exchange_id} 交易所的市场数据失败: {str(e)}")
                self.exchange_errors[exchange_id] = f"加载市场数据失败: {str(e)}"
    
    def get_all_symbols(self):
        """获取所有交易所支持的交易对"""
        all_symbols = set()
        
        # 获取所有合约交易所支持的交易对
        for exchange_id, exchange in self.futures_exchanges.items():
            try:
                if not hasattr(exchange, "markets") or exchange.markets is None:
                    exchange.load_markets()
                
                # 获取该交易所支持的所有永续合约交易对
                symbols = []
                for symbol, market in exchange.markets.items():
                    if market.get("swap", False) and market.get("active", False):
                        standard_symbol = self.normalize_symbol(symbol)
                        if standard_symbol:
                            symbols.append(standard_symbol)
                
                # 记录该交易所支持的交易对
                self.exchange_symbols[exchange_id] = symbols
                all_symbols.update(symbols)
                
                logger.info(f"{exchange_id} 交易所支持 {len(symbols)} 个永续合约交易对")
            except Exception as e:
                logger.error(f"获取 {exchange_id} 交易所的交易对失败: {str(e)}")
                self.exchange_errors[exchange_id] = f"获取交易对失败: {str(e)}"
        
        # 限制交易对数量
        all_symbols = list(all_symbols)[:self.config.MAX_SYMBOLS]
        logger.info(f"所有交易所共支持 {len(all_symbols)} 个交易对")
        
        return all_symbols
    
    def get_funding_rates(self):
        """获取所有交易所的资金费率"""
        funding_rates = {}
        
        # 如果SYMBOLS为空，获取所有交易对
        if not self.config.SYMBOLS:
            self.config.SYMBOLS = self.get_all_symbols()
        
        # 获取每个交易所的资金费率
        for exchange_id, exchange in self.futures_exchanges.items():
            try:
                funding_rates[exchange_id] = {}
                
                # 尝试批量获取资金费率
                try:
                    all_rates = exchange.fetch_funding_rates()
                    if all_rates:
                        for symbol, rate_info in all_rates.items():
                            standard_symbol = self.normalize_symbol(symbol)
                            if standard_symbol:
                                funding_rates[exchange_id][standard_symbol] = {
                                    "rate": rate_info.get("fundingRate", None),
                                    "timestamp": rate_info.get("timestamp", int(time.time() * 1000))
                                }
                        
                        logger.info(f"成功批量获取 {exchange_id} 交易所的资金费率，共 {len(funding_rates[exchange_id])} 个")
                        continue
                except Exception as e:
                    logger.warning(f"批量获取 {exchange_id} 交易所的资金费率失败: {str(e)}，尝试逐个获取")
                    self.exchange_errors[exchange_id] = f"批量获取资金费率失败: {str(e)}"
                
                # 如果批量获取失败，逐个获取
                for symbol in self.config.SYMBOLS:
                    try:
                        # 获取该交易所特定的合约符号
                        contract_symbol = self.get_contract_symbol(exchange_id, symbol)
                        if not contract_symbol:
                            continue
                        
                        # 获取资金费率
                        rate_info = exchange.fetch_funding_rate(contract_symbol)
                        
                        if rate_info and "fundingRate" in rate_info:
                            funding_rates[exchange_id][symbol] = {
                                "rate": rate_info["fundingRate"],
                                "timestamp": rate_info.get("timestamp", int(time.time() * 1000))
                            }
                    except Exception as e:
                        # 减少错误日志输出，只在调试模式下显示
                        pass
                
                logger.info(f"成功获取 {exchange_id} 交易所的资金费率，共 {len(funding_rates[exchange_id])} 个")
            except Exception as e:
                logger.error(f"获取 {exchange_id} 交易所的资金费率失败: {str(e)}")
                self.exchange_errors[exchange_id] = f"获取资金费率失败: {str(e)}"
        
        return funding_rates
    
    def get_tickers(self, symbols=None):
        """获取所有交易所的行情数据"""
        tickers = {}
        
        if symbols is None:
            symbols = self.config.SYMBOLS
        
        # 获取每个交易所的行情数据
        for exchange_type in ["spot", "futures"]:
            tickers[exchange_type] = {}
            
            exchanges = self.spot_exchanges if exchange_type == "spot" else self.futures_exchanges
            
            for exchange_id, exchange in exchanges.items():
                try:
                    tickers[exchange_type][exchange_id] = {}
                    
                    # 尝试批量获取行情
                    try:
                        all_tickers = exchange.fetch_tickers()
                        if all_tickers:
                            for symbol in symbols:
                                # 对于合约交易所，需要获取特定的合约符号
                                if exchange_type == "futures":
                                    contract_symbol = self.get_contract_symbol(exchange_id, symbol)
                                    if not contract_symbol or contract_symbol not in all_tickers:
                                        continue
                                    ticker = all_tickers[contract_symbol]
                                else:
                                    # 对于现货交易所，直接使用标准符号
                                    if symbol not in all_tickers:
                                        # 尝试没有斜杠的格式
                                        plain_symbol = symbol.replace("/", "")
                                        if plain_symbol in all_tickers:
                                            ticker = all_tickers[plain_symbol]
                                        else:
                                            continue
                                    else:
                                        ticker = all_tickers[symbol]
                                
                                tickers[exchange_type][exchange_id][symbol] = ticker
                            
                            logger.info(f"成功批量获取 {exchange_id} {exchange_type} 行情，共 {len(tickers[exchange_type][exchange_id])} 个")
                            continue
                    except Exception as e:
                        logger.warning(f"批量获取 {exchange_id} {exchange_type} 行情失败: {str(e)}，尝试逐个获取")
                        self.exchange_errors[exchange_id] = f"批量获取{exchange_type}行情失败: {str(e)}"
                    
                    # 如果批量获取失败，逐个获取
                    for symbol in symbols:
                        try:
                            # 对于合约交易所，需要获取特定的合约符号
                            if exchange_type == "futures":
                                contract_symbol = self.get_contract_symbol(exchange_id, symbol)
                                if not contract_symbol:
                                    continue
                                ticker = exchange.fetch_ticker(contract_symbol)
                            else:
                                ticker = exchange.fetch_ticker(symbol)
                            
                            tickers[exchange_type][exchange_id][symbol] = ticker
                        except Exception as e:
                            # 减少错误日志输出，只在调试模式下显示
                            pass
                    
                    logger.info(f"成功获取 {exchange_id} {exchange_type} 行情，共 {len(tickers[exchange_type][exchange_id])} 个")
                except Exception as e:
                    logger.error(f"获取 {exchange_id} {exchange_type} 行情失败: {str(e)}")
                    self.exchange_errors[exchange_id] = f"获取{exchange_type}行情失败: {str(e)}"
        
        return tickers
    
    def find_spot_futures_arbitrage_opportunities(self):
        """寻找现货-合约套利机会"""
        if not self.config.ENABLE_SPOT_FUTURES_ARBITRAGE:
            return []
            
        opportunities = []
        
        # 获取资金费率和行情数据
        funding_rates = self.funding_rates
        tickers = self.get_tickers()
        
        # 遍历所有交易所
        for exchange_id in self.futures_exchanges:
            if exchange_id not in funding_rates or exchange_id not in tickers["futures"]:
                continue
                
            # 检查该交易所是否同时支持现货和合约
            if exchange_id not in tickers["spot"]:
                continue
                
            # 遍历该交易所的所有资金费率
            for symbol, rate_info in funding_rates[exchange_id].items():
                # 检查该交易对是否同时有现货和合约行情
                if symbol not in tickers["spot"][exchange_id] or symbol not in tickers["futures"][exchange_id]:
                    continue
                    
                # 获取资金费率
                rate = rate_info.get("rate")
                if rate is None:
                    # logger.warning(f"{exchange_id} {symbol} 资金费率为 None，跳过")
                    continue
                
                # 获取现货和合约价格
                spot_ticker = tickers["spot"][exchange_id][symbol]
                futures_ticker = tickers["futures"][exchange_id][symbol]
                
                spot_bid = spot_ticker.get("bid")
                spot_ask = spot_ticker.get("ask")
                futures_bid = futures_ticker.get("bid")
                futures_ask = futures_ticker.get("ask")
                
                if spot_bid is None or spot_ask is None or futures_bid is None or futures_ask is None:
                    # logger.warning(f"{exchange_id} {symbol} 现货或合约价格为 None，跳过")
                    continue
                
                spot_price = (spot_bid + spot_ask) / 2
                futures_price = (futures_bid + futures_ask) / 2
                
                if spot_price == 0: # 避免除零错误
                    continue
                    
                # 计算价格差异
                price_diff = abs(futures_price - spot_price) / spot_price
                
                # 检查价格差异是否过大
                if price_diff > self.config.PRICE_DIFF_THRESHOLD:
                    # logger.warning(f"{exchange_id} {symbol} 现货-合约价格差异过大: {price_diff:.4f}, 跳过")
                    continue
                
                # 根据资金费率确定套利方向
                if rate > self.config.FUNDING_RATE_THRESHOLD:
                    # 资金费率为正，做空合约，买入现货
                    direction = "long_spot_short_futures"
                    fee = self.config.TRADING_FEES.get(exchange_id, {"maker": 0.0002, "taker": 0.0004}) # 使用默认费率
                    expected_profit = rate - price_diff - (fee["maker"] + fee["maker"]) # 假设都用maker fee
                else:
                    # 只考虑资金费率为正的情况
                    continue
                
                # 检查预期利润是否为正
                if expected_profit <= 0:
                    continue
                
                # 记录套利机会
                opportunity = {
                    "exchange": exchange_id,
                    "symbol": symbol,
                    "direction": direction,
                    "funding_rate": rate,
                    "spot_price": spot_price,
                    "futures_price": futures_price,
                    "price_diff": price_diff,
                    "expected_profit": expected_profit,
                    "timestamp": int(time.time())
                }
                
                opportunities.append(opportunity)
                logger.info(f"发现现货-合约套利机会: {exchange_id} {symbol} {direction} 资金费率: {rate:.8f} 预期利润: {expected_profit:.4f}")
        
        return opportunities
    
    def find_cross_exchange_arbitrage_opportunities(self):
        """寻找跨交易所套利机会"""
        if not self.config.ENABLE_CROSS_EXCHANGE_ARBITRAGE:
            return []
            
        opportunities = []
        
        # 获取所有交易所的资金费率
        funding_rates = self.funding_rates
        
        # 获取所有交易所的合约行情
        tickers = self.get_tickers()
        
        # 遍历所有交易对
        for symbol in self.config.SYMBOLS:
            # 找出该交易对在各交易所的资金费率
            symbol_rates = {}
            for exchange_id, rates in funding_rates.items():
                if symbol in rates and rates[symbol].get("rate") is not None:
                    symbol_rates[exchange_id] = rates[symbol].get("rate")
            
            # 如果少于2个交易所有该交易对的资金费率，则跳过
            if len(symbol_rates) < 2:
                continue
            
            # 手动找出最大和最小值，避免使用max/min函数
            symbol_rates_list = [(exchange_id, rate) for exchange_id, rate in symbol_rates.items()]
            
            max_rate_exchange = None
            min_rate_exchange = None
            max_rate = float("-inf")
            min_rate = float("inf")
            
            for exchange_id, rate in symbol_rates_list:
                if rate > max_rate:
                    max_rate = rate
                    max_rate_exchange = exchange_id
                if rate < min_rate:
                    min_rate = rate
                    min_rate_exchange = exchange_id
            
            if max_rate_exchange is None or min_rate_exchange is None or max_rate == float("-inf") or min_rate == float("inf"):
                continue
            
            # 计算资金费率差异
            rate_diff = max_rate - min_rate
            
            # 检查资金费率差异是否足够大
            if rate_diff < self.config.FUNDING_RATE_THRESHOLD:
                continue
            
            # 获取两个交易所的合约价格
            if max_rate_exchange not in tickers["futures"] or min_rate_exchange not in tickers["futures"]:
                continue
                
            if symbol not in tickers["futures"][max_rate_exchange] or symbol not in tickers["futures"][min_rate_exchange]:
                continue
                
            max_rate_ticker = tickers["futures"][max_rate_exchange][symbol]
            min_rate_ticker = tickers["futures"][min_rate_exchange][symbol]
            
            max_rate_bid = max_rate_ticker.get("bid")
            max_rate_ask = max_rate_ticker.get("ask")
            min_rate_bid = min_rate_ticker.get("bid")
            min_rate_ask = min_rate_ticker.get("ask")
            
            if max_rate_bid is None or max_rate_ask is None or min_rate_bid is None or min_rate_ask is None:
                # logger.warning(f"{symbol} {max_rate_exchange} 或 {min_rate_exchange} 价格为 None，跳过")
                continue
                
            max_rate_price = (max_rate_bid + max_rate_ask) / 2
            min_rate_price = (min_rate_bid + min_rate_ask) / 2
            
            if min_rate_price == 0: # 避免除零错误
                continue
                
            # 计算价格差异
            price_diff = abs(max_rate_price - min_rate_price) / min_rate_price
            
            # 检查价格差异是否过大
            if price_diff > self.config.PRICE_DIFF_THRESHOLD:
                # logger.warning(f"{symbol} {max_rate_exchange}-{min_rate_exchange} 跨交易所价格差异过大: {price_diff:.4f}, 跳过")
                continue
            
            # 计算预期利润
            fee_max = self.config.TRADING_FEES.get(max_rate_exchange, {"maker": 0.0002, "taker": 0.0004})
            fee_min = self.config.TRADING_FEES.get(min_rate_exchange, {"maker": 0.0002, "taker": 0.0004})
            expected_profit = rate_diff - price_diff - (fee_max["maker"] + fee_min["maker"]) # 假设都用maker fee
            
            # 检查预期利润是否为正
            if expected_profit <= 0:
                continue
            
            # 记录套利机会
            opportunity = {
                "symbol": symbol,
                "long_exchange": min_rate_exchange,
                "short_exchange": max_rate_exchange,
                "long_rate": min_rate,
                "short_rate": max_rate,
                "rate_diff": rate_diff,
                "long_price": min_rate_price,
                "short_price": max_rate_price,
                "price_diff": price_diff,
                "expected_profit": expected_profit,
                "timestamp": int(time.time())
            }
            
            opportunities.append(opportunity)
            logger.info(f"发现跨交易所套利机会: {symbol} 做多{min_rate_exchange}(费率:{min_rate:.8f}) 做空{max_rate_exchange}(费率:{max_rate:.8f}) 预期利润: {expected_profit:.4f}")
        
        return opportunities
    
    def execute_spot_futures_arbitrage(self, opportunity):
        """执行现货-合约套利"""
        if not self.config.ENABLE_TRADING:
            logger.info(f"执行现货-合约套利: {opportunity['exchange']} {opportunity['symbol']} {opportunity['direction']}")
            return
            
        exchange_id = opportunity["exchange"]
        symbol = opportunity["symbol"]
        direction = opportunity["direction"]
        
        # 检查账户余额是否足够
        if not self.check_balance(exchange_id):
            logger.error(f"{exchange_id} 账户余额不足，无法执行套利")
            return
        
        # 获取最新价格
        try:
            spot_ticker = self.spot_exchanges[exchange_id].fetch_ticker(symbol)
            futures_ticker = self.futures_exchanges[exchange_id].fetch_ticker(self.get_contract_symbol(exchange_id, symbol))
            
            spot_bid = spot_ticker.get("bid")
            spot_ask = spot_ticker.get("ask")
            futures_bid = futures_ticker.get("bid")
            futures_ask = futures_ticker.get("ask")
            
            if spot_bid is None or spot_ask is None or futures_bid is None or futures_ask is None:
                logger.error(f"获取 {exchange_id} {symbol} 价格失败: 价格为 None")
                return
                
            spot_price = (spot_bid + spot_ask) / 2
            futures_price = (futures_bid + futures_ask) / 2
            
            if spot_price == 0: # 避免除零错误
                logger.error(f"获取 {exchange_id} {symbol} 价格失败: 现货价格为 0")
                return
                
        except Exception as e:
            logger.error(f"获取 {exchange_id} {symbol} 价格失败: {str(e)}")
            self.exchange_errors[exchange_id] = f"获取价格失败: {str(e)}"
            return
        
        # 计算交易数量
        amount = self.config.POSITION_SIZE / spot_price
        
        # 执行交易
        spot_order = None
        futures_order = None
        
        try:
            if direction == "long_spot_short_futures":
                # 买入现货
                spot_order = self.spot_exchanges[exchange_id].create_market_buy_order(symbol, amount)
                
                if spot_order:
                    logger.info(f"已在 {exchange_id} 买入现货 {symbol} {amount}")
                    
                    # 做空合约
                    futures_order = self.futures_exchanges[exchange_id].create_market_sell_order(
                        self.get_contract_symbol(exchange_id, symbol),
                        amount * self.config.LEVERAGE
                    )
                    
                    if futures_order:
                        logger.info(f"已在 {exchange_id} 做空合约 {symbol} {amount * self.config.LEVERAGE}")
                        
                        # 记录持仓
                        position = {
                            "type": "spot_futures",
                            "exchange": exchange_id,
                            "symbol": symbol,
                            "direction": direction,
                            "amount": amount,
                            "spot_price": spot_price,
                            "futures_price": futures_price,
                            "funding_rate": opportunity["funding_rate"],
                            "timestamp": int(time.time()),
                            "spot_order_id": spot_order["id"],
                            "futures_order_id": futures_order["id"]
                        }
                        
                        self.positions.append(position)
                        logger.info(f"已添加持仓: {exchange_id} {symbol} {direction}")
                    else:
                        # 如果合约订单失败，尝试卖出已买入的现货
                        logger.error(f"做空合约失败，尝试卖出已买入的现货")
                        try:
                            self.spot_exchanges[exchange_id].create_market_sell_order(symbol, amount)
                        except Exception as e:
                            logger.error(f"卖出现货失败: {str(e)}")
                            self.exchange_errors[exchange_id] = f"卖出现货失败: {str(e)}"
            else:
                logger.error(f"无效的套利方向: {direction}")
        
        except Exception as e:
            logger.error(f"执行现货-合约套利失败: {str(e)}")
            self.exchange_errors[exchange_id] = f"执行套利失败: {str(e)}"
    
    def execute_cross_exchange_arbitrage(self, opportunity):
        """执行跨交易所套利"""
        if not self.config.ENABLE_TRADING:
            logger.info(f"执行跨交易所套利: {opportunity['symbol']} 做多{opportunity['long_exchange']} 做空{opportunity['short_exchange']}")
            return
            
        symbol = opportunity["symbol"]
        long_exchange = opportunity["long_exchange"]
        short_exchange = opportunity["short_exchange"]
        
        # 检查账户余额是否足够
        if not self.check_balance(long_exchange) or not self.check_balance(short_exchange):
            logger.error(f"{long_exchange} 或 {short_exchange} 账户余额不足，无法执行套利")
            return
        
        # 获取最新价格
        try:
            long_ticker = self.futures_exchanges[long_exchange].fetch_ticker(self.get_contract_symbol(long_exchange, symbol))
            short_ticker = self.futures_exchanges[short_exchange].fetch_ticker(self.get_contract_symbol(short_exchange, symbol))
            
            long_bid = long_ticker.get("bid")
            long_ask = long_ticker.get("ask")
            short_bid = short_ticker.get("bid")
            short_ask = short_ticker.get("ask")
            
            if long_bid is None or long_ask is None or short_bid is None or short_ask is None:
                logger.error(f"获取 {long_exchange} 或 {short_exchange} {symbol} 价格失败: 价格为 None")
                return
                
            long_price = (long_bid + long_ask) / 2
            short_price = (short_bid + short_ask) / 2
            
            if long_price == 0: # 避免除零错误
                logger.error(f"获取 {long_exchange} {symbol} 价格失败: 做多价格为 0")
                return
                
        except Exception as e:
            logger.error(f"获取 {long_exchange} 或 {short_exchange} {symbol} 价格失败: {str(e)}")
            self.exchange_errors[f"{long_exchange}/{short_exchange}"] = f"获取价格失败: {str(e)}"
            return
        
        # 计算交易数量
        amount = self.config.POSITION_SIZE / long_price
        
        # 执行交易
        long_order = None
        short_order = None
        
        try:
            # 在资金费率低的交易所做多
            long_order = self.futures_exchanges[long_exchange].create_market_buy_order(
                self.get_contract_symbol(long_exchange, symbol),
                amount * self.config.LEVERAGE
            )
            
            if long_order:
                logger.info(f"已在 {long_exchange} 做多合约 {symbol} {amount * self.config.LEVERAGE}")
                
                # 在资金费率高的交易所做空
                short_order = self.futures_exchanges[short_exchange].create_market_sell_order(
                    self.get_contract_symbol(short_exchange, symbol),
                    amount * self.config.LEVERAGE
                )
                
                if short_order:
                    logger.info(f"已在 {short_exchange} 做空合约 {symbol} {amount * self.config.LEVERAGE}")
                    
                    # 记录持仓
                    position = {
                        "type": "cross_exchange",
                        "symbol": symbol,
                        "long_exchange": long_exchange,
                        "short_exchange": short_exchange,
                        "amount": amount,
                        "long_price": long_price,
                        "short_price": short_price,
                        "long_rate": opportunity["long_rate"],
                        "short_rate": opportunity["short_rate"],
                        "timestamp": int(time.time()),
                        "long_order_id": long_order["id"],
                        "short_order_id": short_order["id"]
                    }
                    
                    self.positions.append(position)
                    logger.info(f"已添加持仓: {symbol} 做多{long_exchange} 做空{short_exchange}")
                else:
                    # 如果做空订单失败，尝试平掉做多订单
                    logger.error(f"做空合约失败，尝试平掉做多订单")
                    try:
                        self.futures_exchanges[long_exchange].create_market_sell_order(
                            self.get_contract_symbol(long_exchange, symbol),
                            amount * self.config.LEVERAGE
                        )
                    except Exception as e:
                        logger.error(f"平掉做多订单失败: {str(e)}")
                        self.exchange_errors[long_exchange] = f"平掉做多订单失败: {str(e)}"
        
        except Exception as e:
            logger.error(f"执行跨交易所套利失败: {str(e)}")
            self.exchange_errors[f"{long_exchange}/{short_exchange}"] = f"执行套利失败: {str(e)}"
    
    def close_position(self, position):
        """平仓"""
        if not self.config.ENABLE_TRADING:
            logger.info(f"平仓: {position}")
            return
            
        try:
            if position["type"] == "spot_futures":
                exchange_id = position["exchange"]
                symbol = position["symbol"]
                direction = position["direction"]
                amount = position["amount"]
                
                if direction == "long_spot_short_futures":
                    # 卖出现货
                    self.spot_exchanges[exchange_id].create_market_sell_order(symbol, amount)
                    logger.info(f"已在 {exchange_id} 卖出现货 {symbol} {amount}")
                    
                    # 平掉做空合约
                    self.futures_exchanges[exchange_id].create_market_buy_order(
                        self.get_contract_symbol(exchange_id, symbol),
                        amount * self.config.LEVERAGE
                    )
                    
                    logger.info(f"已在 {exchange_id} 平掉做空合约 {symbol} {amount * self.config.LEVERAGE}")
                else:
                    logger.error(f"无效的平仓方向: {direction}")
            
            elif position["type"] == "cross_exchange":
                symbol = position["symbol"]
                long_exchange = position["long_exchange"]
                short_exchange = position["short_exchange"]
                amount = position["amount"]
                
                # 平掉做多合约
                self.futures_exchanges[long_exchange].create_market_sell_order(
                    self.get_contract_symbol(long_exchange, symbol),
                    amount * self.config.LEVERAGE
                )
                
                logger.info(f"已在 {long_exchange} 平掉做多合约 {symbol} {amount * self.config.LEVERAGE}")
                
                # 平掉做空合约
                self.futures_exchanges[short_exchange].create_market_buy_order(
                    self.get_contract_symbol(short_exchange, symbol),
                    amount * self.config.LEVERAGE
                )
                
                logger.info(f"已在 {short_exchange} 平掉做空合约 {symbol} {amount * self.config.LEVERAGE}")
            
            else:
                logger.error(f"无效的持仓类型: {position['type']}")
        
        except Exception as e:
            logger.error(f"平仓失败: {str(e)}")
            if position["type"] == "spot_futures":
                self.exchange_errors[position["exchange"]] = f"平仓失败: {str(e)}"
            elif position["type"] == "cross_exchange":
                self.exchange_errors[f"{position['long_exchange']}/{position['short_exchange']}"] = f"平仓失败: {str(e)}"
    
    def update_position_profit_loss(self, position):
        """更新持仓盈亏"""
        try:
            if position["type"] == "spot_futures":
                exchange_id = position["exchange"]
                symbol = position["symbol"]
                direction = position["direction"]
                
                # 获取最新价格
                spot_ticker = self.spot_exchanges[exchange_id].fetch_ticker(symbol)
                futures_ticker = self.futures_exchanges[exchange_id].fetch_ticker(self.get_contract_symbol(exchange_id, symbol))
                
                spot_bid = spot_ticker.get("bid")
                spot_ask = spot_ticker.get("ask")
                futures_bid = futures_ticker.get("bid")
                futures_ask = futures_ticker.get("ask")
                
                if spot_bid is None or spot_ask is None or futures_bid is None or futures_ask is None:
                    logger.error(f"更新盈亏失败: {exchange_id} {symbol} 价格为 None")
                    return 0
                    
                spot_price = (spot_bid + spot_ask) / 2
                futures_price = (futures_bid + futures_ask) / 2
                
                if position["spot_price"] == 0 or position["futures_price"] == 0: # 避免除零错误
                    logger.error(f"更新盈亏失败: {exchange_id} {symbol} 开仓价格为 0")
                    return 0
                    
                # 计算盈亏
                if direction == "long_spot_short_futures":
                    # 现货盈亏
                    spot_pl = (spot_price - position["spot_price"]) / position["spot_price"]
                    # 合约盈亏
                    futures_pl = (position["futures_price"] - futures_price) / position["futures_price"]
                    # 总盈亏
                    total_pl = spot_pl + futures_pl
                else:
                    logger.error(f"无效的持仓方向: {direction}")
                    return 0
                
                # 更新持仓盈亏
                position["spot_pl"] = spot_pl
                position["futures_pl"] = futures_pl
                position["total_pl"] = total_pl
                position["profit"] = total_pl * position["amount"] * position["spot_price"]
                
                return position["profit"]
            
            elif position["type"] == "cross_exchange":
                symbol = position["symbol"]
                long_exchange = position["long_exchange"]
                short_exchange = position["short_exchange"]
                
                # 获取最新价格
                long_ticker = self.futures_exchanges[long_exchange].fetch_ticker(self.get_contract_symbol(long_exchange, symbol))
                short_ticker = self.futures_exchanges[short_exchange].fetch_ticker(self.get_contract_symbol(short_exchange, symbol))
                
                long_bid = long_ticker.get("bid")
                long_ask = long_ticker.get("ask")
                short_bid = short_ticker.get("bid")
                short_ask = short_ticker.get("ask")
                
                if long_bid is None or long_ask is None or short_bid is None or short_ask is None:
                    logger.error(f"更新盈亏失败: {long_exchange} 或 {short_exchange} {symbol} 价格为 None")
                    return 0
                    
                long_price = (long_bid + long_ask) / 2
                short_price = (short_bid + short_ask) / 2
                
                if position["long_price"] == 0 or position["short_price"] == 0: # 避免除零错误
                    logger.error(f"更新盈亏失败: {long_exchange} 或 {short_exchange} {symbol} 开仓价格为 0")
                    return 0
                    
                # 计算盈亏
                long_pl = (long_price - position["long_price"]) / position["long_price"]
                short_pl = (position["short_price"] - short_price) / position["short_price"]
                total_pl = long_pl + short_pl
                
                # 更新持仓盈亏
                position["long_pl"] = long_pl
                position["short_pl"] = short_pl
                position["total_pl"] = total_pl
                position["profit"] = total_pl * position["amount"] * position["long_price"]
                
                return position["profit"]
            
            else:
                logger.error(f"无效的持仓类型: {position['type']}")
                return 0
        
        except Exception as e:
            logger.error(f"更新持仓盈亏失败: {str(e)}")
            return 0
    
    def manage_positions(self):
        """管理持仓"""
        if not self.positions:
            return
            
        # 获取需要处理的持仓
        positions_to_process = []
        positions_to_close = []
        
        # 如果持仓数量小于批处理大小，处理所有持仓
        if len(self.positions) <= self.config.BATCH_SIZE:
            positions_to_process = self.positions
        else:
            # 否则，按批次处理持仓
            start_index = self.last_position_index
            end_index = min(start_index + self.config.BATCH_SIZE, len(self.positions))
            
            positions_to_process = self.positions[start_index:end_index]
            
            # 更新下次处理的起始索引
            self.last_position_index = end_index if end_index < len(self.positions) else 0
        
        for position in positions_to_process:
            # 更新持仓盈亏
            profit_or_loss = self.update_position_profit_loss(position)
            total_pl = position.get("total_pl", 0) # 获取盈亏比例
            
            # 检查是否需要平仓
            close_reason = None
            
            # 检查持仓时间
            position_duration = int(time.time()) - position["timestamp"]
            if position_duration > self.config.MAX_POSITION_DURATION:
                close_reason = "持仓时间过长"
            
            # 检查止盈
            elif total_pl >= self.config.TAKE_PROFIT_THRESHOLD:
                close_reason = "达到止盈条件"
            
            # 检查止损
            elif total_pl <= self.config.STOP_LOSS_THRESHOLD:
                close_reason = "达到止损条件"
            
            # 检查资金费率变化
            elif position["type"] == "spot_futures":
                exchange_id = position["exchange"]
                symbol = position["symbol"]
                direction = position["direction"]
                
                # 获取最新资金费率
                if exchange_id in self.funding_rates and symbol in self.funding_rates[exchange_id]:
                    current_rate = self.funding_rates[exchange_id][symbol].get("rate")
                    
                    if current_rate is not None:
                        if direction == "long_spot_short_futures" and current_rate < self.config.RATE_DIFF_CLOSE_THRESHOLD:
                            close_reason = "资金费率下降"
                        # elif direction == "short_spot_long_futures" and current_rate > -self.config.RATE_DIFF_CLOSE_THRESHOLD:
                        #     close_reason = "资金费率上升" # 当前策略只做正费率
            
            elif position["type"] == "cross_exchange":
                symbol = position["symbol"]
                long_exchange = position["long_exchange"]
                short_exchange = position["short_exchange"]
                
                # 获取最新资金费率
                if (long_exchange in self.funding_rates and symbol in self.funding_rates[long_exchange] and
                    short_exchange in self.funding_rates and symbol in self.funding_rates[short_exchange]):
                    
                    current_long_rate = self.funding_rates[long_exchange][symbol].get("rate")
                    current_short_rate = self.funding_rates[short_exchange][symbol].get("rate")
                    
                    if current_long_rate is not None and current_short_rate is not None:
                        current_rate_diff = current_short_rate - current_long_rate
                        
                        if current_rate_diff < self.config.RATE_DIFF_CLOSE_THRESHOLD:
                            close_reason = "资金费率差异减小"
            
            # 如果需要平仓
            if close_reason:
                logger.info(f"准备平仓: {position}, 原因: {close_reason}")
                positions_to_close.append(position)
        
        # 平仓
        for position in positions_to_close:
            self.close_position(position)
            # 从持仓列表中移除已平仓的仓位
            try:
                self.positions.remove(position)
            except ValueError:
                logger.warning(f"尝试移除不存在的持仓: {position}")
    
    def save_data_to_csv(self):
        """保存数据到CSV文件"""
        if not self.config.SAVE_TO_CSV:
            return
            
        try:
            # 保存资金费率
            funding_rates_data = []
            for exchange_id, rates in self.funding_rates.items():
                for symbol, rate_info in rates.items():
                    funding_rates_data.append({
                        "exchange": exchange_id,
                        "symbol": symbol,
                        "rate": rate_info.get("rate"),
                        "timestamp": rate_info.get("timestamp")
                    })
            
            if funding_rates_data:
                funding_rates_df = pd.DataFrame(funding_rates_data)
                funding_rates_df.to_csv(f"{self.config.CSV_DIR}/funding_rates_{int(time.time())}.csv", index=False)
                logger.info(f"已保存资金费率数据，共 {len(funding_rates_data)} 条")
            
            # 保存套利机会
            if self.opportunities:
                opportunities_df = pd.DataFrame(self.opportunities)
                opportunities_df.to_csv(f"{self.config.CSV_DIR}/opportunities_{int(time.time())}.csv", index=False)
                logger.info(f"已保存套利机会数据，共 {len(self.opportunities)} 条")
            
            # 保存持仓
            if self.positions:
                positions_df = pd.DataFrame(self.positions)
                positions_df.to_csv(f"{self.config.CSV_DIR}/positions_{int(time.time())}.csv", index=False)
                logger.info(f"已保存持仓数据，共 {len(self.positions)} 条")
        
        except Exception as e:
            logger.error(f"保存数据到CSV失败: {str(e)}")

    # 状态栏显示功能
    def fetch_all_balances(self):
        """获取所有交易所的账户余额 (现货和合约)"""
        balances = {}
        # 获取现货交易所余额
        for exchange_id, exchange in self.spot_exchanges.items():
            try:
                balance = exchange.fetch_balance()
                if balance:
                    balances[f"{exchange_id}_spot"] = balance # 存储完整余额信息
                # logger.info(f"成功获取 {exchange_id} 现货账户余额") # 减少日志
            except Exception as e:
                logger.error(f"获取 {exchange_id} 现货账户余额失败: {str(e)}")
                balances[f"{exchange_id}_spot"] = None # 标记获取失败
                self.exchange_errors[exchange_id] = f"获取现货账户余额失败: {str(e)}"

        # 获取合约交易所余额
        for exchange_id, exchange in self.futures_exchanges.items():
            try:
                # 注意：部分交易所区分合约账户类型 (如币本位/U本位)，这里简化处理
                balance = exchange.fetch_balance()
                if balance:
                    balances[f"{exchange_id}_futures"] = balance # 存储完整余额信息
                # logger.info(f"成功获取 {exchange_id} 合约账户余额") # 减少日志
            except Exception as e:
                logger.error(f"获取 {exchange_id} 合约账户余额失败: {str(e)}")
                balances[f"{exchange_id}_futures"] = None # 标记获取失败
                self.exchange_errors[exchange_id] = f"获取合约账户余额失败: {str(e)}"

        return balances

    def calculate_position_profits(self):
        """计算所有持仓的当前盈亏，并将结果存储在position字典的profit键中"""
        updated_positions = []
        for position in self.positions:
            try:
                # 调用盈亏计算函数
                profit = self.update_position_profit_loss(position)
                position["profit"] = profit # 将计算出的盈亏存入字典
                updated_positions.append(position)
            except Exception as e:
                logger.error(f"计算持仓 {position.get('symbol', '未知')} 盈亏失败: {str(e)}")
                position["profit"] = 0 # 标记计算失败，使用0而不是字符串
                updated_positions.append(position)
        return updated_positions

    def safe_format(self, value, format_str, default="--"):
        """安全格式化函数，处理None值和格式化错误"""
        if value is None:
            return default
        try:
            if isinstance(value, (int, float)):
                return format_str.format(value)
            return str(value)
        except Exception:
            return default

    def update_status_bar(self):
        """更新FMZ状态栏，显示套利机会、账户余额和持仓信息"""
        try:
            # 分离现货套利和跨交易所套利机会
            spot_opportunities = []
            cross_opportunities = []

            # 确保opportunities存在且是列表
            if hasattr(self, "opportunities") and isinstance(self.opportunities, list):
                for opp in self.opportunities:
                    if isinstance(opp, dict):
                        if "exchange" in opp:  # 现货-合约套利
                            spot_opportunities.append(opp)
                        elif "long_exchange" in opp:  # 跨交易所套利
                            cross_opportunities.append(opp)
                    else:
                        logger.warning(f"发现无效的套利机会格式: {opp}")
            else:
                logger.warning("opportunities 不存在或格式不正确")

            # 获取账户余额
            balances = self.fetch_all_balances()

            # 获取持仓信息并计算盈亏
            positions = self.calculate_position_profits()

            # 格式化数据为表格
            tables = []
            
            # 添加交易所错误信息显示
            if self.exchange_errors:
                error_rows = []
                for exchange_id, error_msg in self.exchange_errors.items():
                    error_rows.append([exchange_id, error_msg])
                
                if error_rows:
                    exchange_error_table = {
                        "type": "table",
                        "title": "交易所错误信息",
                        "cols": ["交易所", "错误信息"],
                        "rows": error_rows
                    }
                    tables.append(exchange_error_table)
                    # 显示一次后清除
                    self.exchange_errors = {}
            
            # 添加上次运行错误信息显示
            if self.last_error:
                error_table = {
                    "type": "table",
                    "title": "上次错误信息",
                    "cols": ["时间", "错误"],
                    "rows": [[_D(), str(self.last_error)]]
                }
                tables.append(error_table)
                self.last_error = None # 显示一次后清除

            # 现货-合约套利表格
            if spot_opportunities:
                spot_table = {
                    "type": "table",
                    "title": "现货-合约套利机会",
                    "cols": ["交易所", "交易对", "方向", "资金费率", "现货价", "合约价", "价差%", "预期利润%"],
                    "rows": []
                }
                for opp in spot_opportunities:
                    spot_table["rows"].append([
                        opp.get("exchange", "--"),
                        opp.get("symbol", "--"),
                        opp.get("direction", "--"),
                        self.safe_format(opp.get("funding_rate"), "{:.6f}"),
                        self.safe_format(opp.get("spot_price"), "{:.4f}"),
                        self.safe_format(opp.get("futures_price"), "{:.4f}"),
                        self.safe_format(opp.get("price_diff", 0) * 100, "{:.2f}%"),
                        self.safe_format(opp.get("expected_profit", 0) * 100, "{:.4f}%")
                    ])
                tables.append(spot_table)

            # 跨交易所套利表格
            if cross_opportunities:
                cross_table = {
                    "type": "table",
                    "title": "跨交易所套利机会",
                    "cols": ["交易对", "做多交易所", "做空交易所", "做多费率", "做空费率", "费率差", "做多价", "做空价", "价差%", "预期利润%"],
                    "rows": []
                }
                for opp in cross_opportunities:
                    cross_table["rows"].append([
                        opp.get("symbol", "--"),
                        opp.get("long_exchange", "--"),
                        opp.get("short_exchange", "--"),
                        self.safe_format(opp.get("long_rate"), "{:.6f}"),
                        self.safe_format(opp.get("short_rate"), "{:.6f}"),
                        self.safe_format(opp.get("rate_diff"), "{:.6f}"),
                        self.safe_format(opp.get("long_price"), "{:.4f}"),
                        self.safe_format(opp.get("short_price"), "{:.4f}"),
                        self.safe_format(opp.get("price_diff", 0) * 100, "{:.2f}%"),
                        self.safe_format(opp.get("expected_profit", 0) * 100, "{:.4f}%")
                    ])
                tables.append(cross_table)

            # 账户余额表格
            if balances:
                balance_table = {
                    "type": "table",
                    "title": "交易所账户余额 (USDT为主)",
                    "cols": ["交易所账户", "可用USDT", "总USDT", "总资产估值(USDT)"],
                    "rows": []
                }
                total_estimated_value = 0
                for account_id, bal_data in balances.items():
                    if bal_data is None: # 跳过获取失败的账户
                        balance_table["rows"].append([account_id, "获取失败", "获取失败", "获取失败"])
                        continue

                    usdt_free = bal_data.get("free", {}).get("USDT", 0)
                    usdt_total = bal_data.get("total", {}).get("USDT", 0)
                    # 简单估值：仅计算USDT总额，实际应考虑所有币种价值
                    estimated_value = usdt_total
                    total_estimated_value += estimated_value # 累加总估值

                    balance_table["rows"].append([
                        account_id,
                        self.safe_format(usdt_free, "{:.2f}"),
                        self.safe_format(usdt_total, "{:.2f}"),
                        self.safe_format(estimated_value, "{:.2f}")
                    ])
                # 添加总计行
                balance_table["rows"].append(["---", "---", "---", "---"]) # 分隔符
                balance_table["rows"].append(["总计", "", "", self.safe_format(total_estimated_value, "{:.2f}")])
                tables.append(balance_table)

            # 持仓信息表格
            if positions:
                position_table = {
                    "type": "table",
                    "title": "持仓信息",
                    "cols": ["类型", "交易所/对", "交易对", "方向/数量", "开仓均价", "当前盈亏(USDT)", "持仓时间(H)"],
                    "rows": []
                }
                current_time = time.time()
                for pos in positions:
                    duration_hours = (current_time - pos.get("timestamp", current_time)) / 3600
                    
                    if pos.get("type") == "spot_futures":
                        position_table["rows"].append([
                            "现货-合约",
                            pos.get("exchange", "--"),
                            pos.get("symbol", "--"),
                            f"{pos.get('direction', '--')} / {self.safe_format(pos.get('amount'), '{:.4f}')}",
                            f"S:{self.safe_format(pos.get('spot_price'), '{:.4f}')} F:{self.safe_format(pos.get('futures_price'), '{:.4f}')}",
                            self.safe_format(pos.get("profit"), "{:.4f}"),
                            self.safe_format(duration_hours, "{:.2f}")
                        ])
                    elif pos.get("type") == "cross_exchange":
                        position_table["rows"].append([
                            "跨交易所",
                            f"{pos.get('long_exchange', '--')} <-> {pos.get('short_exchange', '--')}",
                            pos.get("symbol", "--"),
                            self.safe_format(pos.get('amount'), "{:.4f}"),
                            f"L:{self.safe_format(pos.get('long_price'), '{:.4f}')} S:{self.safe_format(pos.get('short_price'), '{:.4f}')}",
                            self.safe_format(pos.get("profit"), "{:.4f}"),
                            self.safe_format(duration_hours, "{:.2f}")
                        ])
                tables.append(position_table)

            # 构造LogStatus字符串
            if not tables:
                status_msg = f"状态更新于: {_D()} - 无数据"
            else:
               
                try:
                    tables_json_str = json.dumps(tables)
                    status_msg = f"状态更新于: {_D()}\n`{tables_json_str}`"
                except Exception as e:
                    logger.error(f"序列化状态栏表格失败: {str(e)}")
                    status_msg = f"状态更新于: {_D()} - 表格生成错误: {str(e)}"

            # 调用FMZ LogStatus函数
            try:
                LogStatus(status_msg)
                logger.info("状态栏更新成功")
            except NameError:
                logger.error("LogStatus函数未定义。请在FMZ环境中运行此代码。")
            except Exception as e:
                logger.error(f"调用LogStatus失败: {str(e)}")
        except Exception as e:
            logger.error(f"更新状态栏失败: {str(e)}")
            self.last_error = e
    
    def run(self):
        """运行套利策略"""
        logger.info("开始运行套利策略")
        
        while True:
            try:
                # 获取资金费率
                self.funding_rates = self.get_funding_rates()
                
                # 寻找套利机会
                spot_futures_opportunities = []
                cross_exchange_opportunities = []
                
                if self.config.ENABLE_SPOT_FUTURES_ARBITRAGE:
                    spot_futures_opportunities = self.find_spot_futures_arbitrage_opportunities()
                
                if self.config.ENABLE_CROSS_EXCHANGE_ARBITRAGE:
                    cross_exchange_opportunities = self.find_cross_exchange_arbitrage_opportunities()
                
                # 合并所有套利机会
                self.opportunities = spot_futures_opportunities + cross_exchange_opportunities
                
                # 执行套利
                for opportunity in self.opportunities:
                    if "exchange" in opportunity:  # 现货-合约套利
                        self.execute_spot_futures_arbitrage(opportunity)
                    else:  # 跨交易所套利
                        self.execute_cross_exchange_arbitrage(opportunity)
                
                # 管理持仓
                self.manage_positions()
                
                # 保存数据
                self.save_data_to_csv()
                
                # 更新状态栏
                try:
                    self.update_status_bar()
                except Exception as e:
                    logger.error(f"更新状态栏失败: {str(e)}")
                    self.last_error = e
                
                # 等待下一次刷新
                logger.info(f"等待 {self.config.REFRESH_INTERVAL} 秒后刷新")
                time.sleep(self.config.REFRESH_INTERVAL)
            
            except Exception as e:
                self.last_error = e # 记录错误以便在状态栏显示
                logger.error(f"运行套利策略出错: {str(e)}")
                # 即使出错，也尝试更新状态栏显示错误信息
                try:
                    self.update_status_bar()
                except Exception as status_e:
                    logger.error(f"在错误处理中更新状态栏失败: {str(status_e)}")
                time.sleep(10)  # 出错后等待10秒再重试


def _D():
    """返回当前时间的格式化字符串"""
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")



# --- FMZ平台入口函数 ---
def main():
    # 初始化配置
    config = Config()
    
    # 创建套利实例
    arbitrage = MultiExchangeArbitrage(config)
    
    # 运行套利策略
    arbitrage.run()


