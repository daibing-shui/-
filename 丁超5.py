import math
import sys
import os
import pandas as pd
import numpy as np
from datetime import datetime, timedelta
from PyQt5.QtWidgets import (QApplication, QMainWindow, QFileDialog, QPushButton,
                             QVBoxLayout, QHBoxLayout, QWidget, QLabel, QComboBox,
                             QTableView, QCheckBox, QProgressBar, QMessageBox,
                             QGroupBox, QSpinBox, QTabWidget, QGridLayout, QHeaderView,
                             QLineEdit, QStatusBar, QScrollArea, QFrame, QSplitter,
                             QToolBar, QAction, QMenu, QToolButton, QDockWidget, QDoubleSpinBox)
from PyQt5.QtCore import Qt, QAbstractTableModel, QThread, pyqtSignal, QSize
from PyQt5.QtGui import QColor, QPalette, QIcon, QFont, QBrush
import matplotlib.pyplot as plt
from matplotlib.backends.backend_qt5agg import FigureCanvasQTAgg as FigureCanvas
from matplotlib.figure import Figure
import json
import tempfile
import shutil
import gc
import csv
import geopandas as gpd
from shapely import MultiPolygon
from shapely.geometry import Point, Polygon
import webbrowser
import re
from concurrent.futures import ThreadPoolExecutor, ProcessPoolExecutor, as_completed
import multiprocessing
import pickle
import warnings
warnings.filterwarnings('ignore')
print(123)
# 确保在Windows上正确使用多进程
if sys.platform.startswith('win'):
    multiprocessing.freeze_support()

# 44列数据源列名
COLUMN_NAMES = [
    "采样时间", "网络类型", "MCC", "运营商", "小区ID", "CI", "PCI", "EARFCN", "Band", "TAC",
    "RSRP", "SINR", "RSSI", "RSRQ", "邻区RSRP列表", "邻区PCI列表", "邻区频点列表", "数据列1", "数据列2",
    "数据列3", "数据列4", "数据列5", "数据列6", "数据列7", "数据列8", "数据列9", "数据列10",
    "数据列11", "加密信息", "终端品牌", "终端机型", "数据列15", "经度（WGS84）", "纬度（WGS84）", "定位方式", "室内外",
    "距离", "服务小区名", "服务小区MAC", "服务小区信号强度", "服务小区运营商", "SIM卡数量", "SIM卡1运营商", "SIM卡2运营商"
]
# 51列数据源列名（替换为真实OTT数据字段名称）
COLUMN_NAMES_51 = [
    "ts", "dynamic_network_type", "opt_id", "opt_source", "cell_id", "lac_id", "clinsite",
    "enbid", "pci", "lte_earfcn", "rsrp", "sinr", "rssi", "rsrq", "neighbor_rsrp_list",
    "neighbor_pci_list", "neighbor_earfcn_list", "nr_pci", "nr_earfcn", "nr_ssb_rsrp",
    "nr_csi_rsrp", "nr_rsrq", "nr_rssi", "nr_ssb_sinr", "nr_csi_sinr", "nr_neighbor_rsrp_list",
    "nr_neighbor_pci_list", "nr_neighbor_earfcn_list", "DID", "brand", "model",
    "android_ver", "app_list", "wifi_name", "is_wifi_mobile", "wifi_mac", "wifi_std",
    "wifi_strenth", "carrier", "lgt", "ltt", "geo_from", "in_out_door", "asulevel",
    "dual_sim", "main_opt", "attach_opt", "gps_alt", "url_ping", "download", "upload"
]

# 场景类型映射
SCENE_MAPPING = {
    '高等学校': 'education',
    '交通枢纽': 'transport',
    '商务楼宇及酒店': 'business',
    '文旅场景': 'tourism',
    '医疗机构': 'medical',
    '政务中心': 'government',
    '重点商超': 'shopping',
    '住宅小区': 'residential'
}


def print_debug(message):
    """处理中文编码问题的调试输出"""
    try:
        # 尝试使用GBK编码输出
        print(message.encode('gbk', errors='replace').decode('gbk'))
    except:
        # 回退到原始输出
        print(message)


# 多进程处理函数 - 必须在全局作用域定义
def process_grid_chunk_worker(args):
    """多进程工作函数 - 处理单个数据块"""
    try:
        (temp_file, required_columns, min_lng, min_lat, max_lng, max_lat,
         grid_size_degrees, lng_grids, lat_grids, aoi_polygons_data,
         building_polygons_data, filter_aoi, lon_offset, lat_offset,
         data_source_type, aoi_names, building_names, aoi_scene_mapping) = args

        # 反序列化多边形数据
        aoi_polygons = {}
        for name, poly_wkt in aoi_polygons_data.items():
            from shapely import wkt
            aoi_polygons[name] = wkt.loads(poly_wkt)

        building_polygons = {}
        for name, poly_wkt in building_polygons_data.items():
            from shapely import wkt
            building_polygons[name] = wkt.loads(poly_wkt)

        # 初始化数据结构
        operators = ['mobile', 'unicom', 'telecom']
        networks = ['4g', '5g']

        grid_data = {}
        for operator in operators:
            grid_data[operator] = {}
            for network in networks:
                grid_data[operator][network] = {
                    'data': np.full((lat_grids, lng_grids), np.nan),
                    'count': np.zeros((lat_grids, lng_grids))
                }

        # 初始化统计信息
        aoi_stats = {}
        for name in aoi_names:
            aoi_stats[name] = {
                'mobile': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                           '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                'unicom': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                           '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                'telecom': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                            '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                'total': 0
            }

        building_stats = {}
        for name in building_names:
            building_stats[name] = {
                'mobile': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                           '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                'unicom': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                           '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                'telecom': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                            '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                'total': 0,
                'rsrp_sum': 0.0
            }

        chunk_stats = {
            'total_rows': 0,
            'valid_rows': 0,
            'terminal_brands': {},
            'terminal_models': {},
            'operators': {
                'mobile': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                           '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                'unicom': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                           '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                'telecom': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                            '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}}
            },
            'scenes': {scene: {'count': 0, 'rsrp_4g_sum': 0.0, 'rsrp_5g_sum': 0.0, 'weak_4g': 0, 'weak_5g': 0}
                       for scene in SCENE_MAPPING.values()}
        }

        # 读取数据块
        chunk = pd.read_parquet(temp_file)
        chunk_stats['total_rows'] = len(chunk)

        # 数据预处理
        current_data = chunk.copy()

        # 根据数据源类型设置列名
        if data_source_type == 51:
            basic_required_cols = ['lgt', 'ltt', 'opt_source', 'dynamic_network_type']
            lon_col, lat_col = 'lgt', 'ltt'
            operator_col = 'opt_source'
            network_col = 'dynamic_network_type'
            terminal_brand_col = 'brand'
            terminal_model_col = 'model'
        else:
            basic_required_cols = ['经度（WGS84）', '纬度（WGS84）', '运营商', '网络类型']
            lon_col, lat_col = '经度（WGS84）', '纬度（WGS84）'
            operator_col = '运营商'
            network_col = '网络类型'
            terminal_brand_col = '终端品牌'
            terminal_model_col = '终端机型'

        # 检查必要列
        missing_columns = [col for col in basic_required_cols if col not in current_data.columns]
        if missing_columns:
            return grid_data, aoi_stats, building_stats, chunk_stats

        # 过滤和转换数据
        for col in basic_required_cols:
            current_data = current_data.dropna(subset=[col])

        if len(current_data) == 0:
            return grid_data, aoi_stats, building_stats, chunk_stats

        current_data[lon_col] = pd.to_numeric(current_data[lon_col], errors='coerce')
        current_data[lat_col] = pd.to_numeric(current_data[lat_col], errors='coerce')

        if data_source_type == 51:
            if 'rsrp' in current_data.columns:
                current_data['rsrp'] = pd.to_numeric(current_data['rsrp'], errors='coerce')
            if 'nr_ssb_rsrp' in current_data.columns:
                current_data['nr_ssb_rsrp'] = pd.to_numeric(current_data['nr_ssb_rsrp'], errors='coerce')
        else:
            if 'RSRP' in current_data.columns:
                current_data['RSRP'] = pd.to_numeric(current_data['RSRP'], errors='coerce')

        current_data[operator_col] = current_data[operator_col].astype(str)
        valid_data = current_data.dropna(subset=[lon_col, lat_col])
        chunk_stats['valid_rows'] = len(valid_data)

        if len(valid_data) == 0:
            return grid_data, aoi_stats, building_stats, chunk_stats

        # 处理数据点
        for idx, row in valid_data.iterrows():
            try:
                lng = float(row[lon_col]) + lon_offset
                lat = float(row[lat_col]) + lat_offset
                operator = str(row[operator_col]).lower()
                net_type = str(row[network_col])

                # 获取RSRP值
                rsrp = None
                net_key = '4g'

                if data_source_type == 51:
                    if '5G_SA' in net_type or '5G_NSA' in net_type:
                        rsrp = row.get('nr_ssb_rsrp', np.nan)
                        net_key = '5g'
                    else:
                        rsrp = row.get('rsrp', np.nan)
                        net_key = '4g'
                else:
                    rsrp = row.get('RSRP', np.nan)
                    net_key = '5g' if '5g' in net_type.lower() else '4g'

                if pd.isna(rsrp):
                    continue

                try:
                    rsrp = float(rsrp)
                except:
                    continue

                # 标准化运营商名称
                operator_key = 'mobile'
                if 'unicom' in operator or '联通' in operator:
                    operator_key = 'unicom'
                elif 'telecom' in operator or '电信' in operator:
                    operator_key = 'telecom'
                elif '移动' in operator:
                    operator_key = 'mobile'

                # 检查边界
                in_bounds = (min_lng <= lng <= max_lng and min_lat <= lat <= max_lat)
                if not in_bounds:
                    continue

                # 创建点对象
                point_obj = Point(lng, lat)

                # 检查AOI
                point_in_aoi = False
                aoi_name = None
                if aoi_polygons:
                    for name, polygon in aoi_polygons.items():
                        try:
                            if polygon.contains(point_obj):
                                point_in_aoi = True
                                aoi_name = name
                                break
                        except:
                            continue

                # 先处理建筑物统计（不受AOI筛选影响）
                building_name = None
                if building_polygons:
                    for name, polygon in building_polygons.items():
                        try:
                            if polygon.contains(point_obj):
                                building_name = name
                                break
                        except:
                            continue

                if building_name and building_name in building_stats:
                    stats = building_stats[building_name]
                    stats['total'] += 1
                    stats['rsrp_sum'] += rsrp
                    stats[operator_key][net_key]['total'] += 1
                    stats[operator_key][net_key]['rsrp_sum'] += rsrp

                    weak_threshold = -115 if net_key == '4g' else -110
                    if rsrp < weak_threshold:
                        stats[operator_key][net_key]['weak'] += 1

                # 对于栅格和AOI统计，应用AOI筛选
                if filter_aoi and not point_in_aoi:
                    continue

                # 计算网格索引
                lng_idx = int((lng - min_lng) / grid_size_degrees)
                lat_idx = int((lat - min_lat) / grid_size_degrees)

                if 0 <= lng_idx < lng_grids and 0 <= lat_idx < lat_grids:
                    if np.isnan(grid_data[operator_key][net_key]['data'][lat_idx, lng_idx]):
                        grid_data[operator_key][net_key]['data'][lat_idx, lng_idx] = rsrp
                        grid_data[operator_key][net_key]['count'][lat_idx, lng_idx] = 1
                    else:
                        grid_data[operator_key][net_key]['data'][lat_idx, lng_idx] += rsrp
                        grid_data[operator_key][net_key]['count'][lat_idx, lng_idx] += 1

                # 更新统计信息
                chunk_stats['operators'][operator_key][net_key]['total'] += 1
                chunk_stats['operators'][operator_key][net_key]['rsrp_sum'] += rsrp

                weak_threshold = -115 if net_key == '4g' else -110
                if rsrp < weak_threshold:
                    chunk_stats['operators'][operator_key][net_key]['weak'] += 1

                # 统计终端品牌和型号
                terminal_brand = str(row.get(terminal_brand_col, '未知')).strip()
                if terminal_brand and terminal_brand != '未知' and terminal_brand != 'nan':
                    chunk_stats['terminal_brands'][terminal_brand] = chunk_stats['terminal_brands'].get(terminal_brand,
                                                                                                        0) + 1

                terminal_model = str(row.get(terminal_model_col, '未知')).strip()
                if terminal_model and terminal_model != '未知' and terminal_model != 'nan':
                    chunk_stats['terminal_models'][terminal_model] = chunk_stats['terminal_models'].get(terminal_model,
                                                                                                        0) + 1

                # 更新AOI统计
                if aoi_name and aoi_name in aoi_stats:
                    stats = aoi_stats[aoi_name]
                    stats['total'] += 1
                    stats[operator_key][net_key]['total'] += 1
                    stats[operator_key][net_key]['rsrp_sum'] += rsrp

                    if rsrp < weak_threshold:
                        stats[operator_key][net_key]['weak'] += 1

                    # 更新场景统计
                    scene_type = aoi_scene_mapping.get(aoi_name)
                    if scene_type:
                        scene_stats = chunk_stats['scenes'][scene_type]
                        scene_stats['count'] += 1
                        if net_key == '4g':
                            scene_stats['rsrp_4g_sum'] += rsrp
                            if rsrp < weak_threshold:
                                scene_stats['weak_4g'] += 1
                        else:
                            scene_stats['rsrp_5g_sum'] += rsrp
                            if rsrp < weak_threshold:
                                scene_stats['weak_5g'] += 1

            except Exception as e:
                continue

        return grid_data, aoi_stats, building_stats, chunk_stats

    except Exception as e:
        print_debug(f"[ERROR] Worker进程出错: {e}")
        import traceback
        print_debug(f"[ERROR] 详细错误: {traceback.format_exc()}")
        # 返回空结果
        return {}, {}, {}, {}
class PandasModel(QAbstractTableModel):
    """用于在QTableView中显示pandas DataFrame的模型"""

    def __init__(self, data):
        super().__init__()
        self._data = data

    def rowCount(self, parent=None):
        return len(self._data)

    def columnCount(self, parent=None):
        return len(self._data.columns)

    def data(self, index, role=Qt.DisplayRole):
        if role == Qt.DisplayRole:
            value = self._data.iloc[index.row(), index.column()]
            return str(value)
        elif role == Qt.BackgroundRole:
            # 为特定列添加背景色
            col_name = self._data.columns[index.column()]

            # 处理RSRP列（44列数据源）
            if col_name == 'RSRP':
                try:
                    rsrp = float(self._data.iloc[index.row(), index.column()])
                    if rsrp > -70:
                        return QBrush(QColor(0, 255, 0, 30))  # 浅绿色
                    elif rsrp > -90:
                        return QBrush(QColor(255, 255, 0, 30))  # 浅黄色
                    elif rsrp > -110:
                        return QBrush(QColor(255, 165, 0, 30))  # 浅橙色
                    else:
                        return QBrush(QColor(255, 0, 0, 30))  # 浅红色
                except:
                    pass

            # 处理RSRP_4G列（51列数据源）
            elif col_name == 'RSRP_4G':
                try:
                    rsrp = float(self._data.iloc[index.row(), index.column()])
                    if rsrp > -70:
                        return QBrush(QColor(0, 255, 0, 30))  # 浅绿色
                    elif rsrp > -90:
                        return QBrush(QColor(255, 255, 0, 30))  # 浅黄色
                    elif rsrp > -110:
                        return QBrush(QColor(255, 165, 0, 30))  # 浅橙色
                    else:
                        return QBrush(QColor(255, 0, 0, 30))  # 浅红色
                except:
                    pass

            # 处理RSRP_5G列（51列数据源）
            elif col_name == 'RSRP_5G':
                try:
                    rsrp = float(self._data.iloc[index.row(), index.column()])
                    if rsrp > -65:
                        return QBrush(QColor(0, 255, 0, 30))  # 浅绿色
                    elif rsrp > -85:
                        return QBrush(QColor(255, 255, 0, 30))  # 浅黄色
                    elif rsrp > -105:
                        return QBrush(QColor(255, 165, 0, 30))  # 浅橙色
                    else:
                        return QBrush(QColor(255, 0, 0, 30))  # 浅红色
                except:
                    pass

            # 处理SINR列
            elif col_name == 'SINR':
                try:
                    sinr = float(self._data.iloc[index.row(), index.column()])
                    if sinr > 15:
                        return QBrush(QColor(0, 255, 0, 30))  # 浅绿色
                    elif sinr > 0:
                        return QBrush(QColor(255, 255, 0, 30))  # 浅黄色
                    else:
                        return QBrush(QColor(255, 0, 0, 30))  # 浅红色
                except:
                    pass
        return None

    def headerData(self, section, orientation, role=Qt.DisplayRole):
        if orientation == Qt.Horizontal and role == Qt.DisplayRole:
            return str(self._data.columns[section])
        if orientation == Qt.Vertical and role == Qt.DisplayRole:
            return str(self._data.index[section])
        return None


class DataLoaderThread(QThread):
    """数据加载线程，支持多种数据源格式"""
    progress_update = pyqtSignal(int, str)
    data_loaded = pyqtSignal(list, list, dict, list)  # 增加列名参数

    def __init__(self, file_paths, data_source_type=44, chunk_size=5000):
        super().__init__()
        self.file_paths = file_paths
        self.chunk_size = chunk_size
        self.data_source_type = data_source_type  # 44列或51列
        self.temp_dir = tempfile.mkdtemp(prefix="ott_mr_")
        self.file_row_counts = {}
        # 根据数据源类型设置列名
        self.column_names = COLUMN_NAMES if data_source_type == 44 else COLUMN_NAMES_51

    def run(self):
        try:
            total_size = sum(os.path.getsize(file_path) for file_path in self.file_paths)
            processed_size = 0
            loaded_files = []
            temp_files = []
            self.file_row_counts = {}

            for file_idx, file_path in enumerate(self.file_paths):
                file_name = os.path.basename(file_path)
                self.progress_update.emit(5, f"正在加载 {file_name}...")

                file_size = os.path.getsize(file_path)
                file_processed_size = 0
                self.file_row_counts[file_name] = 0

                # 使用pandas的chunksize参数实现懒加载
                for chunk_idx, chunk in enumerate(
                        pd.read_csv(file_path, sep='\t', header=None, chunksize=self.chunk_size,
                                    low_memory=False, on_bad_lines='warn')):
                    # 修复列数不一致的问题
                    num_columns = len(self.column_names)

                    # 如果实际列数多于预期
                    if len(chunk.columns) > num_columns:
                        # 只保留前num_columns列
                        chunk = chunk.iloc[:, :num_columns]
                        print_debug(f"警告: 文件 {file_name} 分块 {chunk_idx} 有 {len(chunk.columns)} 列，"
                                    f"超过预期的 {num_columns} 列，已截断")

                    # 如果实际列数少于预期
                    elif len(chunk.columns) < num_columns:
                        # 添加缺失列
                        missing = num_columns - len(chunk.columns)
                        for i in range(missing):
                            chunk[f'缺失列_{i}'] = np.nan

                    # 更新列名
                    chunk.columns = self.column_names[:len(chunk.columns)]

                    # 处理日期时间列
                    if '采样时间' in chunk.columns:
                        try:
                            chunk['采样时间'] = pd.to_datetime(chunk['采样时间'])
                        except:
                            print(f"解析采样时间失败: {file_name} 分块 {chunk_idx}")
                            chunk['采样时间'] = pd.NaT

                    # 记录文件名
                    chunk['文件名'] = file_name

                    # 更新文件行数统计
                    self.file_row_counts[file_name] += len(chunk)

                    # 保存分块到临时文件
                    temp_file = os.path.join(self.temp_dir, f"{file_idx}_{chunk_idx}.parquet")
                    chunk.to_parquet(temp_file)
                    temp_files.append(temp_file)

                    # 更新进度
                    chunk_size_bytes = os.path.getsize(temp_file)
                    file_processed_size += chunk_size_bytes
                    processed_size += chunk_size_bytes

                    progress = int((processed_size / total_size) * 100)
                    self.progress_update.emit(progress,
                                              f"正在加载 {file_name}... 分块 {chunk_idx + 1} ({int((file_processed_size / file_size) * 100)}%)")

                    del chunk
                    gc.collect()

                loaded_files.append(file_name)

            self.data_loaded.emit(temp_files, loaded_files, self.file_row_counts, self.column_names)

        except Exception as e:
            print(f"加载数据时出错: {e}")
            self.data_loaded.emit([], [], {}, [])


class DataProcessorThread(QThread):
    """数据处理线程，避免UI卡顿（使用多线程并行处理）"""
    progress_update = pyqtSignal(int, str)
    process_complete = pyqtSignal(str)  # 返回处理后的临时目录路径
    error_occurred = pyqtSignal(str)

    def __init__(self, temp_files, output_dir=None, time_interval=None, output_format=None,
                 selected_columns=None, remove_duplicates=False, remove_nan=False,
                 ignore_unselected=False):
        super().__init__()
        self.temp_files = temp_files
        self.output_dir = output_dir
        self.time_interval = time_interval
        self.output_format = output_format
        self.selected_columns = selected_columns
        self.remove_duplicates = remove_duplicates
        self.remove_nan = remove_nan
        self.ignore_unselected = ignore_unselected  # 新增参数：是否忽略未选中列
        self.processed_dir = tempfile.mkdtemp(prefix="ott_mr_processed_")  # 创建处理后的临时目录
        self.xlsx_data = {}  # 新增：用于存储XLSX格式的数据块

    def run(self):
        try:
            # 1. 数据清理部分
            total_chunks = len(self.temp_files)
            processed_chunks = 0

            # 创建用于存储处理后的临时文件列表
            processed_files = []

            for temp_file in self.temp_files:
                # 读取临时文件
                chunk = pd.read_parquet(temp_file)

                # 如果不忽略未选中列，只基于选中列进行过滤，但保留所有列
                if not self.ignore_unselected and self.selected_columns:
                    # 创建一个基于选中列的掩码
                    mask = pd.Series(True, index=chunk.index)

                    # 对选中列进行空值检查
                    if self.remove_nan:
                        mask &= chunk[self.selected_columns].notna().all(axis=1)

                    # 应用掩码
                    chunk = chunk[mask]

                    # 移除重复行
                    if self.remove_duplicates:
                        chunk = chunk.drop_duplicates()
                else:
                    # 原始逻辑：只保留选中的列并进行处理
                    if self.selected_columns:
                        # 只保留选中的列
                        chunk = chunk[self.selected_columns]

                    if self.remove_duplicates:
                        # 移除重复行
                        chunk = chunk.drop_duplicates()

                    if self.remove_nan and self.selected_columns:
                        # 删除所选列中包含空值的行
                        chunk = chunk.dropna(subset=self.selected_columns)

                # 保存处理后的分块
                processed_file = os.path.join(self.processed_dir, os.path.basename(temp_file))
                chunk.to_parquet(processed_file)
                processed_files.append(processed_file)

                # 更新进度
                processed_chunks += 1
                progress = int((processed_chunks / total_chunks) * 50)  # 清理阶段占50%
                self.progress_update.emit(progress, f"数据清理中... ({processed_chunks}/{total_chunks})")

                # 释放内存
                del chunk
                gc.collect()

            # 2. 时间分割部分（如果需要）
            if self.output_dir and self.time_interval:
                # 确保输出目录存在
                os.makedirs(self.output_dir, exist_ok=True)

                # 获取最小和最大时间
                min_time = None
                max_time = None

                # 第一遍：确定时间范围
                for processed_file in processed_files:
                    chunk = pd.read_parquet(processed_file)
                    if '采样时间' in chunk.columns:
                        chunk_min = chunk['采样时间'].min()
                        chunk_max = chunk['采样时间'].max()

                        if min_time is None or chunk_min < min_time:
                            min_time = chunk_min
                        if max_time is None or chunk_max > max_time:
                            max_time = chunk_max

                    del chunk
                    gc.collect()

                if min_time is None or max_time is None:
                    self.progress_update.emit(100, "错误: 数据中没有'采样时间'列")
                    self.error_occurred.emit("数据中没有'采样时间'列")
                    return

                # 计算时间间隔
                if self.time_interval == '1小时':
                    delta = timedelta(hours=1)
                elif self.time_interval == '5小时':
                    delta = timedelta(hours=5)
                elif self.time_interval == '12小时':
                    delta = timedelta(hours=12)
                elif self.time_interval == '1天':
                    delta = timedelta(days=1)
                else:
                    delta = timedelta(hours=1)  # 默认1小时

                # 计算需要分割的块数
                total_blocks = int((max_time - min_time) / delta) + 1
                current_block = 0
                self.progress_update.emit(50, f"开始时间分割，共{total_blocks}个时间段...")

                # 为每个时间段创建输出文件
                time_files = {}
                current_time = min_time
                while current_time <= max_time:
                    end_time = current_time + delta

                    # 生成输出文件名
                    if self.time_interval == '1小时':
                        time_str = current_time.strftime('%Y-%m-%d_%H')
                    elif self.time_interval == '5小时':
                        time_str = current_time.strftime('%Y-%m-%d_%H') + f"_{current_time.hour + 5}"
                    elif self.time_interval == '12小时':
                        time_str = current_time.strftime('%Y-%m-%d_%H') + f"_{current_time.hour + 12}"
                    elif self.time_interval == '1天':
                        time_str = current_time.strftime('%Y-%m-%d')
                    else:
                        time_str = current_time.strftime('%Y-%m-%d_%H')

                    output_file = os.path.join(self.output_dir, f"OTT_MR_{time_str}")

                    # 根据输出格式确定文件名
                    if self.output_format == 'CSV':
                        output_file += '.csv'
                        # 对于CSV，第一次写入时需要包含表头
                        if not os.path.exists(output_file):
                            with open(output_file, 'w', newline='', encoding='utf-8') as f:
                                writer = csv.writer(f)
                                if self.selected_columns:
                                    writer.writerow(self.selected_columns)
                                else:
                                    writer.writerow(chunk.columns.tolist())
                        time_files[(current_time, end_time)] = output_file
                    elif self.output_format == 'XLSX':
                        output_file += '.xlsx'
                        # 对于XLSX，稍后一次性写入
                        time_files[(current_time, end_time)] = output_file

                    current_time = end_time

                # 第二遍：按时间段处理数据
                for idx, processed_file in enumerate(processed_files):
                    chunk = pd.read_parquet(processed_file)

                    if '采样时间' not in chunk.columns:
                        continue

                    # 将采样时间转换为datetime
                    chunk['采样时间'] = pd.to_datetime(chunk['采样时间'])

                    # 按时间段处理数据
                    for (start_time, end_time), output_file in time_files.items():
                        # 筛选当前时间段的数据
                        mask = (chunk['采样时间'] >= start_time) & (chunk['采样时间'] < end_time)
                        time_chunk = chunk[mask]

                        if not time_chunk.empty:
                            if self.output_format == 'CSV':
                                # 追加数据到CSV
                                time_chunk.to_csv(output_file, mode='a', header=False, index=False)
                            elif self.output_format == 'XLSX':
                                # 对于XLSX，先收集数据，最后一次性写入
                                if output_file not in self.xlsx_data:
                                    self.xlsx_data[output_file] = []
                                self.xlsx_data[output_file].append(time_chunk)

                    # 更新进度
                    current_block += 1
                    progress = 50 + int(((idx + 1) / len(processed_files)) * 50)  # 从50%开始，到100%结束
                    self.progress_update.emit(progress,
                                              f"时间分割中... ({idx + 1}/{len(processed_files)})")

                    # 释放内存
                    del chunk
                    gc.collect()

                # 处理XLSX输出
                if self.output_format == 'XLSX':
                    total_files = len(time_files)
                    processed_files_count = 0
                    for output_file, chunks in self.xlsx_data.items():
                        if chunks:
                            combined = pd.concat(chunks)
                            combined.to_excel(output_file, index=False)
                        processed_files_count += 1
                        progress = 50 + int((processed_files_count / total_files) * 50)
                        self.progress_update.emit(progress, f"保存XLSX文件... ({processed_files_count}/{total_files})")

            # 处理完成，返回处理后的临时目录
            self.process_complete.emit(self.processed_dir)

        except Exception as e:
            print(f"处理数据时出错: {e}")
            self.error_occurred.emit(str(e))


def process_single_point(args):
    """处理单个数据点 - 用于多进程并行处理（修改版）"""
    try:
        (point, min_lng, min_lat, max_lng, max_lat, grid_size_degrees,
         lng_grids, lat_grids, aoi_polygons, building_polygons,
         filter_aoi, lon_offset, lat_offset, data_source_type) = args

        # 提取点数据
        if data_source_type == 51:
            lng = point.get('lgt', 0)
            lat = point.get('ltt', 0)
            net_type = str(point.get('dynamic_network_type', ''))
            operator = point.get('opt_source', '')

            # 根据网络类型获取对应的信号值
            rsrp = None
            if '5G_SA' in net_type or '5G_NSA' in net_type:
                # 5G网络，使用nr_ssb_rsrp
                rsrp = point.get('nr_ssb_rsrp', None)
                net_key = '5g'
            else:  # 4G或其他
                # 4G网络，使用rsrp
                rsrp = point.get('rsrp', None)
                net_key = '4g'

            # 如果信号值为空或无效，跳过该点
            if rsrp is None or pd.isna(rsrp):
                return None

            try:
                rsrp = float(rsrp)
            except:
                return None

        else:
            # 44列数据源保持原有逻辑
            lng = point.get('经度（WGS84）', 0)
            lat = point.get('纬度（WGS84）', 0)
            rsrp = point.get('RSRP', 0)
            operator = point.get('运营商', '')
            net_type = point.get('网络类型', '')
            net_key = '4g' if '4g' not in net_type.lower() else '5g'

        # 应用偏移
        lng += lon_offset
        lat += lat_offset

        # 检查点是否在边界范围内
        in_bounds = (min_lng <= lng <= max_lng and min_lat <= lat <= max_lat)
        point_in_aoi = False
        aoi_name = None
        building_name = None

        # 计算网格索引
        lng_idx = int((lng - min_lng) / grid_size_degrees) if in_bounds else -1
        lat_idx = int((lat - min_lat) / grid_size_degrees) if in_bounds else -1

        # 标准化运营商名称
        operator_key = 'mobile'  # 默认移动
        if 'unicom' in operator.lower() or '联通' in operator:
            operator_key = 'unicom'
        elif 'telecom' in operator.lower() or '电信' in operator:
            operator_key = 'telecom'
        elif '移动' in operator:
            operator_key = 'mobile'

        # 如果不在边界内，直接返回
        if not in_bounds:
            return (lng_idx, lat_idx, rsrp, aoi_name, building_name,
                    operator_key, net_key, in_bounds, point_in_aoi)

        # 创建点对象
        point_obj = Point(lng, lat)

        # 查找点所在的AOI
        for name, polygon in aoi_polygons.items():
            if polygon.contains(point_obj):
                point_in_aoi = True
                aoi_name = name
                break

        # 查找点所在的建筑物
        for name, polygon in building_polygons.items():
            if polygon.contains(point_obj):
                building_name = name
                break

        # 如果点不在任何AOI内但启用了AOI筛选，则跳过
        if filter_aoi and not point_in_aoi and not building_name:
            return (lng_idx, lat_idx, rsrp, aoi_name, building_name,
                    operator_key, net_key, in_bounds, point_in_aoi)

        return (lng_idx, lat_idx, rsrp, aoi_name, building_name,
                operator_key, net_key, in_bounds, point_in_aoi)

    except Exception as e:
        print(f"[ERROR] 处理单点时出错: {e}")
        return None


def process_points_chunk(args):
    """处理数据点块 - 全局函数用于多进程"""
    try:
        (points, min_lng, min_lat, max_lng, max_lat, grid_size_degrees,
         lng_grids, lat_grids, aoi_polygons, building_polygons,
         filter_aoi, lon_offset, lat_offset, data_source_type) = args

        results = []

        for point in points:
            try:
                # 提取点数据
                lng = float(point['经度（WGS84）']) + lon_offset
                lat = float(point['纬度（WGS84）']) + lat_offset
                rsrp = float(point['RSRP'])
                operator = point['运营商']
                net_key = point['网络类型']

                # 检查点是否在边界范围内
                in_bounds = (min_lng <= lng <= max_lng and min_lat <= lat <= max_lat)
                point_in_aoi = False
                aoi_name = None
                building_name = None

                # 计算网格索引
                lng_idx = int((lng - min_lng) / grid_size_degrees) if in_bounds else -1
                lat_idx = int((lat - min_lat) / grid_size_degrees) if in_bounds else -1

                # 标准化运营商名称
                operator_key = 'mobile'  # 默认移动
                if 'unicom' in operator or '联通' in operator:
                    operator_key = 'unicom'
                elif 'telecom' in operator or '电信' in operator:
                    operator_key = 'telecom'

                # 如果不在边界内，直接返回
                if not in_bounds:
                    results.append((lng_idx, lat_idx, rsrp, aoi_name, building_name,
                                    operator_key, net_key, in_bounds, point_in_aoi))
                    continue

                # 创建点对象
                point_obj = Point(lng, lat)

                # 查找点所在的AOI
                for name, polygon in aoi_polygons.items():
                    try:
                        if polygon.contains(point_obj):
                            point_in_aoi = True
                            aoi_name = name
                            break
                    except Exception:
                        continue

                # 查找点所在的建筑物
                for name, polygon in building_polygons.items():
                    try:
                        if polygon.contains(point_obj):
                            building_name = name
                            break
                    except Exception:
                        continue

                # 如果点不在任何AOI内但启用了AOI筛选，则跳过
                if filter_aoi and not point_in_aoi and not building_name:
                    results.append((lng_idx, lat_idx, rsrp, aoi_name, building_name,
                                    operator_key, net_key, in_bounds, point_in_aoi))
                    continue

                results.append((lng_idx, lat_idx, rsrp, aoi_name, building_name,
                                operator_key, net_key, in_bounds, point_in_aoi))

            except Exception as e:
                # 单个点处理失败不影响其他点
                continue

        return results

    except Exception as e:
        print(f"[ERROR] 处理点块时出错: {e}")
        return []


class GridVisualizationThread(QThread):
    """栅格化可视化线程 - 优化版本，使用多进程处理"""
    progress_update = pyqtSignal(int, str)
    grid_ready = pyqtSignal(str, str, str, str)
    error_occurred = pyqtSignal(str)

    def __init__(self, temp_files, shp_path=None, building_shp_path=None, grid_size=0.001, filter_aoi=False,
                 lon_offset=0.0, lat_offset=0.0, discrete_points=None, data_source_type=44):
        super().__init__()
        self.temp_files = temp_files
        self.shp_path = shp_path
        self.building_shp_path = building_shp_path
        self.grid_size = grid_size
        self.filter_aoi = filter_aoi
        self.aoi_polygons = {}
        self.building_polygons = {}
        self.aoi_stats = {}
        self.building_stats = {}
        self.lon_offset = lon_offset
        self.lat_offset = lat_offset
        self.discrete_points = discrete_points or []
        self.output_dir = None
        self.num_cores = max(1, multiprocessing.cpu_count() - 1)
        self.aoi_names = []
        self.building_names = []
        self.scene_aoi_mapping = {}
        self.aoi_scene_mapping = {}
        self.data_source_type = data_source_type
        self.building_gdf = None
        self.stats = {
            "data": {
                "total_rows": 0,
                "valid_rows": 0,
                "building_count": 0,
                "aoi_count": 0,
                "grid_count": 0,
                "discrete_points": 0
            },
            "operators": {
                "mobile": {"4g": {"total": 0, "weak": 0, "rsrp_sum": 0.0},
                           "5g": {"total": 0, "weak": 0, "rsrp_sum": 0.0}},
                "unicom": {"4g": {"total": 0, "weak": 0, "rsrp_sum": 0.0},
                           "5g": {"total": 0, "weak": 0, "rsrp_sum": 0.0}},
                "telecom": {"4g": {"total": 0, "weak": 0, "rsrp_sum": 0.0},
                            "5g": {"total": 0, "weak": 0, "rsrp_sum": 0.0}}
            },
            "scenes": {
                "education": {"count": 0, "avg_rsrp_4g": 0, "avg_rsrp_5g": 0, "weak_coverage_4g": 0,
                              "weak_coverage_5g": 0},
                "transport": {"count": 0, "avg_rsrp_4g": 0, "avg_rsrp_5g": 0, "weak_coverage_4g": 0,
                              "weak_coverage_5g": 0},
                "business": {"count": 0, "avg_rsrp_4g": 0, "avg_rsrp_5g": 0, "weak_coverage_4g": 0,
                             "weak_coverage_5g": 0},
                "tourism": {"count": 0, "avg_rsrp_4g": 0, "avg_rsrp_5g": 0, "weak_coverage_4g": 0,
                            "weak_coverage_5g": 0},
                "medical": {"count": 0, "avg_rsrp_4g": 0, "avg_rsrp_5g": 0, "weak_coverage_4g": 0,
                            "weak_coverage_5g": 0},
                "government": {"count": 0, "avg_rsrp_4g": 0, "avg_rsrp_5g": 0, "weak_coverage_4g": 0,
                               "weak_coverage_5g": 0},
                "shopping": {"count": 0, "avg_rsrp_4g": 0, "avg_rsrp_5g": 0, "weak_coverage_4g": 0,
                             "weak_coverage_5g": 0},
                "residential": {"count": 0, "avg_rsrp_4g": 0, "avg_rsrp_5g": 0, "weak_coverage_4g": 0,
                                "weak_coverage_5g": 0}
            },
            "terminal_brands": {},
            "terminal_models": {},
            "time_distribution": {},
            "aoi_stats": [],
            "building_stats": []
        }

    def run(self):
        try:
            print_debug("=" * 80)
            print_debug("[DEBUG] 开始栅格化可视化线程")
            print_debug(f"[DEBUG] 输入参数:")
            print_debug(f"  - temp_files数量: {len(self.temp_files)}")
            print_debug(f"  - shp_path: {self.shp_path}")
            print_debug(f"  - building_shp_path: {self.building_shp_path}")
            print_debug(f"  - grid_size: {self.grid_size}")
            print_debug(f"  - filter_aoi: {self.filter_aoi}")
            print_debug(f"  - lon_offset: {self.lon_offset}")
            print_debug(f"  - lat_offset: {self.lat_offset}")
            print_debug(f"  - discrete_points数量: {len(self.discrete_points)}")
            print_debug(f"  - data_source_type: {self.data_source_type}")
            print_debug("=" * 80)

            # 创建输出目录
            self.output_dir = tempfile.mkdtemp(prefix="ott_mr_grid_")
            print_debug(f"[DEBUG] 创建输出目录: {self.output_dir}")

            aoi_geojson = ""
            discrete_geojson = ""
            grid_geojson = ""
            building_geojson = ""

            # 1. 处理离散点数据预处理（提前分析）
            print_debug("[DEBUG] ========== 开始离散点数据预处理 ==========")
            self.preprocess_discrete_points()

            # 2. 处理AOI数据
            if self.shp_path:
                print_debug("[DEBUG] ========== 开始处理AOI数据 ==========")
                aoi_geojson = self.process_aoi()
                self.progress_update.emit(5, "AOI数据处理完成")
                print_debug(f"[DEBUG] AOI数据处理完成，输出文件: {aoi_geojson}")
            else:
                print_debug("[DEBUG] 未提供AOI shp文件，跳过AOI处理")

            # 3. 处理建筑物数据
            if self.building_shp_path:
                print_debug("[DEBUG] ========== 开始处理建筑物数据 ==========")
                building_geojson = self.process_buildings()
                self.progress_update.emit(10, "建筑物数据处理完成")
                print_debug(f"[DEBUG] 建筑物数据处理完成，输出文件: {building_geojson}")
            else:
                print_debug("[DEBUG] 未提供建筑物shp文件，跳过建筑物处理")

            # 4. 先处理栅格数据（计算统计信息）
            print_debug("[DEBUG] ========== 开始处理栅格数据 ==========")
            self.process_grid_data_by_operator_and_network()
            self.progress_update.emit(70, "栅格数据处理完成")
            print_debug("[DEBUG] 栅格数据处理完成")

            # 5. 生成按运营商和网络类型分类的建筑物文件
            if self.building_shp_path and self.building_gdf is not None:
                print_debug("[DEBUG] ========== 开始生成分类建筑物文件 ==========")
                self.generate_classified_building_files()
                self.progress_update.emit(85, "分类建筑物文件生成完成")

            # 6. 生成download和upload热力图
            if self.aoi_polygons:
                print_debug("[DEBUG] ========== 开始生成下载/上传热力图 ==========")
                self.generate_throughput_heatmaps()
                self.progress_update.emit(90, "下载/上传热力图生成完成")

            # 7. 再处理离散点（此时统计信息已计算完成）
            if self.discrete_points:
                print_debug("[DEBUG] ========== 开始处理离散点数据 ==========")
                discrete_geojson = self.process_discrete_points()
                self.progress_update.emit(95, "离散点数据处理完成")
                print_debug(f"[DEBUG] 离散点数据处理完成，输出文件: {discrete_geojson}")
            else:
                print_debug("[DEBUG] 没有离散点数据，跳过离散点处理")

            # 8. 保存统计信息
            print_debug("[DEBUG] ========== 开始保存统计信息 ==========")
            self.save_statistics()

            # 发射完成信号
            self.grid_ready.emit(aoi_geojson, discrete_geojson, "", building_geojson)
            self.progress_update.emit(100, "处理完成")
            print_debug("[DEBUG] 栅格化可视化线程完成")
            print_debug("=" * 80)

        except Exception as e:
            print_debug(f"[ERROR] 处理栅格数据时出错: {e}")
            import traceback
            print_debug(f"[ERROR] 详细错误信息: {traceback.format_exc()}")
            self.error_occurred.emit(str(e))

    def process_grid_chunk_by_operator(self, temp_file, required_columns, min_lng, min_lat, max_lng, max_lat,
                                       grid_size_degrees, lng_grids, lat_grids):
        """按运营商和网络类型处理单个数据块（修改版）"""

        # 首先初始化返回数据结构，确保即使出错也有正确的结构
        operators = ['mobile', 'unicom', 'telecom']
        networks = ['4g', '5g']

        # 初始化网格数据结构
        grid_data = {}
        for operator in operators:
            grid_data[operator] = {}
            for network in networks:
                grid_data[operator][network] = {
                    'data': np.full((lat_grids, lng_grids), np.nan),
                    'count': np.zeros((lat_grids, lng_grids))
                }

        # 初始化AOI统计信息结构
        aoi_stats = {}
        for name in self.aoi_names:
            aoi_stats[name] = {
                'mobile': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                           '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                'unicom': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                           '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                'telecom': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                            '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                'total': 0
            }

        # 初始化建筑物统计信息结构
        building_stats = {}
        for name in self.building_names:
            building_stats[name] = {
                'mobile': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                           '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                'unicom': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                           '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                'telecom': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                            '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                'total': 0,
                'rsrp_sum': 0.0
            }

        # 初始化全局统计信息
        chunk_stats = {
            'total_rows': 0,
            'valid_rows': 0,
            'terminal_brands': {},
            'terminal_models': {},
            'operators': {
                'mobile': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                           '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                'unicom': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                           '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                'telecom': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                            '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}}
            },
            'scenes': {scene: {'count': 0, 'rsrp_4g_sum': 0.0, 'rsrp_5g_sum': 0.0, 'weak_4g': 0, 'weak_5g': 0}
                       for scene in SCENE_MAPPING.values()}
        }

        try:
            print_debug(f"[DEBUG] ========== 处理分块: {os.path.basename(temp_file)} ==========")
            chunk = pd.read_parquet(temp_file)
            chunk_stats['total_rows'] = len(chunk)
            print_debug(f"[DEBUG] 分块数据行数: {len(chunk)}")

            # 数据预处理
            current_data = chunk.copy()

            # 根据数据源类型设置基本必需列
            if self.data_source_type == 51:
                basic_required_cols = ['lgt', 'ltt', 'opt_source', 'dynamic_network_type']
                lon_col, lat_col = 'lgt', 'ltt'
                operator_col = 'opt_source'
                network_col = 'dynamic_network_type'
                terminal_brand_col = 'brand'
                terminal_model_col = 'model'
            else:
                basic_required_cols = ['经度（WGS84）', '纬度（WGS84）', '运营商', '网络类型']
                lon_col, lat_col = '经度（WGS84）', '纬度（WGS84）'
                operator_col = '运营商'
                network_col = '网络类型'
                terminal_brand_col = '终端品牌'
                terminal_model_col = '终端机型'

            # 检查必要列是否存在
            missing_columns = [col for col in basic_required_cols if col not in current_data.columns]
            if missing_columns:
                print_debug(f"[ERROR] 数据块中缺少列: {', '.join(missing_columns)}")
                return grid_data, aoi_stats, building_stats

            # 对基本必需列进行空值过滤
            for col in basic_required_cols:
                current_data = current_data.dropna(subset=[col])

            if len(current_data) == 0:
                print_debug(f"[ERROR] 基本列过滤后没有有效数据！")
                return grid_data, aoi_stats, building_stats

            # 转换数据类型
            current_data[lon_col] = pd.to_numeric(current_data[lon_col], errors='coerce')
            current_data[lat_col] = pd.to_numeric(current_data[lat_col], errors='coerce')

            # 对于51列数据，不需要预先转换rsrp和nr_ssb_rsrp，因为会根据网络类型动态选择
            if self.data_source_type == 51:
                if 'rsrp' in current_data.columns:
                    current_data['rsrp'] = pd.to_numeric(current_data['rsrp'], errors='coerce')
                if 'nr_ssb_rsrp' in current_data.columns:
                    current_data['nr_ssb_rsrp'] = pd.to_numeric(current_data['nr_ssb_rsrp'], errors='coerce')
            else:
                if 'RSRP' in current_data.columns:
                    current_data['RSRP'] = pd.to_numeric(current_data['RSRP'], errors='coerce')

            # 标准化运营商
            current_data[operator_col] = current_data[operator_col].astype(str)

            # 最终过滤经纬度
            valid_data = current_data.dropna(subset=[lon_col, lat_col])
            chunk_stats['valid_rows'] = len(valid_data)
            print_debug(f"[DEBUG] 最终有效数据行数: {len(valid_data)}")

            if len(valid_data) == 0:
                print_debug(f"[ERROR] 最终过滤后没有有效数据！")
                return grid_data, aoi_stats, building_stats

            # 处理数据点
            processed_points = 0
            points_in_bounds = 0
            points_in_aoi = 0
            points_in_buildings = 0
            aoi_filtered_points = 0
            skipped_points = 0

            for idx, row in valid_data.iterrows():
                try:
                    # 提取基本信息
                    lng = float(row[lon_col]) + self.lon_offset
                    lat = float(row[lat_col]) + self.lat_offset
                    operator = str(row[operator_col]).lower()
                    net_type = str(row[network_col])

                    # 根据网络类型获取RSRP值
                    rsrp = None
                    net_key = '4g'

                    if self.data_source_type == 51:
                        if '5G_SA' in net_type or '5G_NSA' in net_type:
                            # 5G网络，使用nr_ssb_rsrp
                            rsrp = row.get('nr_ssb_rsrp', np.nan)
                            net_key = '5g'
                        else:
                            # 4G网络，使用rsrp
                            rsrp = row.get('rsrp', np.nan)
                            net_key = '4g'
                    else:
                        # 44列数据源
                        rsrp = row.get('RSRP', np.nan)
                        net_key = '5g' if '5g' in net_type.lower() else '4g'

                    # 如果RSRP值无效，跳过该点
                    if pd.isna(rsrp):
                        skipped_points += 1
                        continue

                    try:
                        rsrp = float(rsrp)
                    except:
                        skipped_points += 1
                        continue

                    # 标准化运营商名称
                    operator_key = 'mobile'  # 默认移动
                    if 'unicom' in operator or '联通' in operator:
                        operator_key = 'unicom'
                    elif 'telecom' in operator or '电信' in operator:
                        operator_key = 'telecom'
                    elif '移动' in operator:
                        operator_key = 'mobile'

                    # 检查点是否在边界范围内
                    in_bounds = (min_lng <= lng <= max_lng and min_lat <= lat <= max_lat)
                    if not in_bounds:
                        continue

                    points_in_bounds += 1

                    # 创建点对象
                    point_obj = Point(lng, lat)

                    # 检查是否需要AOI过滤
                    point_in_aoi = False
                    aoi_name = None
                    if self.aoi_polygons:
                        for name, polygon in self.aoi_polygons.items():
                            try:
                                if polygon.contains(point_obj):
                                    point_in_aoi = True
                                    aoi_name = name
                                    break
                            except Exception:
                                continue

                    # 先处理建筑物统计（不受AOI筛选影响）
                    building_name = None
                    if self.building_polygons:
                        for name, polygon in self.building_polygons.items():
                            try:
                                if polygon.contains(point_obj):
                                    building_name = name
                                    break
                            except Exception:
                                continue

                    if building_name and building_name in building_stats:
                        points_in_buildings += 1
                        stats = building_stats[building_name]
                        stats['total'] += 1
                        stats['rsrp_sum'] += rsrp
                        stats[operator_key][net_key]['total'] += 1
                        stats[operator_key][net_key]['rsrp_sum'] += rsrp

                        weak_threshold = -115 if net_key == '4g' else -110
                        if rsrp < weak_threshold:
                            stats[operator_key][net_key]['weak'] += 1

                    # 对于栅格和AOI统计，应用AOI筛选
                    if self.filter_aoi and not point_in_aoi:
                        aoi_filtered_points += 1
                        continue

                    processed_points += 1

                    # 计算网格索引
                    lng_idx = int((lng - min_lng) / grid_size_degrees)
                    lat_idx = int((lat - min_lat) / grid_size_degrees)

                    # 检查网格索引是否有效
                    if 0 <= lng_idx < lng_grids and 0 <= lat_idx < lat_grids:
                        # 更新网格数据
                        if np.isnan(grid_data[operator_key][net_key]['data'][lat_idx, lng_idx]):
                            grid_data[operator_key][net_key]['data'][lat_idx, lng_idx] = rsrp
                            grid_data[operator_key][net_key]['count'][lat_idx, lng_idx] = 1
                        else:
                            grid_data[operator_key][net_key]['data'][lat_idx, lng_idx] += rsrp
                            grid_data[operator_key][net_key]['count'][lat_idx, lng_idx] += 1

                    # 更新全局统计信息
                    chunk_stats['operators'][operator_key][net_key]['total'] += 1
                    chunk_stats['operators'][operator_key][net_key]['rsrp_sum'] += rsrp

                    # 检查弱覆盖
                    weak_threshold = -115 if net_key == '4g' else -110
                    if rsrp < weak_threshold:
                        chunk_stats['operators'][operator_key][net_key]['weak'] += 1

                    # 统计终端品牌
                    terminal_brand = str(row.get(terminal_brand_col, '未知')).strip()
                    if terminal_brand and terminal_brand != '未知' and terminal_brand != 'nan':
                        chunk_stats['terminal_brands'][terminal_brand] = chunk_stats['terminal_brands'].get(
                            terminal_brand, 0) + 1

                    # 统计终端机型
                    terminal_model = str(row.get(terminal_model_col, '未知')).strip()
                    if terminal_model and terminal_model != '未知' and terminal_model != 'nan':
                        chunk_stats['terminal_models'][terminal_model] = chunk_stats['terminal_models'].get(
                            terminal_model, 0) + 1

                    # 更新AOI统计
                    if aoi_name and aoi_name in aoi_stats:
                        points_in_aoi += 1
                        stats = aoi_stats[aoi_name]
                        stats['total'] += 1
                        stats[operator_key][net_key]['total'] += 1
                        stats[operator_key][net_key]['rsrp_sum'] += rsrp

                        if rsrp < weak_threshold:
                            stats[operator_key][net_key]['weak'] += 1

                        # 更新场景统计
                        scene_type = self.aoi_scene_mapping.get(aoi_name)
                        if scene_type:
                            scene_stats = chunk_stats['scenes'][scene_type]
                            scene_stats['count'] += 1
                            if net_key == '4g':
                                scene_stats['rsrp_4g_sum'] += rsrp
                                if rsrp < weak_threshold:
                                    scene_stats['weak_4g'] += 1
                            else:
                                scene_stats['rsrp_5g_sum'] += rsrp
                                if rsrp < weak_threshold:
                                    scene_stats['weak_5g'] += 1

                except Exception as e:
                    print_debug(f"[ERROR] 处理数据点 {idx} 时出错: {e}")
                    continue

            print_debug(f"[DEBUG] 数据点处理完成:")
            print_debug(f"  - 总处理点数: {processed_points}")
            print_debug(f"  - 边界内点数: {points_in_bounds}")
            print_debug(f"  - AOI内点数: {points_in_aoi}")
            print_debug(f"  - 建筑物内点数: {points_in_buildings}")
            print_debug(f"  - 跳过的无效RSRP点数: {skipped_points}")
            if self.filter_aoi:
                print_debug(f"  - AOI过滤掉的点数: {aoi_filtered_points}")

            # 更新全局统计信息
            for operator in ['mobile', 'unicom', 'telecom']:
                for net_type in ['4g', '5g']:
                    self.stats['operators'][operator][net_type]['total'] += \
                        chunk_stats['operators'][operator][net_type]['total']
                    self.stats['operators'][operator][net_type]['weak'] += chunk_stats['operators'][operator][net_type][
                        'weak']
                    self.stats['operators'][operator][net_type]['rsrp_sum'] += \
                        chunk_stats['operators'][operator][net_type]['rsrp_sum']

            # 更新终端品牌统计
            for brand, count in chunk_stats['terminal_brands'].items():
                self.stats['terminal_brands'][brand] = self.stats['terminal_brands'].get(brand, 0) + count

            # 更新终端机型统计
            for model, count in chunk_stats['terminal_models'].items():
                self.stats['terminal_models'][model] = self.stats['terminal_models'].get(model, 0) + count

            # 更新场景统计
            for scene, scene_data in chunk_stats['scenes'].items():
                self.stats['scenes'][scene]['count'] += scene_data['count']
                self.stats['scenes'][scene]['avg_rsrp_4g'] += scene_data['rsrp_4g_sum']
                self.stats['scenes'][scene]['avg_rsrp_5g'] += scene_data['rsrp_5g_sum']
                self.stats['scenes'][scene]['weak_coverage_4g'] += scene_data['weak_4g']
                self.stats['scenes'][scene]['weak_coverage_5g'] += scene_data['weak_5g']

            # 更新数据统计
            self.stats['data']['total_rows'] += chunk_stats['total_rows']
            self.stats['data']['valid_rows'] += chunk_stats['valid_rows']

            print_debug(f"[DEBUG] ========== 分块处理完成 ==========")

            return grid_data, aoi_stats, building_stats

        except Exception as e:
            print_debug(f"[ERROR] 处理数据块 {temp_file} 时出错: {e}")
            import traceback
            print_debug(f"[ERROR] 详细错误信息: {traceback.format_exc()}")
            return grid_data, aoi_stats, building_stats

    def process_grid_data_by_operator_and_network(self):
        """按运营商和网络类型分别处理栅格数据 - 多进程优化版本"""
        try:
            print_debug("[DEBUG] 开始处理栅格数据（多进程版本）")

            # 对于51列数据源，不强制要求所有列都存在
            if self.data_source_type == 51:
                required_columns = ['lgt', 'ltt', 'opt_source', 'dynamic_network_type']
            else:
                required_columns = ['经度（WGS84）', '纬度（WGS84）', 'RSRP', '运营商', '网络类型']

            print_debug(f"[DEBUG] 需要的基本数据列: {required_columns}")

            # 检查列是否存在
            sample_chunk = pd.read_parquet(self.temp_files[0])
            print_debug(f"[DEBUG] 样本数据列: {list(sample_chunk.columns)}")

            for col in required_columns:
                if col not in sample_chunk.columns:
                    error_msg = f"错误: 数据中缺少必要的列 '{col}'"
                    print_debug(f"[ERROR] {error_msg}")
                    self.error_occurred.emit(error_msg)
                    return

            # 获取边界
            min_lng, min_lat, max_lng, max_lat = -180, -90, 180, 90
            if self.aoi_polygons or self.building_polygons:
                all_bounds = []
                if self.aoi_polygons:
                    all_bounds.extend([polygon.bounds for polygon in self.aoi_polygons.values()])
                if self.building_polygons:
                    all_bounds.extend([polygon.bounds for polygon in self.building_polygons.values()])

                min_lng = min(b[0] for b in all_bounds)
                min_lat = min(b[1] for b in all_bounds)
                max_lng = max(b[2] for b in all_bounds)
                max_lat = max(b[3] for b in all_bounds)
                self.progress_update.emit(20, f"边界范围: {min_lng},{min_lat} - {max_lng},{max_lat}")
                print_debug(f"[DEBUG] 边界范围: {min_lng},{min_lat} - {max_lng},{max_lat}")

            # 计算网格参数
            center_lat = (min_lat + max_lat) / 2
            center_lng = (min_lng + max_lng) / 2
            print_debug(f"[DEBUG] 中心点: ({center_lng}, {center_lat})")

            grid_size_degrees = self.grid_size / (111000 * math.cos(math.radians(center_lat)))
            print_debug(f"[DEBUG] 网格大小: {self.grid_size}米 ≈ {grid_size_degrees}度")

            lng_grids = int((max_lng - min_lng) / grid_size_degrees) + 1
            lat_grids = int((max_lat - min_lat) / grid_size_degrees) + 1
            print_debug(f"[DEBUG] 网格尺寸: {lng_grids} x {lat_grids}")

            # 初始化网格数据
            operators = ['mobile', 'unicom', 'telecom']
            networks = ['4g', '5g']
            grid_data = {}
            grid_count = {}

            for operator in operators:
                grid_data[operator] = {}
                grid_count[operator] = {}
                for network in networks:
                    grid_data[operator][network] = np.full((lat_grids, lng_grids), np.nan)
                    grid_count[operator][network] = np.zeros((lat_grids, lng_grids))

            # 序列化多边形数据（用于多进程传递）
            aoi_polygons_data = {}
            for name, polygon in self.aoi_polygons.items():
                aoi_polygons_data[name] = polygon.wkt

            building_polygons_data = {}
            for name, polygon in self.building_polygons.items():
                building_polygons_data[name] = polygon.wkt

            # 使用多进程处理数据块
            total_tasks = len(self.temp_files)
            completed_tasks = 0
            self.progress_update.emit(25, f"准备处理 {total_tasks} 个数据块（使用 {self.num_cores} 个进程）...")
            print_debug(f"[DEBUG] 准备处理 {total_tasks} 个数据块（使用 {self.num_cores} 个进程）...")

            # 准备参数列表
            process_args = []
            for temp_file in self.temp_files:
                args = (temp_file, required_columns, min_lng, min_lat, max_lng, max_lat,
                        grid_size_degrees, lng_grids, lat_grids, aoi_polygons_data,
                        building_polygons_data, self.filter_aoi, self.lon_offset,
                        self.lat_offset, self.data_source_type, self.aoi_names,
                        self.building_names, self.aoi_scene_mapping)
                process_args.append(args)

            # 使用进程池处理
            with ProcessPoolExecutor(max_workers=self.num_cores) as executor:
                # 提交所有任务
                future_to_args = {executor.submit(process_grid_chunk_worker, args): args
                                  for args in process_args}

                # 处理完成的任务
                for future in as_completed(future_to_args):
                    try:
                        chunk_grids, chunk_aoi_stats, chunk_building_stats, chunk_stats = future.result()
                        completed_tasks += 1
                        print_debug(f"[DEBUG] 处理完数据块 {completed_tasks}/{total_tasks}")

                        # 合并网格数据
                        for operator in operators:
                            for network in networks:
                                if operator in chunk_grids and network in chunk_grids[operator]:
                                    chunk_data = chunk_grids[operator][network]['data']
                                    chunk_count_data = chunk_grids[operator][network]['count']

                                    for i in range(lat_grids):
                                        for j in range(lng_grids):
                                            if not np.isnan(chunk_data[i, j]) and chunk_count_data[i, j] > 0:
                                                if np.isnan(grid_data[operator][network][i, j]):
                                                    grid_data[operator][network][i, j] = chunk_data[i, j]
                                                    grid_count[operator][network][i, j] = chunk_count_data[i, j]
                                                else:
                                                    grid_data[operator][network][i, j] += chunk_data[i, j]
                                                    grid_count[operator][network][i, j] += chunk_count_data[i, j]

                        # 合并AOI统计信息
                        print_debug(f"[DEBUG] 合并AOI统计信息，数据块包含 {len(chunk_aoi_stats)} 个AOI")
                        for aoi_name, stats in chunk_aoi_stats.items():
                            if aoi_name not in self.aoi_stats:
                                print_debug(f"[WARNING] 未知AOI名称: '{aoi_name}', 跳过")
                                continue

                            for operator in ['mobile', 'unicom', 'telecom']:
                                for net_type in ['4g', '5g']:
                                    self.aoi_stats[aoi_name][operator][net_type]['total'] += stats[operator][net_type][
                                        'total']
                                    self.aoi_stats[aoi_name][operator][net_type]['weak'] += stats[operator][net_type][
                                        'weak']
                                    self.aoi_stats[aoi_name][operator][net_type]['rsrp_sum'] += \
                                    stats[operator][net_type]['rsrp_sum']

                            self.aoi_stats[aoi_name]['total'] += stats['total']

                        # 合并建筑物统计信息
                        print_debug(f"[DEBUG] 合并建筑物统计信息，数据块包含 {len(chunk_building_stats)} 个建筑物")
                        for building_name, stats in chunk_building_stats.items():
                            if building_name not in self.building_stats:
                                print_debug(f"[WARNING] 未知建筑物名称: '{building_name}', 跳过")
                                continue

                            for operator in ['mobile', 'unicom', 'telecom']:
                                for net_type in ['4g', '5g']:
                                    self.building_stats[building_name][operator][net_type]['total'] += \
                                    stats[operator][net_type]['total']
                                    self.building_stats[building_name][operator][net_type]['weak'] += \
                                    stats[operator][net_type]['weak']
                                    self.building_stats[building_name][operator][net_type]['rsrp_sum'] += \
                                    stats[operator][net_type]['rsrp_sum']

                            self.building_stats[building_name]['total'] += stats['total']
                            self.building_stats[building_name]['avg_rsrp'] += stats['rsrp_sum']

                        # 更新全局统计
                        if chunk_stats:
                            for operator in ['mobile', 'unicom', 'telecom']:
                                for net_type in ['4g', '5g']:
                                    self.stats['operators'][operator][net_type]['total'] += \
                                    chunk_stats['operators'][operator][net_type]['total']
                                    self.stats['operators'][operator][net_type]['weak'] += \
                                    chunk_stats['operators'][operator][net_type]['weak']
                                    self.stats['operators'][operator][net_type]['rsrp_sum'] += \
                                    chunk_stats['operators'][operator][net_type]['rsrp_sum']

                            for brand, count in chunk_stats.get('terminal_brands', {}).items():
                                self.stats['terminal_brands'][brand] = self.stats['terminal_brands'].get(brand,
                                                                                                         0) + count

                            for model, count in chunk_stats.get('terminal_models', {}).items():
                                self.stats['terminal_models'][model] = self.stats['terminal_models'].get(model,
                                                                                                         0) + count

                            for scene, scene_data in chunk_stats.get('scenes', {}).items():
                                self.stats['scenes'][scene]['count'] += scene_data['count']
                                self.stats['scenes'][scene]['avg_rsrp_4g'] += scene_data['rsrp_4g_sum']
                                self.stats['scenes'][scene]['avg_rsrp_5g'] += scene_data['rsrp_5g_sum']
                                self.stats['scenes'][scene]['weak_coverage_4g'] += scene_data['weak_4g']
                                self.stats['scenes'][scene]['weak_coverage_5g'] += scene_data['weak_5g']

                            self.stats['data']['total_rows'] += chunk_stats.get('total_rows', 0)
                            self.stats['data']['valid_rows'] += chunk_stats.get('valid_rows', 0)

                        progress = 25 + int((completed_tasks / total_tasks) * 45)
                        self.progress_update.emit(progress, f"处理数据块中... ({completed_tasks}/{total_tasks})")

                    except Exception as e:
                        print_debug(f"[ERROR] 处理数据块时出错: {e}")
                        import traceback
                        print_debug(f"[ERROR] 详细错误信息: {traceback.format_exc()}")

            # 计算建筑物平均RSRP
            for building_name, stats in self.building_stats.items():
                if stats['total'] > 0:
                    stats['avg_rsrp'] = stats['avg_rsrp'] / stats['total']

            # 生成各运营商和网络类型的栅格GeoJSON文件
            self.progress_update.emit(75, "生成栅格GeoJSON文件...")
            print_debug("[DEBUG] 开始生成栅格GeoJSON文件")

            for operator in operators:
                for network in networks:
                    print_debug(f"[DEBUG] 生成 {operator} {network} 栅格文件")

                    # 计算平均值
                    grid_avg = grid_data[operator][network] / grid_count[operator][network]

                    # 生成GeoJSON文件
                    features = []
                    for i in range(lat_grids):
                        for j in range(lng_grids):
                            if not np.isnan(grid_avg[i, j]) and grid_count[operator][network][i, j] > 0:
                                feature = self.create_grid_feature_by_network(
                                    i, j, grid_avg, grid_count[operator][network],
                                    min_lat, min_lng, grid_size_degrees, network)
                                if feature:
                                    features.append(feature)

                    # 创建GeoJSON FeatureCollection
                    feature_collection = {
                        'type': 'FeatureCollection',
                        'features': features
                    }

                    # 保存为GeoJSON
                    grid_path = os.path.join(self.output_dir, f"grid_{operator}_{network}.geojson")
                    with open(grid_path, 'w', encoding='utf-8') as f:
                        json.dump(feature_collection, f, ensure_ascii=False)

                    print_debug(f"[DEBUG] 栅格GeoJSON保存成功: {grid_path}，包含 {len(features)} 个栅格")

            # 按场景生成AOI边界和栅格文件
            print_debug("[DEBUG] 开始按场景生成文件")
            for scene_zh, scene_en in SCENE_MAPPING.items():
                print_debug(f"[DEBUG] 处理场景: {scene_zh} -> {scene_en}")
                self.generate_scene_files(scene_en, operators, networks, grid_data, grid_count,
                                          min_lat, min_lng, grid_size_degrees, lng_grids, lat_grids)

            print_debug("[DEBUG] 栅格数据处理完成")

        except Exception as e:
            print_debug(f"[ERROR] 处理栅格数据时出错: {e}")
            import traceback
            print_debug(f"[ERROR] 详细错误信息: {traceback.format_exc()}")

    def preprocess_discrete_points(self):
        """预处理离散点数据，提取场景信息"""
        try:
            if not self.discrete_points:
                return

            print_debug(f"[DEBUG] 开始预处理 {len(self.discrete_points)} 个离散点")

            # 统计场景类型
            scene_counts = {}
            site_scene_mapping = {}  # 站点到场景的映射

            for point in self.discrete_points:
                scene_type = point.get('场景类型1', '未知')
                site_name = point.get('现站点', '')

                if scene_type and scene_type != '未知':
                    scene_counts[scene_type] = scene_counts.get(scene_type, 0) + 1

                if site_name and scene_type and scene_type != '未知':
                    site_scene_mapping[site_name] = scene_type

            print_debug(f"[DEBUG] 离散点场景统计: {scene_counts}")
            print_debug(f"[DEBUG] 站点-场景映射数量: {len(site_scene_mapping)}")

            # 打印一些映射示例
            print_debug("[DEBUG] 站点-场景映射示例（前10个）:")
            for i, (site, scene) in enumerate(site_scene_mapping.items()):
                if i >= 10:
                    break
                print_debug(f"  {i + 1}. '{site}' -> '{scene}'")

        except Exception as e:
            print_debug(f"[ERROR] 预处理离散点数据时出错: {e}")


    def process_aoi(self):
        """处理AOI shp文件，返回GeoJSON文件路径"""
        try:
            print_debug(f"[DEBUG] 开始处理AOI shp文件: {self.shp_path}")

            # 尝试不同的编码读取shp文件
            encodings = ['gbk', 'gb2312', 'gb18030', 'utf-8', 'iso-8859-1']
            gdf = None

            for encoding in encodings:
                try:
                    gdf = gpd.read_file(self.shp_path, encoding=encoding)
                    # 检查是否有乱码
                    sample_name = gdf.iloc[0]['name'] if 'name' in gdf.columns and len(gdf) > 0 else ""
                    if sample_name and '?' not in sample_name:
                        print_debug(f"[DEBUG] 使用编码 {encoding} 成功读取shapefile")
                        break
                except Exception as e:
                    print_debug(f"[DEBUG] 使用编码 {encoding} 读取失败: {e}")
                    continue

            if gdf is None:
                # 如果所有编码都失败，使用默认编码
                print_debug("[WARNING] 所有编码尝试失败，使用默认编码")
                gdf = gpd.read_file(self.shp_path)

            print_debug(f"[DEBUG] AOI文件包含 {len(gdf)} 个要素")
            print_debug(f"[DEBUG] AOI字段: {list(gdf.columns)}")

            # 打印前5行数据样本
            print_debug("[DEBUG] AOI数据样本（前5行）:")
            for idx in range(min(5, len(gdf))):
                row_data = {}
                for col in gdf.columns:
                    if col != 'geometry':
                        row_data[col] = gdf.iloc[idx][col]
                print_debug(f"  行{idx}: {row_data}")

            # 转换坐标系到WGS84
            if gdf.crs and str(gdf.crs) != 'EPSG:4326':
                print_debug(f"[DEBUG] 将坐标系从 {gdf.crs} 转换为 WGS84")
                gdf = gdf.to_crs('EPSG:4326')

            # 初始化场景映射
            self.scene_aoi_mapping = {scene: [] for scene in SCENE_MAPPING.values()}

            # 创建离散点站址到场景类型的映射
            discrete_point_scene_map = {}
            if self.discrete_points:
                print_debug(f"[DEBUG] 创建离散点站址到场景类型的映射...")
                for point in self.discrete_points:
                    site_name = point.get('现站点', '')
                    scene_type = point.get('场景类型1', '')
                    if site_name and scene_type:
                        discrete_point_scene_map[site_name] = scene_type
                        print_debug(f"  [DEBUG] 离散点映射: '{site_name}' -> '{scene_type}'")

                print_debug(f"[DEBUG] 创建了 {len(discrete_point_scene_map)} 个站址到场景的映射")
                # 打印前10个映射示例
                for i, (site, scene) in enumerate(discrete_point_scene_map.items()):
                    if i >= 10:
                        break
                    print_debug(f"  示例{i + 1}: '{site}' -> '{scene}'")
            else:
                print_debug("[WARNING] 没有离散点数据，无法进行场景匹配")

            # 存储AOI多边形
            matched_aoi_count = 0
            unmatched_aoi_names = []

            for idx, row in gdf.iterrows():
                geometry = row.geometry
                # 从可能的名称字段中获取AOI名称
                name = None
                for col in ['name', 'Name', 'NAME', '名称', 'label', 'Label', 'LABEL']:
                    if col in row and row[col]:
                        name = str(row[col])
                        break

                if not name:
                    name = f"AOI_{idx}"

                self.aoi_names.append(name)

                # 处理MultiPolygon
                if geometry.geom_type == 'MultiPolygon':
                    print_debug(f"[DEBUG] AOI '{name}' 是MultiPolygon，包含 {len(geometry.geoms)} 个部分")
                    self.aoi_polygons[name] = geometry
                else:
                    self.aoi_polygons[name] = geometry

                # 初始化AOI统计
                self.aoi_stats[name] = {
                    'mobile': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                               '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                    'unicom': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                               '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                    'telecom': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                                '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                    'total': 0
                }

                # 通过name字段匹配离散点的场景类型
                scene_type = None
                scene_type_zh = None

                # 尝试直接匹配
                if name in discrete_point_scene_map:
                    scene_type_zh = discrete_point_scene_map[name]
                    print_debug(f"[DEBUG] AOI '{name}' 直接匹配到场景类型: '{scene_type_zh}'")
                else:
                    # 尝试模糊匹配（去除空格、特殊字符等）
                    name_clean = name.strip().replace(' ', '').replace('　', '')
                    for site_name, scene in discrete_point_scene_map.items():
                        site_clean = site_name.strip().replace(' ', '').replace('　', '')
                        if name_clean == site_clean:
                            scene_type_zh = scene
                            print_debug(f"[DEBUG] AOI '{name}' 模糊匹配到场景类型: '{scene_type_zh}'")
                            break
                        # 也可以尝试包含关系匹配
                        elif name_clean in site_clean or site_clean in name_clean:
                            scene_type_zh = scene
                            print_debug(f"[DEBUG] AOI '{name}' 包含关系匹配到场景类型: '{scene_type_zh}'")
                            break

                # 将中文场景类型映射到英文
                if scene_type_zh:
                    for scene_zh, scene_en in SCENE_MAPPING.items():
                        if scene_zh in scene_type_zh:
                            scene_type = scene_en
                            break

                    if scene_type:
                        self.scene_aoi_mapping[scene_type].append(name)
                        self.aoi_scene_mapping[name] = scene_type
                        matched_aoi_count += 1
                        print_debug(f"[DEBUG] AOI '{name}' 被分类为场景 '{scene_type}' (原始: '{scene_type_zh}')")
                    else:
                        print_debug(f"[WARNING] AOI '{name}' 的场景类型 '{scene_type_zh}' 无法映射到标准场景")
                        unmatched_aoi_names.append(name)
                else:
                    print_debug(f"[WARNING] AOI '{name}' 未能匹配到任何离散点站址")
                    unmatched_aoi_names.append(name)

            print_debug(f"[DEBUG] 成功加载 {len(self.aoi_polygons)} 个AOI多边形")
            print_debug(f"[DEBUG] 成功匹配场景类型的AOI数量: {matched_aoi_count}")
            print_debug(f"[DEBUG] 未匹配场景类型的AOI数量: {len(unmatched_aoi_names)}")
            if unmatched_aoi_names:
                print_debug(f"[DEBUG] 未匹配的AOI列表（前20个）: {unmatched_aoi_names[:20]}")

            print_debug(f"[DEBUG] 场景映射统计:")
            for scene, aois in self.scene_aoi_mapping.items():
                if aois:
                    print_debug(f"  - {scene}: {len(aois)}个AOI")
                    print_debug(f"    AOI列表（前5个）: {aois[:5]}{'...' if len(aois) > 5 else ''}")

            self.stats['data']['aoi_count'] = len(self.aoi_polygons)

            # 保存为GeoJSON，并添加场景类型属性
            # 为gdf添加场景类型列
            gdf['scene_type'] = None
            gdf['scene_type_zh'] = None

            for idx, row in gdf.iterrows():
                name = None
                for col in ['name', 'Name', 'NAME', '名称', 'label', 'Label', 'LABEL']:
                    if col in row and row[col]:
                        name = str(row[col])
                        break

                if name and name in self.aoi_scene_mapping:
                    scene_type = self.aoi_scene_mapping[name]
                    gdf.at[idx, 'scene_type'] = scene_type

                    # 找到对应的中文场景类型
                    for scene_zh, scene_en in SCENE_MAPPING.items():
                        if scene_en == scene_type:
                            gdf.at[idx, 'scene_type_zh'] = scene_zh
                            break

            # 保存为GeoJSON
            output_path = os.path.join(self.output_dir, "aoi.geojson")
            gdf.to_file(output_path, driver='GeoJSON')

            return output_path

        except Exception as e:
            print_debug(f"[ERROR] 处理AOI文件时出错: {e}")
            import traceback
            print_debug(f"[ERROR] 详细错误信息: {traceback.format_exc()}")
            return ""

    def process_buildings(self):
        """处理建筑物shp文件，返回GeoJSON文件路径"""
        try:
            print_debug(f"[DEBUG] 开始处理建筑物shp文件: {self.building_shp_path}")

            # 读取shp文件
            self.building_gdf = gpd.read_file(self.building_shp_path)
            print_debug(f"[DEBUG] 建筑物文件包含 {len(self.building_gdf)} 个要素")
            print_debug(f"[DEBUG] 建筑物字段: {list(self.building_gdf.columns)}")

            # 转换坐标系到WGS84
            if self.building_gdf.crs and str(self.building_gdf.crs) != 'EPSG:4326':
                print_debug(f"[DEBUG] 将坐标系从 {self.building_gdf.crs} 转换为 WGS84")
                self.building_gdf = self.building_gdf.to_crs('EPSG:4326')

            # 存储建筑物多边形
            for idx, row in self.building_gdf.iterrows():
                geometry = row.geometry
                # 从可能的名称字段中获取建筑物名称
                name = None
                for col in ['name', 'Name', 'NAME', '名称', 'building_name', '建筑物名称']:
                    if col in row and row[col]:
                        name = str(row[col])
                        break

                if not name:
                    name = f"Building_{idx}"

                self.building_names.append(name)
                self.building_polygons[name] = geometry

                # 初始化建筑物统计
                self.building_stats[name] = {
                    'mobile': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                               '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                    'unicom': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                               '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                    'telecom': {'4g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0},
                                '5g': {'total': 0, 'weak': 0, 'rsrp_sum': 0.0}},
                    'total': 0,
                    'avg_rsrp': 0.0
                }

            print_debug(f"[DEBUG] 成功加载 {len(self.building_polygons)} 个建筑物多边形")
            self.stats['data']['building_count'] = len(self.building_polygons)

            # 保存为GeoJSON
            output_path = os.path.join(self.output_dir, "buildings.geojson")
            self.building_gdf.to_file(output_path, driver='GeoJSON')

            return output_path

        except Exception as e:
            print_debug(f"[ERROR] 处理建筑物文件时出错: {e}")
            import traceback
            print_debug(f"[ERROR] 详细错误信息: {traceback.format_exc()}")
            return ""

    def generate_classified_building_files(self):
        """生成按运营商和网络类型分类的建筑物文件"""
        try:
            if self.building_gdf is None:
                return

            print_debug("[DEBUG] 开始生成分类建筑物文件")

            operators = ['mobile', 'unicom', 'telecom']
            networks = ['4g', '5g']

            for operator in operators:
                for network in networks:
                    print_debug(f"[DEBUG] 生成 {operator} {network} 建筑物文件")

                    # 创建建筑物特征列表
                    features = []

                    for idx, row in self.building_gdf.iterrows():
                        geometry = row.geometry
                        # 获取建筑物名称
                        name = None
                        for col in ['name', 'Name', 'NAME', '名称', 'building_name', '建筑物名称']:
                            if col in row and row[col]:
                                name = str(row[col])
                                break

                        if not name:
                            name = f"Building_{idx}"

                        # 获取该建筑物的统计信息
                        if name in self.building_stats:
                            stats = self.building_stats[name]
                            operator_network_stats = stats[operator][network]

                            if operator_network_stats['total'] > 0:
                                avg_rsrp = operator_network_stats['rsrp_sum'] / operator_network_stats['total']
                                weak_percent = (operator_network_stats['weak'] / operator_network_stats['total']) * 100

                                # 根据RSRP值确定颜色
                                color = self.get_rsrp_color(avg_rsrp, network)

                                # 创建特征
                                feature = {
                                    'type': 'Feature',
                                    'geometry': geometry.__geo_interface__,
                                    'properties': {
                                        'name': name,
                                        'operator': operator,
                                        'network': network,
                                        'point_count': operator_network_stats['total'],
                                        'avg_rsrp': avg_rsrp,
                                        'weak_count': operator_network_stats['weak'],
                                        'weak_percent': weak_percent,
                                        'color': color
                                    }
                                }
                                features.append(feature)

                    # 保存GeoJSON
                    if features:
                        feature_collection = {
                            'type': 'FeatureCollection',
                            'features': features
                        }

                        output_path = os.path.join(self.output_dir, f"buildings_{operator}_{network}.geojson")
                        with open(output_path, 'w', encoding='utf-8') as f:
                            json.dump(feature_collection, f, ensure_ascii=False)

                        print_debug(f"[DEBUG] 保存建筑物文件: {output_path}，包含 {len(features)} 个建筑物")

            # 保存建筑物统计信息
            self.save_building_stats()

        except Exception as e:
            print_debug(f"[ERROR] 生成分类建筑物文件时出错: {e}")
            import traceback
            print_debug(f"[ERROR] 详细错误信息: {traceback.format_exc()}")

    def save_building_stats(self):
        """保存建筑物统计信息为GeoJSON格式"""
        try:
            features = []

            for name, stats in self.building_stats.items():
                if name in self.building_polygons:
                    polygon = self.building_polygons[name]

                    # 创建属性字典
                    properties = {
                        'name': name,
                        'total_points': stats['total'],
                        'avg_rsrp': stats['avg_rsrp'] if stats['total'] > 0 else None
                    }

                    # 添加各运营商和网络类型的统计
                    for operator in ['mobile', 'unicom', 'telecom']:
                        for network in ['4g', '5g']:
                            prefix = f"{operator}_{network}"
                            op_net_stats = stats[operator][network]

                            properties[f"{prefix}_total"] = op_net_stats['total']
                            properties[f"{prefix}_weak"] = op_net_stats['weak']

                            if op_net_stats['total'] > 0:
                                properties[f"{prefix}_avg_rsrp"] = op_net_stats['rsrp_sum'] / op_net_stats['total']
                                properties[f"{prefix}_weak_percent"] = (op_net_stats['weak'] / op_net_stats[
                                    'total']) * 100
                            else:
                                properties[f"{prefix}_avg_rsrp"] = None
                                properties[f"{prefix}_weak_percent"] = None

                    # 创建特征
                    feature = {
                        'type': 'Feature',
                        'geometry': polygon.__geo_interface__,
                        'properties': properties
                    }
                    features.append(feature)

            # 保存为GeoJSON
            feature_collection = {
                'type': 'FeatureCollection',
                'features': features
            }

            output_path = os.path.join(self.output_dir, "buildings_stats.geojson")
            with open(output_path, 'w', encoding='utf-8') as f:
                json.dump(feature_collection, f, ensure_ascii=False)

            print_debug(f"[DEBUG] 保存建筑物统计文件: {output_path}")

        except Exception as e:
            print_debug(f"[ERROR] 保存建筑物统计信息时出错: {e}")

    def generate_throughput_heatmaps(self):
        """生成download和upload热力图"""
        try:
            print_debug("[DEBUG] 开始生成下载/上传热力图")

            # 检查必要的列是否存在
            if self.data_source_type == 51:
                required_columns = ['lgt', 'ltt', 'download', 'upload']
                lon_col, lat_col = 'lgt', 'ltt'
            else:
                required_columns = ['经度（WGS84）', '纬度（WGS84）', 'download', 'upload']
                lon_col, lat_col = '经度（WGS84）', '纬度（WGS84）'

            # 获取AOI边界
            min_lng, min_lat, max_lng, max_lat = -180, -90, 180, 90
            if self.aoi_polygons:
                all_bounds = [polygon.bounds for polygon in self.aoi_polygons.values()]
                min_lng = min(b[0] for b in all_bounds)
                min_lat = min(b[1] for b in all_bounds)
                max_lng = max(b[2] for b in all_bounds)
                max_lat = max(b[3] for b in all_bounds)

            # 计算中心点和网格大小
            center_lat = (min_lat + max_lat) / 2
            center_lng = (min_lng + max_lng) / 2
            grid_size_degrees = self.grid_size / (111000 * math.cos(math.radians(center_lat)))

            # 创建网格
            lng_grids = int((max_lng - min_lng) / grid_size_degrees) + 1
            lat_grids = int((max_lat - min_lat) / grid_size_degrees) + 1

            # 初始化下载和上传的网格数据
            download_grid = np.zeros((lat_grids, lng_grids))
            upload_grid = np.zeros((lat_grids, lng_grids))
            download_count = np.zeros((lat_grids, lng_grids))
            upload_count = np.zeros((lat_grids, lng_grids))

            # 为每个场景初始化网格数据
            scene_download_grids = {}
            scene_upload_grids = {}
            scene_download_counts = {}
            scene_upload_counts = {}

            for scene in SCENE_MAPPING.values():
                scene_download_grids[scene] = np.zeros((lat_grids, lng_grids))
                scene_upload_grids[scene] = np.zeros((lat_grids, lng_grids))
                scene_download_counts[scene] = np.zeros((lat_grids, lng_grids))
                scene_upload_counts[scene] = np.zeros((lat_grids, lng_grids))

            # 处理数据点
            total_chunks = len(self.temp_files)
            processed_chunks = 0

            for temp_file in self.temp_files:
                chunk = pd.read_parquet(temp_file)

                # 检查必要列
                missing_columns = [col for col in required_columns if col not in chunk.columns]
                if missing_columns:
                    print_debug(f"[WARNING] 数据块中缺少列: {', '.join(missing_columns)}")
                    continue

                # 数据预处理
                valid_data = chunk.dropna(subset=[lon_col, lat_col])

                for idx, row in valid_data.iterrows():
                    try:
                        lng = float(row[lon_col]) + self.lon_offset
                        lat = float(row[lat_col]) + self.lat_offset
                        download_val = float(row.get('download', 0))
                        upload_val = float(row.get('upload', 0))

                        # 检查点是否在边界内
                        if not (min_lng <= lng <= max_lng and min_lat <= lat <= max_lat):
                            continue

                        # 创建点对象
                        point_obj = Point(lng, lat)

                        # 检查点在哪个AOI内
                        point_in_aoi = False
                        aoi_name = None
                        scene_type = None

                        for name, polygon in self.aoi_polygons.items():
                            if polygon.contains(point_obj):
                                point_in_aoi = True
                                aoi_name = name
                                scene_type = self.aoi_scene_mapping.get(aoi_name)
                                break

                        # 如果启用了AOI过滤且点不在任何AOI内，跳过
                        if self.filter_aoi and not point_in_aoi:
                            continue

                        # 计算网格索引
                        lng_idx = int((lng - min_lng) / grid_size_degrees)
                        lat_idx = int((lat - min_lat) / grid_size_degrees)

                        # 检查索引有效性
                        if 0 <= lng_idx < lng_grids and 0 <= lat_idx < lat_grids:
                            # 更新总体网格
                            download_grid[lat_idx, lng_idx] += download_val
                            upload_grid[lat_idx, lng_idx] += upload_val
                            download_count[lat_idx, lng_idx] += 1
                            upload_count[lat_idx, lng_idx] += 1

                            # 更新场景网格
                            if scene_type:
                                scene_download_grids[scene_type][lat_idx, lng_idx] += download_val
                                scene_upload_grids[scene_type][lat_idx, lng_idx] += upload_val
                                scene_download_counts[scene_type][lat_idx, lng_idx] += 1
                                scene_upload_counts[scene_type][lat_idx, lng_idx] += 1

                    except Exception as e:
                        continue

                processed_chunks += 1
                print_debug(f"[DEBUG] 处理热力图数据块 {processed_chunks}/{total_chunks}")

            # 生成总体热力图文件
            self.save_throughput_heatmap(download_grid, download_count, 'download',
                                         min_lat, min_lng, grid_size_degrees)
            self.save_throughput_heatmap(upload_grid, upload_count, 'upload',
                                         min_lat, min_lng, grid_size_degrees)

            # 生成场景热力图文件
            for scene in SCENE_MAPPING.values():
                if np.any(scene_download_counts[scene] > 0):
                    self.save_throughput_heatmap(scene_download_grids[scene],
                                                 scene_download_counts[scene],
                                                 f'download_{scene}',
                                                 min_lat, min_lng, grid_size_degrees)
                    self.save_throughput_heatmap(scene_upload_grids[scene],
                                                 scene_upload_counts[scene],
                                                 f'upload_{scene}',
                                                 min_lat, min_lng, grid_size_degrees)

            print_debug("[DEBUG] 下载/上传热力图生成完成")

        except Exception as e:
            print_debug(f"[ERROR] 生成热力图时出错: {e}")
            import traceback
            print_debug(f"[ERROR] 详细错误信息: {traceback.format_exc()}")

    def save_throughput_heatmap(self, grid_data, grid_count, type_name,
                                min_lat, min_lng, grid_size_degrees):
        """保存吞吐量热力图为GeoJSON"""
        try:
            features = []
            lat_grids, lng_grids = grid_data.shape

            # 计算非零值的最大最小值用于颜色映射
            non_zero_data = grid_data[grid_count > 0]
            if len(non_zero_data) > 0:
                max_val = np.max(non_zero_data)
                min_val = np.min(non_zero_data)
            else:
                max_val = min_val = 0

            for i in range(lat_grids):
                for j in range(lng_grids):
                    if grid_count[i, j] > 0:
                        # 计算网格坐标
                        lat = min_lat + i * grid_size_degrees
                        lng = min_lng + j * grid_size_degrees

                        # 创建网格多边形
                        polygon = Polygon([
                            [lng, lat],
                            [lng + grid_size_degrees, lat],
                            [lng + grid_size_degrees, lat + grid_size_degrees],
                            [lng, lat + grid_size_degrees],
                            [lng, lat]
                        ])

                        # 计算颜色（热力图颜色）
                        value = grid_data[i, j]
                        if max_val > min_val:
                            normalized = (value - min_val) / (max_val - min_val)
                            # 使用红黄绿渐变
                            if normalized < 0.5:
                                # 绿到黄
                                r = int(255 * (normalized * 2))
                                g = 255
                                b = 0
                            else:
                                # 黄到红
                                r = 255
                                g = int(255 * (2 - normalized * 2))
                                b = 0
                            color = f'#{r:02x}{g:02x}{b:02x}'
                        else:
                            color = '#00FF00'  # 默认绿色

                        # 创建特征
                        feature = {
                            'type': 'Feature',
                            'geometry': polygon.__geo_interface__,
                            'properties': {
                                'value': value,
                                'count': int(grid_count[i, j]),
                                'color': color,
                                'type': type_name
                            }
                        }
                        features.append(feature)

            # 保存GeoJSON
            feature_collection = {
                'type': 'FeatureCollection',
                'features': features
            }

            output_path = os.path.join(self.output_dir, f"{type_name}.geojson")
            with open(output_path, 'w', encoding='utf-8') as f:
                json.dump(feature_collection, f, ensure_ascii=False)

            print_debug(f"[DEBUG] 保存热力图: {output_path}，包含 {len(features)} 个网格")

        except Exception as e:
            print_debug(f"[ERROR] 保存热力图时出错: {e}")

    def process_discrete_points(self):
        """处理离散点数据，生成GeoJSON文件"""
        try:
            if not self.discrete_points:
                return ""

            print_debug(f"[DEBUG] 开始处理 {len(self.discrete_points)} 个离散点")

            # 获取离散点偏移量（这里应该从主线程传入，暂时使用0）
            discrete_lon_offset = 0.0
            discrete_lat_offset = 0.0

            features = []
            processed_count = 0

            for point in self.discrete_points:
                try:
                    # 获取经纬度
                    lng = float(point.get('经度', 0)) + discrete_lon_offset
                    lat = float(point.get('纬度', 0)) + discrete_lat_offset

                    # 创建点对象
                    point_geom = Point(lng, lat)

                    # 检查点是否在任何AOI内
                    in_aoi = False
                    aoi_name = None
                    for name, polygon in self.aoi_polygons.items():
                        if polygon.contains(point_geom):
                            in_aoi = True
                            aoi_name = name
                            break

                    # 如果启用了AOI过滤且点不在任何AOI内，跳过
                    if self.filter_aoi and not in_aoi:
                        continue

                    # 准备属性（包含所有原始字段）
                    properties = {}
                    for key, value in point.items():
                        if pd.isna(value) or value == "暂无":
                            properties[key] = None
                        else:
                            properties[key] = value

                    # 添加关联的AOI信息
                    if aoi_name:
                        properties['所属AOI'] = aoi_name

                    # 查找关联的栅格化统计信息
                    if self.building_stats:
                        building_name = properties.get('场所名称') or properties.get('现站点')
                        if building_name and building_name in self.building_stats:
                            stats = self.building_stats[building_name]

                            # 添加统计信息到属性
                            for operator in ['mobile', 'unicom', 'telecom']:
                                for network in ['4g', '5g']:
                                    prefix = f"{operator}_{network}"
                                    op_net_stats = stats[operator][network]

                                    if op_net_stats['total'] > 0:
                                        properties[f"{prefix}_avg_rsrp"] = op_net_stats['rsrp_sum'] / op_net_stats[
                                            'total']
                                        properties[f"{prefix}_weak_percent"] = (op_net_stats['weak'] / op_net_stats[
                                            'total']) * 100
                                    else:
                                        properties[f"{prefix}_avg_rsrp"] = None
                                        properties[f"{prefix}_weak_percent"] = None

                    # 创建特征
                    feature = {
                        'type': 'Feature',
                        'geometry': point_geom.__geo_interface__,
                        'properties': properties
                    }
                    features.append(feature)
                    processed_count += 1

                except Exception as e:
                    print_debug(f"[WARNING] 处理离散点时出错: {e}")
                    continue

            print_debug(f"[DEBUG] 成功处理 {processed_count} 个离散点")

            # 保存为GeoJSON
            feature_collection = {
                'type': 'FeatureCollection',
                'features': features
            }

            output_path = os.path.join(self.output_dir, "discrete_points.geojson")
            with open(output_path, 'w', encoding='utf-8') as f:
                json.dump(feature_collection, f, ensure_ascii=False)

            # 更新统计信息
            self.stats['data']['discrete_points'] = processed_count

            return output_path

        except Exception as e:
            print_debug(f"[ERROR] 处理离散点数据时出错: {e}")
            import traceback
            print_debug(f"[ERROR] 详细错误信息: {traceback.format_exc()}")
            return ""

    def save_statistics(self):
        """保存统计信息到JSON文件"""
        try:
            # 计算场景平均RSRP
            for scene, scene_data in self.stats['scenes'].items():
                if scene_data['count'] > 0:
                    if scene_data['avg_rsrp_4g'] > 0:
                        scene_data['avg_rsrp_4g'] = scene_data['avg_rsrp_4g'] / scene_data['count']
                    if scene_data['avg_rsrp_5g'] > 0:
                        scene_data['avg_rsrp_5g'] = scene_data['avg_rsrp_5g'] / scene_data['count']
                    if scene_data['weak_coverage_4g'] > 0:
                        scene_data['weak_coverage_4g'] = (scene_data['weak_coverage_4g'] / scene_data['count']) * 100
                    if scene_data['weak_coverage_5g'] > 0:
                        scene_data['weak_coverage_5g'] = (scene_data['weak_coverage_5g'] / scene_data['count']) * 100

            # 添加AOI统计到总统计中
            self.stats['aoi_stats'] = []
            for aoi_name, aoi_stat in self.aoi_stats.items():
                aoi_info = {
                    'name': aoi_name,
                    'scene': self.aoi_scene_mapping.get(aoi_name, '未分类'),
                    'total_points': aoi_stat['total'],
                    'operators': {}
                }

                for operator in ['mobile', 'unicom', 'telecom']:
                    op_info = {}
                    for network in ['4g', '5g']:
                        net_stats = aoi_stat[operator][network]
                        if net_stats['total'] > 0:
                            op_info[network] = {
                                'total': net_stats['total'],
                                'weak': net_stats['weak'],
                                'avg_rsrp': net_stats['rsrp_sum'] / net_stats['total'],
                                'weak_percent': (net_stats['weak'] / net_stats['total']) * 100
                            }
                    if op_info:
                        aoi_info['operators'][operator] = op_info

                self.stats['aoi_stats'].append(aoi_info)

            # 添加建筑物统计到总统计中
            self.stats['building_stats'] = []
            for building_name, building_stat in self.building_stats.items():
                building_info = {
                    'name': building_name,
                    'total_points': building_stat['total'],
                    'avg_rsrp': building_stat['avg_rsrp'],
                    'operators': {}
                }

                for operator in ['mobile', 'unicom', 'telecom']:
                    op_info = {}
                    for network in ['4g', '5g']:
                        net_stats = building_stat[operator][network]
                        if net_stats['total'] > 0:
                            op_info[network] = {
                                'total': net_stats['total'],
                                'weak': net_stats['weak'],
                                'avg_rsrp': net_stats['rsrp_sum'] / net_stats['total'],
                                'weak_percent': (net_stats['weak'] / net_stats['total']) * 100
                            }
                    if op_info:
                        building_info['operators'][operator] = op_info

                self.stats['building_stats'].append(building_info)

            # 保存统计信息
            stats_path = os.path.join(self.output_dir, "statistics.json")
            with open(stats_path, 'w', encoding='utf-8') as f:
                json.dump(self.stats, f, ensure_ascii=False, indent=2)

            print_debug(f"[DEBUG] 统计信息已保存到: {stats_path}")

        except Exception as e:
            print_debug(f"[ERROR] 保存统计信息时出错: {e}")

    def get_rsrp_color(self, rsrp, network_type='4g'):
        """根据RSRP值返回对应的颜色"""
        if network_type == '4g':
            if rsrp > -80:
                return '#00FF00'  # 绿色
            elif rsrp > -100:
                return '#0000FF'  # 蓝色
            elif rsrp > -115:
                return '#FFFF00'  # 黄色
            else:
                return '#FF0000'  # 红色
        else:  # 5G
            if rsrp > -75:
                return '#00FF00'  # 绿色
            elif rsrp > -95:
                return '#0000FF'  # 蓝色
            elif rsrp > -110:
                return '#FFFF00'  # 黄色
            else:
                return '#FF0000'  # 红色


    def create_grid_feature_by_network(self, i, j, grid_avg, grid_count, min_lat, min_lng,
                                       grid_size_degrees, network_type):
        """根据网络类型创建网格特征"""
        try:
            rsrp = grid_avg[i, j]
            count = grid_count[i, j]

            if np.isnan(rsrp) or count == 0:
                return None

            # 计算网格坐标
            lat = min_lat + i * grid_size_degrees
            lng = min_lng + j * grid_size_degrees

            # 创建网格多边形
            polygon = Polygon([
                [lng, lat],
                [lng + grid_size_degrees, lat],
                [lng + grid_size_degrees, lat + grid_size_degrees],
                [lng, lat + grid_size_degrees],
                [lng, lat]
            ])

            # 根据RSRP值确定颜色
            color = self.get_rsrp_color(rsrp, network_type)

            # 创建特征
            feature = {
                'type': 'Feature',
                'geometry': polygon.__geo_interface__,
                'properties': {
                    'rsrp': rsrp,
                    'count': int(count),
                    'color': color,
                    'network_type': network_type
                }
            }

            return feature

        except Exception as e:
            print_debug(f"[ERROR] 创建网格特征时出错: {e}")
            return None

    def generate_scene_files(self, scene_type, operators, networks, grid_data, grid_count,
                             min_lat, min_lng, grid_size_degrees, lng_grids, lat_grids):
        """生成场景相关的文件"""
        try:
            # 获取该场景对应的AOI列表
            aoi_names = self.scene_aoi_mapping.get(scene_type, [])
            if not aoi_names:
                return

            print_debug(f"[DEBUG] 生成场景 {scene_type} 的文件，包含 {len(aoi_names)} 个AOI")

            # 1. 生成场景AOI边界文件
            features = []
            for aoi_name in aoi_names:
                if aoi_name in self.aoi_polygons:
                    polygon = self.aoi_polygons[aoi_name]
                    feature = {
                        'type': 'Feature',
                        'geometry': polygon.__geo_interface__,
                        'properties': {
                            'name': aoi_name,
                             'scene_type': scene_type
                        }
                    }
                    features.append(feature)

            if features:
                feature_collection = {
                    'type': 'FeatureCollection',
                    'features': features
                }

                aoi_path = os.path.join(self.output_dir, f"aoi_{scene_type}.geojson")
                with open(aoi_path, 'w', encoding='utf-8') as f:
                    json.dump(feature_collection, f, ensure_ascii=False)

                print_debug(f"[DEBUG] 保存场景AOI文件: {aoi_path}")

            # 2. 生成场景栅格文件（按运营商和网络类型）
            for operator in operators:
                for network in networks:
                    scene_features = []

                    # 遍历所有网格
                    for i in range(lat_grids):
                        for j in range(lng_grids):
                            if grid_count[operator][network][i, j] > 0:
                                # 计算网格中心点
                                lat = min_lat + (i + 0.5) * grid_size_degrees
                                lng = min_lng + (j + 0.5) * grid_size_degrees
                                point = Point(lng, lat)

                                # 检查该网格是否在场景的任何AOI内
                                in_scene = False
                                for aoi_name in aoi_names:
                                    if aoi_name in self.aoi_polygons:
                                        if self.aoi_polygons[aoi_name].contains(point):
                                            in_scene = True
                                            break

                                if in_scene:
                                    # 计算平均RSRP
                                    avg_rsrp = grid_data[operator][network][i, j] / grid_count[operator][network][i, j]
                                    feature = self.create_grid_feature_by_network(
                                        i, j, grid_data[operator][network] / grid_count[operator][network],
                                        grid_count[operator][network], min_lat, min_lng,
                                        grid_size_degrees, network
                                    )
                                    if feature:
                                        scene_features.append(feature)

                    # 保存场景栅格文件
                    if scene_features:
                        feature_collection = {
                            'type': 'FeatureCollection',
                            'features': scene_features
                        }

                        grid_path = os.path.join(self.output_dir,
                                                 f"grid_{scene_type}_{operator}_{network}.geojson")
                        with open(grid_path, 'w', encoding='utf-8') as f:
                            json.dump(feature_collection, f, ensure_ascii=False)

                        print_debug(f"[DEBUG] 保存场景栅格文件: {grid_path}，包含 {len(scene_features)} 个栅格")

        except Exception as e:
            print_debug(f"[ERROR] 生成场景文件时出错: {e}")
            import traceback
            print_debug(f"[ERROR] 详细错误信息: {traceback.format_exc()}")

    # process_grid_chunk_by_operator 和 process_grid_data_by_operator_and_network 方法已在前面提供


class OTTMRAnalyzer(QMainWindow):
    """OTT_MR文件分析工具主窗口"""

    def __init__(self):
        super().__init__()
        self.temp_dir = None  # 存储临时目录
        self.temp_files = []  # 存储临时文件路径
        self.processed_temp_dir = None  # 存储处理后的临时目录
        self.file_paths = []  # 存储选择的文件路径列表
        self.loaded_files = []  # 存储已加载的文件名
        self.shp_path = None  # 存储AOI shp文件路径
        self.initUI()
        # 在初始化时创建列选择区域（即使没有数据）
        self.update_column_checkboxes(None)  # 传入None表示没有数据
        self.data_source_type = 44  # 默认44列数据源
        self.current_columns = []  # 存储当前数据源的列名
        self.discrete_points = []  # 存储离散点数据
        self.grid_output_dir = None  # 栅格化输出目录
        self.building_shp_path = None  # 存储建筑物shp文件路径

    def initUI(self):
        """初始化用户界面"""
        self.setWindowTitle('OTT_MR栅格化分析工具')
        self.setGeometry(100, 100, 1600, 900)

        # 创建菜单栏
        menubar = self.menuBar()

        # 文件菜单
        file_menu = menubar.addMenu('文件')

        open_action = QAction('打开文件', self)
        open_action.setShortcut('Ctrl+O')
        open_action.triggered.connect(self.select_file)
        file_menu.addAction(open_action)

        save_action = QAction('保存数据', self)
        save_action.setShortcut('Ctrl+S')
        save_action.triggered.connect(self.save_processed_data)
        file_menu.addAction(save_action)

        file_menu.addSeparator()

        exit_action = QAction('退出', self)
        exit_action.setShortcut('Ctrl+Q')
        exit_action.triggered.connect(self.close)
        file_menu.addAction(exit_action)

        # 帮助菜单
        help_menu = menubar.addMenu('帮助')

        about_action = QAction('关于', self)
        about_action.triggered.connect(self.show_about)
        help_menu.addAction(about_action)

        # 创建工具栏
        toolbar = QToolBar("主工具栏")
        toolbar.setIconSize(QSize(16, 16))
        self.addToolBar(toolbar)

        toolbar.addAction(open_action)
        toolbar.addAction(save_action)

        # 创建主布局
        main_layout = QVBoxLayout()

        # 创建选项卡
        self.tab_widget = QTabWidget()
        self.tab_widget.setStyleSheet("""
            QTabWidget::pane {
                border: 1px solid #C2C7CB;
                background: white;
            }
            QTabWidget::tab-bar {
                left: 5px;
            }
            QTabBar::tab {
                background: #E0E0E0;
                border: 1px solid #C4C4C3;
                padding: 8px 16px;
                margin-right: 2px;
                border-top-left-radius: 4px;
                border-top-right-radius: 4px;
            }

            QTabBar::tab:selected {
                background: #4A708B;
                color: white;
                border-color: #4A708B;
            }
        """)

        # 创建数据加载选项卡
        load_tab = QWidget()
        load_layout = QVBoxLayout(load_tab)

        # 添加文件选择按钮
        file_layout = QHBoxLayout()

        self.file_label = QLabel('未选择文件')
        self.file_label.setStyleSheet("padding: 5px;")
        file_btn = QPushButton('选择OTT_MR文件')
        file_btn.setStyleSheet("padding: 5px;")
        file_btn.clicked.connect(self.select_file)
        file_layout.addWidget(self.file_label, 1)
        file_layout.addWidget(file_btn)
        load_layout.addLayout(file_layout)

        # 在文件选择区域添加数据源选择
        source_layout = QHBoxLayout()
        source_layout.addWidget(QLabel('数据源类型:'))
        self.source_combo = QComboBox()
        self.source_combo.addItem("44列标准格式")
        self.source_combo.addItem("51列扩展格式")
        self.source_combo.setStyleSheet("padding: 5px;")
        source_layout.addWidget(self.source_combo)
        file_layout.addLayout(source_layout)  # 添加到文件选择布局中

        # 添加进度条
        self.progress_bar = QProgressBar()
        self.progress_bar.setStyleSheet("""
                    QProgressBar {
                        border: 1px solid #C4C4C3;
                        border-radius: 2px;
                        text-align: center;
                        height: 16px;
                    }
                    QProgressBar::chunk {
                        background-color: #4A708B;
                        width: 10px;
                        margin: 0.5px;
                    }
                """)
        load_layout.addWidget(self.progress_bar)

        # 创建文件列表和数据预览的分割布局
        splitter = QSplitter(Qt.Horizontal)
        splitter.setStyleSheet("QSplitter::handle { background-color: #E0E0E0; }")

        # 左侧面板 - 文件列表
        file_list_panel = QWidget()
        file_list_layout = QVBoxLayout(file_list_panel)

        # 文件列表标题
        self.file_list_label = QLabel('已选择文件: 0个')
        self.file_list_label.setStyleSheet("padding: 5px; font-style: italic; font-weight: bold;")
        file_list_layout.addWidget(self.file_list_label)

        # 文件列表滚动区域
        self.file_list_scroll = QScrollArea()
        self.file_list_scroll.setWidgetResizable(True)
        self.file_list_scroll.setStyleSheet("border: 1px solid #C4C4C3; border-radius: 2px;")

        # 文件列表容器
        self.file_list_container = QWidget()
        self.file_list_layout = QVBoxLayout(self.file_list_container)

        # 将文件列表容器添加到滚动区域
        self.file_list_scroll.setWidget(self.file_list_container)
        file_list_layout.addWidget(self.file_list_scroll)

        # 设置左侧面板最小宽度
        file_list_panel.setMinimumWidth(300)
        file_list_panel.setMaximumWidth(400)

        # 右侧面板 - 数据预览
        preview_panel = QWidget()
        preview_layout = QVBoxLayout(preview_panel)

        # 数据预览标题
        preview_layout.addWidget(QLabel('数据预览:'))

        # 创建表格视图容器
        table_container = QWidget()
        table_layout = QVBoxLayout(table_container)

        # 创建表格视图
        self.table_view = QTableView()
        self.table_view.setStyleSheet("""
                    QTableView {
                        border: 1px solid #C4C4C3;
                        border-radius: 2px;
                        gridline-color: #E0E0E0;
                    }
                    QHeaderView::section {
                        background-color: #F0F0F0;
                        padding: 4px;
                        border: 1px solid #C4C4C3;
                        border-left: 0px;
                        border-top: 0px;
                    }
                    QHeaderView::section:first {
                        border-left: 1px solid #C4C4C3;
                    }
                """)

        # 设置水平和垂直滚动条策略
        self.table_view.setHorizontalScrollBarPolicy(Qt.ScrollBarAsNeeded)
        self.table_view.setVerticalScrollBarPolicy(Qt.ScrollBarAsNeeded)

        # 设置表头
        self.table_view.horizontalHeader().setSectionResizeMode(QHeaderView.Interactive)
        self.table_view.horizontalHeader().setStretchLastSection(True)
        self.table_view.verticalHeader().setSectionResizeMode(QHeaderView.ResizeToContents)

        # 启用表格视图的水平和垂直滚动
        self.table_view.setHorizontalScrollMode(QTableView.ScrollPerPixel)
        self.table_view.setVerticalScrollMode(QTableView.ScrollPerPixel)

        # 添加表格视图到容器
        table_layout.addWidget(self.table_view)

        # 添加数据统计信息
        self.stats_label = QLabel('')
        self.stats_label.setStyleSheet("padding: 5px; font-style: italic;")
        table_layout.addWidget(self.stats_label)

        # 添加表格容器到预览布局
        preview_layout.addWidget(table_container)

        # 将左右面板添加到分割器
        splitter.addWidget(file_list_panel)
        splitter.addWidget(preview_panel)

        # 设置初始分割比例 (左侧30%，右侧70%)
        splitter.setSizes([300, 700])

        # 将分割器添加到加载布局
        load_layout.addWidget(splitter)

        # 创建数据处理选项卡
        process_tab = QWidget()
        process_layout = QVBoxLayout(process_tab)

        # 创建分组框
        data_clean_group = QGroupBox("数据清理选项")
        data_clean_layout = QVBoxLayout(data_clean_group)

        # 添加列选择区域
        data_clean_layout.addWidget(QLabel('选择需要保留数据的列:'))

        # 创建滚动区域
        scroll_area = QScrollArea()
        scroll_area.setWidgetResizable(True)
        scroll_area.setStyleSheet("border: 1px solid #C4C4C3; border-radius: 2px;")

        # 创建列选择容器
        column_container = QWidget()
        self.column_layout = QGridLayout(column_container)  # 使用网格布局

        # 添加全选/取消全选按钮
        select_buttons_layout = QHBoxLayout()
        select_all_btn = QPushButton('全选')
        select_all_btn.setStyleSheet("padding: 5px;")
        select_all_btn.clicked.connect(self.select_all_columns)
        deselect_all_btn = QPushButton('取消全选')
        deselect_all_btn.setStyleSheet("padding: 5px;")
        deselect_all_btn.clicked.connect(self.deselect_all_columns)
        select_buttons_layout.addWidget(select_all_btn)
        select_buttons_layout.addWidget(deselect_all_btn)
        select_buttons_layout.addStretch()

        # 将列选择容器添加到滚动区域
        scroll_area.setWidget(column_container)

        # 添加数据清理选项
        clean_options_layout = QHBoxLayout()
        self.remove_duplicates_checkbox = QCheckBox("移除重复行")
        self.remove_nan_checkbox = QCheckBox("移除所选列中的空值")
        clean_options_layout.addWidget(self.remove_duplicates_checkbox)
        clean_options_layout.addWidget(self.remove_nan_checkbox)
        clean_options_layout.addStretch()

        # 添加"导出是否忽略未选中列"选项
        self.ignore_unselected_checkbox = QCheckBox("导出是否忽略未选中列")
        self.ignore_unselected_checkbox.setStyleSheet("padding: 5px;")
        self.ignore_unselected_checkbox.setToolTip("选中此项将选中的列，不选中则保留所有列但基于选中列进行过滤")
        clean_options_layout.addWidget(self.ignore_unselected_checkbox)

        # 将滚动区域和按钮添加到清理布局
        data_clean_layout.addLayout(select_buttons_layout)
        data_clean_layout.addWidget(scroll_area)
        data_clean_layout.addLayout(clean_options_layout)

        # 创建时间分割分组框
        time_split_group = QGroupBox("时间分割选项")
        time_split_layout = QVBoxLayout(time_split_group)

        # 添加输出目录选择
        output_layout = QHBoxLayout()
        self.output_label = QLabel('未选择输出目录')
        self.output_label.setStyleSheet("padding: 5px;")
        output_btn = QPushButton('选择输出目录')
        output_btn.setStyleSheet("padding: 5px;")
        output_btn.clicked.connect(self.select_output_dir)
        output_layout.addWidget(self.output_label, 1)
        output_layout.addWidget(output_btn)
        time_split_layout.addLayout(output_layout)

        # 添加时间间隔选择
        interval_layout = QHBoxLayout()
        interval_layout.addWidget(QLabel('时间间隔:'))
        self.interval_combo = QComboBox()
        self.interval_combo.addItems(['1小时', '5小时', '12小时', '1天'])
        self.interval_combo.setStyleSheet("padding: 5px;")
        interval_layout.addWidget(self.interval_combo)
        time_split_layout.addLayout(interval_layout)

        # 添加输出格式选择
        format_layout = QHBoxLayout()
        format_layout.addWidget(QLabel('输出格式:'))
        self.format_combo = QComboBox()
        self.format_combo.addItems(['CSV', 'XLSX'])
        self.format_combo.setStyleSheet("padding: 5px;")
        format_layout.addWidget(self.format_combo)
        time_split_layout.addLayout(format_layout)

        # 添加是否仅清理数据的选项
        self.only_clean_checkbox = QCheckBox("仅清理数据而不进行时间分割")
        self.only_clean_checkbox.setStyleSheet("padding: 5px;")
        time_split_layout.addWidget(self.only_clean_checkbox)

        # 添加执行按钮
        process_btn = QPushButton('开始处理数据')
        process_btn.setStyleSheet("padding: 8px; background-color: #4A708B; color: white; border-radius: 4px;")
        process_btn.clicked.connect(self.process_data)
        time_split_layout.addWidget(process_btn)

        # 添加处理进度条
        self.process_progress = QProgressBar()
        self.process_progress.setStyleSheet("""
                    QProgressBar {
                        border: 1px solid #C4C4C3;
                        border-radius: 2px;
                        text-align: center;
                        height: 16px;
                    }
                    QProgressBar::chunk {
                        background-color: #4A708B;
                        width: 10px;
                        margin: 0.5px;
                    }
                """)
        time_split_layout.addWidget(self.process_progress)

        # 添加保存按钮
        save_btn = QPushButton('保存处理后的数据')
        save_btn.setStyleSheet("padding: 8px; background-color: #4A708B; color: white; border-radius: 4px;")
        save_btn.clicked.connect(self.save_processed_data)
        time_split_layout.addWidget(save_btn)

        # 将两个分组框添加到处理布局
        process_layout.addWidget(data_clean_group)
        process_layout.addWidget(time_split_group)

        # 创建栅格可视化选项卡
        grid_tab = QWidget()
        grid_layout = QVBoxLayout(grid_tab)

        # 添加AOI文件选择
        aoi_layout = QHBoxLayout()
        aoi_layout.addWidget(QLabel('AOI shp文件:'))
        self.aoi_label = QLabel('未选择文件')
        self.aoi_label.setStyleSheet("padding: 5px; color: #666;")
        aoi_btn = QPushButton('选择shp文件')
        aoi_btn.setStyleSheet("padding: 5px;")
        aoi_btn.clicked.connect(self.select_aoi_file)
        aoi_layout.addWidget(self.aoi_label, 1)
        aoi_layout.addWidget(aoi_btn)
        grid_layout.addLayout(aoi_layout)
        # 添加建筑物shp文件选择
        building_layout = QHBoxLayout()
        building_layout.addWidget(QLabel('建筑物shp文件:'))
        self.building_label = QLabel('未选择文件')
        self.building_label.setStyleSheet("padding: 5px; color: #666;")
        building_btn = QPushButton('选择shp文件')
        building_btn.setStyleSheet("padding: 5px;")
        building_btn.clicked.connect(self.select_building_file)
        building_layout.addWidget(self.building_label, 1)
        building_layout.addWidget(building_btn)
        grid_layout.addLayout(building_layout)
        # 添加离散点导入功能
        discrete_points_layout = QHBoxLayout()
        discrete_points_layout.addWidget(QLabel('导入离散点数据:'))
        self.discrete_points_label = QLabel('未选择文件')
        self.discrete_points_label.setStyleSheet("padding: 5px; color: #666;")
        discrete_points_btn = QPushButton('选择Excel文件')
        discrete_points_btn.setStyleSheet("padding: 5px;")
        discrete_points_btn.clicked.connect(self.select_discrete_points_file)
        discrete_points_layout.addWidget(self.discrete_points_label, 1)
        discrete_points_layout.addWidget(discrete_points_btn)
        grid_layout.addLayout(discrete_points_layout)

        # 添加偏移量输入
        offset_layout = QHBoxLayout()
        offset_layout.addWidget(QLabel('经度偏移(度):'))
        self.lon_offset_spin = QDoubleSpinBox()
        self.lon_offset_spin.setRange(-1.0, 1.0)
        self.lon_offset_spin.setValue(0.0)
        self.lon_offset_spin.setSingleStep(0.0001)
        self.lon_offset_spin.setDecimals(6)
        self.lon_offset_spin.setStyleSheet("padding: 5px;")
        offset_layout.addWidget(self.lon_offset_spin)

        offset_layout.addWidget(QLabel('纬度偏移(度):'))
        self.lat_offset_spin = QDoubleSpinBox()
        self.lat_offset_spin.setRange(-1.0, 1.0)
        self.lat_offset_spin.setValue(0.0)
        self.lat_offset_spin.setSingleStep(0.0001)
        self.lat_offset_spin.setDecimals(6)
        self.lat_offset_spin.setStyleSheet("padding: 5px;")
        offset_layout.addWidget(self.lat_offset_spin)
        grid_layout.addLayout(offset_layout)

        # 添加离散点偏移量输入
        discrete_offset_layout = QHBoxLayout()
        discrete_offset_layout.addWidget(QLabel('离散点经度偏移(度):'))
        self.discrete_lon_offset_spin = QDoubleSpinBox()
        self.discrete_lon_offset_spin.setRange(-1.0, 1.0)
        self.discrete_lon_offset_spin.setValue(0.0)
        self.discrete_lon_offset_spin.setSingleStep(0.0001)
        self.discrete_lon_offset_spin.setDecimals(6)
        self.discrete_lon_offset_spin.setStyleSheet("padding: 5px;")
        discrete_offset_layout.addWidget(self.discrete_lon_offset_spin)

        discrete_offset_layout.addWidget(QLabel('离散点纬度偏移(度):'))
        self.discrete_lat_offset_spin = QDoubleSpinBox()
        self.discrete_lat_offset_spin.setRange(-1.0, 1.0)
        self.discrete_lat_offset_spin.setValue(0.0)
        self.discrete_lat_offset_spin.setSingleStep(0.0001)
        self.discrete_lat_offset_spin.setDecimals(6)
        self.discrete_lat_offset_spin.setStyleSheet("padding: 5px;")
        discrete_offset_layout.addWidget(self.discrete_lat_offset_spin)
        grid_layout.addLayout(discrete_offset_layout)

        # 添加网格大小选择
        grid_size_layout = QHBoxLayout()
        grid_size_layout.addWidget(QLabel('网格大小(米):'))
        self.grid_spin = QDoubleSpinBox()
        self.grid_spin.setRange(5, 200)
        self.grid_spin.setValue(20)
        self.grid_spin.setSingleStep(5)
        self.grid_spin.setStyleSheet("padding: 5px;")
        grid_size_layout.addWidget(self.grid_spin)
        grid_layout.addLayout(grid_size_layout)

        # 添加AOI筛选选项
        aoi_filter_layout = QHBoxLayout()
        self.aoi_filter_checkbox = QCheckBox("仅处理AOI内部数据")
        self.aoi_filter_checkbox.setStyleSheet("padding: 5px;")
        self.aoi_filter_checkbox.setToolTip("勾选此项将只处理位于AOI边界内部的数据点")
        aoi_filter_layout.addWidget(self.aoi_filter_checkbox)
        aoi_filter_layout.addStretch()
        grid_layout.addLayout(aoi_filter_layout)

        # 添加输出目录选择
        output_dir_layout = QHBoxLayout()
        output_dir_layout.addWidget(QLabel('输出目录:'))
        self.grid_output_label = QLabel('未选择目录')
        self.grid_output_label.setStyleSheet("padding: 5px; color: #666;")
        grid_output_btn = QPushButton('选择目录')
        grid_output_btn.setStyleSheet("padding: 5px;")
        grid_output_btn.clicked.connect(self.select_grid_output_dir)
        output_dir_layout.addWidget(self.grid_output_label, 1)
        output_dir_layout.addWidget(grid_output_btn)
        grid_layout.addLayout(output_dir_layout)

        # 添加执行按钮
        grid_btn = QPushButton('生成栅格化数据')
        grid_btn.setStyleSheet("padding: 8px; background-color: #4A708B; color: white; border-radius: 4px;")
        grid_btn.clicked.connect(self.generate_grid_data)
        grid_layout.addWidget(grid_btn)

        # 添加进度条
        self.grid_progress = QProgressBar()
        self.grid_progress.setStyleSheet("""
                    QProgressBar {
                        border: 1px solid #C4C4C3;
                        border-radius: 2px;
                        text-align: center;
                        height: 16px;
                    }
                    QProgressBar::chunk {
                        background-color: #4A708B;
                        width: 10px;
                        margin: 0.5px;
                    }
                """)
        grid_layout.addWidget(self.grid_progress)

        # 添加查看按钮
        self.view_btn = QPushButton('查看可视化结果')
        self.view_btn.setStyleSheet("padding: 8px; background-color: #4A708B; color: white; border-radius: 4px;")
        self.view_btn.setEnabled(False)
        self.view_btn.clicked.connect(self.view_grid_results)
        grid_layout.addWidget(self.view_btn)

        # 将选项卡添加到选项卡控件
        self.tab_widget.addTab(load_tab, '数据加载')
        self.tab_widget.addTab(process_tab, '数据处理')
        self.tab_widget.addTab(grid_tab, '栅格可视化')

        # 将选项卡控件添加到主布局
        main_layout.addWidget(self.tab_widget)

        # 设置中心部件
        central_widget = QWidget()
        central_widget.setLayout(main_layout)
        self.setCentralWidget(central_widget)

        # 创建状态栏
        self.statusBar = QStatusBar()
        self.setStatusBar(self.statusBar)
        self.statusBar.showMessage('就绪')

        # 设置整体样式
        self.setStyleSheet("""
                    QMainWindow {
                        background-color: #F8F8F8;
                    }
                    QLabel {
                        font-family: 'SimHei', 'Microsoft YaHei', sans-serif;
                    }
                    QPushButton {
                        font-family: 'SimHei', 'Microsoft YaHei', sans-serif;
                    }
                    QComboBox {
                        font-family: 'SimHei', 'Microsoft YaHei', sans-serif;
                    }
                    QTableView {
                        font-family: 'SimHei', 'Microsoft YaHei', sans-serif;
                    }
                    QHeaderView::section {
                        font-family: 'SimHei', 'Microsoft YaHei', sans-serif;
                    }
                    QTabWidget {
                        font-family: 'SimHei', 'Microsoft YaHei', sans-serif;
                    }
                """)

        # 初始化临时目录
        self.temp_dir = tempfile.mkdtemp(prefix="ott_mr_")

    def select_building_file(self):
        """选择建筑物shp文件"""
        file_path, _ = QFileDialog.getOpenFileName(self, '选择建筑物shp文件', '', 'Shapefiles (*.shp)')
        if file_path:
            self.building_shp_path = file_path
            self.building_label.setText(os.path.basename(file_path))
            self.statusBar.showMessage(f'已选择建筑物文件: {file_path}')

    def select_discrete_points_file(self):
        """选择离散点Excel文件"""
        file_path, _ = QFileDialog.getOpenFileName(self, '选择离散点数据文件', '',
                                                   'Excel Files (*.xlsx *.xls);;All Files (*)')
        if file_path:
            try:
                # 读取Excel文件
                df = pd.read_excel(file_path)

                # 检查必要的列
                required_columns = ['经度', '纬度']
                for col in required_columns:
                    if col not in df.columns:
                        QMessageBox.warning(self, '错误', f'Excel文件中缺少必要的列: {col}')
                        return

                # 转换数据格式
                self.discrete_points = []
                for _, row in df.iterrows():
                    point = {}
                    for col in df.columns:
                        # 处理空值
                        value = row[col]
                        if pd.isna(value):
                            value = "暂无"
                        point[col] = value
                    self.discrete_points.append(point)

                self.discrete_points_label.setText(os.path.basename(file_path))
                self.statusBar.showMessage(f'已导入离散点数据: {len(self.discrete_points)}个点')

            except Exception as e:
                QMessageBox.warning(self, '导入错误', f'导入Excel文件时出错: {str(e)}')
                self.statusBar.showMessage(f'导入Excel文件失败: {str(e)}')

    def select_file(self):
        """选择OTT_MR文件（支持多选）"""
        file_paths, _ = QFileDialog.getOpenFileNames(self, '选择OTT_MR文件', '', 'Text Files (*.txt)')
        if file_paths:
            # 更新文件路径列表
            self.file_paths = file_paths

            # 更新文件标签
            if len(file_paths) == 1:
                self.file_label.setText(file_paths[0])
            else:
                self.file_label.setText(f"已选择 {len(file_paths)} 个文件")

            # 更新文件列表显示
            self.update_file_list()

            self.statusBar.showMessage(f'已选择 {len(file_paths)} 个文件')

            # 设置数据源类型
            self.data_source_type = 44 if self.source_combo.currentIndex() == 0 else 51

            # 清理之前的临时文件
            if self.temp_dir:
                try:
                    shutil.rmtree(self.temp_dir)
                except:
                    pass
            self.temp_dir = tempfile.mkdtemp(prefix="ott_mr_")
            self.temp_files = []

            # 询问用户是否立即加载文件
            reply = QMessageBox.question(self, '确认',
                                         f'已选择 {len(file_paths)} 个文件，是否立即加载？',
                                         QMessageBox.Yes | QMessageBox.No, QMessageBox.Yes)
            if reply == QMessageBox.Yes:
                self.load_data(file_paths)

    def select_aoi_file(self):
        """选择AOI shp文件"""
        file_path, _ = QFileDialog.getOpenFileName(self, '选择AOI shp文件', '', 'Shapefiles (*.shp)')
        if file_path:
            self.shp_path = file_path
            self.aoi_label.setText(os.path.basename(file_path))
            self.statusBar.showMessage(f'已选择AOI文件: {file_path}')

    def select_grid_output_dir(self):
        """选择栅格化输出目录"""
        dir_path = QFileDialog.getExistingDirectory(self, '选择输出目录')
        if dir_path:
            self.grid_output_dir = dir_path
            self.grid_output_label.setText(dir_path)
            self.statusBar.showMessage(f'已选择输出目录: {dir_path}')

    def load_data(self, file_paths):
        """加载多个数据文件"""
        self.progress_bar.setValue(0)
        self.progress_bar.setVisible(True)

        # 创建并启动数据加载线程
        self.loader_thread = DataLoaderThread(file_paths, self.data_source_type)
        self.loader_thread.progress_update.connect(self.update_progress)
        self.loader_thread.data_loaded.connect(self.data_loaded)
        self.loader_thread.start()

    def update_progress(self, value, message):
        """更新进度条和状态栏消息"""
        self.progress_bar.setValue(value)
        self.statusBar.showMessage(message)

    def data_loaded(self, temp_files, loaded_files, file_row_counts, column_names):
        """数据加载完成后的处理"""
        self.temp_files = temp_files
        self.loaded_files = loaded_files
        self.file_row_counts = file_row_counts  # 存储文件行数统计
        self.current_columns = column_names  # 存储当前列名
        self.progress_bar.setVisible(False)

        if temp_files:
            # 尝试读取前10000行用于预览
            try:
                preview_dfs = []
                total_rows = 0
                for temp_file in temp_files[:10]:  # 最多读取10个分块
                    chunk = pd.read_parquet(temp_file)
                    rows_to_read = min(10000 - total_rows, len(chunk))
                    if rows_to_read <= 0:
                        break
                    preview_dfs.append(chunk.head(rows_to_read))
                    total_rows += rows_to_read
                    if total_rows >= 10000:
                        break

                if preview_dfs:
                    preview_df = pd.concat(preview_dfs, ignore_index=True)
                    model = PandasModel(preview_df)
                    self.table_view.setModel(model)
                    self.table_view.resizeColumnsToContents()

                    # 更新统计信息（基于预览数据）
                    self.update_stats(preview_df)

                    # 更新列选择区域的复选框
                    self.update_column_checkboxes(preview_df)  # 传入预览数据
            except Exception as e:
                print(f"预览数据时出错: {e}")

            # 更新文件列表状态
            self.update_file_list_status(loaded_files)

            self.statusBar.showMessage(f'数据加载完成，共{len(temp_files)}个分块，来自{len(loaded_files)}个文件')
            QMessageBox.information(self, '加载完成',
                                    f'数据加载完成，共{len(temp_files)}个分块，来自{len(loaded_files)}个文件')
        else:
            self.statusBar.showMessage('数据加载失败')
            QMessageBox.warning(self, '加载失败', '未能加载数据，请检查文件格式')

    def update_file_list(self):
        """更新文件列表显示"""
        # 清除现有文件标签
        while self.file_list_layout.count():
            item = self.file_list_layout.takeAt(0)
            widget = item.widget()
            if widget:
                widget.deleteLater()

        # 更新文件计数标签
        self.file_list_label.setText(f'已选择文件: {len(self.file_paths)}个')

        # 添加新的文件标签
        for file_path in self.file_paths:
            file_name = os.path.basename(file_path)
            file_label = QLabel(f"• {file_name} (未加载)")
            file_label.setStyleSheet("padding: 2px; color: #888;")
            self.file_list_layout.addWidget(file_label)

        # 添加伸展以保持布局
        self.file_list_layout.addStretch()

    def update_file_list_status(self, loaded_files):
        """更新文件列表的加载状态"""
        # 清除现有文件标签
        while self.file_list_layout.count():
            item = self.file_list_layout.takeAt(0)
            widget = item.widget()
            if widget:
                widget.deleteLater()

        # 更新文件计数标签
        self.file_list_label.setText(f'已选择文件: {len(self.file_paths)}个 (已加载: {len(loaded_files)})')

        # 添加新的文件标签
        for file_path in self.file_paths:
            file_name = os.path.basename(file_path)
            file_label = QLabel(f"• {file_name}")

            # 设置颜色根据加载状态
            if file_name in loaded_files:
                # 获取该文件的总行数
                row_count = self.file_row_counts.get(file_name, 0)
                file_label.setText(f"• {file_name} ({row_count}行)")
                file_label.setStyleSheet("padding: 2px; color: #28a745;")  # 绿色表示已加载
            else:
                file_label.setStyleSheet("padding: 2px; color: #dc3545;")  # 红色表示加载失败

            self.file_list_layout.addWidget(file_label)

        # 添加伸展以保持布局
        self.file_list_layout.addStretch()

    def update_stats(self, df):
        """更新数据统计信息"""
        stats_text = f"数据统计: {len(df)} 行 x {len(df.columns)} 列 (预览)"

        # 计算文件来源统计
        if '文件名' in df.columns:
            file_counts = df['文件名'].value_counts()
            stats_text += f" | 来自 {len(file_counts)} 个文件"
            for file_name, count in file_counts.items():
                stats_text += f" | {file_name}: {count}行"

        # 计算RSRP统计信息（根据数据源类型）
        if self.data_source_type == 51:
            # 51列数据源，分别统计4G和5G的RSRP
            if 'RSRP_4G' in df.columns:
                rsrp_4g_values = pd.to_numeric(df['RSRP_4G'], errors='coerce')
                valid_rsrp_4g = rsrp_4g_values.dropna()
                if not valid_rsrp_4g.empty:
                    stats_text += f" | RSRP_4G: 平均 {valid_rsrp_4g.mean():.2f} dBm, 最小 {valid_rsrp_4g.min():.2f} dBm, 最大 {valid_rsrp_4g.max():.2f} dBm"

            if 'RSRP_5G' in df.columns:
                rsrp_5g_values = pd.to_numeric(df['RSRP_5G'], errors='coerce')
                valid_rsrp_5g = rsrp_5g_values.dropna()
                if not valid_rsrp_5g.empty:
                    stats_text += f" | RSRP_5G: 平均 {valid_rsrp_5g.mean():.2f} dBm, 最小 {valid_rsrp_5g.min():.2f} dBm, 最大 {valid_rsrp_5g.max():.2f} dBm"
        else:
            # 44列数据源，统一RSRP列
            if 'RSRP' in df.columns:
                rsrp_values = pd.to_numeric(df['RSRP'], errors='coerce')
                valid_rsrp = rsrp_values.dropna()
                if not valid_rsrp.empty:
                    stats_text += f" | RSRP: 平均 {valid_rsrp.mean():.2f} dBm, 最小 {valid_rsrp.min():.2f} dBm, 最大 {valid_rsrp.max():.2f} dBm"

        # 计算SINR统计信息
        if 'SINR' in df.columns:
            sinr_values = pd.to_numeric(df['SINR'], errors='coerce')
            valid_sinr = sinr_values.dropna()
            if not valid_sinr.empty:
                stats_text += f" | SINR: 平均 {valid_sinr.mean():.2f} dB, 最小 {valid_sinr.min():.2f} dB, 最大 {valid_sinr.max():.2f} dB"

        self.stats_label.setText(stats_text)

    def update_column_checkboxes(self, df):
        """更新列选择区域的复选框"""
        # 清除现有复选框
        while self.column_layout.count():
            item = self.column_layout.takeAt(0)
            widget = item.widget()
            if widget:
                widget.deleteLater()

        # 添加新的复选框
        self.checkboxes = {}
        if df is not None:
            # 使用当前列名
            columns = self.current_columns

            for i, column in enumerate(columns):
                row, col = divmod(i, 4)  # 每行4个复选框
                checkbox = QCheckBox(column)
                checkbox.setStyleSheet("padding: 2px;")

                # 默认选中重要列
                important_columns = [
                    "采样时间", "网络类型", "运营商", "小区ID", "SINR",
                    "经度（WGS84）", "纬度（WGS84）", "文件名"
                ]

                # 根据数据源类型添加不同的RSRP列
                if self.data_source_type == 51:
                    important_columns.extend(["RSRP_4G", "RSRP_5G", "设备IMSI", "TAC", "数据流量", "上行带宽", "下行带宽"])
                else:
                    important_columns.extend(["RSRP"])

                if column in important_columns:
                    checkbox.setChecked(True)

                self.checkboxes[column] = checkbox
                self.column_layout.addWidget(checkbox, row, col)
        else:
            # 没有数据时显示提示
            no_data_label = QLabel("请先加载数据")
            no_data_label.setStyleSheet("padding: 10px; font-style: italic; color: #888;")
            self.column_layout.addWidget(no_data_label, 0, 0, 1, 4)  # 跨4列显示

    def select_all_columns(self):
        """全选所有列"""
        for checkbox in self.checkboxes.values():
            checkbox.setChecked(True)

    def deselect_all_columns(self):
        """取消全选所有列"""
        for checkbox in self.checkboxes.values():
            checkbox.setChecked(False)

    def select_output_dir(self):
        """选择输出目录"""
        dir_path = QFileDialog.getExistingDirectory(self, '选择输出目录')
        if dir_path:
            self.output_label.setText(dir_path)
            self.statusBar.showMessage(f'已选择输出目录: {dir_path}')

    def process_data(self):
        if not self.temp_files:
            QMessageBox.warning(self, '错误', '请先加载数据')
            return

        # 获取用户选择的列
        selected_columns = [column for column, checkbox in self.checkboxes.items()
                            if checkbox.isChecked()]

        # 确保选择了必要的列（根据数据源类型）
        if self.data_source_type == 51:
            required_columns = ["经度（WGS84）", "纬度（WGS84）", "RSRP_4G", "RSRP_5G"]
        else:
            required_columns = ["经度（WGS84）", "纬度（WGS84）", "RSRP"]

        missing_required = [col for col in required_columns if col not in selected_columns]

        # 初始化回复变量
        reply = QMessageBox.No

        if missing_required:
            reply = QMessageBox.question(
                self, '警告',
                f"缺少必要列: {', '.join(missing_required)}。这些列是地图可视化必需的。是否继续？",
                QMessageBox.Yes | QMessageBox.No, QMessageBox.No
            )
            if reply == QMessageBox.No:
                return
            else:
                # 添加缺失的必要列
                selected_columns.extend(missing_required)

        # 检查是否需要时间分割
        only_clean = self.only_clean_checkbox.isChecked()

        if not only_clean:
            # 检查输出目录是否设置
            if not self.output_label.text() or self.output_label.text() == '未选择输出目录':
                QMessageBox.warning(self, '错误', '请选择输出目录')
                self.statusBar.showMessage('操作失败: 请选择输出目录')
                return

            # 检查时间列是否选择
            if '采样时间' not in selected_columns:
                reply = QMessageBox.question(self, '警告',
                                             '时间分割需要"采样时间"列，但您未选择该列。是否继续？',
                                             QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
                if reply == QMessageBox.No:
                    return
                else:
                    # 如果用户选择继续，则添加采样时间列
                    selected_columns.append('采样时间')

        self.process_progress.setValue(0)
        self.process_progress.setVisible(True)

        # 获取用户选择的参数
        time_interval = self.interval_combo.currentText() if not only_clean else None
        output_format = self.format_combo.currentText() if not only_clean else None
        output_dir = self.output_label.text() if not only_clean else None
        remove_duplicates = self.remove_duplicates_checkbox.isChecked()
        remove_nan = self.remove_nan_checkbox.isChecked()
        ignore_unselected = self.ignore_unselected_checkbox.isChecked()  # 获取是否忽略未选中列的选项

        self.statusBar.showMessage('正在处理数据...')

        # 创建并启动数据处理线程
        self.processor_thread = DataProcessorThread(
            self.temp_files, output_dir, time_interval, output_format,
            selected_columns, remove_duplicates, remove_nan, ignore_unselected
        )
        self.processor_thread.progress_update.connect(self.update_process_progress)
        self.processor_thread.process_complete.connect(self.process_complete)
        self.processor_thread.error_occurred.connect(self.process_error)
        self.processor_thread.start()

    def update_process_progress(self, value, message):
        """更新处理进度条"""
        self.process_progress.setValue(value)
        self.statusBar.showMessage(message)

    def process_complete(self, processed_dir):
        """数据处理完成后的处理"""
        self.process_progress.setVisible(False)
        self.processed_temp_dir = processed_dir

        # 检查是否执行了时间分割
        if not self.only_clean_checkbox.isChecked():
            time_interval = self.interval_combo.currentText()
            output_dir = self.output_label.text()
            self.statusBar.showMessage(f'数据处理完成: 已按{time_interval}分割并保存到{output_dir}')
            QMessageBox.information(self, '处理完成',
                                    f'数据处理完成，已按{time_interval}分割并保存到{output_dir}')
        else:
            self.statusBar.showMessage('数据清理完成')
            QMessageBox.information(self, '清理完成', '数据清理完成')

    def process_error(self, error_msg):
        """处理过程中发生错误"""
        self.process_progress.setVisible(False)
        QMessageBox.warning(self, '处理错误', f'数据处理过程中发生错误:\n{error_msg}')
        self.statusBar.showMessage(f'处理错误: {error_msg}')

    def save_processed_data(self):
        """保存处理后的数据"""
        if not self.processed_temp_dir or not os.path.exists(self.processed_temp_dir):
            QMessageBox.warning(self, '错误', '请先处理数据')
            self.statusBar.showMessage('操作失败: 请先处理数据')
            return

        # 获取输出文件路径
        file_path, _ = QFileDialog.getSaveFileName(self, '保存处理后的数据', '',
                                                   'Parquet Files (*.parquet);;CSV Files (*.csv)')
        if file_path:
            try:
                self.statusBar.showMessage(f'正在保存数据到{file_path}...')

                # 合并所有临时文件
                dfs = []
                for temp_file in os.listdir(self.processed_temp_dir):
                    if temp_file.endswith(".parquet"):
                        df = pd.read_parquet(os.path.join(self.processed_temp_dir, temp_file))
                        dfs.append(df)

                if dfs:
                    combined_df = pd.concat(dfs, ignore_index=True)

                    if file_path.endswith('.parquet'):
                        combined_df.to_parquet(file_path)
                    elif file_path.endswith('.csv'):
                        combined_df.to_csv(file_path, index=False)
                    else:
                        # 默认保存为Parquet
                        file_path += '.parquet'
                        combined_df.to_parquet(file_path)

                    self.statusBar.showMessage(f'数据保存成功: {file_path}')
                    QMessageBox.information(self, '保存成功', f'数据已保存到{file_path}')
                else:
                    self.statusBar.showMessage('没有可保存的数据')
                    QMessageBox.warning(self, '保存失败', '没有可保存的数据')
            except Exception as e:
                self.statusBar.showMessage(f'数据保存失败: {str(e)}')
                QMessageBox.warning(self, '保存失败', f'保存数据时出错: {str(e)}')

    def generate_grid_data(self):
        """生成栅格化数据"""
        if not self.temp_files:
            QMessageBox.warning(self, '错误', '请先加载数据')
            return

        if not self.grid_output_dir:
            QMessageBox.warning(self, '错误', '请选择输出目录')
            return

        # 获取用户输入的偏移量
        lon_offset = self.lon_offset_spin.value()
        lat_offset = self.lat_offset_spin.value()

        # 获取离散点偏移量
        discrete_lon_offset = self.discrete_lon_offset_spin.value()
        discrete_lat_offset = self.discrete_lat_offset_spin.value()

        # 获取网格大小
        grid_size = self.grid_spin.value()

        # 获取是否筛选AOI内部数据
        filter_aoi = self.aoi_filter_checkbox.isChecked()

        self.grid_progress.setValue(0)
        self.grid_progress.setVisible(True)
        self.statusBar.showMessage('正在生成栅格化数据...')

        # 创建并启动栅格可视化线程
        self.grid_thread = GridVisualizationThread(
            self.temp_files,
            self.shp_path,
            self.building_shp_path,  # 添加建筑物shp路径
            grid_size,
            filter_aoi,
            lon_offset,
            lat_offset,
            self.discrete_points,
            self.data_source_type  # 传递数据源类型
        )
        self.grid_thread.progress_update.connect(self.update_grid_progress)
        self.grid_thread.grid_ready.connect(self.grid_data_ready)
        self.grid_thread.error_occurred.connect(self.grid_error)
        self.grid_thread.start()

    def update_grid_progress(self, value, message):
        """更新栅格化进度条"""
        self.grid_progress.setValue(value)
        self.statusBar.showMessage(message)

    def grid_data_ready(self, aoi_geojson, discrete_geojson, grid_geojson, building_geojson):
        """栅格化数据处理完成后的处理"""
        self.grid_progress.setVisible(False)
        self.statusBar.showMessage('栅格化数据处理完成')

        # 保存文件到输出目录
        try:
            # 确保输出目录存在
            os.makedirs(self.grid_output_dir, exist_ok=True)

            # 复制文件到输出目录
            if aoi_geojson and os.path.exists(aoi_geojson):
                shutil.copy(aoi_geojson, os.path.join(self.grid_output_dir, "aoi.geojson"))

            if discrete_geojson and os.path.exists(discrete_geojson):
                shutil.copy(discrete_geojson, os.path.join(self.grid_output_dir, "discrete_points.geojson"))

            if building_geojson and os.path.exists(building_geojson):
                shutil.copy(building_geojson, os.path.join(self.grid_output_dir, "buildings.geojson"))

                # 复制建筑物统计文件
                buildings_stats_path = os.path.join(os.path.dirname(building_geojson), "buildings_stats.geojson")
                if os.path.exists(buildings_stats_path):
                    shutil.copy(buildings_stats_path, os.path.join(self.grid_output_dir, "buildings_stats.geojson"))

            # 复制所有生成的栅格文件和场景文件
            temp_output_dir = os.path.dirname(aoi_geojson) if aoi_geojson else os.path.dirname(discrete_geojson)
            if temp_output_dir:
                for filename in os.listdir(temp_output_dir):
                    if filename.endswith('.geojson') or filename.endswith('.json'):
                        src_path = os.path.join(temp_output_dir, filename)
                        dst_path = os.path.join(self.grid_output_dir, filename)
                        if not os.path.exists(dst_path):
                            shutil.copy(src_path, dst_path)

            # 启用查看按钮
            self.view_btn.setEnabled(True)

            QMessageBox.information(self, '处理完成', f'栅格化数据处理完成，文件已保存到{self.grid_output_dir}')
        except Exception as e:
            QMessageBox.warning(self, '保存错误', f'保存栅格化数据时出错: {str(e)}')

    def grid_error(self, error_msg):
        """栅格化处理过程中发生错误"""
        self.grid_progress.setVisible(False)
        QMessageBox.warning(self, '处理错误', f'栅格化处理过程中发生错误:\n{error_msg}')
        self.statusBar.showMessage(f'栅格化错误: {error_msg}')

    def view_grid_results(self):
        """查看栅格化结果"""
        if self.grid_output_dir:
            # 打开输出目录
            if os.name == 'nt':  # Windows
                os.startfile(self.grid_output_dir)
            elif os.name == 'posix':  # macOS and Linux
                os.system(f'open "{self.grid_output_dir}"')

    def show_about(self):
        """显示关于对话框"""
        QMessageBox.about(self, "关于OTT_MR栅格化分析软件",
                          "OTT_MR栅格化分析工具\n\n"
                          "功能特性：\n"
                          "- 支持44列和51列数据源格式\n"
                          "- 数据清理和时间分割\n"
                          "- 按运营商和网络类型分别栅格化\n"
                          "- 支持场景划分和AOI分析\n"
                          "- 建筑物覆盖分析\n"
                          "- 离散点数据导入和关联\n"
                          "- 支持4G/5G分离RSRP数据处理\n\n"
                          "版本: 2.1\n"
                          "更新日期: 2025-07-08")

    def closeEvent(self, event):
        """关闭窗口时清理临时文件"""
        if self.temp_dir and os.path.exists(self.temp_dir):
            try:
                shutil.rmtree(self.temp_dir)
            except Exception as e:
                print(f"清理临时文件时出错: {e}")

        if self.processed_temp_dir and os.path.exists(self.processed_temp_dir):
            try:
                shutil.rmtree(self.processed_temp_dir)
            except Exception as e:
                print(f"清理处理后的临时文件时出错: {e}")

        event.accept()

if __name__ == '__main__':
    app = QApplication(sys.argv)
    window = OTTMRAnalyzer()
    window.show()
    sys.exit(app.exec_())