#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
浩然大六壬神课 · 网页排盘
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
· 月将加时，天地盘 / 四课 / 三传 / 十二天将 / 旬遁 / 六亲 / 神煞 全出
· 贵人用【甲戊庚牛羊】口诀：
    甲戊庚牛羊，乙己鼠猴乡，丙丁猪鸡位，
    壬癸兔蛇藏，六辛逢虎马，此是贵人方。
· 涉害取用【直取孟仲季】：见机（取四孟）→ 察微（取四仲）→ 缀瑕（取四季），
  不较涉害深浅，同组再等则刚日取干上神、柔日取支上神。

运行：python3 liuren_pan.py
访问：http://127.0.0.1:8081
"""

from __future__ import annotations

import json
from bisect import bisect_right
from datetime import date as _date

import math
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Tuple



# ======================================================================
# 一、基础常量 & 字典
# ======================================================================

GAN = ["甲", "乙", "丙", "丁", "戊", "己", "庚", "辛", "壬", "癸"]
ZHI = ["子", "丑", "寅", "卯", "辰", "巳", "午", "未", "申", "酉", "戌", "亥"]
GAN_IDX = {g: i for i, g in enumerate(GAN)}
ZHI_IDX = {z: i for i, z in enumerate(ZHI)}

GAN_WX = {"甲": "木", "乙": "木", "丙": "火", "丁": "火", "戊": "土",
          "己": "土", "庚": "金", "辛": "金", "壬": "水", "癸": "水"}
ZHI_WX = {"子": "水", "丑": "土", "寅": "木", "卯": "木", "辰": "土", "巳": "火",
          "午": "火", "未": "土", "申": "金", "酉": "金", "戌": "土", "亥": "水"}
GAN_YIN_YANG = {"甲": "阳", "乙": "阴", "丙": "阳", "丁": "阴", "戊": "阳",
                "己": "阴", "庚": "阳", "辛": "阴", "壬": "阳", "癸": "阴"}
ZHI_YIN_YANG = {z: ("阳" if i % 2 == 0 else "阴") for i, z in enumerate(ZHI)}

WX_KE = {"木": "土", "土": "水", "水": "火", "火": "金", "金": "木"}   # a 克 b
WX_SHENG = {"木": "火", "火": "土", "土": "金", "金": "水", "水": "木"}  # a 生 b

# 十干寄宫（甲课寅兮乙课辰，丙戊课巳不须论，丁己课未庚申上，辛戌壬亥是其真，癸课原来丑宫坐）
JI_GONG = {"甲": "寅", "乙": "辰", "丙": "巳", "丁": "未", "戊": "巳",
           "己": "未", "庚": "申", "辛": "戌", "壬": "亥", "癸": "丑"}

# 十二天将（贵蛇雀合勾龙空虎常玄阴后）
# 天将单字简称（盘面用）
JIANG_SHORT = {"贵人": "贵", "螣蛇": "蛇", "朱雀": "雀", "六合": "合", "勾陈": "勾",
               "青龙": "龙", "天空": "空", "白虎": "虎", "太常": "常", "玄武": "玄",
               "太阴": "阴", "天后": "后"}


# 十二天将五行（内战外战之辨所据）
JIANG_WX = {"贵": "土", "蛇": "火", "雀": "火", "合": "木", "勾": "土", "龙": "木",
            "空": "土", "虎": "金", "常": "土", "玄": "水", "阴": "金", "后": "水"}


def wx_of_jiang(name):
    return JIANG_WX.get(j1(name), "")


def j1(name):
    """天将取单字，未收录者取首字"""
    return JIANG_SHORT.get(name, (name or "")[:1])




JIANG = ["贵人", "螣蛇", "朱雀", "六合", "勾陈", "青龙",
         "天空", "白虎", "太常", "玄武", "太阴", "天后"]

JIANG_COLOR = {
    "贵人": "#b8860b", "螣蛇": "#c0392b", "朱雀": "#d35400", "六合": "#27ae60",
    "勾陈": "#8d6e63", "青龙": "#1e8449", "天空": "#95a5a6", "白虎": "#566573",
    "太常": "#b7950b", "玄武": "#2c3e50", "太阴": "#5d6d7e", "天后": "#2980b9",
}

# 月将（神将）名
YUE_JIANG_NAME = {"亥": "登明", "戌": "河魁", "酉": "从魁", "申": "传送",
                  "未": "小吉", "午": "胜光", "巳": "太乙", "辰": "天罡",
                  "卯": "太冲", "寅": "功曹", "丑": "大吉", "子": "神后"}

# 中气换将：雨水亥将，春分戌将，谷雨酉将 ……
ZHONG_QI_TO_JIANG = {"雨水": "亥", "春分": "戌", "谷雨": "酉", "小满": "申",
                     "夏至": "未", "大暑": "午", "处暑": "巳", "秋分": "辰",
                     "霜降": "卯", "小雪": "寅", "冬至": "丑", "大寒": "子"}

# 贵人歌：甲戊庚牛羊，乙己鼠猴乡，丙丁猪鸡位，壬癸兔蛇藏，六辛逢虎马。
# 每干为（昼贵 / 阳贵，夜贵 / 阴贵）
GUI_TABLE = {
    "甲": ("未", "丑"), "乙": ("申", "子"), "丙": ("酉", "亥"), "丁": ("亥", "酉"),
    "戊": ("丑", "未"), "己": ("子", "申"), "庚": ("丑", "未"), "辛": ("寅", "午"),
    "壬": ("卯", "巳"), "癸": ("巳", "卯"),
}
GUI_KOUJUE = "贵人歌：甲戊庚牛羊，乙己鼠猴乡，丙丁猪鸡位，壬癸兔蛇藏，六辛逢虎马，此是贵人方。"

# ---------- 八煞（常用神煞） ----------
DE_TABLE = {"甲": "寅", "己": "寅", "乙": "申", "庚": "申", "丙": "巳", "辛": "巳",
            "丁": "亥", "壬": "亥", "戊": "巳", "癸": "巳"}          # 干德：阳德自处，阴德附阳
LU_TABLE = {"甲": "寅", "乙": "卯", "丙": "巳", "丁": "午", "戊": "巳",
            "己": "午", "庚": "申", "辛": "酉", "壬": "亥", "癸": "子"}   # 日禄
TIAN_MA_SEQ = ["午", "申", "戌", "子", "寅", "辰"]                  # 天马：正月起午，顺行六阳
TAO_TABLE = {"申": "酉", "子": "酉", "辰": "酉", "寅": "卯", "午": "卯", "戌": "卯",
             "巳": "午", "酉": "午", "丑": "午", "亥": "子", "卯": "子", "未": "子"}  # 桃花
REN_TABLE = {"甲": "卯", "乙": "辰", "丙": "午", "丁": "未", "戊": "午",
             "己": "未", "庚": "酉", "辛": "戌", "壬": "子", "癸": "丑"}   # 羊刃
MU_TABLE = {"甲": "未", "乙": "未", "丙": "戌", "丁": "戌", "戊": "辰",
            "己": "辰", "庚": "丑", "辛": "丑", "壬": "辰", "癸": "辰"}    # 日墓（入墓）
SHA_ORDER = ["德", "禄", "驿", "天", "丁", "桃", "刃", "墓"]
SHA_FULL = {"德": "干德", "禄": "日禄", "驿": "驿马", "天": "天马",
            "丁": "旬丁", "桃": "桃花", "刃": "羊刃", "墓": "日墓"}

# ---------- 课经（《六壬大全》课经集）与《毕法赋》对应 ----------
KETI_TEXT = {
    "元首课": ("一上克下，余课无克，为元首，象天。尊能制卑，事从外来，官职首擢。",
                "第一法　前后引从升迁吉"),
    "重审课": ("一下贼上，余课无克，为重审，象地。卑而犯尊，事从内起，先难后成。",
                "第八十六法　将逢内战所谋危"),
    "比用课·知一": ("二克择与日干比者为用，曰知一，亦名比邻。事起同类，狐疑不决。",
                    "第七十六法　彼此猜忌害相随"),
    "涉害课·见机": ("涉害俱深，取四孟上神发用，曰见机。事既有疑，急宜更改。",
                    "第九法　避难逃生须弃旧"),
    "涉害课·察微": ("涉害无孟，取仲上神发用，曰察微。害伏于暗，宜察微防算。",
                    "第八十四法　合中犯杀蜜中砒"),
    "涉害课·缀瑕": ("涉害复等，刚日取干上、柔日取支上，曰缀瑕。两雄交争，众议纷纭。",
                    "第三十二法　三传互克众人欺"),
    "遥克课·蒿矢": ("四课无克，取上神遥克日干为用，曰蒿矢。力弱难伤，虚惊而已。",
                    "第十二法　虽忧狐假虎威仪"),
    "遥克课·弹射": ("无神遥克日，取日干遥克上神为用，曰弹射。我往费力，得少失多。",
                    "第五十七法　费有余而得不足"),
    "昴星课·虎视转蓬": ("无克无遥，刚日仰视地盘酉上神为用，曰虎视转蓬。主惊恐，宜守静。",
                        "第五十四法　虎视逢虎力难施"),
    "昴星课·冬蛇掩目": ("柔日俯视天盘酉下神为用，曰冬蛇掩目。事多暗昧，惟宜潜藏。",
                        "第六法　六阴相继尽昏迷"),
    "别责课": ("四课不全、无克无遥，别取合神为用，曰别责，亦名芜淫。事既不备，借径而行。",
              "第六十四法　夫妇芜淫各有私"),
    "八专课": ("干支同位、止有两课，刚顺柔逆数三为用，曰八专。二人同心，不宜远动。",
              "第四十法　后合占婚岂用媒"),
    "伏吟课·自任": ("伏吟无克，刚日取干上神，中末取刑，曰自任。静中思动，屈不得伸。",
                    "第八十九法　任信丁马须言动"),
    "伏吟课·自信": ("伏吟无克，柔日取支上神，中末取刑，曰自信。不能动身，家宅不宁。",
                    "第八十八法　干支乘墓各昏迷"),
    "伏吟课·有克": ("伏吟用起自刑，传行杜塞，为杜传。事既中止，改求则成。",
                    "第八十二法　不行传者考初时"),
    "返吟课·有克": ("十二神各居冲位，取相克为用，曰返吟，亦名无依。往复无常，惟利复旧。",
                    "第三十三法　有始无终难变易"),
    "返吟课·井栏射·无亲": ("返吟无克，以支辰斜射为用，曰井栏射，又名无亲。无凭无依，速成易破。",
                          "第九十法　来去俱空岂动宜"),
}


# 课经、毕法 标目（依《六壬大全》：卷五—卷八课经，卷九—卷十毕法赋）
# 元组 = (课经象语, 毕法法号, 毕法法句节文)
KETI_BRIEF = {
    "元首课": ("上克下，尊制卑", 1, "引从升迁"),
    "重审课": ("以下犯上", 86, "将逢内战"),
    "比用课·知一": ("二克取比，事有两岐", 76, "彼此猜忌"),
    "涉害课·见机": ("涉害取孟，宜见机", 9, "避难逃生"),
    "涉害课·察微": ("涉害取仲", 84, "合中犯杀"),
    "涉害课·缀瑕": ("涉害复等", 32, "三传互克"),
    "遥克课·蒿矢": ("遥克日干，力弱难伤", 12, "狐假虎威"),
    "遥克课·弹射": ("日克上神，纵得无利", 57, "费余得少"),
    "昴星课·虎视转蓬": ("刚日仰视，虎视转蓬", 54, "虎视逢虎"),
    "昴星课·冬蛇掩目": ("柔日俯视，万事不从", 6, "六阴昏迷"),
    "别责课": ("四课不全，借径而行", 64, "夫妇芜淫"),
    "八专课": ("干支同位，二人同心", 40, "后合占婚"),
    "伏吟课·自任": ("伏吟刚日，自任其刚", 89, "任信丁马"),
    "伏吟课·自信": ("伏吟柔日，静中守常", 88, "干支乘墓"),
    "伏吟课·有克": ("伏吟用刑，守旧待新", 82, "不行考初"),
    "返吟课·有克": ("各居冲位，得失未定", 33, "有始无终"),
    "返吟课·井栏射·无亲": ("斜射取用，来去俱空", 90, "来去俱空"),
}


def keti_brief(keti_full: str):
    if keti_full in KETI_BRIEF:
        return KETI_BRIEF[keti_full]
    for k, v in KETI_BRIEF.items():
        if keti_full.startswith(k.split("·")[0]):
            return v
    return ("", 0, "")


# 毕法取句缘由（课象 → 何以此法）
BIFA_REASON = {
    "元首课": "上克下，尊制卑而事顺，故取「前后引从升迁吉」。",
    "重审课": "下贼上，卑犯尊而内外相战，故取「将逢内战所谋危」。",
    "比用课·知一": "二克并见、以比取一，心怀疑忌，故取「彼此猜忌害相随」。",
    "涉害课·见机": "取孟发用，事始宜改，故取「避难逃生须弃旧」。",
    "涉害课·察微": "取仲而害伏暗处，宜防暗算，故取「合中犯杀蜜中砒」。",
    "涉害课·缀瑕": "两雄并争、众议纷纭，故取「三传互克众人欺」。",
    "遥克课·蒿矢": "遥克力弱、外张内虚，故取「虽忧狐假虎威仪」。",
    "遥克课·弹射": "我往费力而得少，故取「费有余而得不足」。",
    "昴星课·虎视转蓬": "酉为白虎当头，惊恐难施，故取「虎视逢虎力难施」。",
    "昴星课·冬蛇掩目": "阴掩其明、事多暗昧，故取「六阴相继尽昏迷」。",
    "别责课": "课既不备而各怀私，故取「夫妇芜淫各有私」。",
    "八专课": "两课自用、失于检防，故取「后合占婚岂用媒」。",
    "伏吟课·自任": "静极思动，见丁马则动，故取「任信丁马须言动」。",
    "伏吟课·自信": "伏匿不动、家宅昏晦，故取「干支乘墓各昏迷」。",
    "伏吟课·有克": "传行杜塞，事不行当考初传，故取「不行传者考初时」。",
    "返吟课·有克": "往复无常、有始无终，故取「有始无终难变易」。",
    "返吟课·井栏射·无亲": "无凭无依、事多虚动，故取「来去俱空岂动宜」。",
}


def bifa_reason(keti_full: str) -> str:
    if keti_full in BIFA_REASON:
        return BIFA_REASON[keti_full]
    for k, v in BIFA_REASON.items():
        if keti_full.startswith(k.split("·")[0]):
            return v
    return ""


def keti_text(keti_full: str):
    """按课体取课经与毕法；未列者回落按前缀匹配"""
    if keti_full in KETI_TEXT:
        return KETI_TEXT[keti_full]
    for k, v in KETI_TEXT.items():
        if keti_full.startswith(k.split("·")[0]):
            return v
    return ("", "")

# 刑：子刑卯、卯刑子；寅刑巳、巳刑申、申刑寅；丑刑戌、戌刑未、未刑丑；辰午酉亥自刑
XING = {"子": "卯", "卯": "子", "寅": "巳", "巳": "申", "申": "寅",
        "丑": "戌", "戌": "未", "未": "丑", "辰": "辰", "午": "午",
        "酉": "酉", "亥": "亥"}
ZI_XING = {"辰", "午", "酉", "亥"}

# 驿马：申子辰马在寅，寅午戌马在申，巳酉丑马在亥，亥卯未马在巳
YI_MA = {"申": "寅", "子": "寅", "辰": "寅", "寅": "申", "午": "申", "戌": "申",
         "巳": "亥", "酉": "亥", "丑": "亥", "亥": "巳", "卯": "巳", "未": "巳"}

# 十干五合
GAN_HE = {"甲": "己", "己": "甲", "乙": "庚", "庚": "乙", "丙": "辛",
          "辛": "丙", "丁": "壬", "壬": "丁", "戊": "癸", "癸": "戊"}

# 十干禄
GAN_LU = {"甲": "寅", "乙": "卯", "丙": "巳", "丁": "午", "戊": "巳",
          "己": "午", "庚": "申", "辛": "酉", "壬": "亥", "癸": "子"}

# 三合
SAN_HE = {z: ZHI[(i + 4) % 12] for i, z in enumerate(ZHI)}   # 支前三合

MENG = {"寅", "申", "巳", "亥"}   # 四孟
ZHONG = {"子", "午", "卯", "酉"}  # 四仲
JI = {"辰", "戌", "丑", "未"}     # 四季

# 二十四节气（黄经）
TERM_BY_LONGITUDE = {0: "春分", 15: "清明", 30: "谷雨", 45: "立夏", 60: "小满",
                     75: "芒种", 90: "夏至", 105: "小暑", 120: "大暑", 135: "立秋",
                     150: "处暑", 165: "白露", 180: "秋分", 195: "寒露", 210: "霜降",
                     225: "立冬", 240: "小雪", 255: "大雪", 270: "冬至", 285: "小寒",
                     300: "大寒", 315: "立春", 330: "雨水", 345: "惊蛰"}
TERM_LONGITUDE = {v: k for k, v in TERM_BY_LONGITUDE.items()}
ZHONG_QI = ["雨水", "春分", "谷雨", "小满", "夏至", "大暑",
            "处暑", "秋分", "霜降", "小雪", "冬至", "大寒"]
JIE_QI = ["立春", "惊蛰", "清明", "立夏", "芒种", "小暑",
          "立秋", "白露", "寒露", "立冬", "大雪", "小寒"]
JIE_TO_ZHI = {"立春": "寅", "惊蛰": "卯", "清明": "辰", "立夏": "巳", "芒种": "午",
              "小暑": "未", "立秋": "申", "白露": "酉", "寒露": "戌", "立冬": "亥",
              "大雪": "子", "小寒": "丑"}

PINYIN_TERMS = {"XIAO_HAN": "小寒", "DA_HAN": "大寒", "LI_CHUN": "立春",
                "YU_SHUI": "雨水", "JING_ZHE": "惊蛰", "CHUN_FEN": "春分",
                "QING_MING": "清明", "GU_YU": "谷雨", "LI_XIA": "立夏",
                "XIAO_MAN": "小满", "MANG_ZHONG": "芒种", "XIA_ZHI": "夏至",
                "XIAO_SHU": "小暑", "DA_SHU": "大暑", "LI_QIU": "立秋",
                "CHU_SHU": "处暑", "BAI_LU": "白露", "QIU_FEN": "秋分",
                "HAN_LU": "寒露", "SHUANG_JIANG": "霜降", "LI_DONG": "立冬",
                "XIAO_XUE": "小雪", "DA_XUE": "大雪", "DONG_ZHI": "冬至"}

# 课体释义
KETI_DOC = {
    "元首课": "一上克下，尊制卑、上令下行。六壬第一吉体，谋事循理则顺，宜自上而下推动。",
    "重审课": "一下贼上，事起于下、卑犯尊。宜静审详察、先安内而后动，不可躁进。",
    "比用课": "两课以上相克，取与日干阴阳相比者发用（又名知一课），主取舍择类、择善而从。",
    "涉害课": "数课相克、比用不能决，以涉害取用。本局直取孟仲季，不较深浅。",
    "遥克课": "四课全无上下克，取遥相克制者为用，力轻应缓。神克日为蒿矢，日克神为弹射。",
    "昴星课": "四课无克又无遥克，取酉位上下神发用。刚日仰视（虎视转蓬），柔日俯视（冬蛇掩目），主暗昧未明，宜守不宜动。",
    "别责课": "四课不全（只三课）又无克无遥，借干合、支前三合发用，主事有假借、不由正途。",
    "八专课": "日干寄宫与日支同位，干支同处而专，主事涉私昵、易生纠缠，宜自守。",
    "伏吟课": "月将与时支同位，天地盘伏而不动。主迟滞守成、旧事重提；刚日自任、柔日自信，中末以刑相推。",
    "返吟课": "月将与时支相冲，天地盘各居冲位。主反复摇动、去而复来；有克依克发用，无克取支马发用（井栏射·无亲）。",
}

BOARD_POS = {  # 十二宫在 4×4 棋盘中的行列（南上北下、东左西右）
    "巳": (1, 1), "午": (1, 2), "未": (1, 3), "申": (1, 4),
    "辰": (2, 1), "酉": (2, 4),
    "卯": (3, 1), "戌": (3, 4),
    "寅": (4, 1), "丑": (4, 2), "子": (4, 3), "亥": (4, 4),
}


# ======================================================================
# 二、历法引擎（节气 / 干支），与奇门排盘同一套算法
# ======================================================================

def _solar_longitude(jd: float) -> float:
    t = (jd - 2451545.0) / 36525.0
    l0 = 280.46646 + 36000.76983 * t + 0.0003032 * t * t
    m = 357.52911 + 35999.05029 * t - 0.0001537 * t * t
    mr = math.radians(m)
    c = ((1.914602 - 0.004817 * t - 0.000014 * t * t) * math.sin(mr)
         + (0.019993 - 0.000101 * t) * math.sin(2 * mr) + 0.000289 * math.sin(3 * mr))
    omega = 125.04 - 1934.136 * t
    apparent = l0 + c - 0.00569 - 0.00478 * math.sin(math.radians(omega))
    return apparent % 360.0


def _jd_of_datetime(dt: datetime) -> float:
    days = (dt - datetime(2000, 1, 1, 12, 0, 0)).total_seconds() / 86400.0
    return 2451545.0 + days - 8.0 / 24.0


def _datetime_of_jd(jd: float) -> datetime:
    utc = datetime(2000, 1, 1, 12, 0, 0) + timedelta(days=jd - 2451545.0)
    return utc + timedelta(hours=8)


def jdn(year: int, month: int, day: int) -> int:
    a = (14 - month) // 12
    y = year + 4800 - a
    m = month + 12 * a - 3
    return day + (153 * m + 2) // 5 + 365 * y + y // 4 - y // 100 + y // 400 - 32045


def ganzhi_of_index(index: int) -> str:
    return GAN[index % 10] + ZHI[index % 12]


class BuiltinEngine:
    """内置天文近似历法（无 lunar_python 时兜底）"""
    name = "内置天文近似"

    @staticmethod
    def _term_time(year: int, longitude: int) -> datetime:
        target = float(longitude)
        approx = _jd_of_datetime(datetime(year, 3, 20, 12, 0, 0)) + (longitude / 360.0) * 365.2422
        lo, hi = approx - 7.0, approx + 7.0

        def f(x: float) -> float:
            return (_solar_longitude(x) - target + 540.0) % 360.0 - 180.0

        flo, fhi = f(lo), f(hi)
        if flo > fhi:
            if flo > 0:
                flo -= 360.0
            else:
                fhi += 360.0
        for _ in range(80):
            mid = (lo + hi) / 2.0
            fm = f(mid)
            if flo * fm <= 0:
                hi, fhi = mid, fm
            else:
                lo, flo = mid, fm
        return _datetime_of_jd((lo + hi) / 2.0)

    def lunar_text(self, dt: datetime) -> str:
        return ""

    def terms_around(self, dt: datetime) -> List[Tuple[str, datetime]]:
        out = []
        for year in range(dt.year - 2, dt.year + 2):
            for longitude in range(0, 360, 15):
                name = TERM_BY_LONGITUDE[longitude]
                try:
                    term_dt = self._term_time(year, longitude)
                except Exception:
                    continue
                if term_dt.year in (year, year + 1):
                    out.append((name, term_dt))
        return sorted(set(out), key=lambda x: x[1])


class LunarPythonEngine:
    name = "lunar_python 精准历法"

    def __init__(self) -> None:
        from lunar_python import Solar
        self._Solar = Solar

    def lunar_text(self, dt: datetime) -> str:
        try:
            lunar = self._Solar.fromYmdHms(dt.year, dt.month, dt.day,
                                           dt.hour, dt.minute, dt.second).getLunar()
            return lunar.getMonthInChinese() + "月" + lunar.getDayInChinese()
        except Exception:
            return ""

    def terms_around(self, dt: datetime) -> List[Tuple[str, datetime]]:
        collected = {}
        for delta in (-200, 0, 200):
            try:
                d = dt + timedelta(days=delta)
                lunar = self._Solar.fromYmdHms(d.year, d.month, d.day, 12, 0, 0).getLunar()
                for key, solar in lunar.getJieQiTable().items():
                    name = PINYIN_TERMS.get(key, key)
                    collected[(name, datetime(solar.getYear(), solar.getMonth(), solar.getDay(),
                                              solar.getHour(), solar.getMinute(), solar.getSecond()))] = True
            except Exception:
                pass
        return sorted(collected.keys(), key=lambda x: x[1])


def make_engine():
    try:
        return LunarPythonEngine()
    except Exception:
        return BuiltinEngine()


# ======================================================================
# 三、大六壬课体核心算法
# ======================================================================

@dataclass
class Ke:
    """一课"""
    idx: int
    label: str
    xia: str          # 下神（一课为日干）
    xia_wx: str       # 下神五行（一课取日干五行）
    shang: str        # 上神（天盘支）
    note: str = ""

    @property
    def shang_wx(self) -> str:
        return ZHI_WX[self.shang]


@dataclass
class Chuan:
    """一传"""
    idx: int
    label: str
    zhi: str
    jiang: str = ""
    dun: str = ""
    qin: str = ""
    lin: str = ""     # 所临地盘
    kong: bool = False


@dataclass
class Gong:
    """一宫（地盘支 + 其上所加天盘支）"""
    di: str
    tian: str
    jiang: str
    dun: str
    sha: str = ""
    kong: bool = False
    marks: List[str] = field(default_factory=list)
    row: int = 1
    col: int = 1


class LiuRenChart:
    def __init__(self, dt: datetime, gui_fa: str = "甲戊庚牛羊"):
        self.dt = dt
        self.gui_fa = "甲戊庚牛羊"
        self.engine = make_engine()
        self.lunar_text = self.engine.lunar_text(dt)
        self.terms = self.engine.terms_around(dt)
        self.ke: List[Ke] = []
        self.chuan: List[Chuan] = []
        self.gong: List[Gong] = []
        self.quyong_notes: List[str] = []
        self._calc()

    # ---------- 历法：四柱、月将 ----------
    def _latest_term(self, names) -> Optional[Tuple[str, datetime]]:
        valid = [t for t in self.terms if t[0] in names and t[1] <= self.dt]
        return max(valid, key=lambda t: t[1]) if valid else None

    def _calc_sizhu(self):
        dt = self.dt
        day_dt = dt + timedelta(days=1) if dt.hour >= 23 else dt   # 子初换日

        lichun = self._latest_term({"立春"})
        year_for_ganzhi = lichun[1].year if lichun else dt.year
        y_gan = (year_for_ganzhi - 4) % 10
        y_zhi = (year_for_ganzhi - 4) % 12

        jie = self._latest_term(set(JIE_TO_ZHI.keys()))
        m_zhi = ZHI_IDX[JIE_TO_ZHI[jie[0]]]
        m_gan = (y_gan * 2 + 2 + (m_zhi - 2) % 12) % 10

        self.day_index = (jdn(day_dt.year, day_dt.month, day_dt.day) + 49) % 60
        h_zhi = ((dt.hour + 1) // 2) % 12
        h_gan = (self.day_index % 10 * 2 + h_zhi) % 10

        self.si_zhu = (
            GAN[y_gan] + ZHI[y_zhi],
            GAN[m_gan] + ZHI[m_zhi],
            ganzhi_of_index(self.day_index),
            GAN[h_gan] + ZHI[h_zhi],
        )
        self.year_gan, self.year_zhi = GAN[y_gan], ZHI[y_zhi]
        self.month_gan, self.month_zhi = GAN[m_gan], ZHI[m_zhi]
        self.day_gan, self.day_zhi = GAN[self.day_index % 10], ZHI[self.day_index % 12]
        self.hour_gan, self.hour_zhi = GAN[h_gan], ZHI[h_zhi]

    def _calc_yue_jiang(self):
        zhong = self._latest_term(set(ZHONG_QI))
        if zhong is None:
            zhong = ("雨水", self.dt)
        self.zhong_qi = zhong[0]
        self.zhong_qi_dt = zhong[1]
        self.yue_jiang = ZHONG_QI_TO_JIANG[zhong[0]]
        self.yue_jiang_name = YUE_JIANG_NAME[self.yue_jiang]

    # ---------- 天地盘 ----------
    def _calc_tian_pan(self):
        self.yj_idx = ZHI_IDX[self.yue_jiang]
        self.ts_idx = ZHI_IDX[self.hour_zhi]
        # 月将加时：地盘时支之上为月将，顺布十二支
        self.tian_of_di: List[int] = [(self.yj_idx + (d - self.ts_idx)) % 12
                                      for d in range(12)]
        self.di_of_tian: List[int] = [0] * 12
        for d in range(12):
            self.di_of_tian[self.tian_of_di[d]] = d

    def tian(self, zhi: str) -> str:
        return ZHI[self.tian_of_di[ZHI_IDX[zhi]]]

    def tian_i(self, zi: int) -> int:
        return self.tian_of_di[zi]

    # ---------- 四课 ----------
    def _calc_si_ke(self):
        jigong = JI_GONG[self.day_gan]
        c1 = self.tian(jigong)
        c2 = self.tian(c1)
        c3 = self.tian(self.day_zhi)
        c4 = self.tian(c3)
        self.c1_up, self.c2_up, self.c3_up, self.c4_up = c1, c2, c3, c4

        self.ke = [
            Ke(1, "一课", self.day_gan, GAN_WX[self.day_gan], c1, f"寄{jigong}"),
            Ke(2, "二课", c1, ZHI_WX[c1], c2),
            Ke(3, "三课", self.day_zhi, ZHI_WX[self.day_zhi], c3),
            Ke(4, "四课", c3, ZHI_WX[c3], c4),
        ]

    @staticmethod
    def _ke(a_wx: str, b_wx: str) -> bool:
        """a 克 b"""
        return WX_KE[a_wx] == b_wx

    def _zei(self, k: Ke) -> bool:
        """下贼上：下神克上神"""
        return self._ke(k.xia_wx, k.shang_wx)

    def _keup(self, k: Ke) -> bool:
        """上克下：上神克下神"""
        return self._ke(k.shang_wx, k.xia_wx)

    # ---------- 旬遁 ----------
    def _calc_xun(self):
        self.xun_shou_index = self.day_index - self.day_index % 10
        self.xun_shou = ganzhi_of_index(self.xun_shou_index)
        self.xun_kong = (ZHI[(self.xun_shou_index % 12 + 10) % 12],
                         ZHI[(self.xun_shou_index % 12 + 11) % 12])

    def dun_gan(self, zhi: str) -> str:
        """旬遁：以日柱所在旬，为天盘支配遁干"""
        base_zhi = self.xun_shou_index % 12
        base_gan = self.xun_shou_index % 10
        step = (ZHI_IDX[zhi] - base_zhi) % 12
        return GAN[(base_gan + step) % 10]

    def liu_qin(self, zhi: str) -> str:
        me, it = GAN_WX[self.day_gan], ZHI_WX[zhi]
        if me == it:
            return "兄弟"
        if WX_SHENG[me] == it:
            return "子孙"
        if WX_SHENG[it] == me:
            return "父母"
        if WX_KE[me] == it:
            return "妻财"
        return "官鬼"

    # ---------- 三传 ----------
    def _calc_san_chuan(self):
        yj_ts_diff = (self.yj_idx - self.ts_idx) % 12
        if yj_ts_diff == 0:
            self._chuan_fuyin()
        elif yj_ts_diff == 6:
            self._chuan_fanyin()
        else:
            self._chuan_normal()

        # 中末传常规推法（特殊课已在各自方法内显式给出三传）
        if len(self.chuan) < 3:
            mid = self.tian(self.chuan[0].zhi) if self.chuan else ""
            end = self.tian(mid) if mid else ""
            self.chuan = self.chuan[:1]
            self.chuan.append(Chuan(2, "中传", mid))
            self.chuan.append(Chuan(3, "末传", end))

        for i, c in enumerate(self.chuan):
            c.idx = i + 1
            c.label = ["初传", "中传", "末传"][i]
            c.dun = self.dun_gan(c.zhi)
            c.qin = self.liu_qin(c.zhi)
            c.lin = ZHI[self.di_of_tian[ZHI_IDX[c.zhi]]]
            c.kong = c.zhi in self.xun_kong

    def _chuan_normal(self):
        zei = [k for k in self.ke if self._zei(k)]
        keup = [k for k in self.ke if self._keup(k)]
        day_yy = GAN_YIN_YANG[self.day_gan]

        if zei or keup:
            cands = zei if zei else keup
            base = "下贼上" if zei else "上克下"
            if len(cands) > 1:
                self.quyong_notes.append(
                    f"四课{base}者{'、'.join(k.label for k in cands)}")

            if len(cands) == 1:
                k = cands[0]
                self.chuan = [Chuan(1, "初传", k.shang)]
                self.keti = "重审课" if zei else "元首课"
                self.quyong_notes.append(
                    f"{base}仅一课，直取{k.label}上神「{k.shang}」发用")
                return

            bi = [k for k in cands if ZHI_YIN_YANG[k.shang] == day_yy]
            if len(bi) == 1:
                self.keti = "比用课"
                self.keti_shape = "知一"
                self.chuan = [Chuan(1, "初传", bi[0].shang)]
                self.quyong_notes.append(
                    f"数课相克，取与日干{self.day_gan}（{day_yy}）阴阳相比者："
                    f"{bi[0].label}上神「{bi[0].shang}」发用（比用/知一）")
                return

            # 涉害 —— 直取孟仲季
            self.keti = "涉害课"
            chosen, kind, why = self._she_hai(cands)
            self.keti_shape = kind
            self.chuan = [Chuan(1, "初传", chosen.shang)]
            self.quyong_notes.append(
                f"比用不能决（俱比或俱不比），用涉害法直取孟仲季：{why}，"
                f"取{chosen.label}上神「{chosen.shang}」发用（{kind}）")
            return

        # 无贼克 —— 遥克
        shang_ke_ri = [k for k in self.ke if self._ke(k.shang_wx, GAN_WX[self.day_gan])]
        ri_ke_shang = [k for k in self.ke if self._ke(GAN_WX[self.day_gan], k.shang_wx)]
        if shang_ke_ri or ri_ke_shang:
            cands = shang_ke_ri if shang_ke_ri else ri_ke_shang
            kind = "蒿矢" if shang_ke_ri else "弹射"
            bi = [k for k in cands if ZHI_YIN_YANG[k.shang] == day_yy]
            chosen = bi[0] if bi else cands[0]
            self.keti = "遥克课"
            self.keti_shape = kind
            self.chuan = [Chuan(1, "初传", chosen.shang)]
            direction = "上神遥克日干" if shang_ke_ri else "日干遥克上神"
            self.quyong_notes.append(
                f"四课无上下克，{direction}者 {'、'.join(k.label + '「' + k.shang + '」' for k in cands)}，"
                f"取{chosen.label}上神「{chosen.shang}」发用（遥克·{kind}）")
            return

        # 无克无遥 —— 八专 / 别责 / 昴星
        jigong = JI_GONG[self.day_gan]
        if jigong == self.day_zhi:
            self._chuan_bazhuan()
            return
        if self._si_ke_buquan():
            self._chuan_bieze()
            return
        self._chuan_maoxing()

    def _ke_di(self, k: Ke) -> str:
        """本课所临地盘之支（一课以日干寄宫论）"""
        return JI_GONG[self.day_gan] if k.idx == 1 else k.xia

    def _si_ke_buquan(self) -> bool:
        """四课不全：四课中有重复之课，实只三课（课一下以寄宫论）"""
        downs = [JI_GONG[self.day_gan], self.c1_up, self.day_zhi, self.c3_up]
        pairs = {(downs[i], self.ke[i].shang) for i in range(4)}
        return len(pairs) < 4

    def _she_hai(self, cands: List[Ke]):
        """涉害直取孟仲季：四孟（见机）→ 四仲（察微）→ 四季（缀瑕）"""
        for grp, gname, kname in ((MENG, "四孟（寅申巳亥）", "见机"),
                                  (ZHONG, "四仲（子午卯酉）", "察微"),
                                  (JI, "四季（辰戌丑未）", "缀瑕")):
            sub = [k for k in cands if self._ke_di(k) in grp]
            if not sub:
                continue
            if len(sub) == 1:
                return sub[0], kname, f"候选诸课中唯{sub[0].label}临{gname}「{self._ke_di(sub[0])}」"
            # 同组仍相等：刚日取干上神，柔日取支上神
            prefer = self.ke[0] if GAN_YIN_YANG[self.day_gan] == "阳" else self.ke[2]
            if prefer in sub:
                return prefer, kname, (
                    f"临{gname}者不止一课，孟仲季复等，"
                    f"{'刚' if GAN_YIN_YANG[self.day_gan] == '阳' else '柔'}日取"
                    f"{'干' if GAN_YIN_YANG[self.day_gan] == '阳' else '支'}上神")
            return sub[0], kname, f"临{gname}者数课相等，取课序在前者"
        return cands[0], "缀瑕", "诸课临支无孟仲季之别，取课序在前者"

    def _chuan_bazhuan(self):
        """八专：刚日干上神顺数三位，柔日第四课上神逆数三位；中末俱用干上神"""
        self.keti = "八专课"
        if GAN_YIN_YANG[self.day_gan] == "阳":
            first = ZHI[(ZHI_IDX[self.c1_up] + 2) % 12]
            why = f"刚日（{self.day_gan}）以干上神「{self.c1_up}」顺数三位得「{first}」"
        else:
            first = ZHI[(ZHI_IDX[self.c4_up] - 2) % 12]
            why = f"柔日（{self.day_gan}）以第四课上神「{self.c4_up}」逆数三位得「{first}」"
        self.chuan = [Chuan(1, "初传", first), Chuan(2, "中传", self.c1_up),
                      Chuan(3, "末传", self.c1_up)]
        self.quyong_notes.append(f"干支同宫（{self.day_gan}寄{JI_GONG[self.day_gan]}、日支{self.day_zhi}），"
                                 f"八专无克：{why}发用，中末俱取干上神「{self.c1_up}」")

    def _chuan_bieze(self):
        """别责：阳日取干合上神，阴日取支前三合上神；中末俱用干上神"""
        self.keti = "别责课"
        if GAN_YIN_YANG[self.day_gan] == "阳":
            he_gan = GAN_HE[self.day_gan]
            he_gong = JI_GONG[he_gan]
            first = self.tian(he_gong)
            why = f"刚日取干合「{self.day_gan}合{he_gan}」（{he_gan}寄{he_gong}）上神「{first}」"
        else:
            sanhe = SAN_HE[self.day_zhi]
            first = self.tian(sanhe)
            why = f"柔日取支前三合「{self.day_zhi}→{sanhe}」上神「{first}」"
        self.chuan = [Chuan(1, "初传", first), Chuan(2, "中传", self.c1_up),
                      Chuan(3, "末传", self.c1_up)]
        self.quyong_notes.append(f"四课不全（实只三课），又无克无遥，{why}发用，中末俱取干上神")

    def _chuan_maoxing(self):
        """昴星：刚日取地盘酉上神（仰视），柔日取天盘酉下神（俯视）"""
        self.keti = "昴星课"
        if GAN_YIN_YANG[self.day_gan] == "阳":
            first = self.tian("酉")
            mid, end = self.c3_up, self.c1_up
            shape = "虎视转蓬"
            self.quyong_notes.append(f"四课全备、无克无遥，刚日仰视：取地盘酉上神「{first}」发用，"
                                     f"中取支上神「{mid}」，末取干上神「{end}」")
        else:
            first = ZHI[self.di_of_tian[ZHI_IDX["酉"]]]
            mid, end = self.c1_up, self.c3_up
            shape = "冬蛇掩目"
            self.quyong_notes.append(f"四课全备、无克无遥，柔日俯视：取天盘酉下神「{first}」发用，"
                                     f"中取干上神「{mid}」，末取支上神「{end}」")
        self.keti_shape = shape
        self.chuan = [Chuan(1, "初传", first), Chuan(2, "中传", mid), Chuan(3, "末传", end)]

    def _chuan_fuyin(self):
        """伏吟：有克依贼克，中末以刑相推；无克刚日取干上神、柔日取支上神，自刑用杜传"""
        self.keti = "伏吟课"
        jigong = JI_GONG[self.day_gan]
        zei = [k for k in self.ke if self._zei(k)]
        keup = [k for k in self.ke if self._keup(k)]

        if zei or keup:
            k = (zei or keup)[0]
            first = k.shang
            self.keti_shape = "有克"
            self.quyong_notes.append(f"伏吟有克，依贼克法取{k.label}上神「{first}」发用")
        else:
            if GAN_YIN_YANG[self.day_gan] == "阳":
                first = self.c1_up
                self.keti_shape = "自任"
                self.quyong_notes.append(f"伏吟无克，刚日取干上神「{first}」发用（自任格）")
            else:
                first = self.c3_up
                self.keti_shape = "自信"
                self.quyong_notes.append(f"伏吟无克，柔日取支上神「{first}」发用（自信格）")

        # 中传
        if first in ZI_XING:
            mid = self.c3_up if first == jigong else self.c1_up
            self.quyong_notes.append(f"初传「{first}」自刑，中传颠倒日辰取「{mid}」（杜传）")
        else:
            mid = XING[first]
            self.quyong_notes.append(f"中传取初传所刑「{first}刑{mid}」")

        # 末传
        if mid in ZI_XING:
            end = ZHI[(ZHI_IDX[mid] + 6) % 12]
            self.quyong_notes.append(f"中传「{mid}」自刑，末传取其冲「{end}」")
        else:
            nxt = XING[mid]
            if nxt == first:                      # 刑成循环（如卯刑子、子复刑卯）
                end = ZHI[(ZHI_IDX[mid] + 6) % 12]
                self.quyong_notes.append(f"初传「{first}」与中传「{mid}」互刑成环，末传取中传之冲「{end}」")
            else:
                end = nxt
                self.quyong_notes.append(f"末传取中传所刑「{mid}刑{end}」")

        self.chuan = [Chuan(1, "初传", first), Chuan(2, "中传", mid), Chuan(3, "末传", end)]

    def _chuan_fanyin(self):
        """返吟：有克依贼克（初中末以冲相推）；无克取日支驿马（井栏射·无亲）"""
        self.keti = "返吟课"
        zei = [k for k in self.ke if self._zei(k)]
        keup = [k for k in self.ke if self._keup(k)]
        if zei or keup:
            cands = zei if zei else keup
            if len(cands) == 1:
                first = cands[0].shang
            else:
                day_yy = GAN_YIN_YANG[self.day_gan]
                bi = [k for k in cands if ZHI_YIN_YANG[k.shang] == day_yy]
                if len(bi) == 1:
                    first = bi[0].shang
                else:
                    chosen, kind, _ = self._she_hai(cands)
                    first = chosen.shang
            mid = ZHI[(ZHI_IDX[first] + 6) % 12]
            end = ZHI[(ZHI_IDX[mid] + 6) % 12]
            self.keti_shape = "有克"
            self.quyong_notes.append(
                f"返吟有克，取{'下贼上' if zei else '上克下'}者上神「{first}」发用，"
                f"初中末以冲相推：{first}→{mid}→{end}")
        else:
            first = YI_MA[self.day_zhi]
            mid, end = self.c3_up, self.c1_up
            self.keti_shape = "井栏射·无亲"
            self.quyong_notes.append(
                f"返吟无克，取日支{self.day_zhi}之驿马「{first}」发用，"
                f"中取支上神「{mid}」，末取干上神「{end}」（井栏射·无亲格）")
        self.chuan = [Chuan(1, "初传", first), Chuan(2, "中传", mid), Chuan(3, "末传", end)]

    # ---------- 十二天将 ----------
    def _calc_jiang(self):
        # 昼占：卯至申；夜占：酉至寅
        self.zhou_ye = "昼" if 3 <= self.ts_idx <= 8 else "夜"
        gui_zz = GUI_TABLE[self.day_gan][0 if self.zhou_ye == "昼" else 1]
        self.gui_ren = gui_zz
        self.gui_lin_di = ZHI[self.di_of_tian[ZHI_IDX[gui_zz]]]     # 贵人临地盘之位
        self.shun = self.gui_lin_di in {"亥", "子", "丑", "寅", "卯", "辰"}

        gi = ZHI_IDX[gui_zz]
        self.jiang_of_tian: Dict[str, str] = {}
        for t in range(12):
            n = (t - gi) % 12 if self.shun else (gi - t) % 12
            self.jiang_of_tian[ZHI[t]] = JIANG[n]

    # ---------- 八煞 ----------
    def _calc_sha(self):
        """八煞：干德、日禄、驿马、天马、旬丁、桃花、羊刃、日墓（旬空另以红字标）"""
        vals = {
            "德": DE_TABLE[self.day_gan],
            "禄": LU_TABLE[self.day_gan],
            "驿": YI_MA[self.day_zhi],
            "天": TIAN_MA_SEQ[(ZHI_IDX[self.month_zhi] - ZHI_IDX["寅"]) % 6],
            "丁": ZHI[(self.xun_shou_index + 3) % 12],
            "桃": TAO_TABLE[self.day_zhi],
            "刃": REN_TABLE[self.day_gan],
            "墓": MU_TABLE[self.day_gan],
        }
        self.sha_val = vals
        m: Dict[str, List[str]] = {}
        for n in SHA_ORDER:
            m.setdefault(vals[n], []).append(n)
        self.sha_map = m

    def sha_of(self, zhi: str) -> str:
        return "·".join(self.sha_map.get(zhi, []))

    @property
    def sha_items(self):
        return [(n, self.sha_val[n]) for n in SHA_ORDER]

    # ---------- 天地盘宫位 ----------
    def _calc_gong(self):
        self.gong = []
        for d in range(12):
            tian_zhi = ZHI[self.tian_of_di[d]]
            marks = []
            if ZHI[d] == JI_GONG[self.day_gan]:
                marks.append("干")
            if ZHI[d] == self.day_zhi:
                marks.append("支")
            if ZHI[d] == self.hour_zhi:
                marks.append("时")
            if tian_zhi == self.yue_jiang:
                marks.append("将")
            if tian_zhi in self.xun_kong:
                marks.append("空")
            row, col = BOARD_POS[ZHI[d]]
            self.gong.append(Gong(
                di=ZHI[d], tian=tian_zhi,
                jiang=self.jiang_of_tian[tian_zhi],
                dun=self.dun_gan(tian_zhi),
                sha=self.sha_of(tian_zhi),
                kong=tian_zhi in self.xun_kong,
                marks=marks, row=row, col=col))

    def _calc(self):
        self._calc_sizhu()
        self._calc_yue_jiang()
        self._calc_tian_pan()
        self._calc_si_ke()
        self._calc_xun()
        self.keti_shape = ""
        self._calc_san_chuan()
        self._calc_jiang()
        for c in self.chuan:
            c.jiang = self.jiang_of_tian[c.zhi]
        self._calc_sha()
        self._calc_gong()

    # ---------- 传中相克（内战）标位 ----------
    @property
    def chuan_ke_marks(self):
        """返回三传每位的红字标注：克者标『克X』，受克者标『XX克我』"""
        if not self.chuan:
            return {}
        marks = {}
        names = {0: "初", 1: "中", 2: "末"}
        for i, j in ((0, 1), (0, 2), (1, 2)):
            a, b = self.chuan[i].zhi, self.chuan[j].zhi
            if self._ke(ZHI_WX[a], ZHI_WX[b]):
                marks.setdefault(i, f"克{names[j]}")
                marks.setdefault(j, f"受{names[i]}克")
        return marks

    @property
    def ke_flags(self):
        """四课标位（顺序与页面右起一致）：是否发用来源、是否带贼克"""
        yong_zhi = self.chuan[0].zhi if self.chuan else ""
        # 发用来源课：上神为发用者优先取带贼克的那一课（如伏吟两课同为丑，取带克者）
        hit = None
        cands = [k for k in self.ke if k.shang == yong_zhi]
        for k in cands:
            if self._zei(k) or self._keup(k):
                hit = k
                break
        if hit is None and len(cands) == 1:
            hit = cands[0]
        flags = []
        for k in reversed(self.ke):
            flags.append({
                "yong": (k is hit),
                "ke": bool(self._zei(k) or self._keup(k)),
                "kind": self._rel_text(k),
            })
        return flags

    # ---------- 展示辅助 ----------
    @property
    def keti_full(self) -> str:
        base = getattr(self, "keti", "课")
        if getattr(self, "keti_shape", ""):
            return f"{base}·{self.keti_shape}"
        return base

    @property
    def keti_doc(self) -> str:
        return KETI_DOC.get(getattr(self, "keti", ""), "")

    @property
    def zhong_qi_text(self) -> str:
        dt = getattr(self, "zhong_qi_dt", None)
        if not dt:
            return self.zhong_qi
        return f"{self.zhong_qi} {dt.month}月{dt.day}日 {dt.hour:02d}时"

    @property
    def san_chuan_text(self) -> str:
        return " · ".join(c.zhi for c in self.chuan)

    @property
    def shen_sha(self):
        out = [("旬空", "".join(self.xun_kong)), ("日支", self.day_zhi),
               ("月将", self.yue_jiang), ("贵人", self.gui_ren)]
        return out

    @property
    def zhan_chuan(self):
        """三传之战：将克神为内战，神克将为外战"""
        out = []
        for c in self.chuan:
            jw, zw = wx_of_jiang(c.jiang), ZHI_WX[c.zhi]
            if not jw:
                out.append("")
            elif self._ke(jw, zw):
                out.append("内战")
            elif self._ke(zw, jw):
                out.append("外战")
            else:
                out.append("")
        return out

    @property
    def zhan_ke(self):
        """四课之战（与 ke_display 同序）"""
        out = []
        for k in self.ke:
            jw, zw = wx_of_jiang(self.jiang_of_tian[k.shang]), ZHI_WX[k.shang]
            if not jw:
                out.append("")
            elif self._ke(jw, zw):
                out.append("内战")
            elif self._ke(zw, jw):
                out.append("外战")
            else:
                out.append("")
        return out

    def ke_display(self):
        res = []
        for k in self.ke:
            res.append({
                "label": k.label, "xia": k.xia, "shang": k.shang,
                "xia_wx": k.xia_wx, "shang_wx": ZHI_WX[k.shang],
                "note": k.note,
                "jiang": self.jiang_of_tian[k.shang],
                "dun": self.dun_gan(k.shang),
                "kong": k.shang in self.xun_kong,
                "rel": self._rel_text(k),
            })
        return res

    def _rel_text(self, k: Ke) -> str:
        if self._zei(k):
            return "下贼上"
        if self._keup(k):
            return "上克下"
        return ""


# ======================================================================
# 四、Web 界面模板 & 样式
# ======================================================================


# ======================================================================
# 农历（1898-2102 内置月朔表，静态版无需外部历法包）
# ======================================================================
LUNAR_STARTS = [-413,-383,-354,-324,-295,-265,-236,-206,-177,-147,-117,-88,-58,-29,1,30,60,89,118,148,177,207,237,266,296,326,355,385,414,444,473,502,532,561,591,620,650,680,710,739,769,798,828,857,886,916,945,975,1004,1034,1064,1094,1123,1153,1182,1212,1241,1270,1300,1329,1358,1388,1418,1447,1477,1507,1537,1566,1596,1625,1654,1684,1713,1742,1772,1802,1831,1861,1891,1920,1950,1980,2009,2038,2068,2097,2127,2156,2186,2215,2245,2275,2304,2334,2363,2393,2422,2452,2481,2511,2540,2570,2599,2629,2658,2688,2717,2747,2777,2806,2836,2865,2895,2924,2954,2983,3012,3042,3072,3101,3131,3160,3190,3220,3249,3279,3308,3338,3367,3396,3426,3455,3485,3514,3544,3574,3604,3633,3663,3692,3722,3751,3780,3810,3839,3869,3898,3928,3958,3988,4017,4047,4076,4106,4135,4164,4194,4223,4252,4282,4312,4341,4371,4401,4431,4460,4490,4519,4548,4578,4607,4636,4666,4696,4725,4755,4785,4815,4844,4874,4903,4932,4962,4991,5020,5050,5079,5109,5139,5169,5198,5228,5257,5287,5316,5346,5375,5404,5434,5463,5493,5523,5552,5582,5612,5641,5671,5700,5730,5759,5789,5818,5847,5877,5907,5936,5966,5995,6025,6055,6084,6114,6143,6173,6202,6232,6261,6290,6320,6349,6379,6409,6438,6468,6498,6527,6557,6586,6616,6645,6674,6704,6733,6763,6792,6822,6852,6881,6911,6941,6970,7000,7029,7058,7088,7117,7146,7176,7206,7235,7265,7295,7325,7354,7384,7413,7442,7472,7501,7530,7560,7589,7619,7649,7679,7709,7738,7768,7797,7826,7856,7885,7914,7944,7973,8003,8033,8063,8092,8122,8152,8181,8210,8240,8269,8298,8328,8357,8387,8417,8446,8476,8506,8535,8565,8594,8624,8653,8682,8712,8741,8771,8800,8830,8860,8889,8919,8949,8978,9008,9037,9067,9096,9125,9155,9184,9214,9243,9273,9303,9332,9362,9392,9421,9451,9480,9510,9539,9568,9598,9627,9657,9686,9716,9746,9775,9805,9835,9864,9894,9923,9952,9982,10011,10041,10070,10100,10129,10159,10189,10219,10248,10278,10307,10336,10366,10395,10424,10454,10483,10513,10543,10573,10603,10632,10662,10691,10720,10750,10779,10808,10838,10867,10897,10927,10957,10986,11016,11046,11075,11104,11134,11163,11192,11222,11251,11281,11311,11340,11370,11400,11429,11459,11488,11518,11547,11576,11606,11635,11665,11694,11724,11754,11784,11813,11843,11872,11902,11931,11960,11990,12019,12049,12078,12108,12138,12167,12197,12227,12256,12286,12315,12345,12374,12403,12433,12462,12492,12521,12551,12581,12610,12640,12669,12699,12729,12758,12788,12817,12846,12876,12905,12935,12964,12994,13024,13053,13083,13113,13142,13172,13201,13230,13260,13289,13318,13348,13378,13407,13437,13467,13497,13526,13556,13585,13614,13644,13673,13702,13732,13761,13791,13821,13851,13880,13910,13940,13969,13998,14028,14057,14086,14116,14145,14175,14205,14234,14264,14294,14324,14353,14382,14412,14441,14470,14500,14529,14559,14588,14618,14648,14678,14707,14737,14766,14796,14825,14854,14884,14913,14943,14972,15002,15032,15061,15091,15121,15150,15180,15209,15238,15268,15297,15327,15356,15386,15415,15445,15475,15504,15534,15563,15593,15622,15652,15681,15711,15740,15770,15799,15829,15858,15888,15918,15947,15977,16006,16036,16065,16095,16124,16154,16183,16213,16242,16272,16301,16331,16361,16390,16420,16450,16479,16508,16538,16567,16596,16626,16655,16685,16715,16745,16774,16804,16834,16863,16892,16922,16951,16980,17010,17039,17069,17099,17128,17158,17188,17218,17247,17276,17306,17335,17364,17394,17423,17453,17482,17512,17542,17572,17601,17631,17660,17690,17719,17748,17778,17807,17837,17866,17896,17926,17955,17985,18015,18044,18074,18103,18132,18162,18191,18221,18250,18280,18309,18339,18369,18398,18428,18458,18487,18516,18546,18575,18605,18634,18664,18693,18723,18753,18782,18812,18841,18871,18900,18930,18959,18989,19018,19048,19077,19107,19136,19166,19195,19225,19255,19284,19314,19343,19373,19402,19432,19461,19490,19520,19550,19579,19609,19639,19668,19698,19727,19757,19786,19816,19845,19874,19904,19933,19963,19993,20022,20052,20082,20111,20141,20170,20200,20229,20258,20288,20317,20347,20376,20406,20436,20466,20495,20525,20554,20584,20613,20642,20672,20701,20731,20760,20790,20820,20850,20879,20909,20938,20968,20997,21026,21056,21085,21115,21144,21174,21203,21233,21263,21293,21322,21352,21381,21410,21440,21469,21499,21528,21558,21587,21617,21647,21676,21706,21735,21765,21794,21824,21853,21883,21912,21942,21971,22001,22030,22060,22090,22119,22149,22178,22208,22237,22267,22296,22326,22355,22385,22414,22444,22473,22503,22533,22562,22592,22621,22651,22680,22710,22739,22768,22798,22827,22857,22887,22916,22946,22976,23005,23035,23064,23094,23123,23152,23182,23211,23241,23270,23300,23330,23360,23389,23419,23448,23478,23507,23536,23566,23595,23625,23654,23684,23714,23744,23773,23803,23832,23862,23891,23920,23950,23979,24008,24038,24068,24097,24127,24157,24187,24216,24246,24275,24304,24334,24363,24392,24422,24452,24481,24511,24541,24570,24600,24630,24659,24688,24718,24747,24777,24806,24836,24865,24895,24924,24954,24984,25013,25043,25072,25102,25131,25161,25190,25220,25249,25279,25308,25338,25367,25397,25427,25456,25486,25515,25545,25574,25604,25633,25662,25692,25721,25751,25781,25810,25840,25870,25899,25929,25958,25988,26017,26046,26076,26105,26135,26164,26194,26224,26254,26283,26313,26342,26372,26401,26430,26460,26489,26519,26548,26578,26608,26637,26667,26697,26726,26756,26785,26814,26844,26873,26902,26932,26962,26991,27021,27051,27081,27110,27140,27169,27198,27228,27257,27286,27316,27346,27375,27405,27435,27465,27494,27524,27553,27582,27612,27641,27670,27700,27729,27759,27789,27819,27848,27878,27907,27937,27966,27996,28025,28054,28084,28113,28143,28173,28202,28232,28262,28291,28321,28350,28380,28409,28439,28468,28497,28527,28556,28586,28616,28645,28675,28705,28734,28764,28793,28823,28852,28882,28911,28940,28970,28999,29029,29059,29088,29118,29148,29177,29207,29236,29266,29295,29324,29354,29383,29413,29442,29472,29502,29531,29561,29591,29620,29650,29679,29708,29738,29767,29796,29826,29856,29885,29915,29945,29975,30004,30034,30063,30092,30122,30151,30180,30210,30239,30269,30299,30329,30359,30388,30418,30447,30476,30506,30535,30564,30594,30623,30653,30683,30713,30742,30772,30802,30831,30860,30890,30919,30948,30978,31007,31037,31067,31096,31126,31156,31185,31215,31244,31274,31303,31332,31362,31391,31421,31450,31480,31510,31539,31569,31599,31628,31658,31687,31717,31746,31775,31805,31834,31864,31893,31923,31953,31982,32012,32042,32071,32101,32130,32159,32189,32218,32248,32277,32307,32336,32366,32396,32425,32455,32485,32514,32544,32573,32602,32632,32661,32691,32720,32750,32779,32809,32839,32869,32898,32928,32957,32986,33016,33045,33074,33104,33133,33163,33193,33223,33253,33282,33312,33341,33370,33400,33429,33458,33488,33517,33547,33577,33607,33636,33666,33696,33725,33754,33784,33813,33842,33872,33901,33931,33961,33990,34020,34050,34079,34109,34138,34168,34197,34226,34256,34285,34315,34344,34374,34404,34434,34463,34493,34522,34552,34581,34610,34640,34669,34699,34728,34758,34788,34817,34847,34876,34906,34936,34965,34994,35024,35053,35083,35112,35142,35171,35201,35231,35260,35290,35319,35349,35379,35408,35437,35467,35496,35526,35555,35585,35614,35644,35674,35703,35733,35763,35792,35822,35851,35880,35910,35939,35968,35998,36028,36057,36087,36117,36146,36176,36206,36235,36264,36294,36323,36352,36382,36411,36441,36471,36501,36530,36560,36590,36619,36648,36678,36707,36736,36766,36795,36825,36855,36884,36914,36944,36973,37003,37032,37062,37091,37120,37150,37179,37209,37238,37268,37298,37328,37357,37387,37416,37446,37475,37504,37534,37563,37593,37622,37652,37682,37711,37741,37771,37800,37830,37859,37888,37918,37947,37977,38006,38036,38065,38095,38125,38154,38184,38213,38243,38272,38302,38331,38361,38390,38420,38449,38479,38508,38538,38568,38597,38627,38656,38686,38715,38745,38774,38804,38833,38863,38892,38922,38951,38981,39011,39040,39070,39100,39129,39158,39188,39217,39246,39276,39305,39335,39365,39395,39424,39454,39484,39513,39542,39572,39601,39630,39660,39689,39719,39749,39778,39808,39838,39868,39897,39926,39956,39985,40014,40044,40073,40103,40132,40162,40192,40222,40251,40281,40310,40340,40369,40398,40428,40457,40487,40516,40546,40576,40605,40635,40665,40694,40724,40753,40782,40812,40841,40871,40900,40930,40959,40989,41019,41048,41078,41107,41137,41166,41196,41225,41255,41284,41314,41343,41373,41402,41432,41462,41491,41521,41550,41580,41609,41639,41668,41698,41727,41757,41786,41816,41845,41875,41905,41934,41964,41993,42023,42052,42082,42111,42140,42170,42199,42229,42259,42289,42318,42348,42377,42407,42436,42466,42495,42524,42554,42583,42613,42643,42672,42702,42732,42761,42791,42820,42850,42879,42908,42938,42967,42997,43026,43056,43086,43116,43145,43175,43204,43234,43263,43292,43322,43351,43381,43410,43440,43470,43500,43529,43559,43588,43618,43647,43676,43706,43735,43764,43794,43824,43853,43883,43913,43943,43972,44002,44031,44060,44090,44119,44149,44178,44208,44237,44267,44297,44326,44356,44385,44415,44444,44474,44503,44533,44562,44592,44621,44651,44680,44710,44740,44769,44799,44828,44858,44887,44917,44946,44976,45005,45034,45064,45094,45123,45153,45183,45212,45242,45271,45301,45330,45360,45389,45418,45448,45477,45507,45537,45566,45596,45626,45655,45685,45714,45744,45773,45802,45832,45861,45891,45920,45950,45980,46010,46039,46069,46098,46128,46157,46186,46216,46245,46274,46304,46334,46364,46393,46423,46453,46482,46512,46541,46570,46600,46629,46658,46688,46718,46747,46777,46807,46837,46866,46896,46925,46954,46984,47013,47042,47072,47102,47131,47161,47191,47220,47250,47279,47309,47338,47368,47397,47426,47456,47486,47515,47545,47574,47604,47634,47663,47693,47722,47752,47781,47811,47840,47869,47899,47929,47958,47988,48017,48047,48077,48106,48136,48165,48195,48224,48254,48283,48312,48342,48371,48401,48431,48460,48490,48520,48549,48579,48608,48638,48667,48696,48726,48755,48785,48814,48844,48874,48904,48933,48963,48992,49022,49051,49080,49110,49139,49169,49198,49228,49258,49287,49317,49347,49376,49406,49435,49464,49494,49523,49552,49582,49612,49641,49671,49701,49731,49760,49790,49819,49848,49878,49907,49936,49966,49995,50025,50055,50085,50115,50144,50174,50203,50232,50262,50291,50320,50350,50379,50409,50439,50469,50498,50528,50557,50587,50616,50646,50675,50704,50734,50763,50793,50823,50852,50882,50912,50941,50971,51000,51030,51059,51089,51118,51147,51177,51206,51236,51266,51295,51325,51354,51384,51414,51443,51473,51502,51531,51561,51590,51620,51649,51679,51709,51738,51768,51798,51827,51857,51886,51916,51945,51974,52004,52033,52063,52092,52122,52152,52181,52211,52241,52270,52300,52329,52358,52388,52417,52446,52476,52506,52535,52565,52595,52625,52654,52684,52713,52742,52772,52801,52830,52860,52889,52919,52949,52979,53009,53038,53068,53097,53126,53156,53185,53214,53244,53273,53303,53333,53363,53392,53422,53451,53481,53510,53540,53569,53598,53628,53657,53687,53717,53746,53776,53806,53835,53865,53894,53924,53953,53982,54012,54041,54071,54100,54130,54160,54189,54219,54249,54278,54308,54337,54366,54396,54425,54455,54484,54514,54543,54573,54603,54632,54662,54692,54721,54751,54780,54809,54839,54868,54898,54927,54957,54986,55016,55046,55075,55105,55135,55164,55194,55223,55252,55282,55311,55340,55370,55400,55429,55459,55489,55519,55548,55578,55607,55636,55666,55695,55724,55754,55783,55813,55843,55873,55903,55932,55962,55991,56020,56050,56079,56108,56138,56167,56197,56227,56257,56286,56316,56346,56375,56404,56434,56463,56492,56522,56551,56581,56611,56640,56670,56700,56729,56759,56788,56818,56847,56876,56906,56935,56965,56994,57024,57054,57084,57113,57143,57172,57202,57231,57260,57290,57319,57349,57378,57408,57438,57467,57497,57526,57556,57586,57615,57644,57674,57703,57733,57762,57792,57821,57851,57880,57910,57940,57969,57999,58029,58058,58087,58117,58146,58176,58205,58235,58264,58294,58323,58353,58383,58413,58442,58472,58501,58530,58560,58589,58618,58648,58677,58707,58737,58767,58796,58826,58856,58885,58914,58944,58973,59002,59032,59061,59091,59121,59151,59180,59210,59240,59269,59298,59328,59357,59386,59416,59445,59475,59505,59534,59564,59594,59623,59653,59682,59712,59741,59770,59800,59829,59859,59888,59918,59948,59978,60007,60037,60066,60096,60125,60154,60184,60213,60243,60272,60302,60332,60361,60391,60421,60450,60480,60509,60538,60568,60597,60627,60656,60686,60715,60745,60775,60804,60834,60863,60893,60922,60952,60981,61011,61040,61070,61099,61129,61158,61188,61218,61247,61277,61306,61336,61365,61395,61424,61454,61483,61512,61542,61572,61601,61631,61661,61690,61720,61749,61779,61808,61838,61867,61896,61926,61955,61985,62015,62045,62074,62104,62133,62163,62192,62222,62251,62280,62310,62339,62369,62399,62428,62458,62488,62517,62547,62576,62606,62635,62664,62694,62723,62753,62782,62812,62842,62872,62901,62931,62960,62990,63019,63048,63078,63107,63137,63166,63196,63226,63255,63285,63315,63344,63374,63403,63432,63462,63491,63521,63550,63580,63609,63639,63669,63698,63728,63757,63787,63816,63846,63875,63905,63934,63964,63993,64023,64052,64082,64112,64141,64171,64200,64230,64259,64289,64318,64348,64377,64407,64436,64466,64495,64525,64555,64584,64614,64643,64673,64702,64732,64761,64790,64820,64849,64879,64909,64939,64968,64998,65027,65057,65086,65116,65145,65174,65204,65233,65263,65293,65322,65352,65382,65411,65441,65470,65500,65529,65558,65588,65617,65647,65676,65706,65736,65766,65795,65825,65854,65884,65913,65942,65972,66001,66030,66060,66090,66120,66149,66179,66209,66238,66268,66297,66326,66356,66385,66414,66444,66474,66503,66533,66563,66593,66622,66651,66681,66710,66740,66769,66798,66828,66858,66887,66917,66947,66976,67006,67035,67065,67094,67124,67153,67183,67212,67242,67271,67301,67330,67360,67390,67419,67449,67478,67508,67537,67567,67596,67626,67655,67684,67714,67744,67773,67803,67833,67862,67892,67921,67951,67980,68010,68039,68068,68098,68127,68157,68187,68216,68246,68276,68305,68335,68364,68394,68423,68452,68482,68511,68541,68570,68600,68630,68660,68689,68719,68748,68778,68807,68836,68866,68895,68924,68954,68984,69014,69043,69073,69103,69132,69162,69191,69220,69249,69279,69308,69338,69368,69397,69427,69457,69487,69516,69546,69575,69604,69634,69663,69692,69722,69752,69781,69811,69841,69870,69900,69929,69959,69988,70018,70047,70076,70106,70135,70165,70195,70224,70254,70284,70313,70343,70372,70402,70431,70461,70490,70519,70549,70579,70608,70638,70667,70697,70727,70756,70786,70815,70845,70874,70903,70933,70962,70992,71021,71051,71081,71110,71140,71170,71199,71229,71258,71288,71317,71346,71376,71405,71435,71464,71494,71524,71554,71583,71613,71642,71672,71701,71730,71760,71789,71818,71848,71878,71908,71937,71967,71997,72026,72056,72085,72114,72143,72173,72202,72232,72262,72291,72321,72351,72381,72410,72440,72469,72498,72527,72557,72586,72616,72645,72675,72705,72735,72764,72794,72824,72853,72882,72912,72941,72970,73000,73029,73059,73089,73119,73148,73178,73207,73237,73266,73296,73325,73354,73384,73413,73443,73473,73502,73532,73562,73591,73621,73650,73680,73709,73738,73768]
LUNAR_CODES = [11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,-8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,-5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,-4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,-2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,-6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,-5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,-2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,-7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,-5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,-4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,-2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,-6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,-5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,-3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,-7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,-6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,-4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,-2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,-7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,-5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,-3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,-8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,-6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,-4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,-3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,-7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,-5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,-4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,-8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,-6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,-4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,-10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,-6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,-5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,-3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,-8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,-5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,-4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,-2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,-7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,-5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,-4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,-9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,-6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,-4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,-2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,-6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,-5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,-3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,-11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,-6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,-5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,-2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,-7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,-5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,-3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,-8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,-6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,-4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,-3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,-7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,-5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,-4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,-8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,-6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,-4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,-3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,-7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,-5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,-4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,-8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,-6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,-4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,-2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,8,9,10,11,12,1,2,3,4,5,6,7,-7,8,9,10,11,12]

_L_MONTH = ["正", "二", "三", "四", "五", "六", "七", "八", "九", "十", "冬", "腊"]
_L_DAY = ["初一", "初二", "初三", "初四", "初五", "初六", "初七", "初八", "初九", "初十",
          "十一", "十二", "十三", "十四", "十五", "十六", "十七", "十八", "十九", "二十",
          "廿一", "廿二", "廿三", "廿四", "廿五", "廿六", "廿七", "廿八", "廿九", "三十"]


def lunar_text_of(dt):
    """公历 -> 农历"""
    try:
        off = (_date(dt.year, dt.month, dt.day) - _date(1900, 1, 30)).days
        i = bisect_right(LUNAR_STARTS, off) - 1
        if i < 0 or i >= len(LUNAR_CODES):
            return ""
        code = LUNAR_CODES[i]
        day = off - LUNAR_STARTS[i] + 1
        m = -code if code < 0 else code
        if not (1 <= m <= 12 and 1 <= day <= 30):
            return ""
        return ("闰" if code < 0 else "") + _L_MONTH[m - 1] + "月" + _L_DAY[day - 1]
    except Exception:
        return ""


def _builtin_lunar(self, dt):
    return lunar_text_of(dt)


BuiltinEngine.lunar_text = _builtin_lunar


TERM_CODES_LIST = [234336,913025,1593314,2277155,2965156,3658853,4358150,5063911,5775208,6492041,7212746,7936619,8661452,9386125,10108494,10827503,11541648,12250257,12952754,13649139,14339828,15025525,15707382,16386615,17064736,17743233,18423650,19107331,19795524,20489061,21188614,21894183,22605768,23322377,24043402,24766955,25492076,26216429,26939086,27657839,28372176,29080593,29783250,30479571,31170388,31856053,32538006,33217175,33895392,34573793,35254338,35937891,36626148,37319557,38019110,38724615,39436104,40152745,40873578,41597291,42322124,43046701,43769038,44488111,45202128,45910897,46613298,47309939,48000564,48686581,49368374,50047863,50725856,51404577,52084834,52768643,53456580,54150213,54849446,55555143,56266408,56983209,57703914,58427659,59152524,59877069,60599534,61318447,62032720,62741233,63443890,64140275,64831156,65516853,66198902,66878103,67556384,68234785,68915330,69598851,70287076,70980421,71679942,72385351,73096904,73813385,74534410,75257963,75983084,76707501,77430126,78149007,78863280,79571857,80274418,80970867,81661588,82347381,83029302,83708599,84386784,85065313,85745762,86429443,87117604,87811109,88510534,89216103,89927496,90644201,91364906,92088683,92813420,93538093,94260366,94979471,95693488,96402225,97104626,97801203,98491828,99177749,99859542,100538999,101217056,101895777,102576098,103259971,103948036,104641669,105341030,106046695,106758024,107474697,108195466,108919083,109644012,110368397,111090926,111809711,112524048,113232465,113935186,114631507,115322452,116008117,116690230,117369399,118047712,118726081,119406658,120090179,120778468,121471749,122171334,122876711,123588264,124304745,125025674,125749195,126474220,127198637,127921134,128640111,129354320,130062993,130765522,131462131,132152852,132838805,133520630,134200055,134878112,135556737,136237026,136920739,137608740,138302309,139001574,139707239,140418504,141135305,141855978,142579819,143304588,144029261,144751566,145470607,146184720,146893393,147595858,148292371,148983124,149668949,150350838,151030199,151708320,152386881,153067266,153750979,154439044,155132549,155831974,156537511,157248968,157965577,158686506,159410091,160135148,160859533,161582158,162300911,163015248,163723665,164426354,165122643,165813556,166499221,167181270,167860471,168538784,169217217,169897826,170581379,171269636,171962949,172662470,173367847,174079336,174795849,175516682,176240267,176965164,177689677,178412078,179131119,179845200,180553937,181256370,181953011,182643636,183329621,184011414,184690935,185368960,186047713,186728002,187411843,188099780,188793413,189492614,190198247,190909448,191626185,192346794,193070571,193795340,194519949,195242382,195961359,196675632,197384241,198086866,198783315,199474164,200159861,200841846,201521079,202199264,202877729,203558178,204241763,204929924,205623333,206322822,207028231,207739752,208456233,209177194,209900683,210625804,211350189,212072878,212791727,213506096,214214641,214917330,215613779,216304596,216990357,217672278,218351511,219029664,219708129,220388546,221072131,221760260,222453669,223153126,223858631,224570056,225286697,226007466,226731179,227455948,228180589,228902894,229622031,230336080,231044881,231747314,232443987,233134644,233820661,234502454,235181911,235859904,236538593,237218850,237902627,238590564,239284165,239983398,240689063,241400328,242117033,242837738,243561451,244286316,245010765,245733294,246452143,247166480,247874993,248577746,249274163,249965172,250650901,251333046,252012247,252690560,253368929,254049442,254732899,255421060,256114277,256813734,257518983,258230472,258946889,259667850,260391339,261116396,261840845,262563438,263282383,263996720,264705393,265408018,266104627,266795444,267481397,268163318,268842743,269520864,270199457,270879778,271563427,272251428,272944837,273644070,274349575,275060776,275777449,276498090,277221899,277946668,278671405,279393742,280112911,280827024,281535825,282238322,282934963,283625684,284311605,284993494,285672919,286351008,287029665,287709986,288393731,289081732,289775269,290474534,291180071,291891368,292607945,293328746,294052299,294777292,295501677,296224334,296943151,297657584,298366097,299068882,299765235,300456212,301141909,301824022,302503223,303181568,303859969,304540578,305224067,305912324,306605605,307305126,308010407,308721864,309438249,310159050,310882539,311607436,312331885,313054318,313773359,314487536,315196337,315898898,316595603,317286356,317972437,318654294,319333815,320011872,320690561,321370850,322054627,322742564,323436133,324135302,324840903,325552072,326268777,326989322,327713067,328437772,329162381,329884750,330603791,331318000,332026737,332729394,333425971,334116852,334802741,335484726,336164087,336842240,337520769,338201154,338884739,339572836,340266213,340965574,341671015,342382440,343098921,343819850,344543339,345268428,345992781,346715470,347434287,348148688,348857233,349559986,350256403,350947348,351633141,352315222,352994455,353672736,354351169,355031682,355715171,356403364,357096645,357796102,358501511,359212936,359929481,360650282,361373931,362098764,362823373,363545710,364264815,364978864,365687665,366390098,367086803,367777460,368463509,369145334,369824887,370502912,371181665,371861954,372545795,373233700,373927301,374626502,375332103,376043272,376760009,377480650,378204363,378929196,379653741,380376238,381095183,381809488,382518065,383220786,383917203,384608180,385293941,385976022,386655255,387333568,388011969,388692482,389375971,390064132,390757381,391456806,392162087,392873544,393589929,394310858,395034315,395759436,396483853,397206542,397925487,398639920,399348593,400051314,400747859,401438740,402124597,402806550,403485879,404164000,404842497,405522850,406206435,406894468,407587845,408287142,408992583,409703848,410420489,411141162,411864939,412589740,413314477,414036878,414756079,415470256,416179153,416881682,417578387,418269108,418955093,419636886,420316343,420994336,421672961,422353154,423036867,423724772,424418309,425117510,425823079,426534312,427250953,427971722,428695339,429420300,430144781,430867438,431586351,432300816,433009393,433712242,434408691,435099732,435785461,436467606,437146775,437825088,438503425,439183938,439867331,440555492,441248677,441948102,442653319,443364744,444081097,444801962,445525419,446250412,446974861,447697422,448416431,449130736,449839569,450542226,451238995,451929844,452615925,453297878,453977399,454655488,455334113,456014402,456698051,457385924,458079333,458778438,459483879,460194984,460911593,461632138,462355915,463080620,463805325,464527726,465246895,465961136,466669969,467372658,468069331,468760212,469446197,470128214,470807639,471485792,472164353,472844674,473528291,474216228,474909573,475608774,476314119,477025384,477741833,478462634,479186123,479911180,480635597,481358318,482077231,482791728,483500337,484203186,484899667,485590708,486276501,486958646,487637879,488316224,488994625,489675138,490358595,491046756,491739973,492439398,493144647,493856008,494572393,495293130,496016651,496741484,497466029,498188430,498907567,499621744,500330641,501033202,501729971,502420724,503106837,503788694,504468247,505146304,505825025,506505314,507189091,507876996,508570533,509269670,509975207,510686280,511402921,512123466,512847115,513571820,514296365,515018766,515737807,516452112,517160817,517863602,518560179,519251220,519937109,520619222,521298551,521976800,522655265,523335682,524019203,524707268,525400517,526099846,526805095,527516456,528232809,528953642,529677067,530402092,531126445,531849102,532568015,533282480,533991153,534693970,535390579,536081588,536767509,537449622,538128951,538807200,539485633,540166050,540849539,541537572,542230821,542930118,543635463,544346728,545063241,545783914,546507595,547232396,547957037,548679406,549398607,550112720,550821617,551524146,552220915,552911668,553597781,554279638,554959191,555637216,556315905,556996130,557679875,558367716,559061221,559760326,560465863,561177000,561893641,562614314,563337963,564062860,564787373,565509934,566228879,566943280,567651889,568354674,569051155,569742164,570427957,571110134,571789367,572467712,573146113,573826658,574510115,575198276,575891429,576590822,577296007,578007368,578723657,579444522,580167915,580892940,581617357,582339950,583058959,583773328,584482097,585184786,585881491,586572372,587258389,587940374,588619831,589297984,589976577,590656898,591340515,592028484,592721829,593420998,594126407,594837512,595554057,596274602,596998315,597723052,598447757,599170158,599889391,600603664,601312593,602015218,602711987,603402804,604088821,604770710,605450167,606128192,606806785,607487010,608170659,608858532,609551909,610251078,610956519,611667720,612384233,613104970,613828523,614553548,615277997,616000750,616719695,617434256,618142897,618845842,619542355,620233428,620919221,621601366,622280535,622958816,623637121,624317602,625000963,625689092,626382245,627081638,627786855,628498248,629214633,629935434,630658923,631383852,632108365,632830894,633549999,634264304,634973201,635675858,636372691,637063540,637749653,638431574,639111095,639789152,640467777,641147970,641831651,642519460,643212901,643911942,644617415,645328488,646045129,646765642,647489387,648214124,648938797,649661198,650380335,651094672,651803505,652506290,653202995,653894036,654580053,655262134,655941559,656619744,657298241,657978562,658662051,659349956,660043141,660742310,661447527,662158760,662875081,663595882,664319339,665044428,665768845,666491630,667210607,667925200,668633905,669336850,670033459,670724596,671410517,672092726,672772023,673450336,674128769,674809186,675492579,676180580,676873701,677572934,678278087,678989320,679705705,680426378,681149963,681874828,682599501,683321966,684041231,684755504,685464497,686167122,686863987,687554772,688240917,688922806,689602391,690280416,690959137,691639330,692323075,693010884,693704325,694403334,695108807,695819816,696536393,697256938,697980587,698705388,699429965,700152494,700871567,701586032,702294801,702997714,703694323,704385428,705071285,705753462,706432791,707111104,707789537,708470018,709153475,709841572,710534725,711234022,711939175,712650440,713366665,714087434,714810763,715535724,716260077,716982734,717701711,718416208,719125009,719827890,720524659,721215732,721901781,722583894,723263351,723941568,724620097,725300482,725984003,726671940,727365189,728064358,728769639,729480744,730197193,730917706,731641355,732366028,733090701,733813070,734532303,735246576,735955569,736658258,737355155,738046036,738732213,739414166,740093751,740771808,741450465,742130626,742814307,743502084,744195461,744894502,745599911,746311016,747027529,747748170,748471755,749196684,749921133,750643790,751362767,752077296,752785969,753488914,754185459,754876628,755562485,756244726,756923991,757602368,758280737,758961250,759644611,760332708,761025829,761725158,762430279,763141640,763857929,764578730,765302155,766027084,766751533,767474094,768193135,768907472,769616305,770319026,771015795,771706708,772392821,773074806,773754359,774432512,775111169,775791458,776475139,777163012,777856389,778555462,779260871,779971880,780688425,781408906,782132619,782857292,783581997,784304366,785023567,785737840,786446737,787149458,787846227,788537204,789223253,789905302,790584759,791262912,791941473,792621762,793305315,793993188,794686469,795385606,796090855,796801992,797518377,798239082,798962507,799687532,800411981,801134734,801853711,802568368,803277073,803980082,804676659,805367828,806053685,806735894,807415127,808093440,808771777,809452226,810135555,810823588,811516677,812215974,812921095,813632392,814348713,815069450,815792971,816517868,817242477,817965006,818684239,819398544,820107569,820810258,821507123,822197972,822884117,823566006,824245559,824923552,825602177,826282306,826965987,827653732,828347141,829046118,829751591,830462600,831179209,831899722,832623435,833348204,834072845,834795342,835514511,836228944,836937777,837640690,838337363,839028468,839714453,840396598,841075927,841754176,842432609,843112962,843796387,844484324,845177445,845876614,846581735,847292936,848009193,848729962,849453323,850178348,850902701,851625454,852344431,853058992,853767793,854470770,855167507,855858676,856544725,857226934,857906359,858584640,859263105,859943458,860626851,861314756,862007845,862706950,863412103,864123176,864839529,865560074,866283659,867008428,867733133,868455598,869174927,869889232,870598289,871301010,871997971,872688852,873375093,874057046,874736663,875414688,876093377,876773506,877457155,878144868,878838181,879537126,880242439,880953416,881669865,882390410,883113995,883838860,884563437,885286094,886005199,886719792,887428593,888131602,888828243,889519412,890205301,890887542,891566839,892245184,892923553,893604002,894287395,894975428,895668485,896367750,897072807,897784072,898500233,899221002,899944299,900669260,901393677,902116302,902835375,903549840,904258737,904961618,905658451,906349460,907035605,907717654,908397175,909075360,909753953,910434242,911117827,911805700,912498981,913198054,913903335,914614344,915330793,916051210,916774859,917499500,918224141,918946542,919665775,920380080,921089137,921791922,922488851,923179860,923866069,924548118,925227671,925905760,926584353,927264546,927948099,928635844,929329125,930028102,930733351,931444392,932160777,932881386,933604843,934329772,935054221,935776974,936495951,937210608,937919377,938622482,939319155,940010420,940696341,941378646,942057943,942736320,943414657,944095074,944778371,945466372,946159365,946858598,947563623,948274856,948991113,949711850,950435307,951160236,951884781,952607374,953326543,954040912,954749937,955452658,956149587,956840500,957526709,958208726,958888311,959566400,960245057,960925250,961608867,962296644,962989957,963688902,964394279,965105224,965821769,966542218,967265931,967990668,968715341,969437838,970157039,970871440,971580369,972283186,972979987,973671060,974357109,975039222,975718679,976396928,977075457,977755810,978439299,979127172,979820325,980519430,981224519,981935656,982651881,983372554,984095883,984820908,985545293,986268078,986987055,987701712,988410513,989113586,989810291,990501492,991187509,991869750,992549111,993227456,993905857,994586306,995269667,995957636,996650693,997349862,998054919,998766024,999482313,1000202890,1000926379,1001651180,1002375853,1003098382,1003817711,1004532080,1005241233,1005943986,1006640979,1007331924,1008018133,1008700086,1009379671,1010057664,1010736321,1011416418,1012100035,1012787716,1013481029,1014179942,1014885287,1015596232,1016312745,1017033226,1017756875,1018481676,1019206317,1019928942,1020648143,1021362736,1022071633,1022774674,1023471411,1024162644,1024848597,1025530806,1026210103,1026888384,1027566753,1028247106,1028930435,1029618372,1030311429,1031010630,1031715687,1032426920,1033143113,1033863882,1034587211,1035312204,1036036589,1036759310,1037478351,1038192944,1038901841,1039604818,1040301683,1040992852,1041678965,1042361142,1043040631,1043718848,1044397345,1045077666,1045761091,1046448932,1047142053,1047841094,1048546247,1049257256,1049973641,1050694122,1051417739,1052142444,1052867117,1053589550,1054308879,1055023216,1055732337,1056435122,1057132147,1057823188,1058509493,1059191574,1059871223,1060549312,1061227937,1061908066,1062591619,1063279268,1063972453,1064671302,1065376519,1066087400,1066803785,1067524298,1068247819,1068972716,1069697261,1070420014,1071139119,1071853808,1072562673,1073265810,1073962515,1074653844,1075339829,1076022166,1076701495,1077379904,1078058273,1078738690,1079421987,1080109924,1080802853,1081502022,1082206951,1082918120,1083634217,1084354922,1085078283,1085803276,1086527757,1087250446,1087969647,1088684144,1089393169,1090096050,1090792979,1091484020,1092170197,1092852278,1093531831,1094209952,1094888577,1095568834,1096252387,1096940164,1097633413,1098332358,1099037639,1099748520,1100464969,1101185354,1101908971,1102633644,1103358349,1104080782,1104800079,1105514480,1106223537,1106926450,1107623347,1108314452,1109000629,1109682742,1110362263,1111040448,1111719009,1112399266,1113082787,1113770596,1114463749,1115162758,1115867879,1116578888,1117295113,1118015658,1118738987,1119463884,1120188269,1120910990,1121629999,1122344720,1123053553,1123756690,1124453459,1125144820,1125830869,1126513206,1127192599,1127870976,1128549345,1129229762,1129913059,1130600996,1131293957,1131993094,1132698087,1133409192,1134125353,1134845962,1135569355,1136294188,1137018733,1137741262,1138460559,1139174960,1139884113,1140586930,1141283955,1141974964,1142661269,1143343286,1144022935,1144700992,1145379649,1146059746,1146743331,1147430948,1148124229,1148823046,1149528359,1150239208,1150955689,1151676138,1152399787,1153124524,1153849197,1154571758,1155290959,1156005488,1156714449,1157417426,1158114227,1158805428,1159491477,1160173718,1160853111,1161531392,1162209857,1162890178,1163573571,1164261444,1164954501,1165653574,1166358599,1167069736,1167785897,1168506602,1169229931,1169954924,1170679309,1171402062,1172121071,1172835696,1173544529,1174247570,1174944371,1175635572,1176321653,1177003894,1177683319,1178361632,1179040097,1179720482,1180403875,1181091780,1181784837,1182483878,1183188935,1183899944,1184616233,1185336714,1186060235,1186784972,1187509645,1188232142,1188951471,1189665840,1190374993,1191077810,1191774867,1192465844,1193152149,1193834166,1194513783,1195191840,1195870465,1196550562,1197234115,1197921732,1198614981,1199313798,1200019015,1200729864,1201446217,1202166666,1202890219,1203615084,1204339661,1205062414,1205781615,1206496336,1207205265,1207908434,1208605235,1209296532,1209982517,1210664822,1211344119,1212022432,1212700737,1213381122,1214064355,1214752260,1215445157,1216144262,1216849191,1217560360,1218276457,1218997162,1219720523,1220445516,1221169997,1221892750,1222611951,1223326576,1224035601,1224738610,1225435571,1226126708,1226812885,1227494998,1228174487,1228852640,1229531137,1230211330,1230894755,1231582468,1232275589,1232974502,1233679687,1234390600,1235106985,1235827402,1236551051,1237275756,1238000493,1238722958,1239442351,1240156784,1240865969,1241568882,1242265939,1242957044,1243643349,1244325462,1245005047,1245683168,1246361761,1247041922,1247725379,1248413028,1249106117,1249804966,1250510023,1251220904,1251937161,1252657642,1253381035,1254105964,1254830413,1255553198,1256272271,1256987056,1257695953,1258399186,1259096019,1259787444,1260473557,1261155990,1261835383,1262513824,1263192193,1263872610,1264555811,1265243684,1265936517,1266635558,1267340391,1268051432,1268767465,1269488074,1270211403,1270936300,1271660845,1272383502,1273102831,1273817392,1274526577,1275229522,1275926611,1276617684,1277304021,1277986134,1278665783,1279343904,1280022561,1280702690,1281386211,1282073860,1282767013,1283465798,1284170951,1284881736,1285598121,1286318442,1287042059,1287766732,1288491469,1289214030,1289933391,1290647952,1291357073,1292060114,1292757075,1293448276,1294134453,1294816662,1295496183,1296174432,1296852929,1297533218,1298216643,1298904452,1299597509,1300296486,1301001511,1301712520,1302428617,1303149194,1303872427,1304597356,1305321709,1306044494,1306763535,1307478256,1308187185,1308890354,1309587219,1310278580,1310964693,1311647062,1312326519,1313004896,1313683297,1314363714,1315047043,1315734980,1316427941,1317127014,1317831975,1318542984,1319259145,1319979626,1320703019,1321427724,1322152333,1322874798,1323594127,1324308560,1325017777,1325720658,1326417843,1327108948,1327795349,1328477462,1329157143,1329835232,1330513889,1331193986,1331877539,1332565092,1333258277,1333957030,1334662247,1335373032,1336089385,1336809770,1337533323,1338258060,1338982669,1339705294,1340424527,1341139184,1341848209,1342551378,1343248243,1343939604,1344625749,1345308086,1345987511,1346665856,1347344257,1348024610,1348707875,1349395716,1350088613,1350787654,1351492551,1352203656,1352919753,1353640426,1354363755,1355088748,1355813165,1356535950,1357255055,1357969712,1358678673,1359381746,1360078643,1360769876,1361456053,1362138294,1362817815,1363496064,1364174561,1364854882,1365538275,1366226084,1366919109,1367618086,1368323143,1369034056,1369750377,1370470794,1371194379,1371919084,1372643821,1373366318,1374085711,1374800112,1375509297,1376212146,1376909203,1377600276,1378286581,1378968694,1379648343,1380326464,1381005121,1381685282,1382368835,1383056452,1383749605,1384448390,1385153511,1385864296,1386580553,1387300970,1388024395,1388749260,1389473773,1390196526,1390915695,1391630448,1392339409,1393042642,1393739443,1394430868,1395116917,1395799318,1396478679,1397157056,1397835393,1398515810,1399199043,1399886948,1400579781,1401278854,1401983687,1402694728,1403410761,1404131370,1404854667,1405579628,1406304141,1407026862,1407746159,1408460816,1409169969,1409873010,1410570067,1411261204,1411947477,1412629558,1413309111,1413987200,1414665761,1415345858,1416029315,1416716932,1417410053,1418108870,1418814023,1419524808,1420241193,1420961546,1421685195,1422409900,1423134669,1423857198,1424576655,1425291184,1426000401,1426703442,1427400499,1428091700,1428777941,1429460118,1430139607,1430817760,1431496225,1432176354,1432859747,1433547396,1434240421,1434939302,1435644327,1436355272,1437071433,1437791978,1438515339,1439240268,1439964685,1440687502,1441406575,1442121392,1442830321,1443533586,1444230451,1444921908,1445608021,1446290454,1446969847,1447648256,1448326593,1449006946,1449690147,1450377988,1451070789,1451769798,1452474631,1453185608,1453901673,1454622218,1455345579,1456070412,1456795021,1457517614,1458236975,1458951504,1459660753,1460363730,1461060947,1461752084,1462438549,1463120662,1463800407,1464478496,1465157121,1465837154,1466520611,1467208100,1467901157,1468599814,1469304871,1470015528,1470731849,1471452106,1472175691,1472900428,1473625165,1474347822,1475067183,1475781904,1476491057,1477194226,1477891219,1478582580,1479268789,1479951126,1480630583,1481308896,1481987329,1482667586,1483350883,1484038596,1484731461,1485430374,1486135175,1486846120,1487562121,1488282698,1489005963,1489730956,1490455405,1491178254,1491897423,1492612208,1493321233,1494024466,1494721427,1495412756,1496098933,1496781270,1497460727,1498139040,1498817473,1499497826,1500181123,1500868932,1501561861,1502260774,1502965703,1503676584,1504392745,1505113130,1505836587,1506561260,1507285933,1508008430,1508727887,1509442352,1510151665,1510854642,1511551859,1512242996,1512929429,1513611542,1514291287,1514969376,1515648033,1516328130,1517011651,1517699172,1518392293,1519090950,1519796039,1520506728,1521222953,1521943242,1522666635,1523391372,1524115885,1524838574,1525557775,1526272560,1526981617,1527684914,1528381875,1529073396,1529759573,1530442070,1531121495,1531799936,1532478305,1533158658,1533841859,1534529668,1535222437,1535921414,1536626183,1537337160,1538053129,1538773706,1539496907,1540221836,1540946285,1541669038,1542388239,1543102960,1543812113,1544515250,1545212339,1545903604,1546589941,1547272214,1547951799,1548630016,1549308545,1549988738,1550672099,1551359748,1552052741,1552751526,1553456519,1554167304,1554883593,1555603914,1556327499,1557052172,1557776909,1558499438,1559218895,1559933392,1560642641,1561345650,1562042803,1562734004,1563420341,1564102550,1564782199,1565460352,1566138945,1566819106,1567502563,1568190148,1568883205,1569581990,1570287015,1570997800,1571713961,1572434410,1573157739,1573882636,1574607053,1575329838,1576048975,1576763760,1577472721,1578176018,1578872883,1579564340,1580250453,1580932918,1581612343,1582290816,1582969185,1583649602,1584332835,1585020708,1585713541,1586412518,1587117319,1587828296,1588544265,1589264778,1589988075,1590712940,1591437485,1592160142,1592879471,1593594096,1594303345,1595006386,1595703571,1596394740,1597081141,1597763286,1598442967,1599121088,1599799681,1600479746,1601163203,1601850756,1602543813,1603242502,1603947559,1604658248,1605374537,1606094794,1606818379,1607543084,1608267821,1608990446,1609709903,1610424592,1611133873,1611837042,1612534131,1613225460,1613911733,1614594006,1615273495,1615951712,1616630145,1617310306,1617993603,1618681252,1619374181,1620073030,1620777895,1621488840,1622204905,1622925450,1623648747,1624373772,1625098189,1625821070,1626540239,1627255120,1627964177,1628667474,1629364435,1630055892,1630742069,1631424470,1632103863,1632782208,1633460545,1634140834,1634824035,1635511812,1636204613,1636903558,1637608391,1638319336,1639035433,1639755914,1640479339,1641204140,1641928813,1642651406,1643370863,1644085392,1644794737,1645497778,1646195027,1646886228,1647572725,1648254870,1648934647,1649612736,1650291393,1650971394,1651654851,1652342308,1653035333,1653733894,1654438919,1655149544,1655865769,1656586026,1657309515,1658034252,1658758893,1659481582,1660200911,1660915696,1661624881,1662328178,1663025235,1663716756,1664403029,1665085494,1665765015,1666443424,1667121825,1667802146,1668485315,1669173028,1669865765,1670564614,1671269319,1671980200,1672696073,1673416618,1674139819,1674864780,1675589261,1676312142,1677031407,1677746224,1678455409,1679158674,1679855763,1680547124,1681233429,1681915766,1682595319,1683273600,1683952097,1684632322,1685315619,1686003268,1686696165,1687394918,1688099815,1688810568,1689526697,1690246986,1690970475,1691695148,1692419917,1693142478,1693862031,1694576624,1695286001,1695989074,1696686323,1697377556,1698063989,1698746166,1699425847,1700103968,1700782593,1701462658,1702146147,1702833668,1703526725,1704225414,1704930407,1705641096,1706357257,1707077546,1707800875,1708525644,1709250125,1709972878,1710692079,1711406928,1712115985,1712819378,1713516339,1714207892,1714894101,1715576598,1716256055,1716934496,1717612865,1718293250,1718976419,1719664228,1720356997,1721055942,1721760647,1722471592,1723187497,1723907978,1724631179,1725356044,1726080461,1726803182,1727522447,1728237168,1728946417,1729649586,1730346803,1731038132,1731724597,1732406870,1733086551,1733764704,1734443265,1735123362,1735806723,1736494212,1737187173,1737885830,1738590791,1739301448,1740017673,1740737898,1741461451,1742186092,1742910861,1743633422,1744352911,1745067536,1745776849,1746480018,1747177235,1747868596,1748554997,1749237302,1749916919,1750595136,1751273665,1751953794,1752637091,1753324644,1754017541,1754716262,1755421127,1756131912,1756847977,1757568426,1758291723,1759016684,1759741133,1760463982,1761183151,1761898000,1762607025,1763310386,1764007315,1764698836,1765385013,1766067478,1766746935,1767425344,1768103713,1768784098,1769467235,1770155044,1770847781,1771546694,1772251431,1772962312,1773678313,1774398762,1775122123,1775846924,1776571533,1777294190,1778013615,1778728208,1779437553,1780140594,1780837843,1781529044,1782215509,1782897686,1783577431,1784255552,1784934241,1785614306,1786297763,1786985220,1787678245,1788376806,1789081799,1789792328,1790508521,1791228682,1791952171,1792676844,1793401517,1794124174,1794843599,1795558384,1796267633,1796970930,1797668051,1798359508,1799045813,1799728214,1800407767,1801086080,1801764481,1802444738,1803127939,1803815588,1804508389,1805207174,1805911911,1806622728,1807338601,1808059114,1808782283,1809507244,1810231693,1810954606,1811673839,1812388784,1813097969,1813801330,1814498419,1815189908,1815876149,1816558550,1817238007,1817916288,1818594657,1819274882,1819958051,1820645700,1821338501,1822037286,1822742119,1823452904,1824168969,1824889322,1825612779,1826337484,1827062221,1827784846,1828504399,1829219024,1829928465,1830631570,1831328915,1832020180,1832706709,1833388886,1834068599,1834746688,1835425281,1836105250,1836788675,1837476068,1838169061,1838867622,1839572615,1840283208,1840999401,1841719658,1842443051,1843167788,1843892333,1844615086,1845334351,1846049200,1846758353,1847461778,1848158835,1848850452,1849536725,1850219286,1850898775,1851577216,1852255585,1852935906,1853619043,1854306756,1854999429,1855698246,1856402855,1857113736,1857829545,1858550058,1859273227,1859998156,1860722605,1861445422,1862164687,1862879504,1863588785,1864292050,1864989299,1865680724,1866367189,1867049558,1867729239,1868407488,1869086017,1869766146,1870449443,1871136932,1871829765,1872528358,1873233191,1873943784,1874659881,1875380074,1876103563,1876828236,1877553005,1878275630,1878995215,1879709904,1880419345,1881122546,1881819859,1882511188,1883197685,1883879990,1884559703,1885237856,1885916449,1886596546,1887279907,1887967396,1888660293,1889358886,1890063751,1890774376,1891490409,1892210730,1892934027,1893658892,1894383373,1895106254,1895825487,1896540464,1897249553,1897953010,1898650035,1899341620,1900027861,1900710358,1901389815,1902068256,1902746593,1903426978,1904110115,1904797892,1905490597,1906189510,1906894183,1907605064,1908320937,1909041386,1909764587,1910489420,1911213933,1911936654,1912656047,1913370768,1914080145,1914783314,1915480627,1916171956,1916858517,1917540758,1918220535,1918898688,1919577313,1920257378,1920940771,1921628228,1922321189,1923019718,1923724647,1924435176,1925151337,1925871466,1926594923,1927319500,1928044205,1928766798,1929486255,1930201008,1930910385,1931613682,1932310963,1933002452,1933688917,1934371350,1935050999,1935729280,1936407777,1937087938,1937771171,1938458724,1939151525,1939850214,1940554919,1941265672,1941981577,1942702026,1943425195,1944150156,1944874573,1945597486,1946316719,1947031664,1947740817,1948444242,1949141331,1949832916,1950519221,1951201718,1951881207,1952559616,1953237985,1953918274,1954601379,1955289060,1955981765,1956680550,1957385255,1958096040,1958812041,1959532426,1960255819,1960980588,1961705293,1962427950,1963147471,1963862128,1964571569,1965274674,1965972019,1966663284,1967349845,1968032054,1968711831,1969389920,1970068577,1970748610,1971432035,1972119428,1972812421,1973510950,1974215911,1974926440,1975642569,1976362762,1977086219,1977810892,1978535533,1979258254,1979977615,1980692432,1981401649,1982105042,1982802131,1983493684,1984179989,1984862486,1985542007,1986220416,1986898849,1987579138,1988262339,1988950020,1989642725,1990341510,1991046151,1991756968,1992472777,1993193258,1993916395,1994641324,1995365773,1996088654,1996807951,1997522864,1998232145,1998935506,1999632723,2000324212,2001010613,2001692982,2002372567,2003050816,2003729249,2004409410,2005092579,2005780132,2006472901,2007171558,2007876327,2008586952,2009303017,2010023242,2010746699,2011471372,2012196173,2012918830,2013638479,2014353168,2015062737,2015765938,2016463347,2017154708,2017841237,2018523478,2019203191,2019881280,2020559809,2021239778,2021923107,2022610436,2023303333,2024001862,2024706727,2025417320,2026133417,2026853706,2027577067,2028301900,2029026445,2029749326,2030468623,2031183632,2031892817,2032596338,2033293427,2033985076,2034671349,2035353910,2036033367,2036711776,2037390049,2038070338,2038753379,2039441060,2040133669,2040832486,2041537063,2042247912,2042963753,2043684234,2044407435,2045132332,2045856845,2046579630,2047299023,2048013840,2048723249,2049426546,2050123891,2050815316,2051501877,2052184246,2052863991,2053542208,2054220769,2054900802,2055584099,2056271460,2056964261,2057662726,2058367495,2059077928,2059793993,2060514090,2061237547,2061962188,2062686957,2063409582,2064129167,2064843920,2065553393,2066256722,2066954099,2067645620,2068332181,2069014614,2069694359,2070372608,2071051169,2071731266,2072414531,2073101956,2073794693,2074493222,2075197863,2075908424,2076624297,2077344586,2078067755,2078792652,2079517133,2080240078,2080959407,2081674448,2082383665,2083087218,2083784339,2084476020,2085162325,2085844886,2086524407,2087202848,2087881185,2088561506,2089244579,2089932228,2090624837,2091323590,2092028135,2092738888,2093454697,2094175018,2094898283,2095623052,2096347661,2097070382,2097789935,2098504688,2099214193,2099917426,2100614867,2101306260,2101992853,2102675126,2103354903,2104033024,2104711681,2105391682,2106075075,2106762468,2107455397,2108153862,2108858759,2109569192,2110285257,2111005322,2111728715,2112453260,2113177901,2113900526,2114619951,2115334768,2116044145,2116747570,2117444819,2118136468,2118822901,2119505430,2120185079,2120863456,2121541889,2122222146,2122905315,2123592932,2124285605,2124984326,2125688935,2126399624,2127115401,2127835786,2128558859,2129283724,2130008109,2130730958,2131450191,2132165168,2132874417,2133577906,2134275123,2134966804,2135653237,2136335766,2137015383,2137693728,2138372129,2139052354,2139735459,2140423012,2141115653,2141814310,2142518951,2143229608,2143945545,2144665770,2145389131,2146113836,2146838541,2147561166,2148280783,2148995472,2149705009,2150408242,2151105683,2151797076,2152483733,2153166006,2153845847,2154523968,2155202593,2155882594,2156565955,2157253252,2157946149,2158644582,2159349415,2160059912,2160775977,2161496202,2162219595,2162944332,2163668909,2164391726,2165111055,2165826000,2166535217,2167238674,2167935795,2168627444,2169313749,2169996310,2170675831,2171354272,2172032641,2172712962,2173396067,2174083748,2174776357,2175475142,2176179687,2176890472,2177606249,2178326698,2179049867,2179774796,2180499277,2181222126,2181941487,2182656368,2183365713,2184069074,2184766355,2185457812,2186144309,2186826678,2187506391,2188184640,2188863169,2189543298,2190226531,2190914020,2191606789,2192305318,2193010023,2193720520,2194436521,2195156618,2195880043,2196604652,2197329421,2198052078,2198771727,2199486480,2200196049,2200899378,2201596819,2202288276,2202974869,2203657206,2204336951,2205015136,2205693665,2206373698,2207056963,2207744356,2208437125,2209135622,2209840359,2210550888,2211266793,2211987050,2212710315,2213435148,2214159693,2214882638,2215602031,2216317136,2217026417,2217730002,2218427187,2219118900,2219805205,2220487766,2221167223,2221845632,2222523873,2223204098,2223887107,2224574724,2225267237,2225965990,2226670535,2227381288,2228097129,2228817514,2229540747,2230265612,2230990221,2231713038,2232432591,2233147440,2233856977,2234560338,2235257811,2235949268,2236635893,2237318198,2237997943,2238676096,2239354625,2240034594,2240717859,2241405188,2242097989,2242796422,2243501223,2244211624,2244927689,2245647786,2246371243,2247095820,2247820557,2248543214,2249262767,2249977616,2250687089,2251390514,2252087923,2252779572,2253466133,2254148630,2254828375,2255506688,2256185185,2256865314,2257548483,2258235908,2258928549,2259627078,2260331623,2261042216,2261757961,2262478282,2263201419,2263926316,2264650765,2265373742,2266093039,2266808112,2267517425,2268221042,2268918291,2269610036,2270296469,2270979094,2271658711,2272337120,2273015489,2273695714,2274378755,2275066276,2275758789,2276457382,2277161863,2277872456,2278588265,2279308490,2280031787,2280756524,2281481229,2282203982,2282923663,2283638480,2284348113,2285051442,2285749011,2286440436,2287127157,2287809462,2288489303,2289167456,2289846113,2290526050,2291209411,2291896676,2292589509,2293287878,2293992647,2294703016,2295419017,2296139114,2296862475,2297587116,2298311757,2299034510,2299753999,2300468976,2301178353,2301881906,2302579155,2303270868,2303957301,2304639894,2305319447,2305997888,2306676257,2307356514,2308039619,2308727236,2309419845,2310118534,2310823047,2311533736,2312249449,2312969802,2313692875,2314417772,2315142157,2315865070,2316584399,2317299376,2318008753,2318712242,2319409587,2320101268,2320787797,2321470326,2322150007,2322828352,2323506817,2324186978,2324870147,2325557604,2326250245,2326948774,2327653383,2328363880,2329079753,2329799850,2330523179,2331247756,2331972461,2332695086,2333414735,2334129488,2334839121,2335542450,2336240019,2336931540,2337618293,2338300694,2338980567,2339658752,2340337377,2341017346,2341700643,2342387940,2343080709,2343779046,2344483751,2345194184,2345910089,2346630250,2347353515,2348078284,2348802829,2349525710,2350245071,2350960144,2351669425,2352373042,2353070259,2353762004,2354448405,2355131062,2355810583,2356489056,2357167393,2357847650,2358530659,2359218276,2359910757,2360609446,2361313895,2362024616,2362740329,2363460746,2364183883,2364908780,2365633293,2366356174,2367075631,2367790544,2368499985,2369203378,2369900787,2370592308,2371278901,2371961302,2372641047,2373319296,2373997857,2374677922,2375361187,2376048548,2376741317,2377439750,2378144455,2378854856,2379570825,2380290858,2381014251,2381738828,2382463565,2383186190,2383905807,2384620592,2385330129,2386033522,2386730963,2387422516,2388109109,2388791542,2389471319,2390149600,2390828161,2391508226,2392191491,2392878884,2393571621,2394270086,2394974695,2395685192,2396401001,2397121226,2397844331,2398569196,2399293645,2400016590,2400735951,2401451056,2402160369,2402864018,2403561267,2404253044,2404939445,2405622070,2406301591,2406980000,2407658273,2408338498,2409021475,2409709028,2410401509,2411100166,2411804615,2412515272,2413231017,2413951306,2414674507,2415399276,2416123949,2416846734,2417566383,2418281296,2418990961,2419694322,2420391891,2421083380,2421770101,2422452406,2423132215,2423810304,2424488865,2425168770,2425852003,2426539236,2427232005,2427930342,2428635079,2429345448,2430061481,2430781578,2431505003,2432229612,2432954349,2433677070,2434396623,2435111568,2435821041,2436524594,2437221971,2437913684,2438600181,2439282742,2439962359,2440640704,2441319105,2441999234,2442682307,2443369764,2444062309,2444760870,2445465351,2446175976,2446891721,2447612074,2448335147,2449060108,2449784525,2450507502,2451226863,2451941936,2452651313,2453354898,2454052243,2454743988,2455430517,2456113142,2456792823,2457471232,2458149601,2458829794,2459512803,2460200228,2460892709,2461591206,2462295655,2463006088,2463721865,2464441994,2465165259,2465889932,2466614669,2467337390,2468057103,2468771952,2469481649,2470185042,2470882675,2471574228,2472261013,2472943414,2473623319,2474301504,2474980161,2475660098,2476343363,2477030564,2477723269,2478421510,2479126151,2479836424,2480552329,2481272330,2481995627,2482720332,2483444973,2484167854,2484887375,2485602512,2486311953,2487015602,2487712915,2488404724,2489091157,2489773814,2490453367,2491131808,2491810145,2492490370,2493173379,2493860932,2494553381,2495252006,2495956391,2496667016,2497382665,2498102986,2498826059,2499550924,2500275437,2500998350,2501717839,2502432912,2503142417,2503845970,2504543443,2505235092,2505921717,2506604182,2507283927,2507962176,2508640673,2509320738,2510003907,2510691300,2511383941,2512082374,2512786983,2513497352,2514213225,2514933226,2515656555,2516381068,2517105805,2517828430,2518548079,2519262896,2519972561,2520676018,2521373619,2522065236,2522751989,2523434454,2524114327,2524792576,2525471137,2526151138,2526834403,2527521668,2528214373,2528912742,2529617351,2530327752,2531043529,2531763658,2532486827,2533211596,2533936045,2534658958,2535378319,2536093456,2536802833,2537506578,2538203891,2538895796,2539582293,2540265014,2540944599,2541623104,2542301377,2542981634,2543664547,2544352068,2545044453,2545743014,2546447367,2547157992,2547873641,2548593930,2549317067,2550041900,2550766509,2551489326,2552208943,2552923888,2553633521,2554336978,2555034579,2555726164,2556412885,2557095318,2557775191,2558453376,2559131969,2559811938,2560495139,2561182372,2561875077,2562573350,2563278023,2563988296,2564704297,2565424298,2566147723,2566872332,2567597069,2568319790,2569039407,2569754320,2570463857,2571167346,2571864819,2572556468,2573243093,2573925622,2574605367,2575283712,2575962209,2576642338,2577325507,2578012900,2578705509,2579403974,2580108487,2580818984,2581534697,2582254954,2582978059,2583702956,2584427405,2585150414,2585869775,2586584912,2587294289,2587997970,2588695283,2589387092,2590073557,2590756214,2591435863,2592114304,2592792673,2593472898,2594155875,2594843364,2595535813,2596234342,2596938727,2597649192,2598364905,2599085034,2599808235,2600532908,2601257613,2601980398,2602700111,2603415024,2604124785,2604828242,2605525907,2606217492,2606904277,2607586678,2608266583,2608944704,2609623329,2610303202,2610986467,2611673636,2612366341,2613064582,2613769223,2614479464,2615195401,2615915370,2616638699,2617363372,2618088077,2618810926,2619530511,2620245616,2620955153,2621658866,2622356275,2623048084,2623734613,2624417238,2625096823,2625775200,2626453537,2627133666,2627816643,2628504068,2629196517,2629895046,2630599431,2631310024,2632025673,2632745994,2633469067,2634193996,2634918477,2635641486,2636360943,2637076080,2637785585,2638489266,2639186739,2639878516,2640565141,2641247734,2641927415,2642605760,2643284161,2643964226,2644647267,2645334628,2646027141,2646725510,2647429991,2648140360,2648856169,2649576202,2650299499,2651024076,2651748813,2652471502,2653191215,2653906064,2654615793,2655319250,2656016947,2656708564,2657395413,2658077910,2658757847,2659436096,2660114753,2660794690,2661477923,2662165092,2662857765,2663555974,2664260487,2664970760,2665686537,2666406538,2667129739,2667854444,2668578989,2669301934,2670021391,2670736592,2671446033,2672149810,2672847187,2673539124,2674225621,2674908406,2675588023,2676266528,2676944833,2677625090,2678308003,2678995460,2679687813,2680386310,2681090567,2681801096,2682516617,2683236874,2683959915,2684684748,2685409293,2686132238,2686851855,2687566928,2688276593,2688980178,2689677779,2690369460,2691056213,2691738678,2692418519,2693096736,2693775297,2694455298,2695138467,2695825732,2696518341,2697216614,2697921191,2698631432,2699347305,2700067242,2700790571,2701515116,2702239853,2702962542,2703682223,2704397136,2705106833,2705810354,2706507955,2707199636,2707886357,2708568886,2709248695,2709926976,2710605505,2711285538,2711968739,2712656036,2713348677,2714047046,2714751559,2715461960,2716177673,2716897802,2717620875,2718345676,2719070093,2719793038,2720512431,2721227600,2721937009,2722640786,2723338163,2724030068,2724716629,2725399382,2726078999,2726757504,2727435841,2728116066,2728798979,2729486436,2730178789,2730877286,2731581575,2732292072,2733007657,2733727818,2734450923,2735175628,2735900237,2736622990,2737342671,2738057616,2738767345,2739470866,2740168595,2740860244,2741547125,2742229590,2742909527,2743587744,2744266369,2744946274,2745629475,2746316612,2747009253,2747707398,2748412007,2749122184,2749838057,2750557994,2751281323,2752005932,2752730669,2753453454,2754173071,2754888112,2755597713,2756301330,2756998835,2757690644,2758377237,2759059862,2759739575,2760417952,2761096353,2761776450,2762459491,2763146852,2763839301,2764537734,2765242087,2765952584,2766668201,2767388490,2768111531,2768836460,2769560941,2770283982,2771003407,2771718608,2772428081,2773131794,2773829203,2774521012,2775207573,2775890230,2776569879,2777248288,2777926657,2778606818,2779289827,2779977252,2780669701,2781368102,2782072487,2782782888,2783498569,2784218634,2784941835,2785666444,2786391181,2787113902,2787833647,2788548528,2789258321,2789961778,2790659507,2791351124,2792037973,2792720406,2793400343,2794078528,2794757185,2795437090,2796120323,2796807492,2797500133,2798198310,2798902887,2799613064,2800328873,2801048810,2801772043,2802496684,2803221325,2803944206,2804663791,2805378992,2806088561,2806792338,2807489811,2808181748,2808868277,2809550998,2810230583,2810909024,2811587265,2812267426,2812950307,2813637700,2814330021,2815028486,2815732743,2816443272,2817158793,2817879082,2818602123,2819327020,2820051533,2820774574,2821494159,2822209360,2822919025,2823622738,2824320371,2825012180,2825698901,2826381462,2827061239,2827739488,2828417921,2829097890,2829780899,2830468100,2831160613,2831858854,2832563335,2833273608,2833989449,2834709418,2835432747,2836157324,2836882125,2837604846,2838324591,2839039536,2839749329,2840452914,2841150611,2841842356,2842529205,2843211734,2843891607,2844569856,2845248417,2845928322,2846611491,2847298628,2847991205,2848689414,2849393863,2850104136,2850819881,2851539946,2852263083,2852987852,2853712397,2854435406,2855154863,2855870096,2856579569,2857283442,2857980883,2858672884,2859359477,2860042326,2860722007,2861400544,2862078881,2862759074,2863441955,2864129348,2864821573,2865519974,2866224135,2866934536,2867650025,2868370186,2869093195,2869817996,2870542573,2871265486,2871985199,2872700272,2873410065,2874113714,2874811475,2875503220,2876190101,2876872662,2877552631,2878230880,2878909505,2879589442,2880272611,2880959748,2881652293,2882350406,2883054855,2883764968,2884480713,2885200554,2885923851,2886648396,2887373197,2888095982,2888815727,2889530800,2890240561,2890944242,2891641907,2892333716,2893020437,2893703062,2894382839,2895061184,2895739681,2896419746,2897102819,2897790084,2898482597,2899180902,2899885287,2900595624,2901311209,2902031338,2902754347,2903479212,2904203661,2904926702,2905646159,2906361456,2907070961,2907774834,2908472307,2909164276,2909850901,2910533654,2911213335,2911891776,2912570113,2913250306,2913933251,2914620676,2915313061,2916011494,2916715783,2917426152,2918141737,2918861770,2919584875,2920309452,2921034093,2921756814,2922476527,2923191472,2923901297,2924604850,2925302675,2925994388,2926681333,2927363862,2928043863,2928722112,2929400769,2930080674,2930763907,2931451012,2932143621,2932841766,2933546279,2934256424,2934972201,2935692074,2936415307,2937139852,2937864493,2938587310,2939306895,2940022032,2940731633,2941435442,2942132979,2942824948,2943511605,2944194390,2944874103,2945552544,2946230913,2946911042,2947593955,2948281316,2948973637,2949672038,2950376263,2951086696,2951802217,2952522442,2953245451,2953970348,2954694829,2955417870,2956137391,2956852592,2957562193,2958265970,2958963539,2959655412,2960342133,2961024790,2961704567,2962382944,2963061345,2963741410,2964424419,2965111684,2965804101,2966502406,2967206759,2967917064,2968632777,2969352778,2970076043,2970800652,2971525421,2972248142,2972967919,2973682864,2974392657,2975096146,2975793907,2976485556,2977172405,2977854902,2978534839,2979213056,2979891681,2980571618,2981254819,2981941956,2982634597,2983332742,2984037255,2984747464,2985463209,2986183178,2986906347,2987631052,2988355629,2989078606,2989798127,2990513392,2991222897,2991926738,2992624179,2993316180,2994002741,2994685526,2995365143,2996043648,2996721953,2997402146,2998084995,2998772388,2999464645,3000163078,3000867207,3001577640,3002293097,3003013258,3003736235,3004461068,3005185613,3005908622,3006628271,3007343472,3008053265,3008756978,3009454739,3010146548,3010833365,3011515926,3012195767,3012874016,3013552481,3014232418,3014915459,3015602564,3016295045,3016993190,3017697607,3018407752,3019123497,3019843370,3020566699,3021291244,3022016077,3022738862,3023458703,3024173776,3024883633,3025587314,3026285043,3026976884,3027663669,3028346262,3029026071,3029704288,3030382721,3031062626,3031745667,3032432804,3033125253,3033823430,3034527815,3035238088,3035953737,3036673834,3037396939,3038121772,3038846285,3039569390,3040288879,3041004240,3041713809,3042417746,3043115283,3043807316,3044493941,3045176758,3045856407,3046534912,3047213153,3047893282,3048576099,3049263428,3049955653,3050653990,3051358119,3052068456,3052783945,3053504042,3054227083,3054951788,3055676429,3056399278,3057119023,3057834064,3058543921,3059247570,3059945427,3060637204,3061324213,3062006774,3062686807,3063365056,3064043681,3064723586,3065406723,3066093764,3066786245,3067484262,3068188647,3068898632,3069614345,3070334154,3071057387,3071781932,3072506669,3073229486,3073949231,3074664400,3075374161,3076078002,3076775699,3077467668,3078154421,3078837174,3079516951,3080195392,3080873793,3081553858,3082236803,3082924036,3083616325,3084314566,3085018727,3085729000,3086444425,3087164522,3087887467,3088612332,3089336813,3090059918,3090779503,3091494864,3092204529,3092908466,3093606099,3094298100,3094984821,3095667574,3096347319,3097025760,3097704097,3098384194,3099067107,3099754404,3100446693,3101144966,3101849191,3102559432,3103275017,3103994954,3104718091,3105442668,3106167373,3106890126,3107609935,3108324944,3109034865,3109738482,3110436339,3111128116,3111815093,3112497654,3113177655,3113855872,3114534497,3115214370,3115897571,3116584644,3117277221,3117975302,3118679751,3119389864,3120105545,3120825418,3121548555,3122273164,3122997741,3123720622,3124440207,3125155440,3125865073,3126568978,3127266579,3127958644,3128645365,3129328246,3130007959,3130686496,3131364833,3132044994,3132727843,3133415140,3134107365,3134805670,3135509767,3136220104,3136935497,3137655626,3138378539,3139103372,3139827821,3140550830,3141270415,3141985680,3142695441,3143399282,3144097043,3144788980,3145475861,3146158582,3146838487,3147516864,3148195361,3148875362,3149558339,3150245508,3150937861,3151635974,3152340263,3153050376,3153766057,3154485898,3155209163,3155933676,3156658509,3157381262,3158101103,3158816144,3159526033,3160229682,3160927507,3161619316,3162306229,3162988822,3163668759,3164347040,3165025601,3165705538,3166388643,3167075748,3167768229,3168466310,3169170695,3169880840,3170596489,3171316490,3172039563,3172764332,3173488909,3174211950,3174931503,3175646832,3176356433,3177060370,3177757875,3178449940,3179136565,3179819414,3180499095,3181177632,3181855937,3182536130,3183218979,3183906372,3184598597,3185296966,3186001063,3186711400,3187426825,3188146890,3188869867,3189594604,3190319149,3191042062,3191761775,3192476944,3193186801,3193890482,3194588339,3195280148,3195967093,3196649686,3197329687,3198007936,3198686529,3199366466,3200049571,3200736676,3201429189,3202127238,3202831623,3203541640,3204257353,3204977098,3205700331,3206424844,3207149613,3207872398,3208592239,3209307376,3210017265,3210721074,3211418867,3212110804,3212797621,3213480310,3214160119,3214838432,3215516865,3216196802,3216879779,3217566916,3218259237,3218957446,3219661671,3220371944,3221087433,3221807530,3222530539,3223255372,3223979885,3224703022,3225422607,3226138032,3226847697,3227551730,3228249363,3228941460,3229628181,3230310998,3230990679,3231669120,3232347393,3233027458,3233710275,3234397508,3235089701,3235787974,3236492135,3237202440,3237917961,3238637994,3239361131,3240085772,3240810477,3241533326,3242253135,3242968208,3243678129,3244381810,3245079731,3245771540,3246458581,3247141174,3247821207,3248499424,3249178017,3249857858,3250540995,3251227972,3251920453,3252618438,3253322823,3254032840,3254748553,3255468362,3256191595,3256916172,3257640877,3258363758,3259083471,3259798704,3260508465,3261212370,3261910035,3262602100,3263288885,3263971766,3264651543,3265330048,3266008449,3266688546,3267371395,3268058596,3268750757,3269448966,3270152967,3270863208,3271578537,3272298602,3273021515,3273746380,3274470861,3275193966,3275913615,3276629008,3277338769,3278042738,3278740499,3279432532,3280119381,3280802198,3281482039,3282160480,3282838881,3283518946,3284201859,3284889028,3285581285,3286279366,3286983527,3287693608,3288409129,3289128970,3289852107,3290576684,3291301453,3292024270,3292744207,3293459312,3294169329,3294873042,3295570963,3296262804,3296949813,3297632374,3298312343,3298990560,3299669153,3300348994,3301032099,3301719140,3302411589,3303109606,3303813959,3304524008,3305239625,3305959498,3306682571,3307407244,3308131821,3308854830,3309574447,3310289840,3310999505,3311703538,3312401171,3313093300,3313780021,3314462902,3315142615,3315821120,3316499425,3317179554,3317862371,3318549700,3319241861,3319940166,3320644199,3321354504,3322069833,3322789866,3323512747,3324237484,3324961965,3325684878,3326404559,3327119760,3327829617,3328533458,3329231347,3329923316,3330610325,3331293046,3331973047,3332651392,3333329921,3334009890,3334692899,3335379972,3336072325,3336770342,3337474599,3338184584,3338900201,3339619946,3340343115,3341067596,3341792333,3342515086,3343234927,3343950032,3344659985,3345363762,3346061651,3346753620,3347440597,3348123286,3348803223,3349481568,3350160065,3350839970,3351522947,3352209988,3352902309,3353600358,3354304551,3355014696,3355730185,3356450154,3357173163,3357897964,3358622477,3359345614,3360065199,3360780624,3361490289,3362194322,3362891923,3363584084,3364270805,3364953718,3365633431,3366311968,3366990241,3367670402,3368353187,3369040452,3369732581,3370430822,3371134887,3371845128,3372560553,3373280586,3374003595,3374728300,3375452909,3376175822,3376895599,3377610736,3378320657,3379024370,3379722259,3380414100,3381101109,3381783702,3382463703]
TERM_ORDER = ["小寒","大寒","立春","雨水","惊蛰","春分","清明","谷雨","立夏","小满","芒种","夏至",
              "小暑","大暑","立秋","处暑","白露","秋分","寒露","霜降","立冬","小雪","大雪","冬至"]
_TERM_BASE = datetime(1900, 1, 1)


def terms_from_table(dt):
    lo = dt - timedelta(days=420)
    hi = dt + timedelta(days=420)
    out = []
    for code in TERM_CODES_LIST:
        mins = code >> 5
        t = _TERM_BASE + timedelta(minutes=mins)
        if t > hi:
            break
        if t >= lo:
            out.append((TERM_ORDER[code & 31], t))
    return out


_orig_terms = BuiltinEngine.terms_around


def _builtin_terms(self, dt):
    got = terms_from_table(dt)
    if got:
        return got
    return _orig_terms(self, dt)


BuiltinEngine.terms_around = _builtin_terms

# ======================================================================
# 六、渲染（静态版，自建 HTML，无模板依赖）
# ======================================================================

def A(o, name, d=""):
    if isinstance(o, dict):
        return o.get(name, d)
    return getattr(o, name, d)


def _esc(s):
    return (str(s).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;"))


def build_ctx(dt_str=""):
    if not dt_str:
        dt = datetime.now()
    else:
        dt_str = str(dt_str).replace("T", " ").strip()
        for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H:%M", "%Y-%m-%d"):
            try:
                dt = datetime.strptime(dt_str, fmt)
                break
            except ValueError:
                continue
        else:
            dt = datetime.now()

    chart = LiuRenChart(dt)

    _zhan_c, _zhan_k = chart.zhan_chuan, list(reversed(chart.zhan_ke))
    _zhan_ci = next((i for i, z in enumerate(_zhan_c) if z == "内战"), -1)
    _zhan_ki = next((i for i, z in enumerate(_zhan_k) if z == "内战"), -1)
    _yong_ki = next((i for i, f in enumerate(chart.ke_flags) if f["yong"]), -1)
    _jing, _no, _txt = keti_brief(chart.keti_full)
    _bifa_ci, _bifa_ki = (-1, _yong_ki) if _yong_ki >= 0 else (0, -1)
    if _no == 86:
        if _zhan_ci >= 0 or _zhan_ki >= 0:
            _bifa_ci, _bifa_ki = (_zhan_ci, -1) if _zhan_ci >= 0 else (-1, _zhan_ki)
        else:
            _no, _txt = 63, "彼此全伤"

    return dt, dict(
        chart=chart,
        ke=list(reversed(chart.ke_display())),
        keti_bifa=_txt, keti_bifa_no=_no, keti_jing=_jing,
        chuan_zhan=chart.zhan_chuan, ke_zhan=list(reversed(chart.zhan_ke)),
        bifa_ci=_bifa_ci, bifa_ki=_bifa_ki,
        chuan_marks=chart.chuan_ke_marks,
        ke_flags=chart.ke_flags,
    )


def render_body(dt_str=""):
    dt, c = build_ctx(dt_str)
    chart = c["chart"]
    H = []

    # ---- meta ----
    H.append('<div class="meta">')
    H.append('<div class="pillars">')
    for lab, zhu in zip(["年", "月", "日", "时"], chart.si_zhu):
        H.append('<div class="pil"><span class="ph">%s</span><span class="pz">%s</span>'
                 '<span class="pz">%s</span></div>' % (lab, _esc(zhu[0]), _esc(zhu[1])))
    H.append("</div>")
    H.append('<div class="vline"></div>')
    H.append('<div class="mlines">')
    H.append('<div><span class="k">公历</span>　%s</div>' % _esc(dt.strftime("%Y-%m-%d %H:%M:%S").replace(" ", "　")))
    if chart.lunar_text:
        H.append('<div><span class="k">农历</span>　%s</div>' % _esc(chart.lunar_text))
    H.append('<div><span class="k">旬空</span>　%s旬 %s%s空　<span class="g">%s占</span></div>'
             % (_esc(chart.xun_shou), _esc(chart.xun_kong[0]), _esc(chart.xun_kong[1]), _esc(chart.zhou_ye)))
    H.append('<div><span class="k">月将</span>　%s将%s　<span class="g">%s</span></div>'
             % (_esc(chart.yue_jiang), _esc(chart.yue_jiang_name), _esc(chart.zhong_qi_text)))
    H.append("</div></div>")

    # ---- 三传 ----
    H.append('<div class="chuan">')
    for i, cu in enumerate(chart.chuan):
        cls = "cre first" if i == 0 else "cre"
        H.append('<div class="%s">' % cls)
        H.append('<span class="lab">%s</span>' % _esc(A(cu,"label")[0]))
        H.append('<span class="qn">%s</span>' % _esc(A(cu,"qin")))
        H.append('<span class="bz"><i>%s</i>%s</span>' % (_esc(A(cu,"dun")), _esc(A(cu,"zhi"))))
        H.append('<span class="kebz">%s' % _esc(c["chuan_marks"].get(i, "")))
        if c["bifa_ci"] == i:
            H.append('<span class="bfq">%s</span>' % _esc(c["keti_bifa"]))
        H.append("</span>")
        H.append('<span class="jj">%s' % _esc(j1(A(cu,"jiang"))))
        z = c["chuan_zhan"][i]
        if z:
            k = " zs zs1" if z == "内战" else " zs"
            H.append('<i class="%s">%s</i>' % (k.strip(), _esc(z)))
        sha = chart.sha_of(A(cu,"zhi"))
        if sha:
            H.append('<span class="shas">')
            for t in sha.split("·"):
                H.append('<i class="sc">%s</i>' % _esc(t))
            H.append("</span>")
        H.append("</span></div>")
    H.append("</div>")

    # ---- 四课 ----
    H.append('<div class="ke">')
    for i, kk in enumerate(c["ke"]):
        f = c["ke_flags"][i]
        cls = "kec" + (" yong" if f["yong"] else "") + (" haske" if f["ke"] else "")
        H.append('<div class="%s">' % cls)
        H.append('<span class="lab">%s%s</span>' % (_esc(A(kk,"label")[0]),
                 '<i class="yb">用</i>' if f["yong"] else ""))
        H.append('<span class="jj">%s</span>' % _esc(j1(A(kk,"jiang"))))
        H.append('<span class="up">%s</span>' % _esc(A(kk,"shang")))
        H.append('<span class="dn">%s</span>' % _esc(A(kk,"xia")))
        nt = A(kk,"note") or A(kk,"rel") or ""
        H.append('<span class="nt">%s%s</span>' % (_esc(nt), "·发用" if f["yong"] else ""))
        if c["bifa_ki"] == i:
            H.append('<span class="bfq">%s</span>' % _esc(c["keti_bifa"]))
        H.append("</div>")
    H.append("</div>")

    # ---- 天地盘 ----
    H.append('<div class="pan">')
    for g in chart.gong:
        H.append('<div class="pc" style="grid-row:%s;grid-column:%s;">' % (g.row, g.col))
        H.append('<div class="jj">%s</div>' % _esc(j1(g.jiang)))
        H.append('<div class="tz" style="color:%s">%s</div>'
                 % ("#a03535" if g.kong else "var(--ink)", _esc(g.tian)))
        H.append('<div class="dg"><span>%s</span><span class="shas gsh">' % _esc(g.dun))
        if g.sha:
            for t in g.sha.split("·"):
                H.append('<i class="sc">%s</i>' % _esc(t))
        H.append("</span></div></div>")
    H.append('<div class="pc center">')
    H.append('<div class="kt">%s</div>' % _esc(chart.keti_full))
    H.append('<div class="krow"><span class="tag">课经</span><span class="circ">%s</span></div>' % _esc(c["keti_jing"]))
    H.append('<div class="krow"><span class="tag">毕法</span><span class="fno">第%s法</span>'
             '<span class="circ">%s</span></div>' % (c["keti_bifa_no"], _esc(c["keti_bifa"])))
    H.append("</div></div>")

    return "".join(H)


def render_ctx_json(dt_str=""):
    dt, c = build_ctx(dt_str)
    return json.dumps({"dt": dt.strftime("%Y-%m-%dT%H:%M:%S"), "body": render_body(dt_str)}, ensure_ascii=False)
