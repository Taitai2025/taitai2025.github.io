#!/usr/bin/env python3
"""Derive instrument labels from the published score filenames.

This is an index of observed instruments, not a score transcription. Composite
percussion assignments, doublings, optional parts and uncertain labels stay
visible so the comparison does not silently count them as complete coverage.
"""
from pathlib import Path
import json
import re

HERE = Path(__file__).resolve().parent
ALIASES = {
    "高笙": "高音笙", "中笙": "中音笙", "低笙": "低音笙",
    "高唢": "高音唢呐", "中唢": "中音唢呐", "次中音唢": "次中音唢呐",
    "低唢": "低音唢呐", "低革胡": "低音革胡",
    "筝": "古筝", "贝司": "贝斯", "中音排笙": "中音排笙",
    "吊钹": "吊镲",

    "高音木琴": "高音木琴", "F圆号": "圆号", "B♭小号": "小号",
    "B♭单簧管": "单簧管", "小打击": "小打击", "鼓": "鼓",
    "中胡独奏": "中胡", "扬琴II": "扬琴", "打击": "打击乐",
}
TRAD = str.maketrans("嗩箏鐵鈸鑼擊揚鈴鬍", "唢筝铁钹锣击扬铃胡")
AMBIGUOUS = {"Tim", "打击乐", "鼓", "小打击", "管", "琴", "合奏", "人声"}
FAMILIES = {
    "民族管乐": "笛 箫 埙 排箫 哨笛 小笛 高笛 中笛 梆笛 曲笛 大笛 新笛 长膜笛 短膜笛 笙 高音笙 中音笙 低音笙 高音键笙 中音排笙 低音抱笙 唢呐 高音唢呐 中音唢呐 次中音唢呐 低音唢呐 巴乌 管子 葫芦丝",
    "弹拨与键盘": "扬琴 柳琴 琵琶 三弦 中阮 大阮 古筝 箜篌 竖琴 钢琴",
    "弦乐与低音": "高胡 二胡 中胡 革胡 低音革胡 小提琴 中提琴 大提琴 低音提琴 贝斯",
    "西洋管乐": "短笛 长笛 双簧管 单簧管 大管 低音管 中音萨克斯 小号 圆号 长号 大号",
    "打击乐": "打击乐 鼓 定音鼓 小堂鼓 大堂鼓 大鼓 中国大鼓 大军鼓 小军鼓 低音鼓 排鼓 手鼓 手鼓与小军鼓 小打击 小锣 大锣 中锣 芒锣 低锣 风锣 云锣 京锣 小铮锣 小汤锣 碰铃 铃鼓 小铃鼓 大镲 吊镲 小镲 小钹 大钹 中国钹 铙钹 钹 吊镲 小钹 颤音琴 木琴 高音木琴 铁琴 钢片琴 铝板琴 钟琴 管钟 编钟 三角铁 响板 梆子 竹板 南梆子 木鱼 沙槌 卡巴萨 音树 马铃 铃 铃圈 串钟 风铃 弹弓盒 弹响器 碎子 奶锣 大铙 唢呐",
    "声乐与其他": "声乐",
}
CATEGORY = {name: family for family, names in FAMILIES.items() for name in names.split()}
CATEGORY["唢呐"] = "民族管乐"
SCOPE_NOTES = {
    "la-la-land": "当前索引覆盖简谱中的有音高声部，不能据此排除原总谱中的其他声部。",
    "siji-zuqu": "本组曲按乐章有兼奏与编制变化，逐项显示全曲文件索引中出现的乐器。",
    "taiyang-song": "本作品按乐章有打击乐分工变化，逐项显示全曲文件索引中出现的乐器。",
    "wusheng-zuqu": "五个乐章编制有变化，索引并集不能还原逐乐章所需人数。",
}


def window_json(path):
    text = path.read_text(encoding="utf-8")
    return json.loads(text.split(" = ", 1)[1].strip().removesuffix(";"))


def observed_label(filename):
    stem = filename.removesuffix(".pdf").split("｜")[-1]
    stem = re.sub(r"^(?:\d+_)+", "", stem)
    stem = re.split(r"_(?:固定调|首调)", stem, maxsplit=1)[0]
    return re.sub(r"_整曲$", "", stem).strip()


def normalize(text):
    text = text.translate(TRAD).strip()
    text = re.sub(r"\s+(?:Diyin-Sheng|Daruan|Yangqin|Harp)$", "", text)
    text = re.sub(r"(?:\s*(?:[ⅠⅡⅢⅣⅤⅥⅦⅧ]|[IVX]+|[12]))$", "", text)
    text = re.sub(r"[（(][^）)]*[）)]", "", text)
    text = text.strip()
    return ALIASES.get(text, text)


def parse(label):
    if label.startswith(("主旋律备用", "缺", "钢琴缺员接管")):
        return {"label": label, "kind": "reserve", "instruments": []}
    kind = "optional" if "可选" in label else "observed"
    text = re.sub(r"^打击乐\s+[IVX]+\s*·\s*", "", label.strip())
    trailing_variant = re.search(r"([（(])兼([^）)]+)[）)]$", text)
    if trailing_variant:
        text = text[:trailing_variant.start()] + "兼" + trailing_variant.group(2)
    breaks = r"[、／/・·]|(?<!低音)与|兼"
    names = list(dict.fromkeys(normalize(x) for x in re.split(breaks, text) if x.strip()))
    instruments = [name for name in names if name in CATEGORY and name not in AMBIGUOUS]
    unresolved = [name for name in names if name not in instruments]
    return {"label": label, "kind": kind, "instruments": instruments, "unresolved": unresolved}


def build(catalog, filenames):
    works = []
    for entry in catalog:
        slug = entry["slug"]
        lines = [parse(label) for label in dict.fromkeys(
            observed_label(row["filename"]) for row in filenames.get(slug, [])
        )]
        works.append({
            "slug": slug,
            "title": entry["title"],
            "lines": lines,
            "note": SCOPE_NOTES.get(slug, ""),
        })
    return {"families": {family: list(dict.fromkeys(names.split())) for family, names in FAMILIES.items()}, "works": works}


if __name__ == "__main__":
    data = build(window_json(HERE.parent / "catalog.js"), window_json(HERE.parent / "parts-index.js"))
    assert data["works"] and all(item["lines"] for item in data["works"])
    (HERE / "rosters.json").write_text(
        json.dumps(data, ensure_ascii=False, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
