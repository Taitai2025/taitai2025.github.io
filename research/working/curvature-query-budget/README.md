# 固定方向的曲率查询预算

[论文 PDF](https://taitai2025.github.io/assets/documents/research/curvature-query-budget.pdf) · [一次查询的两坐标步长问题](../coordinate-query/)

2026 年 11 月 26 日，v0.1。生成式 AI 辅助了来源核对、推导、写作和附带检查。工作稿待作者逐项人工核阅。

给定实对称矩阵的谱带、已有的完整矩阵作用和一组固定方向，论文给出最小的最坏加权总宽度与最大单向加权宽度。已知只有两个谱值且重数固定时，初始回复留下 $m$ 个未知维度和非平凡剩余秩，$m-1$ 次完整查询即可确定矩阵。各方向的区间宽度之和与总曲率的区间宽度须分别计算。正文引用了相应的经典子空间宽度结果。

- [main.tex](main.tex) 是完整证明的源码，用 XeLaTeX 编译两遍，CTeX 默认指定 Windows 字体，可按系统调整 fontset。
- [verify_examples.py](verify_examples.py) 仅依赖 Python 标准库，输出 [有理算例](exact-examples.json)。
- [CurvatureQueryChecks.lean](CurvatureQueryChecks.lean) 和 [CurvatureProjectionBounds.lean](CurvatureProjectionBounds.lean) 用 Lean 4.8.0 核验有理例、比较不等式和维数算术。一般补全、子空间最优性和自适应下界的证明见正文。

```text
xelatex main.tex
xelatex main.tex
python verify_examples.py
lean --trust=0 CurvatureQueryChecks.lean
lean --trust=0 CurvatureProjectionBounds.lean
```
