# 单一弱曲率谱值下的梯度重启时间

[论文 PDF](https://taitai2025.github.io/assets/documents/research/gradient-restart-return.pdf) · [此前的有限返回工作稿](../restart-projected-bb/)

2026 年 11 月 26 日，v0.1。生成式 AI 辅助了来源核对、推导、写作和附带检查。工作稿待作者逐项人工核阅。

考虑有限维正定二次函数上的离散梯度重启。当步进矩阵只有一个不同谱值趋于 1，其余谱值留在固定紧区间时，最坏的首次重启或精确终止次数，与纯弱曲率模态首次过零的试探编号至多相差一。论文给出额外一步允许的参数区间以及两个精确二谱例子。次数按试探计，触发后的重算单独计入梯度成本。

- [main.tex](main.tex) 是论文源码，用 XeLaTeX 编译两遍。
- [verify_exact.py](verify_exact.py) 使用 Python 标准库复算有理残差、严格触发和精确零点算例。
- [RestartFirstEvent.lean](RestartFirstEvent.lean) 用 Lean 4.8.0 核验两条有理递推恒等式与九条具体命题。一般谱界和 Bessel 极限由正文数学证明给出。

```text
xelatex main.tex
xelatex main.tex
python verify_exact.py
lean --trust=0 RestartFirstEvent.lean
```
