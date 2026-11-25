# GLL 线搜索的窗口收缩与全步接受

Window Contraction and Full-Step Acceptance for GLL Line Search

2026 年 11 月 25 日 · v0.2.0 · AI 辅助研究工作稿，尚待作者人工复核。

[论文 PDF](../../../assets/documents/research/gll-window.pdf) · [TeX 源稿](main.tex)

## 复现与证明范围

运行 python verify.py，以精确分数复算 M=0 到 11 的周期拒绝和实际接受的窗口不等式。正文给出一般手证。

## 独立审读后的修订

独立核对接受步长下界、凸组合、固定窗索引和原毕业论文算法 4 的记号，展开了两条一步不等式与换窗过程。

## 相关工作稿

- [离散梯度重启的有限返回与投影 BB1 的临界收敛](../restart-projected-bb/)

历版由 Git 提交及各稿的 SHA-256 清单标识，引用时可注明对应版本。
