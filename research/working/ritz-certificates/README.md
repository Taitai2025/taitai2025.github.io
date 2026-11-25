# 历史 Ritz 两篇工作稿的 Lean 证书

这份证书对应[最小活跃谱上的速率](../ritz-minimal-face/)和[历史 Ritz 值的重用](../ritz-reuse/)中的部分推导。Lean 4.8.0 已核查 39 条定理，采用 trust=0，不依赖 mathlib。全文的实数收敛论证仍待形式化。

- 最小活跃谱证书覆盖节点 1、2、4 的插值权、平衡能量比和收缩因子 1/5，以及通分后有理二次多项式的极小极大下界和等号条件。
- 重用证书覆盖 1、2、1、3 周期的矩阵乘积、行列式与特征多项式，以及支撑比较中使用的若干有理区间和整数幂不等式。

用 Lean 4.8.0 运行 lean --trust=0 RitzFinite.lean 可重复核查。

[Lean 源码](RitzFinite.lean) · [声明清单及验证记录](verification.json)
