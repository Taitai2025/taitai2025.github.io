# 有限记忆谱梯度法的完整扫掠、秩退化与统一指数收敛

[中文证明阅读稿](https://taitai2025.github.io/assets/documents/research/lmsd-sweep-proof-note.pdf) · [原始预印本](https://arxiv.org/abs/2609.12114)

这份阅读稿以公开合著预印本为依据，分别展开行列式恒等式、逐谱收敛、退化状态、统一指数界及实际步数换算。源稿可用 XeLaTeX 编译，完整论文推导及形式化范围见正文。

| 文件 | 可复现的内容 |
| --- | --- |
| lmsd-sweep-proof-note.tex | 中文证明阅读稿 |
| CompactConeRate.lean | 从有限维闭锥的连续、正齐次和逐点收敛推出统一指数界 |
| RankBoundary.lean | 低秩证明所用的十四条有限集合、有限乘积换元及支撑引理 |
| verify_rank_loss_example.py | 以有理数核对三个行列式比、合法预热和扫掠后的端点 |

运行 **python verify_rank_loss_example.py** 得到三行精确表。Lean 环境使用 **4.8.0**，mathlib 固定提交由 lakefile.lean 记录。下载依赖后执行 **lake exe cache get** 和 **lake build**，两个 Lean 文件的公理查询仅使用标准公理。本目录的算法收敛证明仍由正文的手证提供。

阅读稿与校验使用了 AI 辅助，尚待作者逐项核阅。引用原论文结论时请引用公开合著预印本。
