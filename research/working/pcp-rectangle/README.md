# PCP 中常数背景与矩形扰动的精确最优性判据

Exact PCP Optimality Criteria for a Constant Background and Rectangular Perturbation

2026 年 11 月 25 日 · v1.1 · AI 辅助研究工作稿，尚待作者人工复核。

[论文 PDF](../../../assets/documents/research/pcp-rectangle.pdf) · [TeX 源稿](main.tex)

## 复现与证明范围

运行 python exact_checks.py，或安装 requirements.txt 中的依赖后运行 python verify.py。实验只使用独立生成的合成矩阵。三个标量 Lean 引理另附历史核验，矩阵判据使用手证。

## 独立审读后的修订

两次独立审查核对四块条件、矩形边界和严格证书唯一性，并复算 171,216 项有理数比较。终稿明确只保留非零奇异值的紧致分解。主题来源是课程小组项目。

历版由 Git 提交及各稿的 SHA-256 清单标识，引用时可注明对应版本。
