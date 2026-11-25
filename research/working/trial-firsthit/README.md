# 用线搜索试探值重选步长

[阅读论文 PDF](https://taitai2025.github.io/assets/documents/research/trial-firsthit.pdf)

固定 ABBmin1 基线、十点 GLL 窗口与相对梯度精度。已经通过线搜索的试探值参与射线插值，
在取得梯度前选择更短步长。两条精确一维轨迹得到相反的首次达标顺序，
进一步给出分别计价模型的完整查询费用比较。

Lean 4.8.0 已核查两个两步截面、通分后的窗口常数消元，以及分项查询计数的整数不等式，共 17 项。
有限族的全局光滑性、滚动窗口的实数收敛证明及一般射线信息命题保留在论文中。运行
lean --trust=0 TrialValue.lean 可复查证书。使用 XeLaTeX 两次编译 main.tex 生成论文。

AI 辅助整理并经独立数学校核，待作者逐项人工复核。

[周期 BB 切换](../periodic-bb/) · [GLL 窗口工作稿](../gll-window/)
