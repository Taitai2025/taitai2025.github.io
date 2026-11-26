# AI 辅助研究工作稿

[个人主页](https://taitai2025.github.io/research/#research-working) · [科研资料总览](../) · [十一月全文整理版](../manuscripts/)

以下版本经 AI 辅助整理，待作者逐项人工核阅。PDF 中列出假设、证明范围与适用条件。目录里若有 Lean 文件，会单独说明已验证的是一般定理、有限子命题还是具体算例。

## 谱梯度与 Ritz

| 稿件 | 结论与适用范围 | 资料 |
| --- | --- | --- |
| LMSD 在最小活跃谱上的精确速率 | 从历史梯度怎样产生下一轮 Ritz 步长入手，推导 p+1 个活跃谱点上的最佳一致因子和非平衡迭代的双指数衰减。 精确速率对应恰有 p+1 个活跃谱点的二次模型。 | [PDF](https://taitai2025.github.io/assets/documents/research/ritz-minimal-face.pdf) · [目录](ritz-minimal-face/) |
| 历史 Ritz 值怎样重用才更快 | 比较固定重复次数与周期重复，写出滚动历史的实际更新递推，并保留周期 1、2、1、3 达到指数上界的条件。 按一次梯度更新计速率，覆盖特定重用序列和规定的初始历史。 | [PDF](https://taitai2025.github.io/assets/documents/research/ritz-reuse.pdf) · [目录](ritz-reuse/) |
| 周期 BB 切换的相位平衡与精确局部速率 | BB1 与 BB2 的混合周期打破共同端点平衡，因而严格改善最坏一致速率。全文含完整证明、有限预算实验与周期系数的 Lean 证书。 精确局部率按梯度更新计。附有限预算实验与三组固定有理证书。 | [PDF](https://taitai2025.github.io/assets/documents/research/periodic-bb.pdf) · [目录](periodic-bb/) |
| 周期 Ritz 步长的光滑非二次实现 | 构造全局强凸的非二次目标，使指定的延迟 Ritz 六周期和每个正缩放都精确重现。给出已访问点上的全阶光滑一致与有限阶实解析版本。 构造由已给定的相容初始历史启动。 | [PDF](https://taitai2025.github.io/assets/documents/research/smooth-ritz.pdf) · [目录](smooth-ritz/) |

## 步长、线搜索与停止

| 稿件 | 结论与适用范围 | 资料 |
| --- | --- | --- |
| 二次模型上的梯度重启与投影 BB1 | 分析固定正定二次模型中的首次触发时刻，并证明闭凸锥上的投影 BB1 在条件数不超过 2 时的 R 线性界。 第一部分使用固定正定二次模型。锥投影结论要求条件数不超过 2。 | [PDF](https://taitai2025.github.io/assets/documents/research/restart-projected-bb.pdf) · [目录](restart-projected-bb/) |
| 单一弱曲率谱值下的梯度重启时间 | 只有一个步进谱值趋于 1 时，最坏的首次重启或归零最多比单模态晚一步。给出额外一步出现的参数区间与精确算例。 有限维正定二次函数。其余谱值固定在远离 0 和 1 的紧区间内。 | [PDF](https://taitai2025.github.io/assets/documents/research/gradient-restart-return.pdf) · [目录](gradient-restart-return/) |
| GLL 线搜索的收敛界与持续回溯 | 给出实际接受迭代的窗口收缩，并构造一维二次例，其中真实搜索收敛但每周期恰好回溯一次。 收缩结论针对实际接受序列。反例使用特定窗口与回溯参数。 | [PDF](https://taitai2025.github.io/assets/documents/research/gll-window.pdf) · [目录](gll-window/) |
| 用线搜索试探值重选步长 | 在试探点已通过 GLL 检验、尚未取得梯度时重选步长。两个精确反例给出相反的首次达标顺序与分项查询费用。 两个固定算例给出相反的首停顺序，并分开计算函数与梯度请求。 | [PDF](https://taitai2025.github.io/assets/documents/research/trial-firsthit.pdf) · [目录](trial-firsthit/) |
| 一次曲率查询如何决定坐标步长 | 在二维二次模型中，一次矩阵向量查询后选择一个坐标和步长。求出最优保证与平衡查询，并推导只沿坐标轴查询时的精确值。 最坏保证针对一次完整查询后的确定性策略。 | [PDF](https://taitai2025.github.io/assets/documents/research/coordinate-query.pdf) · [目录](coordinate-query/) |
| 固定方向的曲率查询预算 | 计算固定方向的最坏总宽度与最大单向宽度。重数已知且剩余谱中两种特征值都存在时，确定 Hessian 的最坏查询数比剩余空间维数少一。 固定方向、确定性策略和完整精确的 Hessian–向量积。 | [PDF](https://taitai2025.github.io/assets/documents/research/curvature-query-budget.pdf) · [目录](curvature-query-budget/) |
| 用两个梯度样本判定弦点可停止 | 从已通过值检验的试探点及当前点的梯度构造终止证书。一个精确算例少提交一步，两条轨道各付四次函数值和四次梯度请求。 结论计精确、分离的函数值与梯度请求。有限精度判定仍需误差控制。 | [PDF](https://taitai2025.github.io/assets/documents/research/certified-chord.pdf) · [目录](certified-chord/) |
| 下一步梯度更小，ABBmin1 为何反而晚停 | 在一个精确算例中，整段首步长度都能降低下一点的梯度范数，但旧割线仍控制 ABBmin1 的窗口。较严容差下，参考法先停止。 停止顺序反转出现在同一个固定算例，费用比较按完整梯度请求计。 | [PDF](https://taitai2025.github.io/assets/documents/research/cold-window.pdf) · [目录](cold-window/) |

## 低秩分解与 ADMM

| 稿件 | 结论与适用范围 | 资料 |
| --- | --- | --- |
| 常数背景上静止矩形目标的 PCP 最优性判据 | 用四块对偶证书计算亮块与暗块的精确参数区间，区分最优性与唯一恢复，并给出相同目标尺寸下的明暗对照。 对偶证书分别刻画最优性与唯一恢复，模型为常数背景与静止矩形。 | [PDF](https://taitai2025.github.io/assets/documents/research/pcp-rectangle.pdf) · [目录](pcp-rectangle/) |
| PCP 的等价计算、最优性核验与重复尺度 | 从实际求解流程出发解释 Gram-SVT、过松弛残差、Huber 约化和重复列的参数换算。附合成检验和匿名结果，不发布课程原始视频。 复现使用合成数据和匿名汇总，公开包未附原始视频。 | [PDF](https://taitai2025.github.io/assets/documents/research/pcp-computation.pdf) · [目录](pcp-computation/) |
| 交替罚参数下的二次 ADMM | 同谱二维二次问题中，固定使用两个端点罚参数各自收敛，交替使用则在一个可精确计算的条件数阈值后出现发散初值。 阈值由二维同谱二次例得到。 | [PDF](https://taitai2025.github.io/assets/documents/research/admm-alternating.pdf) · [目录](admm-alternating/) |

## 最优实验设计

| 稿件 | 结论与适用范围 | 资料 |
| --- | --- | --- |
| 滞后乘法更新与实验设计 | 两种复用旧拟合的更新可以严格改进、无限刷新，却仍停在次优值。以刷新次数限制步长可恢复值收敛，并有代价下界。 反例、修复及成本结论针对有限 c-最优实验设计中的指定更新。 | [PDF](https://taitai2025.github.io/assets/documents/research/delayed-design.pdf) · [目录](delayed-design/) |

## 补充核验

- [Ritz 重用证书](ritz-certificates/)对应有限状态的精确等式与不等式，详见文件中的范围说明。
