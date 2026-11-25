# BB 尖锐渐近率的 Lean 工程

[阅读 PDF](https://taitai2025.github.io/assets/documents/research/bb-asymptotic.pdf)

本项目提供 139 个数学模块和统一入口，依赖由项目清单锁定。形式声明以对应原稿的具体版本为准。对照表中的名称指向原工程中的声明，替代证明仍需按原论文假设阅读。AI 辅助整理，作者逐项人工复核待完成。

原稿绑定到 38 页 COAP 修订稿。原包的 140 个源码哈希与历史构建记录一致。覆盖清单包括 35 个编号结果及 1 个数学备注，另列原文实例和基础接口。历史公理日志含 1,940 项声明。一般一致率下确界与临界因子可取的区别，见论文各定理。

在 Lean 4.8.0 环境中进入 lean 目录，执行 lake exe cache get 与 lake build。依赖可用后再核对指定 Lean 声明的公理依赖。

## 2026 年 11 月 25 日重建

2026 年 11 月 25 日在 Windows 和 Lean 4.8.0 下重新构建 139 个模块及统一入口，逐一匹配 1,940 个定理的名称，并确认覆盖表引用的全部声明存在。使用 Lean 自带的公理依赖遍历，取 1,940 个定理的传递依赖并集，仅得到 propext、Classical.choice 和 Quot.sound。 依赖准备与构建完成后，在 lean 目录下运行 lake env lean --trust=0 PublicAudit.lean 可复核本次公理依赖并集。

[本次验证数据](verification-2026-11-25.json) · [审计程序](lean/PublicAudit.lean)
