# BB 有限维临界一致率的 Lean 工程

[阅读 PDF](https://taitai2025.github.io/assets/documents/research/bb-uniform.pdf)

本项目提供 97 个数学模块和统一入口，依赖由项目清单锁定。形式声明以对应原稿的具体版本为准。对照表中的名称指向原工程中的声明，替代证明仍需按原论文假设阅读。AI 辅助整理，作者逐项人工复核待完成。

历史构建覆盖 97 个 BB 子模块和统一入口，共 98 个构建模块，绑定有限维一致率稿和端点 Lyapunov 基线。此前的 Windows 本机构建与 trust=0 公理审查通过。源论文体量大于某一条证明接口的范围。

在 Lean 4.8.0 环境中进入 lean 目录，执行 lake exe cache get 与 lake build。依赖可用后再核对指定 Lean 声明的公理依赖。
