# 谱梯度法的端点动力学与有限记忆收敛

[个人主页研究页](https://taitai2025.github.io/research/) · [中文导读 PDF](https://taitai2025.github.io/assets/documents/research/spectral-reading-note.pdf)

本文配合四篇已公开的 Yang–Yuan 预印本阅读。内容包括 BB 的平衡端点轨道和单项式极小极大权重、有限维闭锥的统一收缩，以及秩压缩 Ritz 扫掠的整轮多项式。出处、初始化和收敛率的量词在正文中列明。

| 文件 | 用途 |
| --- | --- |
| [spectral-reading-note.tex](spectral-reading-note.tex) | 可编辑源，用 XeLaTeX 编译。 |
| [verify_spectral_examples.py](verify_spectral_examples.py) | 只用 Python 标准库，运行有理数 BB1、BB2 与 LMSD 算例。 |
| [SpectralChecks.lean](SpectralChecks.lean) | 中点乘子、平衡 Rayleigh 商与三坐标二维压缩的三个机器引理。 |

在 Python 3 中直接运行校验脚本。在配有 Lean 4.8.0 与 mathlib b5eba595428809e96f3ed113bc7ba776c5f801ac 的 Lake 工程中，可通过 lake env lean 命令运行 Lean 文件，末尾含三个公理查询。机器验证的范围是文件中的三个引理。

导读及代码整理使用 AI 辅助，逐项人工核阅待完成。研究结论的作者和引用以原预印本为准。
