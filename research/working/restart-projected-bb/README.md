# 离散梯度重启的有限返回与投影 BB1 的临界收敛

Finite Returns for Discrete Gradient Restart and Critical Convergence of Projected BB1

2026 年 11 月 25 日 · v0.2.0 · AI 辅助研究工作稿，尚待作者人工复核。

[论文 PDF](../../../assets/documents/research/restart-projected-bb.pdf) · [TeX 源稿](restart-projected-bb.tex)

## 复现与证明范围

运行 python verify_examples.py。Lean 文件的十项断言和公理输出来自固定 Mathlib 下的此前成功运行，本次复核哈希。COVERAGE.md 列出手证和机器核验范围。

## 独立审读后的修订

独立核查 Darboux 相位、紧性、临界谱等号与两个例子，修正了形式证书与提前终止的区分及状态映射平方的排版。

## 相关工作稿

- [GLL 线搜索的窗口收缩与全步接受](../gll-window/)

历版由 Git 提交及各稿的 SHA-256 清单标识，引用时可注明对应版本。
