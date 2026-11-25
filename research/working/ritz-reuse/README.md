# 历史 Ritz 扫掠重用的精确指数上界

An Exact Bound for Repeating Historical Ritz Sweeps

2026 年 11 月 25 日 · v0.2.0 · AI 辅助研究工作稿，尚待作者人工复核。

[论文 PDF](../../../assets/documents/research/ritz-reuse.pdf) · [TeX 源稿](main.tex)

## 复现与证明范围

运行 python verify_optimal_polytope.py 和 python optimal_reuse_triangle_certificate.py。两份 JSON 分别保存支持线核验和有理区间核验，正文证明如何扩展到所有更大的重复次数。

## 独立审读后的修订

独立审读复跑了 9 个顶点、18 个三角包含、1,396 个严格正号和 80 个精确零。修复失效引用，补明 Gu 的先行公式及周期取等的例外。

## 相关工作稿

- [固定权重 LMSD 在 p+1 个活跃特征值上的收敛率](../ritz-minimal-face/)

历版由 Git 提交及各稿的 SHA-256 清单标识，引用时可注明对应版本。
