# 来源、方法归属与检索边界

核对日期：2026-11-25。

1. Venkat Chandrasekaran, Sujay Sanghavi, Pablo A. Parrilo, Alan S. Willsky, *Rank-Sparsity Incoherence for Matrix Decomposition*, SIAM J. Optim. 21(2), 572–596, 2011. DOI https://doi.org/10.1137/090761793 。作者全文：https://willsky.lids.mit.edu/publ_pdfs/206_pub_SIAMonline.pdf 。实际核对第 4.1 节（印刷页 580，PDF 第 9 页）的公共次梯度必要充分条件、Proposition 2 的严格证书与切空间交条件，以及附录 B 对命题的论证。本文的基本证明框架已有明确先行归属。
2. Emmanuel J. Candès, Xiaodong Li, Yi Ma, John Wright, *Robust Principal Component Analysis?*, JACM 58(3), Article 11, 2011. DOI https://doi.org/10.1145/1970392.1970395 。预印本：https://arxiv.org/abs/0912.3599v1 。核对第 2.3 节和 Lemma 2.4；该文明确指出该唯一性判据等价于 Chandrasekaran 等的 Proposition 2。不得将这一框架归为本稿原创。
3. 问题和原有亮暗区间来自未发表课程报告，后经私人短文整理。公开稿重写方法定位并给出完整证明；私人来源仅保留 SHA-256，不附原视频、课程同组信息、私人目录或未授权第三方 PDF。

本次检索使用了作者全文、原始预印本和出版社题录，并以 principal component pursuit / constant background / rectangular block / exact regularization / dual certificate 等组合查找近邻工作。这不是穷尽检索，不能建立专门闭式公式首次出现的结论。块内平均、核范数次微分、切空间可辨识性、严格证书均应被理解为已有凸分析方法。本文只陈述此明确结构上的计算结果与完整推导，不作新算法或首创声明。

真实视频恢复、随机支撑恢复概率、稳定 PCP、块稀疏惩罚模型与在线子空间跟踪不属于本文定理。本文使用逐元素 l1 惩罚，不可与不同的组稀疏模型混同。

归属补充：本主题由课程小组项目引出；本匿名版本所用矩阵均为独立重新生成的合成样例。原组员身份只在私人归档保存，不声称原项目全部属于个人贡献。公开包使用归档整理阶段独立实现的小矩阵 ADMM，不包含原组实验代码、真实视频或原始私人记录。
