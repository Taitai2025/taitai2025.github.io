/* Research entries and reviewed public attachments. */
window.RESEARCH_CONTENT = {
  "working": [
    {
      "id": "ritz-minimal-face",
      "version": "0.3.0",
      "zh": "LMSD 在最小活跃谱上的精确速率",
      "en": "Exact rates of LMSD on the smallest active spectra",
      "groupZh": "谱梯度与 Ritz",
      "groupEn": "Spectral gradients and Ritz values",
      "descriptionZh": "从历史梯度怎样产生下一轮 Ritz 步长入手，推导 p+1 个活跃谱点上的最佳一致因子和非平衡迭代的双指数衰减。",
      "descriptionEn": "Derives the optimal uniform factor on p+1 active spectral nodes and the double-exponential decay of unbalanced histories.",
      "related": [
        "ritz-reuse"
      ],
      "pages": 7
    },
    {
      "id": "ritz-reuse",
      "version": "0.3.0",
      "zh": "历史 Ritz 值怎样重用才更快",
      "en": "How often should historical Ritz values be reused?",
      "groupZh": "谱梯度与 Ritz",
      "groupEn": "Spectral gradients and Ritz values",
      "descriptionZh": "比较固定重复次数与周期重复，写出滚动历史的实际更新递推，并保留周期 1、2、1、3 达到指数上界的条件。",
      "descriptionEn": "Compares constant and periodic reuse using the recurrence for actual rolling histories, including the conditions under which the cycle 1, 2, 1, 3 attains the exponent bound.",
      "related": [
        "ritz-minimal-face"
      ],
      "pages": 10
    },
    {
      "id": "restart-projected-bb",
      "version": "0.3.0",
      "zh": "二次模型上的梯度重启与投影 BB1",
      "en": "Gradient restart and projected BB1 on quadratic models",
      "groupZh": "重启、投影与线搜索",
      "groupEn": "Restart, projection, and line search",
      "descriptionZh": "分析固定正定二次模型中的首次触发时刻，并证明闭凸锥上的投影 BB1 在条件数不超过 2 时的 R 线性界。",
      "descriptionEn": "Analyzes the first trigger on fixed positive quadratics and proves an R-linear bound for projected BB1 on closed convex cones when the condition number is at most two.",
      "related": [
        "gll-window"
      ],
      "pages": 10
    },
    {
      "id": "gll-window",
      "version": "0.3.0",
      "zh": "GLL 线搜索的收敛界与持续回溯",
      "en": "Convergence bounds and persistent backtracking for GLL line search",
      "groupZh": "重启、投影与线搜索",
      "groupEn": "Restart, projection, and line search",
      "descriptionZh": "给出实际接受迭代的窗口收缩，并构造一维二次例，其中真实搜索收敛但每周期恰好回溯一次。",
      "descriptionEn": "Derives a window contraction for accepted iterates and gives a scalar quadratic on which the actual line search converges while backtracking once per period.",
      "related": [
        "restart-projected-bb"
      ],
      "pages": 3
    },
    {
      "id": "pcp-rectangle",
      "version": "1.2",
      "zh": "常数背景上静止矩形目标的 PCP 最优性判据",
      "en": "Exact PCP optimality for a stationary rectangle on a constant background",
      "groupZh": "低秩分解",
      "groupEn": "Low-rank decomposition",
      "descriptionZh": "用四块对偶证书计算亮块与暗块的精确参数区间，区分最优性与唯一恢复，并给出相同目标尺寸下的明暗对照。",
      "descriptionEn": "Computes exact parameter intervals for bright and dark rectangles using a four-block certificate and distinguishes optimality from unique recovery.",
      "related": [
        "pcp-computation"
      ],
      "pages": 9
    },
    {
      "id": "pcp-computation",
      "version": "1.0",
      "pages": 15,
      "zh": "PCP 的等价计算、最优性核验与重复尺度",
      "en": "Equivalent computations, optimality checks, and replication in PCP",
      "groupZh": "低秩分解",
      "groupEn": "Low-rank decomposition",
      "descriptionZh": "从实际求解流程出发解释 Gram-SVT、过松弛残差、Huber 约化和重复列的参数换算。附合成检验和匿名结果，不发布课程原始视频。",
      "descriptionEn": "Works through Gram-based thresholding, over-relaxed residuals, a Huber reduction, and replication scaling. Includes synthetic checks and anonymous results without releasing the source video.",
      "related": [
        "pcp-rectangle"
      ]
    },
    {
      "id": "admm-alternating",
      "version": "1.0",
      "pages": 4,
      "zh": "交替罚参数下的二次 ADMM",
      "en": "Quadratic ADMM with alternating penalty parameters",
      "groupZh": "ADMM 与参数选择",
      "groupEn": "ADMM and parameter choice",
      "descriptionZh": "同谱二维二次问题中，固定使用两个端点罚参数各自收敛，交替使用则在一个可精确计算的条件数阈值后出现发散初值。",
      "descriptionEn": "In a two-dimensional family, each fixed endpoint penalty converges, while the alternating sequence has divergent initial states above an explicit condition-number threshold.",
      "related": []
    },
    {
      "id": "periodic-bb",
      "version": "1.0",
      "releaseDate": "2026.11.26",
      "pages": 46,
      "zh": "周期 BB 切换的相位平衡与精确局部速率",
      "en": "Periodic Barzilai–Borwein switching: phase balance and exact local gaps",
      "groupZh": "谱梯度与周期切换",
      "groupEn": "Spectral gradients and periodic switching",
      "descriptionZh": "BB1 与 BB2 的混合周期打破共同端点平衡，因而严格改善最坏一致速率。全文含完整证明、有限预算实验与周期系数的 Lean 证书。",
      "descriptionEn": "Mixed BB1–BB2 patterns break common endpoint balance and strictly improve the worst uniform threshold. Includes the supplementary proofs, finite-budget evidence and Lean certificates for three patterns.",
      "related": [
        "trial-firsthit"
      ]
    },
    {
      "id": "trial-firsthit",
      "version": "1.0",
      "releaseDate": "2026.11.26",
      "pages": 6,
      "zh": "用线搜索试探值重选步长",
      "en": "Choosing a shorter step from a line-search trial value",
      "groupZh": "步长设计与停止条件",
      "groupEn": "Stepsizes and stopping criteria",
      "descriptionZh": "在试探点已通过 GLL 检验、尚未取得梯度时重选步长。两个精确反例给出相反的首次达标顺序与分项查询费用。",
      "descriptionEn": "Reconsiders a step after its value passes the GLL test and before querying its gradient. Two exact examples give opposite first-hit and separately priced query comparisons.",
      "related": [
        "periodic-bb",
        "gll-window"
      ]
    },
    {
      "id": "delayed-design",
      "version": "1.0",
      "releaseDate": "2026.11.26",
      "pages": 60,
      "zh": "滞后乘法更新与实验设计",
      "en": "Certifying delayed multiplicative updates for linear experimental design",
      "groupZh": "最优实验设计",
      "groupEn": "Optimal experimental design",
      "descriptionZh": "两种复用旧拟合的更新可以严格改进、无限刷新，却仍停在次优值。以刷新次数限制步长可恢复值收敛，并有代价下界。",
      "descriptionEn": "Two cached-fit rules can improve strictly and refresh infinitely often while converging to a suboptimal design value. The paper proves a convergent capped rule and analyzes its cost.",
      "related": []
    },
    {
      "id": "smooth-ritz",
      "version": "1.0",
      "releaseDate": "2026.11.26",
      "pages": 5,
      "zh": "周期 Ritz 步长的光滑非二次实现",
      "en": "Smooth nonquadratic objectives with periodically repeating Ritz steps",
      "groupZh": "谱梯度与 Ritz",
      "groupEn": "Spectral gradients and Ritz values",
      "descriptionZh": "构造全局强凸的非二次目标，使指定的延迟 Ritz 六周期和每个正缩放都精确重现。给出已访问点上的全阶光滑一致与有限阶实解析版本。",
      "descriptionEn": "Constructs globally strongly convex nonquadratic objectives that preserve a delayed six-sweep Ritz trajectory at every positive scale. Includes a smooth construction matching all derivatives and an analytic finite-order variant.",
      "related": [
        "ritz-minimal-face",
        "ritz-reuse"
      ]
    },
    {
      "id": "coordinate-query",
      "version": "1.0",
      "releaseDate": "2026.11.26",
      "pages": 5,
      "zh": "一次曲率查询如何决定坐标步长",
      "en": "Choosing a coordinate step with one Hessian-vector query",
      "groupZh": "曲率信息与步长",
      "groupEn": "Curvature information and stepsizes",
      "descriptionZh": "在二维二次模型中，一次矩阵向量查询后选择一个坐标和步长。求出最优保证与平衡查询，并推导只沿坐标轴查询时的精确值。",
      "descriptionEn": "Finds the sharp deterministic decrease guarantee for choosing one coordinate and step after one Hessian-vector query. It also gives the exact value when the query is restricted to a coordinate axis.",
      "related": [
        "trial-firsthit"
      ]
    },
    {
      "id": "certified-chord",
      "version": "1.0",
      "releaseDate": "2026.11.26",
      "pages": 5,
      "zh": "用两个梯度样本判定弦点可停止",
      "en": "A certified stopping point from two gradient samples",
      "groupZh": "步长设计与停止条件",
      "groupEn": "Stepsizes and stopping criteria",
      "descriptionZh": "从已通过值检验的试探点及当前点的梯度构造终止证书。一个精确算例少提交一步，两条轨道各付四次函数值和四次梯度请求。",
      "descriptionEn": "Certifies a terminal interior point using the endpoint gradients of a value-accepted segment. In an exact example one commit is saved while both runs make four requests of each type.",
      "related": [
        "trial-firsthit",
        "gll-window"
      ]
    },
    {
      "id": "cold-window",
      "version": "1.0",
      "releaseDate": "2026.11.26",
      "pages": 5,
      "zh": "较好的首步为何可能延迟停止",
      "en": "A better first step can delay stopping in a spectral gradient method",
      "groupZh": "步长设计与停止条件",
      "groupEn": "Stepsizes and stopping criteria",
      "descriptionZh": "在一个精确算例中，整段首步长度都能降低下一点的梯度范数，但旧割线仍控制 ABBmin1 的窗口。较严容差下，参考法先停止。",
      "descriptionEn": "For a fixed example an interval of replacement steps improves the next gradient norm. The retained secant controls the ABBmin1 window, and the reference reaches a stricter tolerance first.",
      "related": [
        "trial-firsthit",
        "certified-chord"
      ]
    }
  ],
  "papers": [
    {
      "id": "2608.07839",
      "title": "The Sharp Worst-Case Asymptotic Rate of the Barzilai–Borwein Method in ℝ^d and Hilbert Spaces",
      "authors": "Shutai Yang, Ya-Xiang Yuan",
      "date": "2026-08",
      "venue": "arXiv preprint",
      "venueZh": "arXiv 预印本",
      "zh": "研究 BB1 与 BB2 在有限维及 Hilbert 空间上一致正定二次问题的最紧渐近速率，并建立非线性问题驻点附近的局部速率结论。",
      "en": "Sharp asymptotic rates for both BB rules on positive quadratics in finite dimensions and Hilbert spaces, together with local nonlinear rate results.",
      "file": "assets/documents/arxiv-2608.07839v1.pdf",
      "fileLabelZh": "arXiv v1 PDF",
      "fileLabelEn": "arXiv v1 PDF",
      "manuscript": "assets/documents/research/bb-sharp-rate-author-manuscript.pdf",
      "manuscriptPages": 55
    },
    {
      "id": "2609.12084",
      "title": "Lyapunov Functions and R-Linear Convergence for Quadratic Barzilai-Borwein Dynamics",
      "authors": "Shutai Yang, Ya-xiang Yuan",
      "date": "2026-09",
      "venue": "Preprint",
      "venueZh": "预印本",
      "zh": "为二次 BB 动力系统构造显式的当前点 Lyapunov 函数，给出端点单项式中的极小极大指数，并由此讨论 R-线性收敛。",
      "en": "An explicit current-point Lyapunov function for quadratic BB dynamics, with minimax endpoint exponents and an R-linear convergence argument.",
      "file": "assets/documents/arxiv-2609.12084v1.pdf",
      "fileLabelZh": "arXiv v1 PDF",
      "fileLabelEn": "arXiv v1 PDF"
    },
    {
      "id": "2609.12100",
      "title": "R-Linear Convergence of Barzilai-Borwein Methods on Strictly Convex Quadratics via Closed-Cone Homogeneous Dynamics",
      "authors": "Shutai Yang, Ya-xiang Yuan",
      "date": "2026-09",
      "venue": "arXiv preprint",
      "venueZh": "arXiv 预印本",
      "zh": "在连续梯度对构成的相容闭锥上刻画齐次动力系统，通过紧性将逐点稳定性转化为统一有限步收缩，证明 BB1、BB2 及固定正谱权重变体的 R-线性收敛。",
      "en": "A closed-cone homogeneous dynamical formulation that turns pointwise stability into uniform finite-step contraction for BB methods and positive spectral-weight variants.",
      "file": "assets/documents/arxiv-2609.12100v1.pdf",
      "fileLabelZh": "arXiv v1 PDF",
      "fileLabelEn": "arXiv v1 PDF",
      "manuscript": "assets/documents/research/bb-closed-cone-author-manuscript.pdf",
      "manuscriptPages": 11
    },
    {
      "id": "2609.12114",
      "title": "Global and Unconditional R-Linear Convergence of Rank-Compressed Weighted LMSD Sweeps for Strictly Convex Quadratics",
      "authors": "Shutai Yang, Ya-xiang Yuan",
      "date": "2026-09",
      "venue": "arXiv preprint",
      "venueZh": "arXiv 预印本",
      "zh": "以精确秩压缩处理 LMSD 梯度历史，通过完整 sweep 的行列式与 Cauchy–Binet 表示处理秩退化，在严格凸二次模型上建立全局、无条件的 R-线性收敛。",
      "en": "Global and unconditional R-linear convergence of rank-compressed weighted LMSD sweeps on strictly convex quadratics, using determinant and Cauchy–Binet representations.",
      "file": "assets/documents/arxiv-2609.12114v1.pdf",
      "fileLabelZh": "arXiv v1 PDF",
      "fileLabelEn": "arXiv v1 PDF",
      "manuscript": "assets/documents/research/weighted-lmsd-author-manuscript.pdf",
      "manuscriptPages": 28
    }
  ],
  "articles": [
    {
      "title": "基于行列式乘子表示的 LMSD 收敛证明及加权 Ritz 推广",
      "meta": "杨书泰 ·《蛙鸣》第 68 期 · 2026.07 · pp. 33–50",
      "zh": "以完整 Ritz-sweep 的行列式乘子表示和 Cauchy–Binet 展开为工具，讨论 LMSD、harmonic-LMSD 及加权 Ritz 方法的全局收敛。",
      "en": "A Chinese article on global convergence of LMSD, harmonic-LMSD and weighted Ritz methods via determinant multipliers and Cauchy–Binet expansions.",
      "file": "assets/documents/warming-68-yang-shutai.pdf"
    },
    {
      "title": "对《三体》中数学问题的一点探究（初二）",
      "meta": "杨书泰 ·《数理天地：初中版》· 2018 年第 5 期 · p. 47",
      "zh": "初二时期围绕《三体》中数学问题写下的早期探索文章。",
      "en": "An early mathematical exploration inspired by The Three-Body Problem, written in the second year of junior secondary school.",
      "url": "https://www.zhangqiaokeyan.com/academic-journal-cn_mathematical-world-junior-high-school-edition_thesis/0201269840423.html"
    }
  ],
  "talks": [
    {
      "title": "谱梯度法的离散动力系统分析：收敛性、最坏收敛因子与 Lyapunov 函数",
      "meta": "2026.10 · 实用最优化算法 · 课程读书报告 · 37 页",
      "zh": "从谱梯度法的离散动力系统表述出发，梳理收敛性、最坏收敛因子与 Lyapunov 函数。此项为课程学习报告，与研究论文分列。",
      "en": "A course reading report on spectral gradient dynamics, convergence, worst-case convergence factors and Lyapunov functions, listed separately from research papers.",
      "file": "assets/documents/research/spectral-gradient-reading-report.pdf"
    },
    {
      "title": "谱梯度法的离散动力系统分析：课程汇报",
      "meta": "2026.10 · 实用最优化算法 · 课程展示 · 42 页（含附录）",
      "zh": "课程汇报幻灯片，包含 27 页主体与 15 页附录，配合读书报告介绍谱梯度动力学和相关理论。",
      "en": "Course presentation accompanying the reading report, with 27 main slides and 15 appendix slides on spectral gradient dynamics and related theory.",
      "file": "assets/documents/research/spectral-gradient-course-slides.pdf"
    },
    {
      "title": "数学与系统科学研究院开学典礼新生代表发言",
      "meta": "2026.09.29 · 新生代表 · 发言稿",
      "zh": "关于数学研究、科研中的坚持，以及面对人工智能发展的思考。",
      "en": "Remarks on mathematical research, persistence and the changing role of AI, delivered as a new-student representative.",
      "file": "assets/documents/amss-2026-opening-speech.pdf",
      "url": "https://amss.cas.cn/ttxw/202609/t20260930_8288764.html"
    },
    {
      "title": "块映射视角下固定记忆谱梯度法的统一收敛理论及应用",
      "meta": "2026.05 · 中国科学技术大学 · 本科毕业论文 · 119 页",
      "zh": "本科毕业论文全文，围绕闭锥上的齐次块映射、固定记忆谱梯度方法与收敛性展开，包含理论分析、数值实验与实现附录。保留毕业阶段的原始研究表述，后续进展见预印本。",
      "en": "The full undergraduate thesis on homogeneous block maps on closed cones, fixed-memory spectral gradient methods and convergence, including numerical experiments and implementation appendices. This historical thesis text is retained; later developments appear in the preprints.",
      "file": "assets/documents/undergraduate-thesis.pdf"
    },
    {
      "title": "块映射视角下固定记忆谱梯度法的统一收敛理论及应用",
      "meta": "2026.05 · 中国科学技术大学 · 毕业设计答辩 · 40 页",
      "zh": "毕业设计答辩幻灯片：闭锥齐次块映射、固定记忆谱梯度法及 BB 紧渐近速率。",
      "en": "Undergraduate thesis defense slides on homogeneous block dynamics, fixed-memory spectral gradient methods and sharp BB asymptotic rates.",
      "file": "assets/documents/undergraduate-thesis-slides.pdf"
    },
    {
      "title": "加权 Ritz-sweep 谱梯度法的齐次块动力系统理论与收敛性分析",
      "meta": "2026.05 · 国家级大创项目 · 答辩报告 · 40 页",
      "zh": "大创项目答辩幻灯片，涵盖加权 Ritz-sweep 方法的统一框架、收敛分析与数值实验。",
      "en": "Innovation project presentation on weighted Ritz-sweep methods, convergence analysis and numerical experiments.",
      "file": "assets/documents/innovation-project-slides.pdf"
    },
    {
      "title": "加权 Ritz-sweep 谱梯度法的齐次块动力系统理论与收敛性分析",
      "meta": "2026.05.14 · 大学生创新训练计划 · 研究报告 · 119 页",
      "zh": "项目研究报告，系统整理闭锥连续正齐次块映射理论、谱梯度方法及其收敛性分析。 原立项题目为《强Lyapunov框架下优化算法的全局收敛性研究与应用》，这里沿用后续研究题目；另附国家级项目立项通知节选。",
      "en": "A research report on continuous positively homogeneous block maps on closed cones and their application to spectral gradient convergence. The original approved project concerned global convergence and applications of optimization algorithms under a strong Lyapunov framework; this report uses the subsequent research title. An excerpt from the national project approval notice is also available.",
      "file": "assets/documents/weighted-ritz-sweep-research-report.pdf",
      "projectNotice": "assets/documents/research/ustc-national-innovation-project-approval-2025.pdf"
    },
    {
      "title": "最优化算法课程汇报：BB 方法的 R 线性收敛",
      "meta": "2026.05 · 中国科学技术大学本科课程 · 最优化算法 · 39 页",
      "zh": "本科课程汇报，围绕 Dai–Liao（2002）的 BB 方法收敛性论文，梳理理论证明、数值复现与个人理解。保留当时汇报版本；后续研究进展见预印本。",
      "en": "Undergraduate course presentation on Dai–Liao (2002), covering the convergence analysis of the BB method, numerical replication and personal observations. This historical presentation is preserved; see the preprints for subsequent research.",
      "file": "assets/documents/research/optimization-algorithms-course-presentation.pdf"
    }
  ],
  "manuscripts": [
    {
      "id": "bb-asymptotic",
      "zh": "BB 方法的最紧渐近速率",
      "en": "Sharp worst-case asymptotic rates for Barzilai–Borwein methods",
      "groupZh": "BB 谱步长",
      "groupEn": "Barzilai–Borwein steps",
      "pages": 38,
      "descriptionZh": "11 月修订稿。证明有限维与 Hilbert 空间二次问题的尖锐根因子，区分初始梯度的活动谱端点、连续谱与精确达到的轨道，并给出局部非线性结论。",
      "descriptionEn": "November revision. Establishes sharp root factors for quadratic problems in finite dimensions and Hilbert spaces, with separate treatments of active spectral endpoints, continuous spectra, attainment, and the local nonlinear problem.",
      "arxiv": "https://arxiv.org/abs/2608.07839",
      "formal": "bb-asymptotic"
    },
    {
      "id": "bb-uniform",
      "zh": "BB 方法的有限维临界一致率",
      "en": "A sharp uniform rate for Barzilai–Borwein methods",
      "groupZh": "BB 谱步长",
      "groupEn": "Barzilai–Borwein steps",
      "pages": 13,
      "descriptionZh": "在有限谱上构造共同 Lyapunov 函数，使 BB2 到 BB1 的任意区间选择共享临界因子。非线性部分给出 Dini 条件和一个 C² 反例。",
      "descriptionEn": "Constructs a common Lyapunov function at the critical factor for finite spectra and arbitrary choices between the BB2 and BB1 steps. The nonlinear section gives a Dini condition and a twice continuously differentiable example.",
      "formal": "bb-uniform",
      "guide": "bb-uniform-guide.pdf",
      "guideZh": "中文证明导读",
      "guideEn": "Proof guide in Chinese"
    },
    {
      "id": "lmsd-spectral",
      "zh": "固定权 LMSD 的谱界与再生",
      "en": "Sharp spectral bounds and regeneration in limited-memory steepest descent",
      "groupZh": "LMSD 与 Ritz 重用",
      "groupEn": "LMSD and Ritz reuse",
      "pages": 115,
      "descriptionZh": "论文 A。研究固定权 LMSD 的可实现历史、最小活跃谱的精确速率和相位，并分析实际六周期与双簇谱下界。正文与全部证明附录同载。",
      "descriptionEn": "Paper A concerns fixed-weight LMSD: compatible histories, exact rates and phases on the smallest active spectra, a realizable six-cycle, and a two-cluster lower bound. Includes the main text and all proof appendices."
    },
    {
      "id": "lmsd-reuse",
      "zh": "历史谱梯度法的共同 Lyapunov 界与最优 Ritz 重用",
      "en": "Common Lyapunov bounds and optimal Ritz reuse in spectral gradient methods",
      "groupZh": "LMSD 与 Ritz 重用",
      "groupEn": "LMSD and Ritz reuse",
      "pages": 37,
      "descriptionZh": "论文 B。研究受控变权、历史 Ritz 值重用和允许改变的排序，给出共同收敛界、达到构造和特定重用模式的最优性条件。",
      "descriptionEn": "Paper B treats controlled changes of weights, reuse of historical Ritz values, and varying orderings. It proves common rate bounds, gives attaining constructions, and analyzes optimal reuse under explicitly stated conditions."
    }
  ]
};
