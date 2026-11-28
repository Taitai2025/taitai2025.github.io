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
      "related": [
        "gll-window",
        "gradient-restart-return"
      ],
      "pages": 10
    },
    {
      "id": "gradient-restart-return",
      "version": "0.1",
      "releaseDate": "2026.11.26",
      "zh": "单一弱曲率谱值下的梯度重启时间",
      "en": "Gradient restart near a single weak-curvature eigenvalue",
      "groupZh": "重启、投影与线搜索",
      "groupEn": "Restart, projection, and line search",
      "related": [
        "restart-projected-bb"
      ],
      "pages": 7
    },
    {
      "id": "gll-window",
      "version": "0.3.0",
      "zh": "GLL 线搜索的收敛界与持续回溯",
      "en": "Convergence bounds and persistent backtracking for GLL line search",
      "groupZh": "重启、投影与线搜索",
      "groupEn": "Restart, projection, and line search",
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
      "related": []
    },
    {
      "id": "periodic-bb",
      "version": "1.1",
      "releaseDate": "2026.11.26",
      "pages": 46,
      "zh": "周期 BB 切换的相位平衡与精确局部速率",
      "en": "Periodic Barzilai–Borwein switching: phase balance and exact local gaps",
      "groupZh": "谱梯度与周期切换",
      "groupEn": "Spectral gradients and periodic switching",
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
      "related": []
    },
    {
      "id": "smooth-ritz",
      "version": "1.1",
      "releaseDate": "2026.11.26",
      "pages": 5,
      "zh": "周期 Ritz 步长的光滑非二次实现",
      "en": "Smooth nonquadratic objectives with periodically repeating Ritz steps",
      "groupZh": "谱梯度与 Ritz",
      "groupEn": "Spectral gradients and Ritz values",
      "related": [
        "ritz-minimal-face",
        "ritz-reuse"
      ]
    },
    {
      "id": "coordinate-query",
      "version": "1.1",
      "releaseDate": "2026.11.26",
      "pages": 5,
      "zh": "一次曲率查询如何决定坐标步长",
      "en": "Choosing a coordinate step with one Hessian-vector query",
      "groupZh": "曲率信息与步长",
      "groupEn": "Curvature information and stepsizes",
      "related": [
        "trial-firsthit",
        "curvature-query-budget"
      ]
    },
    {
      "id": "curvature-query-budget",
      "version": "0.1",
      "releaseDate": "2026.11.26",
      "zh": "固定方向的曲率查询预算",
      "en": "Query budgets for directional curvature",
      "groupZh": "曲率信息与步长",
      "groupEn": "Curvature information and stepsizes",
      "related": [
        "coordinate-query"
      ],
      "pages": 7
    },
    {
      "id": "certified-chord",
      "version": "1.1",
      "releaseDate": "2026.11.26",
      "pages": 5,
      "zh": "用两个梯度样本判定弦点可停止",
      "en": "A certified stopping point from two gradient samples",
      "groupZh": "步长设计与停止条件",
      "groupEn": "Stepsizes and stopping criteria",
      "related": [
        "trial-firsthit",
        "gll-window"
      ]
    },
    {
      "id": "cold-window",
      "version": "1.1",
      "releaseDate": "2026.11.26",
      "pages": 5,
      "zh": "下一步梯度更小，ABBmin1 为何反而晚停",
      "en": "A smaller next gradient norm can delay stopping in ABBmin1",
      "groupZh": "步长设计与停止条件",
      "groupEn": "Stepsizes and stopping criteria",
      "related": [
        "trial-firsthit",
        "certified-chord"
      ]
    },
    {
      "id": "cached-design-certificate",
      "zh": "有限实验设计中的滞后拟合与误差证书",
      "en": "An error certificate for cached fits in finite experimental design",
      "groupZh": "最优实验设计",
      "groupEn": "Optimal experimental design",
      "related": [
        "delayed-design"
      ],
      "version": "0.1",
      "releaseDate": "2026.11.28",
      "pages": 6,
      "archive": true
    },
    {
      "id": "threshold-curvature-risk",
      "zh": "阈值选择后的条件曲率估计",
      "en": "Conditional curvature estimation after threshold selection",
      "groupZh": "步长设计与停止条件",
      "groupEn": "Stepsizes and stopping criteria",
      "related": [],
      "version": "0.1",
      "releaseDate": "2026.11.28",
      "pages": 5,
      "archive": true
    },
    {
      "id": "noisy-ritz-history",
      "zh": "带误差的梯度历史与 Ritz 整轮更新",
      "en": "Ritz sweeps from inexact gradient histories",
      "groupZh": "谱梯度与 Ritz",
      "groupEn": "Spectral gradients and Ritz values",
      "related": [
        "ritz-reuse",
        "ritz-minimal-face"
      ],
      "version": "0.2",
      "releaseDate": "2026.11.28",
      "pages": 11,
      "archive": true
    },
    {
      "id": "noisy-missing-curvature",
      "zh": "已知谱重数时未查询方向的曲率误差",
      "en": "Error in unqueried curvature with known spectral multiplicities",
      "groupZh": "曲率信息与步长",
      "groupEn": "Curvature information and stepsizes",
      "related": [
        "curvature-query-budget",
        "coordinate-query"
      ],
      "version": "0.2",
      "releaseDate": "2026.11.28",
      "pages": 4,
      "archive": true
    },
    {
      "id": "two-weak-mode-restart",
      "zh": "两模态二次目标的梯度重启时间",
      "en": "Gradient restart times for two-mode quadratics",
      "groupZh": "重启、投影与线搜索",
      "groupEn": "Restart, projection, and line search",
      "related": [
        "gradient-restart-return",
        "continuous-spectrum-restart"
      ],
      "version": "0.2",
      "releaseDate": "2026.11.28",
      "pages": 6,
      "archive": true
    },
    {
      "id": "continuous-spectrum-restart",
      "zh": "固定谱带下的梯度重启与维数",
      "en": "Gradient restart with a fixed spectral band",
      "groupZh": "重启、投影与线搜索",
      "groupEn": "Restart, projection, and line search",
      "related": [
        "gradient-restart-return",
        "two-weak-mode-restart"
      ],
      "version": "0.2",
      "releaseDate": "2026.11.28",
      "pages": 7,
      "archive": true
    },
    {
      "id": "periodic-bb-optimal-word",
      "zh": "周期 BB 切换的最优三次改进系数",
      "en": "The optimal cubic coefficient for periodic BB switching",
      "groupZh": "谱梯度与周期切换",
      "groupEn": "Spectral gradients and periodic switching",
      "related": [
        "periodic-bb"
      ],
      "version": "0.1",
      "releaseDate": "2026.11.28",
      "pages": 4,
      "archive": true
    },
    {
      "id": "two-point-bb-optimal-selector",
      "zh": "两点谱上 BB1/BB2 切换的最优五步序列",
      "en": "The optimal five-step BB switching schedule on two-point spectra",
      "groupZh": "谱梯度与周期切换",
      "groupEn": "Spectral gradients and periodic switching",
      "related": [
        "periodic-bb-optimal-word",
        "periodic-bb"
      ],
      "version": "0.1",
      "releaseDate": "2026.11.28",
      "pages": 12,
      "archive": true
    },
    {
      "id": "memory-three-five-point",
      "zh": "三记忆 LMSD 中五点固定线的不可达性",
      "en": "Inaccessibility of a five-point fixed line in three-memory LMSD",
      "groupZh": "谱梯度与 Ritz",
      "groupEn": "Spectral gradients and Ritz",
      "related": [
        "ritz-minimal-face",
        "ritz-reuse",
        "smooth-ritz"
      ],
      "version": "0.1",
      "releaseDate": "2026.11.28",
      "pages": 5,
      "archive": true
    },
    {
      "id": "threshold-binomial-information",
      "zh": "二项阈值选择后的条件信息",
      "en": "Conditional information after binomial threshold selection",
      "groupZh": "步长设计与停止条件",
      "groupEn": "Step design and stopping criteria",
      "related": [
        "threshold-curvature-risk",
        "cold-window"
      ],
      "version": "0.1",
      "releaseDate": "2026.11.28",
      "pages": 7,
      "archive": true
    },
    {
      "id": "large-spectrum-bb-switching",
      "zh": "大谱宽下两点谱 BB 切换的最优指数",
      "en": "The optimal wide-spectrum exponent for two-point BB switching",
      "groupZh": "谱梯度与周期切换",
      "groupEn": "Spectral gradients and periodic switching",
      "related": [
        "two-point-bb-optimal-selector",
        "periodic-bb-optimal-word"
      ],
      "version": "0.1",
      "releaseDate": "2026.11.28",
      "pages": 8,
      "archive": true
    },
    {
      "id": "separated-mode-restart",
      "zh": "分离曲率尺度下的梯度重启时间",
      "en": "Gradient restart with separated curvature scales",
      "groupZh": "重启、投影与线搜索",
      "groupEn": "Restart, projection and line search",
      "related": [
        "two-weak-mode-restart",
        "continuous-spectrum-restart"
      ],
      "version": "0.1",
      "releaseDate": "2026.11.28",
      "pages": 12,
      "archive": true
    },
    {
      "id": "bb-armijo-attracting-cycle",
      "zh": "两特征值 BB 法单调回溯中的吸引四周期",
      "en": "An attracting four-cycle in two-point BB with Armijo backtracking",
      "groupZh": "重启、投影与线搜索",
      "groupEn": "Restart, projection and line search",
      "related": [
        "gll-window",
        "smooth-ritz",
        "two-point-bb-optimal-selector"
      ],
      "version": "0.1",
      "releaseDate": "2026.11.28",
      "pages": 8,
      "archive": true
    },
    {
      "id": "bb-two-point-first-hitting",
      "zh": "两特征值下 BB 法的首次达标步数与最速下降法的比较",
      "en": "First hitting times of BB and steepest descent on two-point spectra",
      "groupZh": "谱梯度与周期切换",
      "groupEn": "Spectral gradients and periodic switching",
      "related": [
        "two-point-bb-optimal-selector",
        "large-spectrum-bb-switching",
        "trial-firsthit"
      ],
      "version": "0.2",
      "releaseDate": "2026.11.28",
      "pages": 10,
      "archive": true
    },
    {
      "id": "admm-residual-feedback",
      "zh": "二次 ADMM 的周期罚参数与残差反馈发散",
      "en": "Periodic penalties and residual-feedback divergence in quadratic ADMM",
      "groupZh": "分裂法与矩阵分解",
      "groupEn": "Splitting and matrix decomposition",
      "related": [
        "admm-alternating",
        "pcp-computation"
      ],
      "version": "0.2",
      "releaseDate": "2026.11.28",
      "pages": 9,
      "archive": true
    },
    {
      "id": "pcp-rectangle-sharp-stability",
      "zh": "静止矩形 PCP 的最优性端点与唯一恢复",
      "en": "Endpoint optimality, uniqueness and sharp stability for rectangular PCP",
      "groupZh": "分裂法与矩阵分解",
      "groupEn": "Splitting and matrix decomposition",
      "related": [
        "pcp-rectangle",
        "pcp-computation",
        "admm-residual-feedback"
      ],
      "version": "0.4",
      "releaseDate": "2026.11.28",
      "pages": 12,
      "archive": true
    },
    {
      "id": "projected-bb-sharp-two-step",
      "zh": "齐次凸锥约束下投影 Barzilai–Borwein 法的收缩与两步回归",
      "en": "Uniform contraction and two-step returns for projected BB",
      "groupZh": "重启、投影与线搜索",
      "groupEn": "Restart, projection and line search",
      "related": [
        "restart-projected-bb",
        "bb-armijo-attracting-cycle"
      ],
      "version": "0.1",
      "releaseDate": "2026.11.28",
      "pages": 5,
      "archive": true
    },
    {
      "id": "two-point-restart-rotation",
      "zh": "两点谱梯度重启的无理旋转与精确调用速率",
      "en": "Irrational rotation and gradient-call rates for two-point restart",
      "groupZh": "重启、投影与线搜索",
      "groupEn": "Restart, projection and line search",
      "related": [
        "two-weak-mode-restart",
        "continuous-spectrum-restart",
        "separated-mode-restart"
      ],
      "version": "0.2",
      "releaseDate": "2026.11.28",
      "pages": 5,
      "archive": true
    },
    {
      "id": "bounded-delay-bb-sharp-rate",
      "zh": "有界滞后谱步长的尖锐收敛界",
      "en": "Sharp convergence rates for bounded-delay spectral steps",
      "groupZh": "谱梯度与周期切换",
      "groupEn": "Spectral gradients and periodic switching",
      "related": [
        "two-point-bb-optimal-selector",
        "large-spectrum-bb-switching"
      ],
      "version": "0.2",
      "releaseDate": "2026.11.28",
      "pages": 9,
      "archive": true
    },
    {
      "id": "restart-three-interval-exchange",
      "zh": "三种梯度重启间隔的区间交换与临界速率",
      "en": "Three restart intervals and failure of the critical prefactor",
      "groupZh": "重启、投影与线搜索",
      "groupEn": "Restart, projection and line search",
      "related": [
        "two-point-restart-rotation",
        "separated-mode-restart",
        "continuous-spectrum-restart"
      ],
      "version": "0.2",
      "releaseDate": "2026.11.28",
      "pages": 6,
      "archive": true
    },
    {
      "id": "pcp-growth-noise-classification",
      "zh": "矩形 PCP 唯一分解的增长阶与噪声稳定性",
      "en": "Growth exponents and sharp noise rates in rectangular PCP",
      "groupZh": "分裂法与矩阵分解",
      "groupEn": "Splitting and matrix decomposition",
      "related": [
        "pcp-rectangle-sharp-stability",
        "pcp-rectangle",
        "admm-residual-feedback"
      ],
      "version": "0.1",
      "releaseDate": "2026.11.28",
      "pages": 9,
      "archive": true
    },
    {
      "id": "unlimited-lag-bb-sharp-envelope",
      "zh": "无滞后上限谱步长的尖锐最坏界",
      "en": "Sharp worst-case bounds for spectral steps with unlimited lag",
      "groupZh": "谱步长与 BB 方法",
      "groupEn": "Spectral steps and BB methods",
      "related": [
        "bounded-delay-bb-sharp-rate",
        "bb-two-point-first-hitting",
        "noisy-ritz-history"
      ],
      "version": "0.2",
      "releaseDate": "2026.11.28",
      "pages": 5,
      "archive": true
    },
    {
      "id": "two-spectrum-fixed-orbit-envelope",
      "zh": "两点谱固定轨道的尖锐对数衰减",
      "en": "Sharp logarithmic decay of fixed two-point spectral orbits",
      "groupZh": "谱步长与 BB 方法",
      "groupEn": "Spectral steps and BB methods",
      "related": [
        "unlimited-lag-bb-sharp-envelope",
        "bounded-delay-bb-sharp-rate"
      ],
      "version": "0.1",
      "releaseDate": "2026.11.28",
      "pages": 2,
      "archive": true
    },
    {
      "id": "nested-log-delay-envelope",
      "zh": "两点谱无界滞后的迭代对数收敛界",
      "en": "Iterated-log decay for two-point spectral steps with unbounded delays",
      "groupZh": "谱步长与 BB 方法",
      "groupEn": "Spectral steps and BB methods",
      "related": [
        "two-spectrum-fixed-orbit-envelope",
        "unlimited-lag-bb-sharp-envelope",
        "bounded-delay-bb-sharp-rate"
      ],
      "version": "0.1",
      "releaseDate": "2026.11.28",
      "pages": 6,
      "archive": true
    },
    {
      "id": "continuous-spectrum-sublinear-delay",
      "zh": "连续谱滞后梯度法及两点谱的尖锐年龄常数",
      "en": "Delayed spectral gradients in Hilbert space and sharp two-point age constants",
      "groupZh": "谱步长与 BB 方法",
      "groupEn": "Spectral steps and BB methods",
      "related": [
        "bounded-delay-bb-sharp-rate",
        "unlimited-lag-bb-sharp-envelope",
        "nested-log-delay-envelope"
      ],
      "version": "0.1",
      "releaseDate": "2026.11.28",
      "pages": 8,
      "archive": true
    },
    {
      "id": "alternating-bb-fixed-score-potential",
      "zh": "交替 BB 固定谱分数的两点势与三点约化",
      "en": "A two-point potential and a three-point reduction for an alternating BB score",
      "groupZh": "谱步长与 BB 方法",
      "groupEn": "Spectral steps and BB methods",
      "related": [
        "two-point-bb-optimal-selector",
        "bounded-delay-bb-sharp-rate"
      ],
      "version": "0.1",
      "releaseDate": "2026.11.28",
      "pages": 13,
      "archive": true
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
      "pages": 115
    },
    {
      "id": "lmsd-reuse",
      "zh": "历史谱梯度法的共同 Lyapunov 界与最优 Ritz 重用",
      "en": "Common Lyapunov bounds and optimal Ritz reuse in spectral gradient methods",
      "groupZh": "LMSD 与 Ritz 重用",
      "groupEn": "LMSD and Ritz reuse",
      "pages": 37
    }
  ]
};
