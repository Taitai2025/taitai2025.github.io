# Recorded evidence: periodic BB switching, bounded mechanism and finite-budget experiments

Run date: 2026-09-22. The synthetic data were generated using the fixed protocol below.

## Reproduce

Use Python 3.12 with NumPy, Matplotlib, and mpmath. The measured environment is saved in `output/environment.json`; the tested package versions are in `requirements.txt`.

```text
python run_experiments.py --out output_reproduction
```

This takes about 6–12 seconds on the recorded machine and creates two vector PDFs, two PNG previews, all CSV data, environment metadata, and SHA-256 hashes. The main script includes direct-secant prefix checks and high-precision cycle assertions; an assertion failure stops execution. Floating-point last digits can differ across numerical libraries. Timing, PDF creation metadata, and their hashes need not agree across reruns. No network, download, tuning, or external dataset is required. The complete starting gradients and spectra are also recorded, so reproducing the Gaussian generator is optional.

`results.tex` is a compact manuscript subsection. Figure captions and integration notes are in `FIGURES.md`. Both publication figures are 6.75 by 2.55 inches, with embedded vector text in PDF. PNG previews were visually inspected.

## Mechanism experiment

Formula sources are Supplement Sections S4, S5, S9, and S11. Section S14 proves the exact unrestricted cubic coefficient and its Fourier interpretation. The implementation independently solves the periodic linear system

`a[k+1] - a[k] + 2*a[k-1] = 2*sigma[k]`,

with indices modulo the word length. It then forms `r[k]=1-a[k-1]+sigma[k]` and checks

`rho=(kappa-1)/exp(mean(log(1+kappa**r[k])))`

against a complete period of the delayed normalized spectral dynamics, using 90 decimal digits. All 35 word/condition-number checks pass with a relative factor error and a projective closure error below `1e-70`. The words are `0`, `1`, `01`, `0011`, and `00011`; condition numbers are 1.00001, 1.01, 2, 10, 100, 1000, and 10000. The two-point trajectory is initialized exactly on the prescribed periodic response. Its realizability is separately checked using a positive, generally unmatched, warm-up.

For `C=(kappa-1)/(kappa+1)`, the limit of `(C-rho)/C**3` is `Var(r)/2`. The independently computed constants are 1/32 for `01`, 1/8 for `0011`, and 9/55 for `00011`. Log-log slopes over `1e-5 <= C < 1e-3` are respectively 2.999999959, 2.999999950, and 2.999999946. The dashed curves in `mechanism.pdf` are evaluations of the explicit theoretical lower bound `C*(1-exp(-delta_L(C)))`; the solid curves are `C-rho`. They bracket the unrestricted-spectrum gap only by using the stated theorems. They are **not** numerical estimates of the unknown unrestricted factor Gamma.

For the alternating three-point construction, the spectral nodes are `{1,(1+kappa)/2,kappa}`. Its masses, delayed selectors, two-step closure, factor `rho3=C/sqrt(2-C*C)`, and unmatched warm-up `alpha0=1/u1` are checked independently. Above `kappa*=577+408*sqrt(2)=1153.9991334482228...`, all three masses are positive. At kappa=2000, `rho01=0.997795863428071` and `rho3=0.9980039905239375`; at kappa=10000, they are 0.9993954276856584 and 0.9996001599240384. Larger factor means slower contraction. Invalid below-threshold masses and the zero midpoint mass at threshold remain in the CSV rather than being discarded. The reciprocal pair itself has the acknowledged CBB precedent; these experiments test the alternating-rule compatibility, not originality of that pair.

## Lag, warm-up, and finite-budget protocol

There are 180 fixed problems and 1,080 method runs. Every Hessian is diagonal, with dimension 64, smallest eigenvalue 1, and kappa in `{10,100,1000}`. Three spectral families are used:

- `log_spaced`: 64 equally spaced points on a logarithmic scale from 1 to kappa.
- `linear_spaced`: 64 equally spaced points from 1 to kappa.
- `two_bands`: 32 equally spaced points in `[1,1.05]` and 32 in `[.95*kappa,kappa]`.

For each spectrum, 20 initial gradients have independent standard Gaussian entries. `SeedSequence([20260922,family_index,kappa,seed])` with seed 0 through 19 fixes the instances. Starting in gradient coordinates means `x0=A^{-1}g0` for the zero-linear-term quadratic; these are not Gaussian initial x vectors. All methods share the same initial gradient and the same positive warm-up `alpha0=2/(1+kappa)`. No parameter or word search was performed on these cases.

After the warm-up, `n=0` is `g1`. At post-warm-up update `n=1`, the step uses `g0` and acts on `g1` to produce `g2`. In general the step acts on `g_n` and is formed from `g_{n-1}`; the phase is `(n-1) mod L`. Thus the first prescribed symbol of `01` and `0011` is BB1. Every method is measured relative to `||g1||`. The shared warm-up is not generally matched to any method.

The code stores normalized log squared spectral weights and a separate accumulated log gradient norm. For a step alpha, the update adds `2*log(abs(1-alpha*lambda_i))` to log weights and normalizes by log-sum-exp. Quotients are evaluated from the previous normalized weights. This prevents absolute gradient underflow. In the reported runs there were zero exact floating-point zero multipliers and zero numerical errors. An independent signed-gradient implementation forms actual secants `s` and `y`; its first 12 updates agree with the spectral implementation within `2.94e-14` in log10 norm ratio for every method.

The maximum budget is 500 updates after warm-up. A run is successful at its first `||g_{n+1}||/||g1|| <= 1e-8`; otherwise it is right-censored at 500. Reported hitting-time medians include censored observations as infinity, not as 500. Fixed-budget residuals and plots clamp successful runs to log10 ratio -8 after their first hit. This is a reporting floor, not finite termination. Norm increases and large transient excursions are retained. No line search, restart, safeguard, convergence smoothing, or per-method parameter tuning is used.

## Baselines and computation costs

BB1 and BB2 use their standard delayed secant quotients. `01` and `0011` change quotient type while recomputing its numerical value each update. `CBB1(m=2)` means BB1 reuse with cycle length two: refresh at post-warm-up updates 1,3,5,... and reuse at 2,4,6,... . This is a fixed cycle diagnostic, not an optimized or adaptive CBB solver.

ABBmin1 follows Frassoldati, Zanni, and Zanghirati (2008), equation (14): if `alpha_BB2/alpha_BB1 < .8`, use the smallest BB2 step with index `j=max(1,k-9),...,k`; otherwise use the current BB1 step. Thus m=9 stores nine preceding values plus the current value. The first window contains only available post-warm-up quotients. Parameters follow the authors' numerical setting. Source: [author preprint, eq. (14) and parameter paragraph](https://optimization-online.org/wp-content/uploads/2007/01/1572.pdf); published [JIMO DOI](https://doi.org/10.3934/jimo.2008.4.299). No changing-threshold variant is mislabeled as ABBmin2.

At n updates, all methods have a budget of n+2 gradient evaluations including g0 and the common warm-up result g1. Each update uses one gradient evaluation, no function evaluations, and no line search. Under direct-secant accounting, forming either BB quotient requires two inner products; obtaining both requires three because `s^T y` is shared. The selector-only counts are:

| Method | Selector inner products for n post-warm-up updates | Stored scalar step history |
|---|---:|---:|
| BB1, BB2, 01, 0011 | 2n | O(1) |
| ABBmin1 | 3n | at most 10 |
| CBB1(m=2) | 2 ceil(n/2) | 1 |

All methods additionally have the same optional norm-monitoring cost, one inner product per computed gradient. These counts intentionally describe a general secant implementation, not the speed of the diagonal spectral simulator. Gradient budgets are matched; total inner-product budgets and wall-clock times are **not** asserted equal. `finite_budget_summary.csv` and the trace contain the actual selector counts at each first hit. At kappa=1000 on log-spaced spectra, for example, medians are 416.5/401/341 updates for BB1/01/ABBmin1 but 833/802/1023 selector inner products. ABBmin1 saves gradients here while using more inner products than 01.

## Results and retained failures

At kappa=1000, median post-warm-up target-hitting updates are:

| Method | Log-spaced | Linear-spaced | Two bands |
|---|---:|---:|---:|
| BB1 | 416.5 | 376.5 | 47 |
| BB2 | 426 | 386.5 | 37 |
| 01 | 401 | 377.5 | 48 |
| 0011 | 408.5 | 370.5 | 25 |
| ABBmin1 | 341 | 152 | 19 |
| CBB1(m=2) | >500 | >500 | 63 |

There are 43 timeouts among 1,080 runs. All occur at kappa=1000: on log-spaced spectra BB1/BB2/01/CBB1(m=2) have 1/3/1/18 failures; on linear-spaced spectra CBB1(m=2) has 19; on two bands CBB1(m=2) has 1. No timeout is removed from the denominator. Every other listed group solves all 20 starts. Full results for kappa=10 and 100 are in `aggregate.csv`.

The endpoint analysis does not rank finite-budget performance: 01 is slightly slower than BB1 on the linear family and on the two-band family, while 0011 is much faster on the two-band family. ABBmin1 is faster in all three displayed median comparisons. These are structured quadratic diagnostics, not a broad optimizer benchmark or evidence of a uniform finite-time speedup.

The periodic endpoint responses are repelling: perturbations grow with multiplier modulus `2**(L/2)` per word. The retained `repeller_roundoff_diagnostic.csv` starts the alternating kappa=100 response in double precision. Its log energy-ratio error first exceeds .01 at update 92. It is therefore inappropriate to fit the exact invariant factor from its late-time slope, or from random starts. High-precision checks deliberately use only one complete cycle; they do not claim long-term floating-point shadowing.

## Files

- `run_experiments.py`: full computation, verification, and plotting code.
- `output/two_point_exact.csv`: all high-precision periodic and warm-up checks.
- `output/cubic_gap.csv`: exact response gaps and the conservative theoretical bound.
- `output/three_point_cycle.csv`: positive and invalid constructions, factors, and closure checks.
- `output/initial_conditions.csv`: every eigenvalue and initial gradient coordinate.
- `output/finite_budget_traces.csv`: every update, step selection, residual, and cost.
- `output/finite_budget_summary.csv`, `aggregate.csv`, `fixed_budget.csv`: uncensored per-run data and the explicitly defined summaries.
- `output/failures.csv`: all 43 budget failures.
- `output/repeller_roundoff_diagnostic.csv`: retained floating-point failure of indefinite cycle shadowing.
- `output/mechanism.pdf`, `finite_budget.pdf`: publication figures, with matching PNGs.
- `output/environment.json`, `SHA256.json`: environment and output checksums.

Numerical verification supports the formulas on the sampled configurations. It does not prove the Hilbert-space realization, the unrestricted-spectrum envelope theorem, or its quantitative certificate; those require the manuscript's independent proof audit.

## Display and cost conventions

The unchanged machine key `CBB2` in code and CSVs maps to the displayed name `CBB1(m=2)`: BB1 step reuse for exactly two updates. It does not denote cyclic BB2. Only the figure label changed in this version; all ten recorded CSVs are unchanged. `replot_from_data.py` redraws both figures from the stored traces without rerunning the trajectories.

The listed costs recompute each secant quadratic form directly. Norm caching and fusing multiple inner products can change additional computation and communication costs. These counts are not communication-reduction counts, and no communication or wall-clock advantage follows.
