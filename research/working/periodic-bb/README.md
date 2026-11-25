# Periodic Barzilai–Borwein switching

[Read the paper and supplementary proofs](https://taitai2025.github.io/assets/documents/research/periodic-bb.pdf)

This public working manuscript follows the E01 version. AI assisted with preparation and independent checks. Author verification is pending.

The proofs give phase compatibility, strict gaps, and exact local coefficients. The finite-dimensional trajectory factor and the threshold for a uniform envelope are tracked separately. The finite-budget results include all 1,080 runs and 43 timeouts. ABBmin1 was faster by median update count in the displayed cells. The data do not measure wall time.

- **paper/** contains the LaTeX for the main manuscript and full supplement.
- **experiments/** contains generation code, initial conditions, results and the compressed historical trace. Unpack the trace in output/ before using the replot script. Re-running to a new output directory preserves the archived tables.
- **word_analysis/** contains the exact coefficient computations and archived tables.
- **P06Exact.lean** checks 15 rational and integer facts for three explicit patterns. The all-spectrum convergence theorem and uniform remainder remain at the paper-proof level. See [the Lean receipt](lean-verification.json).

[Related working paper on line-search trial values](../trial-firsthit/)

The November 26 Windows rerun matches all ten experiment CSVs and all five pattern-analysis CSVs byte for byte, including 145,858 trace rows. [Replay comparison](experiment-replay.json).
