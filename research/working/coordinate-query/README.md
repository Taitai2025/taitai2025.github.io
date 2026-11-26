# Choosing a coordinate step with one Hessian-vector query

The [five-page working paper](https://taitai2025.github.io/assets/documents/research/coordinate-query.pdf) derives the best guaranteed two-coordinate decrease after one Hessian-vector product. It gives the entire decision rule for a fixed reply and treats the exact axis-query guarantee separately.

Build the PDF by running `pdflatex coordinate-query.tex` twice. The supplied figure can be regenerated with `python plot-query-values.py` with Matplotlib installed. The plot evaluates the analytic formulas, using bisection for the implicit axis branch.

With Lean 4.8.0, run `lean --trust=0 -DautoImplicit=false CoordinateQueryChecks.lean`. The eleven Lean examples check exact rational endpoint payoffs, both components of a common reply, its two eigenvalues, and two inequalities locating a sample axis-query crossing. The general minimax and uniqueness claims are covered by the written proofs.

This is an AI-assisted research working paper pending human author review.

Version 1.1 describes the information model and the decrease benchmark in ordinary mathematical language. The title page states that author verification is pending.
