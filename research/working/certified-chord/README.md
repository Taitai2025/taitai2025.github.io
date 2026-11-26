# A certified stopping point from two gradient samples

The [five-page working paper](https://taitai2025.github.io/assets/documents/research/certified-chord.pdf) gives a two-endpoint gradient certificate for stopping inside a nonmonotone line-search segment. The exact fixture ends in two committed steps rather than three, with four value requests and four gradient requests in each run.

Build the source with two runs of `pdflatex certified-chord.tex`. With Lean 4.8.0, run `lean --trust=0 -DautoImplicit=false CertifiedChord.lean` to verify the fixed rational equalities, stopping conditions, acceptance inequalities and count arithmetic. The mathematical text supplies the analytical error bound, finite stopping of the reference and the general coupling.

This is an AI-assisted research working paper pending human author review.

Version 1.1 brings the review notice to the first page and clarifies the trial, commit, and request accounting. The exact rational example and formal checks are the same as in v1.0.
