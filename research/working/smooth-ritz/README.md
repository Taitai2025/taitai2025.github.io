# Smooth nonquadratic objectives with periodically repeating Ritz steps

The [five-page working paper](https://taitai2025.github.io/assets/documents/research/smooth-ritz.pdf) gives a general lifting criterion, the six-sweep memory-two example, and its exact local lower bound. The quadratic six-cycle is taken from the [archived spectral-bounds manuscript](https://taitai2025.github.io/assets/documents/research/lmsd-spectral.pdf). The earlier derivation of the two-derivative lift is distinguished from the smooth and analytic extensions in the paper.

Build the PDF by running `pdflatex smooth-ritz.tex` twice. With Lean 4.8.0, check the discrete results with `lean --trust=0 -DautoImplicit=false SmoothRitzReplay.lean`.

The Lean source proves deterministic state replay, the normalized return recursion, and two possible normalized directions per phase from the stated discrete hypotheses. The smooth and analytic perturbations, existence of the quadratic cycle, and its asymptotic rate are covered by the written analysis and its citation.

This is an AI-assisted research working paper pending human author review.

Version 1.1 clarifies the compatible history, the periodic multiplier, and what the construction preserves. The title page states that author verification is pending.
