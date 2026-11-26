# A smaller next gradient norm can delay stopping in ABBmin1

The [working paper](https://taitai2025.github.io/assets/documents/research/cold-window.pdf) reconstructs an exact stopping reversal for ABBmin1. The initial secant remains in the window after the corresponding eigenmode has vanished. The result compares first-hit gradient requests at fixed tolerances.

Build the source with two runs of pdflatex on cold-window.tex. Run python -B replay.py for 35 exact rational assertions and a small replay table. With Lean 4.8.0, use lean --trust=0 -DautoImplicit=false ColdWindow.lean to check 11 closed rational claims. The analysis of the two-dimensional spectral recurrence and the curvature envelope is in the text.

This is an AI-assisted working paper pending author review.

Version 1.1 spells out the first adaptive update, the information used in the curvature bound, and the two stopping tolerances. The exact benchmark and Lean checks remain applicable.
