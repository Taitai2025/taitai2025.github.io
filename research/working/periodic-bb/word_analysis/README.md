# Exact word coefficients

Supplement Section S14 proves the exact unrestricted coefficient K=Var(r)/2, the Fourier formula, the transition-density bounds, four rational examples, and the long-block formula. These computations verify the finite recurrence and examples; they do not approximate Gamma using finite trajectories.

Use the dependencies pinned in ../experiments/requirements.txt, then run:
    python word_dependence.py --out output_reproduction --max-length 12

The program enumerates all 745 primitive binary rotation classes of lengths 2 through 12. Complements and reversals remain distinct enumeration entries. All recurrence and coefficient inequalities use exact fractions; an independent NumPy DFT checks the Fourier identity. The maximum discrepancy is 2.220446049250313e-16. Long blocks are checked for m=1,...,64 against a 90-digit formula. Section S15 additionally proves a word-independent remainder and a joint growing-block limit when m tends to infinity and m*C tends to zero. The plotted coefficients themselves are exact for every listed m.

Five deterministic CSVs are included: word_responses.csv, enumeration_counts.csv, exact_examples.csv, near_isotropic_examples.csv, and long_blocks.csv. A second fresh-process run reproduced all five byte for byte. No random seeds, training split, or optimizer parameter tuning is involved. The recorded verification.json describes the word-analysis module's conditional dependence on the separately proved unrestricted theorem; that theorem is now provided in the supplement.

The displayed primitive balanced words have coefficients 23/384 for 00010111, 1/12 for 00100111, 11/96 for 000111, and 15/224 for 001011. The first pair has equal transition density. The second pair shows that more switches can give a smaller exact local improvement. No all-condition-number or finite-budget ordering is asserted.
