"""Reproduce the two exact examples in restart-projected-bb.pdf.

Version 0.1.0, 2026-11-25. Standard library only. All arithmetic uses Fraction;
no floating-point value determines a sign or a projection branch.
This program checks examples, not the general convergence theorems.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json


def require(condition, description):
    if not condition:
        raise ArithmeticError(description)


def residuals(s, last):
    """p_0=1, p_1=s; return residuals and c_k for k=1,...,last."""
    require(Q(0) < s < Q(1), "A spectral node must lie in (0,1)")
    require(last >= 1, "At least one trial is required")
    p = [Q(1), s]
    for k in range(1, last):
        p.append(s * ((2*k+1)*p[k] - (k-1)*p[k-1]) / (k+2))
    c = [None] + [(1-s)/s * p[k] * (p[k]-p[k-1])
                  for k in range(1, last+1)]
    return p, c


def restart_example():
    nodes = [Q(1, 2), Q(9, 10)]
    pairs = [residuals(s, 12) for s in nodes]
    margins = [(c[5] + 128*c[12])/129 for _, c in pairs]
    expected = [Q(3409329, 1477468749824),
                Q(2366243076860328051781857,
                  88064000000000000000000000000)]
    require(margins == expected, "Dual margin fractions do not match")
    require(all(x > 0 for x in margins), "Dual margins must be strictly positive")
    criteria = [(pairs[0][1][k] + pairs[1][1][k])/2
                for k in range(1, 13)]
    require(all(x < 0 for x in criteria[:11]), "Earlier trial is not strictly negative")
    require(criteria[11] > 0, "Trial 12 is not strictly positive")
    require(all(x != 0 for p, _ in pairs for x in p),
            "A mode vanishes before or at trial 12")
    return {
        "spectral_nodes": list(map(str, nodes)),
        "realization": {"h": "1", "H_diagonal": ["1/2", "1/10"],
                        "witness_initial_point": ["1", "1"]},
        "worst_first_trigger_trial": 12,
        "gradient_calls_without_cache": 13,
        "dual_weights": {"trial_5": "1/129", "trial_12": "128/129"},
        "strict_positive_margins": list(map(str, margins)),
        "witness_weights": ["1/2", "1/2"],
        "witness_criteria_trials_1_to_12": list(map(str, criteria)),
        "residuals_k0_to_k12": [list(map(str, p)) for p, _ in pairs],
        "no_mode_vanishes_k0_to_k12": True,
    }


def projected_bb_example():
    H = ((Q(1), Q(-1)), (Q(-1), Q(4)))

    def multiply(x):
        return tuple(sum(H[i][j]*x[j] for j in range(2)) for i in range(2))

    def dot(x, y):
        return sum(a*b for a, b in zip(x, y))

    def subtract(x, y):
        return tuple(a-b for a, b in zip(x, y))

    def scale(t, x):
        return tuple(t*a for a in x)

    def project(x):
        return tuple(max(Q(0), a) for a in x)

    u = (Q(3), Q(1))
    v = project(subtract(u, multiply(u)))
    s = subtract(v, u)
    alpha = dot(s, s)/dot(s, multiply(s))
    w = project(subtract(v, scale(alpha, multiply(v))))
    require(v == (Q(1), Q(0)), "Unexpected initialized point")
    require(alpha == Q(5, 4) and w == (Q(0), Q(5, 4)), "Unexpected BB1 step")
    require(dot(v, v) == 1 and dot(w, w) == Q(25, 16), "Unexpected squared norms")
    require(dot(v, multiply(v))/2 == Q(1, 2), "Unexpected initial objective")
    require(dot(w, multiply(w))/2 == Q(25, 8), "Unexpected final objective")
    determinant = H[0][0]*H[1][1]-H[0][1]*H[1][0]
    determinant_shifted = (H[0][0]-1)*(H[1][1]-1)-H[0][1]*H[1][0]
    require(H[0][0] > 0 and determinant > 0, "H must be positive definite")
    # For this real symmetric 2x2 matrix, det(H-I)<0 places 1 between
    # the two eigenvalues. Consequently 1/b < tau=1 < 1/a.
    require(determinant_shifted < 0, "tau=1 must lie in the spectral interval")
    return {
        "H": [[str(a) for a in row] for row in H],
        "cone": "nonnegative orthant in R^2",
        "u": list(map(str, u)), "tau": "1", "v": list(map(str, v)),
        "secant": list(map(str, s)), "alpha": str(alpha), "next": list(map(str, w)),
        "squared_norm_before": str(dot(v, v)), "squared_norm_after": str(dot(w, w)),
        "objective_before": str(dot(v, multiply(v))/2),
        "objective_after": str(dot(w, multiply(w))/2),
        "det_H": str(determinant), "det_H_minus_I": str(determinant_shifted),
        "interpretation": "A one-step expansion; not a nonconvergence or periodic-orbit proof.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("exact-examples.json"))
    args = parser.parse_args()
    result = {
        "version": "0.1.0", "status": "PASS",
        "scope": "Exact examples only; general theorems and novelty are not certified by this program.",
        "restart": restart_example(), "projected_BB1": projected_bb_example(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")
    print("PASS: exact restart certificate and compatible projected BB1 expansion")


if __name__ == "__main__":
    main()
