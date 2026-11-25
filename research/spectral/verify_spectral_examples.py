"""Exact checks accompanying the public BB and LMSD reading note."""
from fractions import Fraction as F
from itertools import combinations
from math import prod


def verify_bb(weight, initial):
    """Verify one matched initialization and its delayed-Rayleigh orbit."""
    lam = (F(1), F(4))
    c = F(3, 5)

    def reciprocal(gradient):
        energy = [w * g**2 for w, g in zip(weight, gradient)]
        return sum(x * l for x, l in zip(energy, lam)) / sum(energy)

    previous = current = tuple(map(F, initial))
    for k in range(13):
        expected = (initial[0] * c**k, (-1)**k * initial[1] * c**k)
        assert current == expected, (k, current, expected)
        tau = reciprocal(previous)
        assert tau == F(5, 2)
        previous, current = current, tuple(
            g * (1 - l / tau) for g, l in zip(current, lam)
        )


def verify_lmsd():
    """Verify the determinant ratio in a nonorthogonal basis of a plane."""
    lam = (1, 3, 7)
    rows = ((1, 0), (1, 1), (0, 1))
    pairs = tuple(combinations(range(3), 2))

    def minor2(i, j):
        (a, b), (c, d) = rows[i], rows[j]
        return (a * d - b * c) ** 2

    def compression_det(t):
        aa = sum((l - t) * x * x for (x, y), l in zip(rows, lam))
        bb = sum((l - t) * x * y for (x, y), l in zip(rows, lam))
        dd = sum((l - t) * y * y for (x, y), l in zip(rows, lam))
        return aa * dd - bb * bb

    denominator = compression_det(F(0))
    assert denominator == 31
    weights = [F(minor2(i, j) * lam[i] * lam[j], denominator) for i, j in pairs]
    assert all(w >= 0 for w in weights) and sum(weights) == 1
    for t in (F(-1), F(0), F(1), F(3, 2), F(3), F(7), F(8)):
        expansion = sum(
            weight * prod(1 - t / lam[i] for i in pair)
            for weight, pair in zip(weights, pairs)
        )
        assert compression_det(t) / denominator == expansion


if __name__ == "__main__":
    verify_bb((1, 1), (1, 1))
    verify_bb((1, 4), (2, 1))
    verify_lmsd()
    print("Exact checks passed: matched BB1, matched BB2, and LMSD determinant ratio.")
