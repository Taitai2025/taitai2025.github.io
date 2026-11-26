"""Exact rational examples for Query budgets for directional curvature."""
from fractions import Fraction as F
import json


def dot(v, w):
    return sum(a * b for a, b in zip(v, w, strict=True))


def outer(v):
    squared_norm = dot(v, v)
    return tuple(tuple(F(a * b, squared_norm) for b in v) for a in v)


def product(a, b):
    return tuple(tuple(dot(row, col) for col in zip(*b, strict=True)) for row in a)


def action(matrix, vector):
    return tuple(dot(row, vector) for row in matrix)


def diagonal(matrix):
    return tuple(row[i] for i, row in enumerate(matrix))


def threshold(weights, budget):
    for active_count in range(budget + 1, len(weights) + 1):
        active = weights[:active_count]
        level = F(active_count - budget) / sum(F(1, x) for x in active)
        if all(x > level for x in active) and all(x <= level for x in weights[active_count:]):
            assert sum(max(1 - level / x, 0) for x in weights) == budget
            return level
    raise AssertionError("No threshold found")


def verify_orthogonal_examples():
    assert threshold((4, 3), 1) == F(12, 7)
    weights = (9, 4, 1)
    one, two = [threshold(weights, budget) for budget in (1, 2)]
    assert (one, two) == (F(36, 13), F(36, 49))
    one_q = outer((3, 2, 0))
    assert diagonal(one_q) == (F(9, 13), F(4, 13), 0)
    assert max(w * (1 - q) for w, q in zip(weights, diagonal(one_q), strict=True)) == one
    complement = (2, 3, 6)
    assert dot(complement, complement) == 49
    residual = outer(complement)
    assert product(residual, residual) == residual
    assert [w * q for w, q in zip(weights, diagonal(residual), strict=True)] == [two] * 3
    return {"weights_4_3": str(F(12, 7)), "weights_9_4_1": [str(one), str(two)]}


def verify_projection_example():
    initial = (1, 1, 1)
    for i in range(3):
        upper, lower = [-1] * 3, [0] * 3
        upper[i] = 2
        j, k = [j for j in range(3) if j != i]
        lower[j], lower[k] = 1, -1
        assert dot(upper, initial) == dot(lower, initial) == 0
        recorded = []
        for v in (lower, upper):
            p = outer(v)
            assert product(p, p) == p
            assert action(p, initial) == (0, 0, 0)
            assert sum(diagonal(p)) == 1
            h_diag = tuple(1 + 4 * x for x in diagonal(p))
            assert sum(h_diag) == 7
            recorded.append(h_diag[i])
        assert recorded == [1, F(11, 3)]
    p = outer((2, -1, -1))
    reply = action(p, (1, 0, 0))
    assert reply[0] != 0
    reconstructed = tuple(tuple(x * y / reply[0] for y in reply) for x in reply)
    assert reconstructed == p
    return {"diagonal_marginal_width": str(F(8, 3)), "sum_of_marginal_widths": "8",
            "trace_width": "0", "one_additional_reply_reconstructs_this_projection": True}


if __name__ == "__main__":
    print(json.dumps({"orthogonal": verify_orthogonal_examples(),
                      "fixed_rank": verify_projection_example()}, indent=2))

