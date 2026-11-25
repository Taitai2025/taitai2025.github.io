"""Exact examples for fixed-weight Ritz sweeps on J={1, 2, 4}."""
from fractions import Fraction as F
from math import prod

nodes = (1, 2, 4)
derivatives = tuple(prod(node - other for other in nodes if other != node) for node in nodes)
lagrange = tuple(F(prod(-other for other in nodes if other != node), d)
                 for node, d in zip(nodes, derivatives))


def evaluate_filter(energies):
    coefficients = tuple(F(1, d * e) for d, e in zip(derivatives, energies))
    scale = sum(w * c for w, c in zip(lagrange, coefficients))
    values = tuple(v / scale for v in coefficients)
    assert sum(w * v for w, v in zip(lagrange, values)) == 1
    for power in range(len(nodes) - 1):
        assert sum(e * v * node ** power for e, v, node in zip(energies, values, nodes)) == 0
    return values


def advance(energies, values):
    return tuple(e * v ** 2 for e, v in zip(energies, values))


def harmonic(energies):
    return sum(e / node for e, node in zip(energies, nodes))


def projective_ratios(energies):
    shape = tuple(e * abs(d) for e, d in zip(energies, derivatives))
    return tuple(x / shape[-1] for x in shape)


def verify():
    tau = 1 / sum(map(abs, lagrange))
    assert tau == F(1, 5)
    balanced = tuple(F(1, abs(d)) for d in derivatives)
    optimum = tuple(1 - x + F(x * x, 5) for x in nodes)
    assert optimum == (tau, -tau, tau)
    assert evaluate_filter(balanced) == optimum
    after = advance(balanced, optimum)
    assert harmonic(after) == tau ** 2 * harmonic(balanced)

    previous = (F(1), F(2), F(3))
    warmup = tuple((1 - F(node, 3)) ** 2 for node in nodes)
    current = advance(previous, warmup)
    assert projective_ratios(previous) != (F(1),) * len(nodes)
    for _ in range(6):
        values = evaluate_filter(previous)
        assert tuple(1 if v > 0 else -1 for v in values) == (1, -1, 1)
        following = advance(current, values)
        old_ratios = projective_ratios(previous)
        new_ratios = projective_ratios(current)
        expected = tuple(z / y ** 2 for y, z in zip(old_ratios, new_ratios))
        assert projective_ratios(following) == expected
        weights = tuple(e / node / harmonic(current) for e, node in zip(current, nodes))
        assert harmonic(following) / harmonic(current) == sum(w * v ** 2 for w, v in zip(weights, values))
        previous, current = current, following
    print("Balanced polynomial and factor 1/5 verified.")
    print("Six nonbalanced sweeps: orthogonality, delay, and norm factors verified.")


if __name__ == "__main__":
    verify()
