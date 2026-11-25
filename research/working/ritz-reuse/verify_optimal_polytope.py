"""Exact facet certificate for the optimal historical-Ritz repetition exponent.

Python standard library only.  No floating-point arithmetic enters verification.
Let t be the unique root of t^14-27*t^7+16 in (159/100,8/5).
All vector coordinates are represented in Q[t]/(t^14-27*t^7+16).
Signs are certified by rational interval arithmetic on a bisected root interval;
identically zero remainders are checked exactly.
"""
from fractions import Fraction as F
import json
from pathlib import Path

DEG = 14
ZERO = (F(0),) * DEG


def poly(coeffs):
    v = list(map(F, coeffs))
    v += [F(0)] * max(0, DEG - len(v))
    for k in range(len(v) - 1, DEG - 1, -1):
        v[k - 7] += 27 * v[k]
        v[k - 14] -= 16 * v[k]
    return tuple(v[:DEG])


ONE = poly([1])
X = poly([0, 1])
INVX = poly([0] * 6 + [F(27, 16)] + [0] * 6 + [F(-1, 16)])


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def neg(a):
    return tuple(-x for x in a)


def sub(a, b):
    return add(a, neg(b))


def scale(a, c):
    return tuple(F(c) * x for x in a)


def mul(a, b):
    v = [F(0)] * (2 * DEG - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    v[i + j] += x * y
    return poly(v)


def power(a, k):
    out = ONE
    while k:
        if k & 1:
            out = mul(out, a)
        a = mul(a, a)
        k //= 2
    return out


assert mul(X, INVX) == ONE
RHO = power(X, 7)
SEED = (ONE, scale(sub(scale(ONE, 21), RHO), F(1, 22)))


def action(v, ell):
    inv = power(INVX, ell)
    return (mul(inv, sub(scale(v[0], 3 - 2 * ell), scale(v[1], 2))),
            mul(inv, v[0]))


def vsub(a, b):
    return (sub(a[0], b[0]), sub(a[1], b[1]))


def vneg(a):
    return (neg(a[0]), neg(a[1]))


def cross(a, b):
    return sub(mul(a[0], b[1]), mul(a[1], b[0]))


def f(t):
    return t ** 14 - 27 * t ** 7 + 16


lo, hi = F(159, 100), F(8, 5)
assert f(lo) < 0 < f(hi)
assert 2 * lo ** 7 > 27  # derivative is positive throughout the interval
for _ in range(200):
    mid = (lo + hi) / 2
    if f(mid) < 0:
        lo = mid
    else:
        hi = mid
assert f(lo) < 0 < f(hi)


def imul(a, b):
    candidates = [x * y for x in a for y in b]
    return min(candidates), max(candidates)


def evaluate(p):
    iv = (F(0), F(0))
    for a in reversed(p):
        v = imul(iv, (lo, hi))
        iv = (v[0] + a, v[1] + a)
    return iv


zero_tests = 0
positive_tests = 0
smallest_positive_lower = None


def nonnegative(p, strict=False):
    global zero_tests, positive_tests, smallest_positive_lower
    if p == ZERO:
        assert not strict, "strict inequality reduced exactly to zero"
        zero_tests += 1
        return
    lower, upper = evaluate(p)
    assert lower > 0, ("unresolved or false sign", str(lower), str(upper))
    positive_tests += 1
    if smallest_positive_lower is None or lower < smallest_positive_lower:
        smallest_positive_lower = lower


# Counterclockwise vertices.  A word [1,2] means A_2 A_1 applied to SEED.
SIGNED_WORDS = [
    (-1, [1]), (-1, [1, 2, 1, 2, 1, 1]),
    (1, [1, 2, 1, 1]), (-1, [1, 1]), (1, [1, 2, 1, 2]),
    (-1, [1, 2]), (1, []), (1, [1, 2, 1, 2, 1]),
    (-1, [1, 2, 1]),
    (1, [1]), (1, [1, 2, 1, 2, 1, 1]),
    (-1, [1, 2, 1, 1]), (1, [1, 1]), (-1, [1, 2, 1, 2]),
    (1, [1, 2]), (-1, []), (-1, [1, 2, 1, 2, 1]),
    (1, [1, 2, 1]),
]
vertices = []
for sign, word in SIGNED_WORDS:
    v = SEED
    for ell in word:
        v = action(v, ell)
    vertices.append(v if sign == 1 else vneg(v))

assert len(set(vertices)) == 18
assert all(vertices[j + 9] == vneg(vertices[j]) for j in range(9))
edges = [vsub(vertices[(j + 1) % 18], vertices[j]) for j in range(18)]

# Convexity, strict turns, and an interior origin.
for j, e in enumerate(edges):
    nonnegative(cross(e, edges[(j + 1) % 18]), strict=True)
    nonnegative(cross(e, vneg(vertices[j])), strict=True)
    for v in vertices:
        nonnegative(cross(e, vsub(v, vertices[j])))

# The finite part of the all-count invariance certificate.
for ell in (1, 2, 3):
    for v in vertices:
        image = action(v, ell)
        for j, e in enumerate(edges):
            nonnegative(cross(e, vsub(image, vertices[j])))

# Outer box: P subset [-1,1] x [-2/3,2/3].
for v in vertices:
    for sign in (-1, 1):
        nonnegative(sub(ONE, scale(v[0], sign)))
        nonnegative(sub(scale(ONE, F(2, 3)), scale(v[1], sign)), strict=True)

# Inner box: [-1,1] x [-6/25,6/25] subset P.
for sx in (-1, 1):
    for sy in (-1, 1):
        corner = (scale(ONE, sx), scale(ONE, F(6, 25) * sy))
        for j, e in enumerate(edges):
            nonnegative(cross(e, vsub(corner, vertices[j])))

# Tail ell>=4.  (2*ell-3+4/3)/t^ell and t^-ell decrease.
tmin = F(159, 100)
assert F(19, 3) / tmin ** 4 < 1
assert 1 / tmin ** 4 < F(6, 25)
assert F(25, 19) < tmin

# Attainment: A_3 A_1 A_2 A_1 SEED = SEED.
v = SEED
for ell in (1, 2, 1, 3):
    v = action(v, ell)
assert v == SEED

result = {
    "status": "verified_exactly",
    "arithmetic": "Python fractions; quotient-polynomial identities and rational interval signs",
    "defining_polynomial": "t^14 - 27*t^7 + 16",
    "root_interval_lower": str(lo),
    "root_interval_upper": str(hi),
    "root_unique_in": ["159/100", "8/5"],
    "vertices": len(vertices),
    "tested_counts": [1, 2, 3],
    "all_counts_ge_four": "outer-box to inner-box rational inequalities and monotonicity",
    "strict_positive_checks": positive_tests,
    "exact_zero_checks": zero_tests,
    "smallest_positive_lower_bound": str(smallest_positive_lower),
    "attaining_word": [1, 2, 1, 3],
    "signed_vertex_words": SIGNED_WORDS,
}
out = Path(__file__).with_name("optimal_polytope_facet_certificate.json")
out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(json.dumps({k: result[k] for k in (
    "status", "vertices", "strict_positive_checks", "exact_zero_checks",
    "attaining_word"
)}))
