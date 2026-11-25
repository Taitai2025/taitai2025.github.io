"""Exact algebra for the alternating-penalty quadratic ADMM note."""
import json
from pathlib import Path
import sympy as s

k = s.Symbol("k", positive=True)
I = s.eye(2)
Q = s.diag(1, k)
R = s.Matrix([[1 + k, k - 1], [k - 1, 1 + k]]) / 2


def transition(penalty):
    return (R + penalty * I).inv() * (Q + penalty * I).inv() * (penalty**2 * I + Q*R)


first, last = transition(1), transition(k)
expected_first = s.Matrix([
    [-k**3 + 11*k**2 + 13*k + 9, -(k-1)**3],
    [(k-1)**2*(k+3), k**3 + 9*k**2 + 11*k + 11],
]) / (16*(k+1)**2)
expected_last = s.Matrix([
    [11*k**3 + 11*k**2 + 9*k + 1, -(k-1)**2*(3*k+1)],
    [-(k-1)**3, 9*k**3 + 13*k**2 + 11*k - 1],
]) / (16*k*(k+1)**2)
assert all(s.cancel(x) == 0 for x in first-expected_first)
assert all(s.cancel(x) == 0 for x in last-expected_last)

second_eigenvalue = (3*k**2 + 2*k + 3)/(4*(k+1)**2)
for matrix in (first,last):
    assert s.cancel(s.trace(matrix) - s.Rational(1,2) - second_eigenvalue) == 0
    assert s.cancel(matrix.det() - second_eigenvalue/2) == 0

period = last * first
actual_trace = s.factor(s.trace(period))
actual_det = s.factor(period.det())
expect_trace = (-k**4+52*k**3+26*k**2+52*k-1)/(64*k*(k+1)**2)
expect_det = (3*k**2+2*k+3)**2/(64*(k+1)**4)
assert s.cancel(actual_trace-expect_trace) == 0
assert s.cancel(actual_det-expect_det) == 0

def F(x):
    return x**3 - 123*x**2 - 400*x - 316

at_one = (k**2+6*k+1)*(k**4+17*k**3+36*k**2+17*k+1)/(64*k*(k+1)**4)
assert s.cancel(1-expect_trace+expect_det-at_one) == 0
assert s.cancel(1+expect_trace+expect_det+k**3*F(k+1/k)/(64*k*(k+1)**4)) == 0
assert F(s.Rational(126)+s.Rational(1,126)) < 0 < F(s.Rational(127)+s.Rational(1,127))
exact = [actual_trace.subs(k,199),actual_det.subs(k,199),(1+actual_trace+actual_det).subs(k,199)]
assert exact == [-s.Rational(14467601,6368000),s.Rational(888099601,6400000000),-s.Rational(1443188379401,1273600000000)]
result = {
    "symbolic_equalities_checked": 10,
    "trace_at_199": str(exact[0]),
    "determinant_at_199": str(exact[1]),
    "characteristic_at_minus_one_at_199": str(exact[2]),
    "threshold_bracket": [126,127],
    "sympy_version": s.__version__,
}
Path("交替罚参数-精确复算.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
