from fractions import Fraction as Q

SPECTRUM = tuple(map(Q, (1, 2, 3)))

def determinant(p, s):
    a, b, c = [sum((x*x * (l-s) * l**j for x, l in zip(p, SPECTRUM)), Q(0))
               for j in range(3)]
    return a*c - b*b

def check(e):
    u = (e, e**2, Q(1))
    denominator = determinant(u, Q(0))
    assert denominator > 0
    d = 6 + 3*e**2 + e**4
    predicted = (e**2/d, -2/d, e**4/d)
    actual = tuple(determinant(u, t) / denominator for t in SPECTRUM)
    assert predicted == actual
    warm_end = tuple(x * (1-l/3)**2 for x, l in zip(u, SPECTRUM))
    post_sweep = tuple(g*m for g, m in zip(warm_end, actual))
    assert post_sweep == (4*e**3/(9*d), -2*e**2/(9*d), Q(0))
    return actual

expected = {
    Q(1): (Q(1,10), Q(-1,5), Q(1,10)),
    Q(1,10): (Q(100,60301), Q(-20000,60301), Q(1,60301)),
    Q(1,100): (Q(10000,600030001), Q(-200000000,600030001), Q(1,600030001)),
}

if __name__ == "__main__":
    for epsilon, reference in expected.items():
        value = check(epsilon)
        assert value == reference, (epsilon, value, reference)
        print(epsilon, *(str(v) for v in value))
