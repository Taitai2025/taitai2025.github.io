#!/usr/bin/env python3
"""Exact rational-interval certificate for the optimal reuse polytope.

No floating-point calculation is used in any assertion.  The optional printed
decimal approximations are for reading the certificate only.  Run with Python's
standard library; the output JSON lists rational outward enclosures for every
nonvertex image.  This is independent of the independent facet verifier.
"""
from fractions import Fraction as F
from dataclasses import dataclass
import json
from pathlib import Path


@dataclass(frozen=True)
class I:
    lo: F
    hi: F

    @staticmethod
    def point(a):
        return I(F(a), F(a))

    def __add__(self, b):
        b = as_i(b)
        return I(self.lo + b.lo, self.hi + b.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, b):
        return self + (-as_i(b))

    def __rsub__(self, b):
        return as_i(b) + (-self)

    def __mul__(self, b):
        b = as_i(b)
        vals = [self.lo*b.lo, self.lo*b.hi, self.hi*b.lo, self.hi*b.hi]
        return I(min(vals), max(vals))

    __rmul__ = __mul__

    def __truediv__(self, b):
        b = as_i(b)
        assert not (b.lo <= 0 <= b.hi), "division interval includes zero"
        return self * I(1/b.hi, 1/b.lo)

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        out = I.point(1)
        for _ in range(n):
            out = out * self
        return out


def as_i(a):
    return a if isinstance(a, I) else I.point(a)


def det(a, b):
    return a[0]*b[1] - a[1]*b[0]


def neg(v):
    return [-v[0], -v[1]]


def image(v, ell, theta):
    scale = theta**ell
    return [((3-2*ell)*v[0] - 2*v[1])/scale, v[0]/scale]


def p(t):
    return t**14 - 27*t**7 + 16


def enclosing_ten_thousandths(interval):
    """Integers a,b prove a/10000 < value < b/10000."""
    a = (interval.lo*10000).numerator // (interval.lo*10000).denominator
    b0 = interval.hi*10000
    b = -((-b0.numerator)//b0.denominator)
    assert F(a, 10000) <= interval.lo <= interval.hi <= F(b, 10000)
    return [a, b]


def main():
    lo = F(1596142626220053845095031259714, 10**30)
    hi = F(1596142626220053845095031259715, 10**30)
    assert p(lo) < 0 < p(hi)
    assert lo > F(159,100) and hi < F(8,5)
    # p'(t)=7t^6(2t^7-27)>0 here. This selects the larger positive root
    # theta=((27+sqrt665)/2)^(1/7), not the much smaller positive root.
    assert 2*lo**7 > 27
    theta = I(lo, hi)
    rho = theta**7
    # v_i=(a+b*rho,c+d*rho)/(22*theta^cost).
    data = [
        (0,22,0,21,-1),
        (1,-20,2,22,0),
        (3,-24,-2,-20,2),
        (4,16,-6,-24,-2),
        (6,32,10,16,-6),
        (7,0,22,32,10),
        (8,-64,2,0,22),
        (2,-64,2,-20,2),
        (5,64,-2,16,-6),
    ]
    vertices = [
        [(a+b*rho)/(22*theta**c), (d+e*rho)/(22*theta**c)]
        for c,a,b,d,e in data
    ]
    # x(v0)=x(v5)=1 exactly; using these identities sharpens dependency
    # overestimation in the otherwise outward interval arithmetic.
    vertices[0][0] = I.point(1)
    vertices[5][0] = I.point(1)
    for v in vertices:
        assert v[0].lo >= -1 and v[0].hi <= 1
        assert v[1].lo > -F(2,3) and v[1].hi < F(2,3)
    # The segments at x=1 and x=-1 contain [-6/25,6/25].
    assert vertices[0][1].hi < -F(6,25)
    assert vertices[5][1].lo > F(6,25)

    # The nine exact vertex identities. All but (3,3)->0 follow by
    # multiplying the displayed integer-linear numerators; that last
    # identity uses rho^2-27rho+16=0.
    exact = [
        (0,1,1),(1,1,7),(1,2,2),(2,1,3),(3,1,8),
        (3,2,4),(3,3,0),(4,1,5),(5,1,6),
    ]

    def linear_num(i):
        cost,a,b,c,d = data[i]
        return cost, (a,b), (c,d)

    for i,ell,j in exact:
        ci,xi,yi = linear_num(i)
        cj,xj,yj = linear_num(j)
        outx = ((3-2*ell)*xi[0]-2*yi[0],
                (3-2*ell)*xi[1]-2*yi[1])
        outy = xi
        if ci+ell == cj:
            assert outx == xj and outy == yj
        else:
            assert (i,ell,j)==(3,3,0) and ci+ell-cj==7
            # rho*(a+b*rho)=(16*(-b))+(a+27*b)*rho.
            times_rho = lambda u: (-16*u[1],u[0]+27*u[1])
            assert outx == times_rho(xj) and outy == times_rho(yj)

    # i,ell; each signed pair spans a triangle with the origin.
    triangles = [
        (0,2,7,1,4,-1),(0,3,2,1,0,-1),(1,3,0,-1,5,-1),
        (2,2,8,1,7,-1),(2,3,4,1,2,-1),
        (4,2,6,1,8,-1),(4,3,7,1,4,-1),
        (5,2,7,1,4,-1),(5,3,2,1,0,-1),
        (6,1,0,-1,5,-1),(6,2,0,-1,5,-1),(6,3,0,-1,5,-1),
        (7,1,0,-1,5,-1),(7,2,0,-1,5,-1),(7,3,0,-1,5,-1),
        (8,1,0,1,5,1),(8,2,0,1,5,1),(8,3,0,1,5,1),
    ]
    covered = {(i,ell) for i,ell,_ in exact}
    cert = []
    for i,ell,j,sj,k,sk in triangles:
        assert (i,ell) not in covered
        covered.add((i,ell))
        z = image(vertices[i],ell,theta)
        a = vertices[j] if sj==1 else neg(vertices[j])
        b = vertices[k] if sk==1 else neg(vertices[k])
        denom = det(a,b)
        assert denom.lo > 0
        alpha = det(z,b)/denom
        beta = det(a,z)/denom
        assert alpha.lo > 0 and beta.lo > 0
        assert alpha.hi + beta.hi < 1
        ai,bi = enclosing_ten_thousandths(alpha),enclosing_ten_thousandths(beta)
        assert ai[0] > 0 and bi[0] > 0 and ai[1]+bi[1] < 10000
        cert.append(dict(vertex=i,repetition=ell,
                         triangle=[[j,sj],[k,sk]],
                         alpha_times_10000=ai,beta_times_10000=bi))
    assert covered=={(i,ell) for i in range(9) for ell in (1,2,3)}

    # All ell>=4 map the containing rectangle into the contained one.
    base = F(159,100)
    assert F(19,3)/base**4 < 1
    assert 1/base**4 < F(6,25)
    # The ratio of consecutive horizontal bounds is largest at ell=4.
    assert F(25,19) < base
    payload = {
        "status":"all_exact_rational_assertions_passed",
        "root_interval":[str(lo),str(hi)],
        "root_polynomial":"theta^14-27 theta^7+16",
        "vertices":"(a+b*rho,c+d*rho)/(22*theta^cost); rho=theta^7",
        "vertex_data":[list(x) for x in data],
        "exact_images":exact,
        "interior_triangle_certificates":cert,
        "matrix_family":"M_ell=[[3-2ell,-2],[1,0]], A_ell=theta^(-ell) M_ell",
        "all_large_counts":"ell>=4: rectangle argument using theta>159/100",
        "conclusion":"A_ell P subset P for every positive integer ell",
    }
    out = Path(__file__).with_suffix(".json")
    out.write_text(json.dumps(payload,indent=2)+"\n")
    print(json.dumps({
        "status":payload["status"],"exact_vertex_images":len(exact),
        "strict_triangle_images":len(cert),
        "all_positive_integer_counts":True,"output":str(out),
    },indent=2))


if __name__ == "__main__":
    main()
