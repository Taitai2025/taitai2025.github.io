"""Replay the exact rational benchmark and check the interval bounds."""
from fractions import Fraction as F
import json
from pathlib import Path

checks = {}

def expect(label, condition):
    if not condition:
        raise AssertionError(label)
    checks[label] = True

L, c = F(5000), F(101, 100)
G, q, b2, d = (L-c)/2, F(201, 200), F(749851, 120000), F(2250149, 600)
delta = (3*L+c)/(3*L**2+c**2)
theta = F(4, 5)
a1cold = 4/(3*L+c)
lo, hi = F(10097, 10000), F(101, 100)
# Compute the two certificates for eigenvalue bounds without diagonalizing.
polynomial = lambda t: (q-t)*(d-t)-b2
expect("global_lower_bound", F(3,4)+1/(600*(L-1)) < 1)
expect("cold_branch", delta/a1cold < theta)
expect("cold_delta", 1/L < delta < F(2001, 10**7))
expect("eigenvalues_low", polynomial(F(1)) > 0 and polynomial(q) < 0)
expect("eigenvalues_high", d > 3750 and q+d-1 < 3751)
expect("cold_unique_minimum", delta < F(1, 3751))
expect("projection_enclosure", F(156,25)/(3750**2+F(25,4)) > F(44,10**8)
       and F(25,4)/3748**2 < F(45,10**8))
expect("ratio_enclosure", F(45,10**8)/(1-F(45,10**8)) < F(46,10**8))
expect("u1_and_v1", F(999,1000)**2 < 1-F(45,10**8) < 1
       and F(45,10**8) < F(1,1400)**2)
expect("delta_multipliers", 1-F(2001,10**7)*hi > F(9997,10000)
       and 1-F(2001,10**7)*3751 > F(249,1000))
expect("chi_enclosure", F(249,1000)**2 > F(31,500)
       and (F(1,4)/F(9997,10000))**2 < F(63,1000))
expect("ratio_at_z1", F(3751)*F(46,10**8) < F(2,1000)
       and F(1012,1000)**2/(1+3750**2*F(44,10**8)) < theta)
expect("reference_z2", F(31,500)*F(44,10**8) > F(27,10**9)
       and F(63,1000)*F(46,10**8) < F(29,10**9))
expect("ratio_at_z2", F(3751)*F(29,10**9) < F(1,1000)
       and F(1011,1000)**2/(1+3750**2*F(27,10**9)) < theta)
expect("reference_z3", F(63,1000)**2*F(46,10**8) < F(2,10**9))
expect("reference_ratio_at_z3", 1+F(2,10**9) < F(1001,1000)
       and 1+3751**2*F(2,10**9) < F(103,100)
       and 1/(F(1001,1000)*F(103,100)) > theta)
expect("reference_before_stop", F(999,1000)*F(9997,10000)**3 > F(99,100))
expect("reference_terminal_components", 3751*F(2,10**9) < F(1,10**5)
       and F(3751,1400*64) < F(1,20)
       and F(1,10**10)+F(1,400) < F(1,4))
expect("alpha_component_bounds", 1-F(7,50)*hi > F(17,20)
       and 1-F(3,25) < F(9,10)
       and F(3,25)*3750-1 == 449
       and F(7,50)*3751-1 < 525)
expect("alternative_z2", F(44,10**8)*(449/F(9,10))**2 > F(1,10)
       and F(46,10**8)*(525/F(17,20))**2 < F(1,5))
expect("alternative_z3", F(31,500)*F(1,10)>F(6,1000)
       and F(63,1000)*F(1,5)<F(13,1000))
expect("alternative_ratios", F(201,1000)**2/F(1,10)<theta
       and F(14,1000)**2/F(6,1000)<theta)
expect("alternative_lower_norm", F(999,1000)*F(17,20)*F(9997,10000)**3>F(84,100))
expect("all_alt_first_better", q*q+b2<8 and F(7,50)+F(2001,10**7)<F(141,1000)
       and 8*F(141,1000)<2*q)
expect("rho_bounds", F(103,100)*300+F(300**2,48) == 2184<G
       and G<330+F(330**2,48)==F(10395,4))
expect("gated_alpha_range", F(300,2500)==F(3,25) and F(330,2499)<F(7,50))
expect("wider_norm_region", 0<G*delta<1 and G*q/(q*q+b2)>330)

# In the basis (u,b*w), each iterate and Hessian product is rational.
def act(vec):
    a, bscale = vec
    return (q*a-b2*bscale, -a+d*bscale)

def dot(v, w):
    return v[0]*w[0]+b2*v[1]*w[1]

def addstep(vec, alpha):
    hv = act(vec)
    return tuple(x-alpha*y for x,y in zip(vec,hv))

def walk(override=None):
    g = [(F(1), F(0))]
    step_data = []
    history = [delta]
    for k in range(1,5):
        if k == 1:
            a1, a2 = a1cold, delta
        else:
            prev = g[k-2]
            hp = act(prev)
            a1 = dot(prev,prev)/dot(prev,hp)
            a2 = dot(prev,hp)/dot(hp,hp)
            history.append(a2)
        ratio = a2/a1
        step = min(history[max(0,k-10):]) if ratio<theta else a1
        if k==1 and override is not None:
            step=override
        step_data.append({"k":k,"below_threshold":ratio<theta,"uses_cold_delta":step==delta})
        g.append(addstep(g[-1],step))
    return step_data,[dot(x,x) for x in g]

rr,rn=walk()
expect("exact_reference_branches", [e["uses_cold_delta"] for e in rr]==[True,True,True,False])
expect("exact_reference_first_stop", all(v>F(1,4) for v in rn[:4]) and rn[4]<F(1,4))
replays=[]
for alpha in (F(121,1000),F(13,100),F(139,1000)):
    trace,norms=walk(alpha)
    expect(f"alt_branches_{alpha}", [e["uses_cold_delta"] for e in trace]==[False,True,True,True])
    expect(f"alt_no_stop_{alpha}", all(v>F(1,4) for v in norms) and norms[1]<rn[1])
    replays.append({"alpha":str(alpha),"branches":trace,"normalized_squared_norms":[float(v) for v in norms]})

answer={"checks":len(checks),"passing":checks,"reference":{"branches":rr,"normalized_squared_norms":[float(v) for v in rn]},
        "example_alternatives":replays,"scope":"Exact rational assertions; displayed norm decimals are approximate. General envelope proof remains in the paper."}
Path(__file__).with_suffix(".json").write_text(json.dumps(answer,indent=2)+"\n",encoding="utf-8")
print(f"{len(checks)} exact rational assertions passed")

