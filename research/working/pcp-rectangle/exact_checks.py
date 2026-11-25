"""Exact finite checks of the scalar interval simplification. No solver or floats."""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json,platform
ROOT=Path(__file__).resolve().parent

def four_tests(p,T,a,b,s,t):
    d=s*t-1
    return (d*d<=F((p-a)*(T-b),a*b)
        and abs(1-d*F(b,T-b))<=t
        and abs(1-d*F(a,p-a))<=t
        and abs(1+d*F(a*b,(p-a)*(T-b)))<=t)

def interval_tests(p,T,a,b,s,t):
    h=F((p-a)*(T-b),a*b)
    if s==1:
        if a*T+b*p>p*T:return t==1
        return (t>=1 and (t-1)**2<=h
            and (2*a<=p or t<=F(p,2*a-p))
            and (2*b<=T or t<=F(T,2*b-T)))
    if 2*a>=p or 2*b>=T:return False
    return t>=max(F(p,p-2*a),F(T,T-2*b)) and (t+1)**2<=h

count=0;valid=0;domains=0
for p in range(2,10):
 for T in range(2,10):
  for a in range(1,p):
   for b in range(1,T):
    values={F(k,10) for k in range(1,61)}|{F(99,100),F(101,100)}
    for n,m in [(p,a),(T,b)]:
     if 2*m!=n:
      edge=F(n,abs(n-2*m));values|={edge,edge*F(99,100),edge*F(101,100)}
    for s in [1,-1]:
     domains+=1
     for t in sorted(values):
      raw=four_tests(p,T,a,b,s,t);closed=interval_tests(p,T,a,b,s,t)
      assert raw==closed,(p,T,a,b,s,str(t),raw,closed)
      count+=1;valid+=raw
result={'version':'1.0','date':'2026-11-25','python':platform.python_version(),
 'arithmetic':'Python fractions.Fraction; all comparisons exact',
 'scope':'Finite comparison of four scalar inequalities with closed bright/dark intervals; no infinite-domain or full-matrix proof',
 'p_and_T':[2,9],'geometries_with_sign':domains,'checked_points':count,'feasible_points':valid,
 'mismatches':0,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'exact_checks.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,ensure_ascii=False))