"""Independent small tests for the public static-rectangle PCP working draft.
All new outputs stay in this directory; original report outputs are untouched.
"""
from pathlib import Path
import numpy as np, json, csv, hashlib, platform
ROOT=Path(__file__).resolve().parent

def bounds(p,T,a,b,sign):
    lm=1/np.sqrt(p*T); omega=np.sqrt((1-a/p)*(1-b/T)/(a*b))
    if sign>0:
        if a/p+b/T>1:return lm,lm
        hi=lm+omega
        if 2*b>T:hi=min(hi,lm*T/(2*b-T))
        if 2*a>p:hi=min(hi,lm*p/(2*a-p))
        return lm,hi
    if 2*a>=p or 2*b>=T:return np.inf,-np.inf
    return lm*max(T/(T-2*b),p/(p-2*a)),omega-lm

def certificate(p,T,a,b,sign,lam):
    lm=1/np.sqrt(p*T); d=sign*lam-lm
    x=np.r_[np.ones(a),np.zeros(p-a)]-a/p
    y=np.r_[np.ones(b),np.zeros(T-b)]-b/T
    W=d*np.outer(x,y)/((1-a/p)*(1-b/T));Q=lm+W
    support=np.zeros((p,T),bool);support[:a,:b]=True
    om=np.sqrt((1-a/p)*(1-b/T)/(a*b))
    vals=[lm-d*b/(T-b),lm-d*a/(p-a),lm+d*a*b/((p-a)*(T-b))]
    computed=np.linalg.norm(W,2)
    assert abs(computed-abs(d)/om)<1e-12
    return dict(spectral_norm=float(computed),off_support_excess=float(np.max(np.abs(Q[~support]))-lam),
                support_error=float(np.max(np.abs(Q[support]-sign*lam))),
                row_sum=float(np.max(np.abs(W.sum(1)))),column_sum=float(np.max(np.abs(W.sum(0)))),
                scalar_off_support_excess=float(max(map(abs,vals))-lam))

def svt(A,t):
    U,s,V=np.linalg.svd(A,full_matrices=False)
    return (U*np.maximum(s-t,0))@V

def solve(M,lam,max_iter=50000,tol=1e-10):
    L=np.zeros_like(M);S=L.copy();Y=L.copy();rho=1.
    scale=max(1.,np.linalg.norm(M));converged=False
    for k in range(1,max_iter+1):
        old=S.copy();L=svt(M-S-Y/rho,1/rho)
        V=M-L-Y/rho;S=np.sign(V)*np.maximum(np.abs(V)-lam/rho,0)
        r=L+S-M;Y+=rho*r;d=rho*(S-old)
        if max(np.linalg.norm(r),np.linalg.norm(d))<=tol*scale:
            converged=True;break
    feasibleS=M-L
    upper=np.linalg.svd(L,compute_uv=False).sum()+lam*np.abs(feasibleS).sum()
    Q=-Y;Q/=max(1.,np.linalg.norm(Q,2),np.abs(Q).max()/lam)
    lower=float(np.sum(M*Q))
    return L,feasibleS,dict(iterations=k,converged=converged,primal=float(np.linalg.norm(r)),dual=float(np.linalg.norm(d)),feasible_objective=float(upper),dual_bound=lower,gap=float(upper-lower))

results=[]
for sign,a,b in [(1,4,6),(1,4,16),(-1,2,4)]:
    p,T=24,20;lo,hi=bounds(p,T,a,b,sign)
    for tag,lam in [('below',.98*lo),('interior',(lo+hi)/2),('above',1.02*hi)]:
        L0=.5*np.ones((p,T));S0=np.zeros((p,T));S0[:a,:b]=sign*.25;M=L0+S0
        F0=np.linalg.svd(L0,compute_uv=False).sum()+lam*np.abs(S0).sum()
        L,S,r=solve(M,lam)
        r.update(sign=sign,p=p,T=T,a=a,b=b,location=tag,lam=float(lam),lower=float(lo),upper=float(hi),
            target_objective=float(F0),target_minus_feasible=float(F0-r['feasible_objective']),
            relative_L_error=float(np.linalg.norm(L-L0)/np.linalg.norm(L0)),certificate=certificate(p,T,a,b,sign,lam))
        assert r['converged']
        assert r['gap']>=-1e-9 and r['gap']<2e-7
        if tag=='interior':
            assert r['relative_L_error']<1e-6
            assert r['certificate']['spectral_norm']<1 and r['certificate']['off_support_excess']<0
        else:assert r['target_minus_feasible']>1e-6
        results.append(r)

# Degenerate bright case: a/p+b/T>1 has only lambda_min.
p,T,a,b=12,10,8,7;lm=1/np.sqrt(p*T)
degenerate=[certificate(p,T,a,b,1,lam) for lam in [.98*lm,lm,1.02*lm]]
assert degenerate[1]['off_support_excess']<1e-12
assert degenerate[0]['off_support_excess']>0 and degenerate[2]['off_support_excess']>0

# Independent scalar rank-one price check; no matrix PCP optimality claim here.
scalar_checks=[]
for a in [1,2,17,104]:
    for b in [1,9,60,120]:
        for fac in [.8,1,1.2]:
            lam=fac/np.sqrt(a*b)
            left=lam*np.sqrt(a*b)<=1+1e-14
            right=lam*lam*a*b<=1+1e-14
            assert left==right
            scalar_checks.append([a,b,float(lam),left])
out=dict(date='2026-11-25',version='1.0-public-working-draft',script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),python=platform.python_version(),numpy=np.__version__,
    test_scope='fresh independent 24x20 ADMM solves and explicit certificate checks; not a rerun of original video experiments',
    cases=results,degenerate_bright=degenerate,scalar_checks=len(scalar_checks))
(ROOT/'verification.json').write_text(json.dumps(out,ensure_ascii=False,indent=2),encoding='utf-8')
with (ROOT/'verification.csv').open('w',newline='',encoding='utf-8-sig') as f:
    keys=['sign','a','b','location','lam','iterations','relative_L_error','target_minus_feasible','gap'];w=csv.DictWriter(f,keys,extrasaction='ignore');w.writeheader();w.writerows(results)
lines=[]
for r in results:
    name='亮' if r['sign']>0 else '暗';loc={'below':'低于下界','interior':'区间内部','above':'高于上界'}[r['location']]
    lines.append(f"{name} & {r['a']},{r['b']} & {loc} & {r['lam']:.6f} & {r['iterations']} & {r['relative_L_error']:.2e} & {r['target_minus_feasible']:.2e} \\")
(ROOT/'verification_rows.tex').write_text('\\newcommand{\\verificationRows}{%\n'+'\n'.join(x+'\\' for x in lines)+'\n}\n',encoding='utf-8')
print(json.dumps({'solves':len(results),'max_gap':max(r['gap'] for r in results),'max_interior_relative_error':max(r['relative_L_error'] for r in results if r['location']=='interior'),'iterations':[r['iterations'] for r in results]},ensure_ascii=False))
