"""Independent synthetic checks for PCP equivalences; no original project imports or data.
Run: python -B verify_equivalences.py. All outputs stay beside this file.
These floating-point checks are regression evidence, not interval certificates.
"""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
os.environ.setdefault('MKL_NUM_THREADS','1')
from pathlib import Path
import json, platform, hashlib
import numpy as np
BASE=Path(__file__).resolve().parent
RNG=np.random.default_rng(20261125)
records=[]
def record(name, value, tolerance, **details):
    value=float(value)
    ok=np.isfinite(value) and value <= tolerance
    records.append(dict(name=name,value=value,tolerance=tolerance,passed=bool(ok),**details))
    assert ok,(name,value,tolerance)
def rel(A,B):
    scale=max(float(np.max(np.abs(A))),float(np.max(np.abs(B))),1e-300)
    return np.linalg.norm((A-B)/scale)/max(np.linalg.norm(B/scale),1.)
def soft(A,t): return np.sign(A)*np.maximum(np.abs(A)-t,0.)
def svt(A,t):
    if t==0:return A.copy()
    U,s,V=np.linalg.svd(A,full_matrices=False)
    return (U*np.maximum(s-t,0))@V
def gram(A,t):
    """Independent guarded Gram implementation; guard is heuristic, not certified."""
    if t==0:return A.copy(),'zero-threshold'
    if not np.any(A):return A.copy(),'zero-matrix'
    with np.errstate(over='ignore',under='ignore',invalid='ignore'):
        G=A.T@A if A.shape[0]>=A.shape[1] else A@A.T
    if not np.isfinite(G).all() or np.max(np.abs(np.diag(G)))<np.finfo(float).tiny:
        return svt(A,t),'full-range'
    d,V=np.linalg.eigh(G/2+G.T/2)
    delta=100*np.finfo(float).eps*max(A.shape)*np.linalg.norm(G,2)
    s=np.sqrt(np.maximum(d,0))
    with np.errstate(over='ignore'):
        near=np.any((d-delta<=t*t)&(d+delta>=t*t))
    if np.min(d)<-delta or near:return svt(A,t),'full-threshold'
    active=s>t
    W=V[:,active]; z=1-t/s[active]
    X=((A@W)*z)@W.T if A.shape[0]>=A.shape[1] else (W*z)@(W.T@A)
    return X,'gram'
def nuc(A):return float(np.linalg.svd(A,compute_uv=False).sum())
def prox_huber(V,eta,lam,rho):
    if eta==0:return soft(V,lam/rho)
    threshold=lam*(eta+1/rho)
    return np.where(np.abs(V)<=threshold,rho*eta/(1+rho*eta)*V,V-lam/rho*np.sign(V))
def gradient_huber_L(L,D,eta,lam):return np.clip((L-D)/eta,-lam,lam)
def iterate(D,L,Z,u,lam,rho,alpha=1.,eta=0.):
    Ln=svt(D-Z-u,1/rho)
    hat=alpha*Ln+(1-alpha)*(D-Z)
    Zn=prox_huber(D-hat-u,eta,lam,rho)
    un=u+hat+Zn-D
    return Ln,Zn,un

def bounds(D,L,u,lam,rho):
    Y=rho*u
    Q=-Y/max(1.,np.linalg.norm(Y,2),np.max(np.abs(Y))/lam)
    lo=float(np.sum(Q*D)); hi=nuc(L)+lam*np.sum(np.abs(D-L))
    return lo,float(hi)
def solve(D,lam,rho=.8):
    L=np.zeros_like(D); Z=L.copy();u=L.copy()
    for it in range(1,200001):
        L,Z,u=iterate(D,L,Z,u,lam,rho)
        if it%20==0:
            lo,hi=bounds(D,L,u,lam,rho)
            if np.linalg.norm(L+Z-D)<=1e-9*max(1,np.linalg.norm(D)) and hi-lo<=1e-8*max(1,hi):break
    else:raise RuntimeError(str((it,lam,lo,hi,hi-lo,np.linalg.norm(L+Z-D))))
    return L,Z,u,it,lo,hi

for shape in [(31,7),(7,31),(9,9)]:
    A=RNG.normal(size=shape)
    for t in [0.,.1,1.,100.]:
        X,mode=gram(A,t)
        record('gram_'+str(shape)+'_'+str(t),rel(X,svt(A,t)),2e-11,mode=mode)
for name,A,t in [
 ('rank_deficient',np.diag([3.,1.,0.,0.]),.5),
 ('threshold',np.diag([3.,1.+1e-13,1.-1e-13]),1.),
 ('zero',np.zeros((6,3)),1.),
 ('underflow',np.diag([3e-200,1e-200]),1e-200),
 ('overflow',np.diag([3e200,1e200]),1e200),
 ('ill_conditioned',np.diag([3.,1e-5,1e-12]),1e-6)]:
    X,mode=gram(A,t);record('gram_'+name,rel(X,svt(A,t)),2e-11,mode=mode)
A=np.diag([5.,2.,.1]);W=np.eye(3)[:,1:];s=np.array([2.,.1])
record('omitted_spectrum_triplet_residual',np.linalg.norm(A@W-W*s),1e-15)
X=(W*np.maximum(s-1,0))@W.T
record('omitted_spectrum_error_is_four',abs(np.linalg.norm(X-svt(A,1))-4),1e-15)

for eta in [.03,.4,3.]:
 for lam in [.07,.9]:
  for rho in [.1,2.,9.]:
   V=np.linspace(-3,3,121)
   Z=prox_huber(V,eta,lam,rho)
   S=soft(V,lam*(eta+1/rho));E=rho*eta/(1+rho*eta)*(V-S)
   record('huber_split',np.linalg.norm(S+E-Z),1e-12,eta=eta,lam=lam,rho=rho)
   record('huber_stationarity',np.max(np.abs(np.clip(Z/eta,-lam,lam)+rho*(Z-V))),1e-12)
for alpha in [.5,1.,1.6,1.95]:
 for eta in [0.,.2]:
  D=RNG.normal(size=(13,5));L=RNG.normal(size=D.shape);Z=RNG.normal(size=D.shape);u=RNG.normal(size=D.shape)
  lam=.4;rho=.8
  Ln,Zn,un=iterate(D,L,Z,u,lam,rho,alpha,eta)
  r=Ln+Zn-D; delta=Zn-Z; Y=rho*un
  d=rho*((alpha-1)*r+(2-alpha)*delta)
  record('relaxed_L_inclusion',rel(Ln,svt(Ln-Y+d,1)),1e-12,alpha=alpha,eta=eta)
  record('relaxed_Z_inclusion',rel(Zn,prox_huber(Zn-Y,eta,lam,1.)),1e-12)
  record('relaxed_two_forms',np.linalg.norm(d-rho*((alpha-1)*(Ln+Z-D)+delta)),1e-12)

eta=.7;lam=1.3
for trial in range(12):
 L0=RNG.uniform(-.2,.2,30);L1=RNG.uniform(-.2,.2,30)
 L0[10:20]+=2.;L1[10:20]+=2.;L0[20:]-=2.;L1[20:]-=2.
 s=L1-L0;y=gradient_huber_L(L1,0,eta,lam)-gradient_huber_L(L0,0,eta,lam)
 BB1=s@s/(s@y);BB2=s@y/(y@y)
 record('BB_fixed_branch_BB2',abs(BB2-eta),1e-12)
 record('BB_fixed_branch_BB1',abs(BB1-eta*(s@s)/(s[:10]@s[:10])),1e-12)
for trial in range(100):
 L0=RNG.normal(size=40)*2;L1=RNG.normal(size=40)*2
 s=L1-L0;y=gradient_huber_L(L1,0,eta,lam)-gradient_huber_L(L0,0,eta,lam)
 BB1=s@s/(s@y);BB2=s@y/(y@y)
 record('BB_crossing_bounds',max(eta-BB2,BB2-BB1,0.),1e-12)

D=RNG.normal(size=(20,2))@RNG.normal(size=(2,8)); sparse=RNG.random(D.shape)<.12
D=D+RNG.choice([-2.,2.],size=D.shape)*sparse
lam=.19
repeat=lambda A,k:np.tile(A,(1,k))
for k in [2,3,7]:
 DD=repeat(D,k);L=RNG.normal(size=DD.shape);S=DD-L
 Lbar=sum(np.hsplit(L,k))/k;Sbar=sum(np.hsplit(S,k))/k
 before=nuc(L)+lam*np.sum(np.abs(S));after=nuc(repeat(Lbar,k))+lam*np.sum(np.abs(repeat(Sbar,k)))
 record('repeat_symmetrization',max(0,after-before),1e-10,k=k)
 record('repeat_nuclear',abs(nuc(repeat(Lbar,k))-np.sqrt(k)*nuc(Lbar)),1e-10,k=k)
 for alpha in [1.,1.6]:
  bL=np.zeros_like(D);bZ=bL.copy();bu=bL.copy();rL=np.zeros_like(DD);rZ=rL.copy();ru=rL.copy()
  for j in range(40):
   bL,bZ,bu=iterate(D,bL,bZ,bu,np.sqrt(k)*lam,np.sqrt(k)*.8,alpha)
   rL,rZ,ru=iterate(DD,rL,rZ,ru,lam,.8,alpha)
  err=max(rel(rL,repeat(bL,k)),rel(rZ,repeat(bZ,k)),rel(ru,repeat(bu,k)))
  record('repeat_ADMM_covariance',err,1e-10,k=k,alpha=alpha,steps=40)
 bL,bZ,bu,bi,blo,bhi=solve(D,np.sqrt(k)*lam)
 rL,rZ,ru,ri,rlo,rhi=solve(DD,lam)
 gapscale=max(1,rhi)
 record('repeat_optimal_value',abs(rhi-np.sqrt(k)*bhi)/gapscale,3e-8,k=k,base_iterations=bi,repeated_iterations=ri,base_bounds=[blo,bhi],repeated_bounds=[rlo,rhi])
 record('repeat_interval_overlap',max(rlo-np.sqrt(k)*bhi,np.sqrt(k)*blo-rhi,0.)/gapscale,1e-11,k=k)

out=dict(version='1.0',date='2026-11-25',seed=20261125,python=platform.python_version(),numpy=np.__version__,claims='Floating point verification of independent synthetic examples, not formal or interval proofs.',checks=len(records),passed=all(x['passed'] for x in records),records=records)
(BASE/'evidence'/'synthetic_checks.json').write_text(json.dumps(out,ensure_ascii=False,indent=2),encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k!='records'},ensure_ascii=False))
print('Max Gram relative error',max(x['value'] for x in records if x['name'].startswith('gram_')))
print('Max repeated ADMM error',max(x['value'] for x in records if x['name']=='repeat_ADMM_covariance'))


