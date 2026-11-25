"""Exact short-word enumeration and Fourier checks. No files outside --out.

python word_dependence.py --out output --max-length 12
No stochastic experiment or word-performance tuning is performed.
"""
import argparse
import csv
import hashlib
import json
import platform
import sys
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import numpy as np
import mpmath as mp


def write_csv(path,rows):
    with path.open("w",newline="",encoding="utf-8") as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)


def response(word):
    """Solve the 2x2 affine return map in rational arithmetic, not an FFT."""
    prev=(0,1,0);cur=(1,0,0)
    for s in word:
        nxt=tuple(cur[i]-2*prev[i]+(2*int(s) if i==2 else 0) for i in range(3))
        prev,cur=cur,nxt
    a,b,x=1-cur[0],-cur[1],cur[2]
    d,e,y=-prev[0],1-prev[1],prev[2]
    det=a*e-b*d
    cur=F(x*e-b*y,det);prev=F(a*y-x*d,det)
    initial=(cur,prev);seq=[]
    for s in word:
        seq.append(cur);prev,cur=cur,cur-2*prev+2*int(s)
    assert (cur,prev)==initial
    L=len(word)
    r=[1-seq[(j-1)%L]+int(s) for j,s in enumerate(word)]
    assert sum(r)==L
    for j,s in enumerate(word):
        assert seq[(j+1)%L]-seq[j]+2*seq[(j-1)%L]==2*int(s)
    return seq,r,sum((x-1)**2 for x in r)/L


def primitive(word):
    L=len(word)
    return all(word!=word[:d]*(L//d) for d in range(1,L) if L%d==0)


def representative(word):
    return min(word[j:]+word[:j] for j in range(len(word)))


def switches(word):
    return sum(word[j]=="1" and word[(j+1)%len(word)]=="0" for j in range(len(word)))


def fourier_variance(word):
    L=len(word);omega=2*np.pi*np.arange(L)/L
    transform=np.fft.fft(np.array(list(map(int,word)),dtype=float))/L
    c=np.cos(omega)
    multiplier=(1-c)/(1-3*c+4*c*c)
    return float(np.sum(multiplier[1:]*abs(transform[1:])**2))


def endpoint_factor(word,C):
    _,r,_=response(word);k=(1+C)/(1-C)
    return (k-1)*mp.exp(-sum(mp.log(1+k**(mp.mpf(x.numerator)/x.denominator)) for x in r)/len(r))


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--out",default="output");ap.add_argument("--max-length",type=int,default=12)
    args=ap.parse_args();out=Path(args.out);out.mkdir(parents=True,exist_ok=True)
    rows=[];counts=[];maxerr=0.
    for L in range(2,args.max_length+1):
        n=0
        for bits in product("01",repeat=L):
            word="".join(bits)
            if not primitive(word) or representative(word)!=word:continue
            a,r,v=response(word);numeric=fourier_variance(word)
            err=abs(float(v)-numeric);maxerr=max(maxerr,err)
            assert err<1e-13
            t=switches(word)
            assert F(t,16*L)<=v/2<=F(8*t,7*L)
            # Independent symmetries: complement and reversal preserve variance.
            assert response("".join("1" if s=="0" else "0" for s in word))[2]==v
            assert response(word[::-1])[2]==v
            rows.append(dict(L=L,word=word,ones=word.count("1"),boundaries_10=switches(word),
                             boundary_density=str(F(switches(word),L)),
                             a=";".join(map(str,a)),r=";".join(map(str,r)),
                             variance=str(v),cubic_coefficient=str(v/2),
                             fourier_variance=numeric,fourier_abs_error=err))
            n+=1
        counts.append(dict(L=L,primitive_rotation_classes=n))
    write_csv(out/"word_responses.csv",rows);write_csv(out/"enumeration_counts.csv",counts)
    examples=[]
    for pair,left,right in (("same_length_density_balance","00010111","00100111"),
                            ("more_switches_smaller_coefficient","000111","001011")):
        a,r,v=response(left);aa,rr,vv=response(right)
        examples.append(dict(example=pair,left_word=left,right_word=right,L=len(left),
                             left_ones=left.count("1"),right_ones=right.count("1"),
                             left_10_boundaries=switches(left),right_10_boundaries=switches(right),
                             left_coefficient=str(v/2),right_coefficient=str(vv/2),
                             left_minus_right=str((v-vv)/2)))
    write_csv(out/"exact_examples.csv",examples)
    # Record the first same-L, same-count, same-switch pair, without replacing
    # the predeclared balanced examples by a post-hoc performance winner.
    first=None
    for left in rows:
        for right in rows:
            if (left["L"],left["ones"],left["boundaries_10"]) == (right["L"],right["ones"],right["boundaries_10"]) and left["cubic_coefficient"]!=right["cubic_coefficient"]:
                first={"left":left["word"],"right":right["word"],"L":left["L"],
                       "ones":left["ones"],"boundaries_10":left["boundaries_10"],
                       "left_coefficient":left["cubic_coefficient"],"right_coefficient":right["cubic_coefficient"]}
                break
        if first is not None:break
    mp.mp.dps=90
    z=(1+mp.j*mp.sqrt(7))/4;A=mp.mpf(3)/8-mp.j/(8*mp.sqrt(7))
    blocks=[]
    for m in range(1,65):
        v=response("0"*m+"1"*m)[2]
        vm=mp.mpf(v.numerator)/v.denominator
        closed=mp.re(A*(1-z**m)/(1+z**m))
        bound=2/mp.sqrt(7)*2**(-mp.mpf(m)/2)/(1-2**(-mp.mpf(m)/2))
        assert abs(m*vm-closed)<mp.mpf("1e-75")
        assert abs(m*vm-mp.mpf(3)/8)<=bound
        blocks.append(dict(m=m,word_length=2*m,variance=str(v),cubic_coefficient=str(v/2),
                           m_variance=float(m*vm),closed_form_m_variance=str(closed),
                           closed_form_error=str(abs(m*vm-closed)),
                           asymptotic_limit="3/8",error_bound=str(bound)))
    write_csv(out/"long_blocks.csv",blocks)
    near=[]
    for word in ("00010111","00100111","000111","001011"):
        coef=response(word)[2]/2
        for cs in ("0.0001","0.001","0.01","0.05"):
            C=mp.mpf(cs);rho=endpoint_factor(word,C)
            near.append(dict(word=word,C=cs,endpoint_factor=str(rho),
                             endpoint_gap_over_C3=str((C-rho)/C**3),
                             coefficient=str(coef)))
    write_csv(out/"near_isotropic_examples.csv",near)
    meta=dict(python=sys.version,numpy=np.__version__,mpmath=mp.__version__,platform=platform.platform(),
              enumeration_max_L=args.max_length,primitive_rotation_classes=len(rows),
              maximum_fourier_error=maxerr,first_same_counts_distinct_coefficient=first,
              exact_arithmetic="fractions.Fraction",dft_normalization="1/L",randomness="none",
              transition_coefficient_bounds="t/(16L) <= Var(r)/2 <= 8t/(7L), checked exactly",
              gamma_ordering="conditional on a separately proved exact unrestricted coefficient theorem")
    (out/"verification.json").write_text(json.dumps(meta,indent=2),encoding="utf-8")
    hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(out.iterdir()) if p.is_file() and p.name!="SHA256.json"}
    (out/"SHA256.json").write_text(json.dumps(hashes,indent=2),encoding="utf-8")
    print(json.dumps(meta,indent=2));print(json.dumps(examples,indent=2))


if __name__=="__main__":main()
