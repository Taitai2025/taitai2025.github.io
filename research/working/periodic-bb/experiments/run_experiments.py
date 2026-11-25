"""Bounded, reproducible evidence for periodic BB switching. See README.md.

Run: python run_experiments.py --out output
No network, external data, or old-project writes. Spectra and seeds are fixed.
"""
from pathlib import Path
import argparse
import csv
import hashlib
import json
import platform
import sys
import time
import numpy as np
import mpmath as mp
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

METHODS = ("BB1", "BB2", "01", "0011", "ABBmin1", "CBB2")
FAMILIES = ("log_spaced", "linear_spaced", "two_bands")
KAPPAS = (10, 100, 1000)
SEEDS = tuple(range(20))
BASE_SEED = 20260922
N, BUDGET, TARGET = 64, 500, -8.0
COLORS = dict(zip(METHODS, ("#777777", "#B79656", "#1671B7", "#DE5D37", "#228653", "#986BB0")))


def csv_write(path, rows):
    if not rows:
        path.write_text("", encoding="utf-8")
        return
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)


def periodic_coefficients(word):
    L = len(word)
    A = mp.matrix(L)
    rhs = mp.matrix([2 * int(s) for s in word])
    for k in range(L):
        A[k, (k + 1) % L] += 1
        A[k, k] -= 1
        A[k, (k - 1) % L] += 2
    a = list(mp.lu_solve(A, rhs))
    r = [1 - a[(k - 1) % L] + int(word[k]) for k in range(L)]
    return a, r


def word_factor(word, kappa):
    _, r = periodic_coefficients(word)
    k = mp.mpf(kappa)
    return (k - 1) * mp.exp(-sum(mp.log(1 + k**v) for v in r) / len(r))


def gap_certificate(C, L):
    C = mp.mpf(C)
    k0 = (1-C)**2 / 2
    H = (3-C) / (2*(1-C))
    Q = 4 + C/(1-C)
    A = ((14+C)*mp.sqrt(L) + 2*Q*L*H) / mp.sqrt(k0)
    B = 2*Q*L
    tau = 2*C / (A + mp.sqrt(A*A + 4*C*(B+C)))
    return C * (-mp.expm1(-tau*tau))


def mp_update(weights, lam, u):
    factors = [(1-x/u)**2 for x in lam]
    z = sum(p*q for p, q in zip(weights, factors))
    return [p*q/z for p,q in zip(weights, factors)], mp.log(z)/2


def mp_selector(p, lam, symbol):
    m1 = sum(w*x for w,x in zip(p,lam))
    return m1 if symbol == 0 else sum(w*x*x for w,x in zip(p,lam))/m1


def mechanism(out):
    mp.mp.dps = 90
    exact, cubic, three = [], [], []
    for word in ("0", "1", "01", "0011", "00011"):
        a, r = periodic_coefficients(word)
        for ks in ("1.00001", "1.01", "2", "10", "100", "1000", "10000"):
            k = mp.mpf(ks)
            def state(index):
                z = k**a[index % len(word)]
                return [z/(1+z), 1/(1+z)]
            prev, cur = state(-1), state(0)
            initial, total = list(cur), mp.mpf(0)
            for symbol in word:
                u = mp_selector(prev, [mp.mpf(1), k], int(symbol))
                nxt, gain = mp_update(cur, [mp.mpf(1), k], u)
                prev, cur = cur, nxt
                total += gain
            formula = word_factor(word, k)
            observed = mp.exp(total/len(word))
            err = max(abs(cur[i]-initial[i]) for i in range(2))
            rel = abs(observed/formula-1)
            assert err < mp.mpf("1e-70") and rel < mp.mpf("1e-70")
            # A positive warm-up realizes the desired pair. With q=sqrt(z0/z-1),
            # alpha=(1+q)/(1+q*k) gives opposite-sign endpoint multipliers.
            ratio = mp.sqrt(k**(a[0]-a[-1]))
            alpha0 = (1+ratio)/(1+k*ratio)
            warmed, _ = mp_update(state(-1), [mp.mpf(1), k], 1/alpha0)
            warm_err = max(abs(warmed[i]-initial[i]) for i in range(2))
            assert warm_err < mp.mpf("1e-70")
            exact.append(dict(word=word, kappa=ks, a=";".join(map(str,a)),
                              r=";".join(map(str,r)), formula=str(formula),
                              one_period_factor=str(observed), closure_error=str(err),
                              relative_factor_error=str(rel), warmup_alpha=str(alpha0),
                              warmup_error=str(warm_err), decimal_digits=90))
    for word in ("01", "0011", "00011"):
        _, r = periodic_coefficients(word)
        constant = sum((v-1)**2 for v in r)/(2*len(r))
        for Cf in np.geomspace(1e-5, .3, 100):
            C = mp.mpf(str(Cf))
            k = (1+C)/(1-C)
            upper = C-word_factor(word,k)
            lower = gap_certificate(C,len(word))
            cubic.append(dict(word=word,C=float(C),kappa=float(k),
                              endpoint_gap=float(upper),certified_gap_lower=float(lower),
                              endpoint_gap_over_C3=float(upper/C**3),
                              lower_over_C3=float(lower/C**3),limit_constant=float(constant)))
    threshold = 577+408*mp.sqrt(2)
    for kf in [300,1000,threshold,1200,2000,10000,100000]:
        k = mp.mpf(kf); c = (k-1)/(k+1)
        sq2 = mp.sqrt(2); m = (k+1)/2; d = (k-1)/2
        u0,u1=m-d/sq2,m+d/sq2
        p = [(12*(1+sq2)+2*c*(sq2-1))/(8*(8*c-3*sq2)),
             (17*c-12*sq2)/(2*(8*c-3*sq2)),
             (12*(sq2-1)-2*c*(1+sq2))/(8*(8*c-3*sq2))]
        valid = k > threshold
        row = dict(kappa=float(k),threshold=str(threshold),valid_positive_weights=valid,
                   p_low=str(p[0]),p_mid=str(p[1]),p_high=str(p[2]),
                   endpoint_factor=str(word_factor("01", k)),
                   rho3=str(c/mp.sqrt(2-c*c)),closure_error="",selector_error="",
                   observed_factor="",warmup_error="")
        if valid:
            p1, gain0 = mp_update(p,[1,m,k],u0)
            p2, gain1 = mp_update(p1,[1,m,k],u1)
            err = max(abs(p2[i]-p[i]) for i in range(3))
            serr = max(abs(mp_selector(p1,[1,m,k],0)/u0-1),
                       abs(mp_selector(p,[1,m,k],1)/u1-1))
            assert err < mp.mpf("1e-75") and serr < mp.mpf("1e-75")
            warmed,_ = mp_update(p1,[1,m,k],u1)
            row.update(closure_error=str(err),selector_error=str(serr),
                       observed_factor=str(mp.exp((gain0+gain1)/2)),
                       warmup_error=str(max(abs(warmed[i]-p[i]) for i in range(3))))
        three.append(row)
    csv_write(out/"two_point_exact.csv",exact)
    csv_write(out/"cubic_gap.csv",cubic)
    csv_write(out/"three_point_cycle.csv",three)
    return exact,cubic,three


def logsumexp(v):
    largest = np.max(v)
    if not np.isfinite(largest):
        return largest
    return largest + np.log(np.sum(np.exp(v-largest)))


def log_update(logw,lam,alpha):
    factors = 1-alpha*lam
    with np.errstate(divide="ignore"):
        tmp = logw + 2*np.log(np.abs(factors))
    logz = logsumexp(tmp)
    zero_count = int(np.count_nonzero((factors == 0) & np.isfinite(logw)))
    return tmp-logz, logz/2, zero_count


def spectrum(family,kappa):
    if family == "log_spaced":
        return np.geomspace(1,kappa,N)
    if family == "linear_spaced":
        return np.linspace(1,kappa,N)
    return np.r_[np.linspace(1,1.05,N//2),np.linspace(.95*kappa,kappa,N//2)]


def run_one(lam,g0,method,maxsteps=BUDGET,stop=TARGET):
    # p0 is the measure of g0; p1 is the measure after the common warm-up.
    logprev=2*np.log(np.abs(g0)); logprev-=logsumexp(logprev)
    alpha0=2/(lam[0]+lam[-1])
    logcur, warm_gain, zeros=log_update(logprev,lam,alpha0)
    lognorm=0.0; history=[]; lastalpha=alpha0; inner=0
    trace=[dict(n=0,log10_norm_ratio=0.0,alpha="",selection="warmup_finished",
                selector_inner_products=0,gradient_evaluations=2,zero_factors=zeros)]
    firsthit=None
    for n in range(1,maxsteps+1):
        weights=np.exp(logprev)
        mean=float(weights@lam)
        if method in ("BB1","01","0011","CBB2"):
            if method == "CBB2" and n%2 == 0:
                alpha=lastalpha; selection="reuse_BB1"
            else:
                symbol=0 if method in ("BB1","CBB2") else int(method[(n-1)%len(method)])
                alpha=1/mean if symbol == 0 else mean/float(weights@(lam*lam))
                selection="BB1" if symbol == 0 else "BB2"
                inner+=2
        elif method == "BB2":
            alpha=mean/float(weights@(lam*lam)); selection="BB2"; inner+=2
        elif method == "ABBmin1":
            alpha1=1/mean; alpha2=mean/float(weights@(lam*lam)); history.append(alpha2)
            if alpha2/alpha1 < .8:
                alpha=min(history[-10:]); selection="min_last_10_BB2"
            else:
                alpha=alpha1; selection="BB1"
            inner+=3
        else:
            raise ValueError(method)
        nxt,gain,zero_count=log_update(logcur,lam,alpha)
        logprev,logcur=logcur,nxt
        lognorm+=gain
        val=float(lognorm/np.log(10))
        trace.append(dict(n=n,log10_norm_ratio=val,alpha=alpha,selection=selection,
                          selector_inner_products=inner,gradient_evaluations=n+2,
                          zero_factors=zero_count))
        lastalpha=alpha
        if np.isnan(val):
            raise FloatingPointError("NaN norm")
        if val <= stop:
            firsthit=n
            break
    return trace,firsthit,warm_gain


def independent_prefix_check():
    # Direct signed-gradient update with secant quotients, independent of moments.
    errors=[]
    for method in METHODS:
        lam=np.geomspace(1,100,17)
        rng=np.random.default_rng(381)
        g0=rng.normal(size=17); alpha0=2/(lam[0]+lam[-1])
        prev=g0.copy(); cur=(1-alpha0*lam)*g0
        reference=np.linalg.norm(cur); last=alpha0; memory=[]
        tr,_,_=run_one(lam,g0,method,maxsteps=12,stop=-1000)
        for n in range(1,13):
            s=-last*prev; y=cur-prev
            a1=float(s@s/(s@y)); a2=float(s@y/(y@y))
            if method == "BB1": alpha=a1
            elif method == "BB2": alpha=a2
            elif method in ("01","0011"): alpha=(a1,a2)[int(method[(n-1)%len(method)])]
            elif method == "CBB2": alpha=a1 if n%2 else last
            else:
                memory.append(a2)
                alpha=min(memory[-10:]) if a2/a1 < .8 else a1
            nxt=(1-alpha*lam)*cur
            prev,cur=cur,nxt; last=alpha
            err=abs(np.log10(np.linalg.norm(cur)/reference)-tr[n]["log10_norm_ratio"])
            errors.append(err)
    assert max(errors)<1e-10, max(errors)
    return max(errors)


def benchmark(out):
    traces=[]; summaries=[]; initial=[]; failures=[]
    alltraces={}
    for fi,family in enumerate(FAMILIES):
        for kappa in KAPPAS:
            lam=spectrum(family,kappa)
            for seed in SEEDS:
                rng=np.random.default_rng(np.random.SeedSequence([BASE_SEED,fi,kappa,seed]))
                g0=rng.normal(size=N)
                case=f"{family}_k{kappa}_s{seed:02}"
                for i in range(N):
                    initial.append(dict(case=case,family=family,kappa=kappa,seed=seed,
                                        coordinate=i,eigenvalue=lam[i],g0=g0[i]))
                for method in METHODS:
                    tr,hit,warm_gain=run_one(lam,g0,method)
                    alltraces[case,method]=tr
                    for row in tr:
                        traces.append(dict(case=case,family=family,kappa=kappa,seed=seed,method=method,**row))
                    inc=sum(tr[i]["log10_norm_ratio"]>tr[i-1]["log10_norm_ratio"] for i in range(1,len(tr)))
                    summaries.append(dict(case=case,family=family,kappa=kappa,seed=seed,method=method,
                                          first_hit_n=hit if hit is not None else "",
                                          reached_target=hit is not None,last_n=tr[-1]["n"],
                                          last_log10_ratio=tr[-1]["log10_norm_ratio"],
                                          max_log10_ratio=max(r["log10_norm_ratio"] for r in tr),
                                          increases=inc,zero_factors=sum(r["zero_factors"] for r in tr),
                                          warmup_alpha=2/(1+kappa),warmup_log_norm_gain=warm_gain,
                                          gradient_evaluations=tr[-1]["gradient_evaluations"],
                                          selector_inner_products=tr[-1]["selector_inner_products"]))
                    if hit is None:
                        failures.append(dict(case=case,method=method,reason="target_not_reached_by_500",
                                             last_log10_ratio=tr[-1]["log10_norm_ratio"]))
    csv_write(out/"initial_conditions.csv",initial)
    csv_write(out/"finite_budget_traces.csv",traces)
    csv_write(out/"finite_budget_summary.csv",summaries)
    csv_write(out/"failures.csv",failures)
    agg=[]
    for family in FAMILIES:
        for kappa in KAPPAS:
            for method in METHODS:
                rows=[r for r in summaries if r["family"]==family and r["kappa"]==kappa and r["method"]==method]
                # Censored median uses +inf, never treats timeout=500 as success.
                times=[r["first_hit_n"] if r["reached_target"] else np.inf for r in rows]
                med=float(np.median(times))
                agg.append(dict(family=family,kappa=kappa,method=method,
                                solved=sum(r["reached_target"] for r in rows),runs=len(rows),
                                median_hit_n=med if np.isfinite(med) else ">500",
                                median_max_log10_ratio=float(np.median([r["max_log10_ratio"] for r in rows]))))
    csv_write(out/"aggregate.csv",agg)
    budgets=[]
    for row in summaries:
        tr=alltraces[row["case"],row["method"]]
        for n in (50,100,200,500):
            val=max(TARGET,tr[min(n,len(tr)-1)]["log10_norm_ratio"])
            budgets.append(dict(case=row["case"],family=row["family"],kappa=row["kappa"],
                                seed=row["seed"],method=row["method"],budget_n=n,
                                gradient_budget=n+2,capped_log10_ratio=val,
                                reached_target_by_budget=row["reached_target"] and row["first_hit_n"]<=n))
    csv_write(out/"fixed_budget.csv",budgets)
    return summaries,agg,alltraces


def instability_diagnostic(out):
    # An exactly initialized double-precision orbit eventually leaves the repeller.
    # Retain this diagnostic; no late-time slope from it estimates the exact cycle.
    word="01"; k=100.0
    a,_=periodic_coefficients(word)
    zprev=k**float(a[-1]); zcur=k**float(a[0])
    prev=np.array([zprev/(1+zprev),1/(1+zprev)])
    cur=np.array([zcur/(1+zcur),1/(1+zcur)])
    prev=np.log(prev); cur=np.log(cur)
    rows=[]; logs=0.0
    for n in range(121):
        ideal=float(a[n%2])*np.log(k)
        observed=cur[0]-cur[1]
        rows.append(dict(n=n,ideal_log_energy_ratio=ideal,observed_log_energy_ratio=observed,
                         absolute_error=abs(observed-ideal),log10_norm_ratio=logs/np.log(10)))
        p=np.exp(prev); mean=float(p@np.array([1,k]))
        alpha=1/mean if n%2==0 else mean/float(p@np.array([1,k*k]))
        nxt,gain,_=log_update(cur,np.array([1,k]),alpha)
        prev,cur=cur,nxt; logs+=gain
        if not np.all(np.isfinite(cur)):
            break
    csv_write(out/"repeller_roundoff_diagnostic.csv",rows)
    return rows


def plots(out,cubic,alltraces):
    plt.rcParams.update({"font.family":"DejaVu Sans","font.size":8,"axes.titlesize":9,
                         "axes.labelsize":8,"legend.fontsize":7,"pdf.fonttype":42,
                         "ps.fonttype":42,"axes.spines.top":False,"axes.spines.right":False})
    fig,axs=plt.subplots(1,2,figsize=(6.75,2.55),layout="constrained")
    for word in ("01","0011"):
        rows=[r for r in cubic if r["word"]==word]
        x=[r["C"] for r in rows]
        axs[0].loglog(x,[r["endpoint_gap_over_C3"] for r in rows],color=COLORS[word],label=f"{word}: endpoint gap")
        axs[0].loglog(x,[r["lower_over_C3"] for r in rows],"--",color=COLORS[word],label=f"{word}: certified lower bound")
    axs[0].set(xlabel=r"Spectral spread $C=(\kappa-1)/(\kappa+1)$",ylabel=r"Gap divided by $C^3$",title="(a) Cubic gap: lower and upper bounds")
    axs[0].legend(loc="center left",frameon=False)
    kappas=np.geomspace(10,100000,200)
    C=(kappas-1)/(kappas+1)
    rho=np.array([float(word_factor("01",mp.mpf(str(k)))) for k in kappas])
    threshold=float(577+408*mp.sqrt(2)); mask=kappas>threshold
    axs[1].loglog(kappas,1-C,color="#555555",linestyle=":",label=r"Fixed-rule barrier $C$")
    axs[1].loglog(kappas,1-rho,color=COLORS["01"],label=r"Two-point response $\rho_{01}$")
    axs[1].loglog(kappas[mask],1-C[mask]/np.sqrt(2-C[mask]**2),color="#B64482",label=r"Three-point cycle $\rho_3$")
    axs[1].axvline(threshold,color="#AAAAAA",linewidth=.8)
    axs[1].text(threshold*1.09,.10,r"$\kappa_*\approx1154$",fontsize=7,rotation=90,va="top")
    axs[1].set(xlabel=r"Condition number $\kappa$",ylabel=r"Contraction deficit $1-\rho$",title="(b) Interior mass makes the cycle slower")
    axs[1].legend(loc="lower left",frameon=False)
    for ax in axs: ax.grid(alpha=.15,which="both")
    fig.savefig(out/"mechanism.pdf");fig.savefig(out/"mechanism.png",dpi=240);plt.close(fig)
    fig,axs=plt.subplots(1,2,figsize=(6.75,2.55),layout="constrained")
    for ax,family,title in zip(axs,("log_spaced","two_bands"),("(a) Log-spaced spectrum","(b) Two narrow endpoint bands")):
        for method in METHODS:
            curves=[]
            for seed in SEEDS:
                tr=alltraces[f"{family}_k1000_s{seed:02}",method]
                vals=np.array([max(TARGET,r["log10_norm_ratio"]) for r in tr])
                vals=np.pad(vals,(0,BUDGET+1-len(vals)),constant_values=vals[-1])
                curves.append(vals)
            data=np.array(curves)
            med=np.median(data,axis=0)
            ax.plot(np.arange(BUDGET+1),med,color=COLORS[method],label=("CBB1(m=2)" if method=="CBB2" else method),linewidth=1.35)
            if method in ("01","ABBmin1"):
                low,high=np.quantile(data,[.25,.75],axis=0)
                ax.fill_between(np.arange(BUDGET+1),low,high,color=COLORS[method],alpha=.10,linewidth=0)
        ax.set(xlabel="Updates after common warm-up",ylabel=r"$\log_{10}(\|g_{n+1}\|/\|g_1\|)$",title=title,ylim=(-8.15,5.0))
        ax.grid(alpha=.2)
    axs[0].legend(ncol=3,frameon=False,loc="upper right")
    axs[1].set_xlim(0,100)
    fig.savefig(out/"finite_budget.pdf");fig.savefig(out/"finite_budget.png",dpi=240);plt.close(fig)


def main():
    parser=argparse.ArgumentParser();parser.add_argument("--out",default="output")
    args=parser.parse_args();out=Path(args.out);out.mkdir(parents=True,exist_ok=True)
    start=time.perf_counter()
    exact,cubic,three=mechanism(out)
    check=independent_prefix_check()
    summaries,agg,traces=benchmark(out)
    unstable=instability_diagnostic(out)
    plots(out,cubic,traces)
    env=dict(python=sys.version,platform=platform.platform(),machine=platform.machine(),
             numpy=np.__version__,matplotlib=matplotlib.__version__,mpmath=mp.__version__,
             base_seed=BASE_SEED,seeds=list(SEEDS),families=list(FAMILIES),kappas=list(KAPPAS),
             dimension=N,max_post_warmup_steps=BUDGET,target_log10_ratio=TARGET,
             adaptive_parameters=dict(method="ABBmin1",tau=.8,m=9,window_including_current=10),
             direct_secant_prefix_max_log10_error=check,
             elapsed_seconds=time.perf_counter()-start,
             method_names=list(METHODS),number_of_instances=180,number_of_runs=len(summaries))
    (out/"environment.json").write_text(json.dumps(env,indent=2),encoding="utf-8")
    hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(out.iterdir()) if p.is_file() and p.name!="SHA256.json"}
    (out/"SHA256.json").write_text(json.dumps(hashes,indent=2),encoding="utf-8")
    print(json.dumps(env,indent=2))
    print("kappa=1000 aggregate:")
    for r in agg:
        if r["kappa"]==1000: print(r)


if __name__=="__main__":
    main()
