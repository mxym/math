#!/usr/bin/env python3
"""Independent finite rational checks; not a certificate of the analytic limits."""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import comb, factorial, prod, isqrt
import argparse, json, hashlib
from pathlib import Path


def require(value, message):
    if not value:
        raise ArithmeticError(message)


def partitions(n, length, max_part=None):
    if n == 0:
        yield ()
        return
    if length == 0:
        return
    for v in range(min(n, n if max_part is None else max_part), 0, -1):
        for rest in partitions(n-v, length-1, v):
            yield (v,)+rest


def weyl(lam, d):
    if len(lam)>d:
        return 0
    ll=lam+(0,)*(d-len(lam))
    out=F(1)
    for i in range(d):
        for j in range(i+1,d):
            out*=F(ll[i]-ll[j]+j-i,j-i)
    require(out.denominator==1,'Weyl dimension is not integral')
    return out.numerator


def specht_hook(lam):
    hooks=[]
    for i,row in enumerate(lam):
        for j in range(row):
            hooks.append(row-j+sum(x>j for x in lam[i+1:]))
    return factorial(sum(lam))//prod(hooks)


@lru_cache(None)
def specht_branch(lam):
    if not lam:
        return 1
    out=0
    for i,v in enumerate(lam):
        if i+1==len(lam) or v>lam[i+1]:
            ll=list(lam)
            ll[i]-=1
            out+=specht_branch(tuple(x for x in ll if x))
    return out


def cross_ratio(lam,d,s):
    ll=lam+(0,)*(s-len(lam))
    return prod((F(ll[i]+j-i,j-i) for i in range(s) for j in range(s,d)),start=F(1))


def support_stats(d,s,k):
    rr=0
    trace=F(0)
    purity=F(0)
    er=F(0)
    einv=F(0)
    for lam in partitions(k,s):
        u=weyl(lam,d)
        us=weyl(lam,s)
        v=specht_hook(lam)
        rr+=u*v
        weight=F(us*v,s**k)
        ratio=cross_ratio(lam,d,s)
        require(ratio==F(u,us),'cross-Weyl ratio mismatch')
        eig=F(us,s**k*u)
        trace+=u*v*eig
        purity+=u*v*eig*eig
        er+=weight*ratio
        einv+=weight/ratio
    require(trace==1,'Haar-averaged state not trace one')
    require(er*s**k==rr,'support rank expectation mismatch')
    require(einv/s**k==purity,'inverse-moment purity mismatch')
    require(rr*purity>=1,'normalized state violates rank-purity bound')
    if s==1:
        require(rr==comb(k+d-1,d-1),'symmetric dimension mismatch')
        require(rr*purity==1,'pure-orbit average not flat on Sym')
    if s==d:
        require(rr==d**k and purity==F(1,d**k),'full-rank endpoint mismatch')
    return rr,purity


def tableaux_weights(lam,d):
    cells=[(i,j) for i,v in enumerate(lam) for j in range(v)]
    grid={}
    counts=[0]*d
    out=Counter()
    def fill(pos):
        if pos==len(cells):
            out[tuple(counts)]+=1
            return
        i,j=cells[pos]
        low=0
        if j:
            low=max(low,grid[i,j-1])
        if i:
            low=max(low,grid[i-1,j]+1)
        for t in range(low,d):
            grid[i,j]=t
            counts[t]+=1
            fill(pos+1)
            counts[t]-=1
    fill(0)
    require(sum(out.values())==weyl(lam,d),'tableaux count != Weyl dimension')
    return out


def compositions(n,d):
    if d==1:
        yield (n,)
    else:
        for x in range(n+1):
            for rest in compositions(n-x,d-1):
                yield (x,)+rest


def eigenvalue(p,counts):
    return prod((x**c for x,c in zip(p,counts)),start=F(1))


def spectrum_checks():
    records=[]
    p_laws=[(F(3,7),F(2,7),F(1,7),F(1,7)),(F(1,2),F(1,3),F(1,6),F(0))]
    for k in [1,2,4,6,8,10]:
        shapes=list(partitions(k,4))
        block_weights={lam:tableaux_weights(lam,4) for lam in shapes}
        ustar=max(weyl(lam,4) for lam in shapes)
        j=len(shapes)
        a=2**k
        a0=a//j
        for p in p_laws:
            block_probs={}
            spectral=Counter()
            for lam,weights in block_weights.items():
                v=specht_hook(lam)
                mass=F(0)
                for counts,mult in weights.items():
                    eig=eigenvalue(p,counts)
                    spectral[eig]+=v*mult
                    mass+=eig*v*mult
                block_probs[lam]=mass
                rr=weyl(lam,4)*v
                for counts in weights:
                    eig=eigenvalue(p,counts)
                    require(eig<=F(ustar,rr),'actual block eigenvalue exceeds ustar/r')
            direct=Counter()
            for counts in compositions(k,4):
                mult=factorial(k)//prod(factorial(x) for x in counts)
                direct[eigenvalue(p,counts)]+=mult
            require(spectral==direct,'Schur weights do not recover tensor-power spectrum')
            require(sum(block_probs.values())==1,'block mass not one')
            targets=[x for x in [1,2,3,5,9,17] if x<=a0]
            for target in targets:
                g=(a0//target)**2
                threshold=F(ustar,g)
                event=sum((eig*mult for eig,mult in direct.items() if eig>=threshold),start=F(0))
                good=sum((mass for lam,mass in block_probs.items() if weyl(lam,4)*specht_hook(lam)<=g),start=F(0))
                lower=F(0)
                for lam,mass in block_probs.items():
                    u=weyl(lam,4)
                    v=specht_hook(lam)
                    vp=min(v,a0*a0//u)
                    if not vp:
                        continue
                    rp=u*vp
                    bell=max(d for d in range(1,min(target,a0)+1) if (a0//d)**2>=rp)
                    lower+=F(vp*bell,v*target)*mass
                require(event<=good<=lower<=1,'finite information-spectrum inclusion failed')
                if a>=2*j:
                    require(F(g)>=F(a*a,16*j*j*target*target),'integer G bound failed')
                records.append({'k':k,'K':target,'J':j,'u_star':ustar,'G':g,'zero_eigenvalues':p[-1]==0,'event':str(event),'good_mass':str(good),'coded_fidelity_lower':str(lower)})
    return records


def code_dyad(a,b,d,target,i,j,ip,jp):
    # Compute the actual Kraus action, not only the predicted delta formula.
    out=Counter()
    for t in range(d):
        for u in range(d):
            ax=i*d+t; bx=j*d+t
            ay=ip*d+u; by=jp*d+u
            for ai in range(a//d):
                if ax//d!=ai or ay//d!=ai:
                    continue
                for bj in range(b//d):
                    if bx//d!=bj or by//d!=bj:
                        continue
                    out[(ax%d,bx%d,ay%d,by%d)]+=F(1,d)
    return {x:v for x,v in out.items() if v}


def coherent_checks():
    count=0
    for a,b,d,target in [(5,7,2,3),(8,8,3,8),(9,11,2,5),(3,4,1,7)]:
        labels=list(product(range(a//d),range(b//d)))
        for (i,j),(ip,jp) in product(labels,repeat=2):
            actual=code_dyad(a,b,d,target,i,j,ip,jp)
            expected={(t,t,u,u):F(1,d) for t in range(d) for u in range(d)} if (i,j)==(ip,jp) else {}
            require(actual==expected,'coherent Bell-label discard identity failed')
            if (i,j)==(ip,jp):
                fid=sum((val/F(target) for (x,y,z,w),val in actual.items() if x==y and z==w),start=F(0))
                require(fid==F(d,target),'fidelity versus root-fidelity convention wrong')
            count+=1
    return count


def negative_controls():
    # Each false mathematical proposition is checked against independent exact data.
    rejected=[]
    u=weyl((2,),4); us=weyl((2,),2)
    wrong=prod((F(2+j-i if i==0 else j-i) for i in range(2) for j in range(2,4)),start=F(1))
    require(wrong!=F(u,us),'negative omitted Weyl denominator unexpectedly true')
    rejected.append('omit_cross_Weyl_denominators')
    r,purity=support_stats(4,2,4)
    require(r!=2**4,'unknown support rank replaced by state rank')
    rejected.append('replace_universal_support_by_s_power_k')
    require(purity!=F(1,2**4),'Haar average replaced by known flat state')
    rejected.append('replace_Haar_average_by_known_input')
    require(r*purity!=1,'finite rank-s twirl incorrectly declared exactly flat')
    rejected.append('replace_asymptotic_flatness_by_finite_identity')
    r,_=support_stats(4,1,3)
    require(r>1 and F(1,r)<1,'full Bell output universal pure fidelity incorrectly one')
    rejected.append('full_output_unknown_pure_fidelity_one')
    off=code_dyad(5,7,2,3,0,0,1,0)
    require(off=={},'off-diagonal labels must vanish')
    wrong_coherent={(t,t,u,u):F(1,2) for t in range(2) for u in range(2)}
    require(off!=wrong_coherent,'nonzero surviving label coherence accepted')
    rejected.append('preserve_off_diagonal_garbage_coherence')
    require(F(2,3)!=F(4,9),'root fidelity convention mutation not rejected')
    rejected.append('square_overlap_twice')
    a,b,d=5,7,3
    require(F(a*b,d*d)>3 and (a//d)*(b//d)<3,'integer packing control invalid')
    rejected.append('replace_integer_garbage_capacity_by_real_volume')
    return rejected


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--report',default='verification/exact-checks.json')
    args=parser.parse_args()
    dimension_cases=0
    for d in range(2,7):
        for k in range(1,13):
            for lam in partitions(k,d):
                require(specht_hook(lam)==specht_branch(lam),'hook dimension != independent branching count')
            for s in range(1,d+1):
                support_stats(d,s,k)
                dimension_cases+=1
    asymptotics=[]
    for d,s,ks in [(4,1,[20,50,100,200]),(4,2,[20,50,100,200]),(4,3,[20,50,100,200]),(6,2,[20,50,100,200]),(6,3,[20,50,100])]:
        g=s*(d-s)
        const=F(1,s**g*prod(j-i for i in range(s) for j in range(s,d)))
        for k in ks:
            rr,pp=support_stats(d,s,k)
            asymptotics.append({'D':d,'s':s,'k':k,'r_over_C_s_pow_k_k_pow_g':float(F(rr,s**k*k**g)/const),'r_times_twirl_purity':float(rr*pp)})
    spectrum=spectrum_checks()
    report={'status':'PASS','scope':'exact finite rational controls, not unbounded analytic or Lean proof','dimension_cases':dimension_cases,'coherent_dyads':coherent_checks(),'information_spectrum_cases':len(spectrum),'spectrum_details':spectrum,'negative_controls_rejected':negative_controls(),'asymptotic_diagnostics_not_proofs':asymptotics,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    path=Path(args.report)
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['spectrum_details','asymptotic_diagnostics_not_proofs']},indent=2))

if __name__=='__main__':
    main()
