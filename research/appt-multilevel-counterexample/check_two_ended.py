#!/usr/bin/env python3
"""Exact ancillary checks for the two-ended APPT working proofs.

No finite graph, state, or integer regression proves the compactness limit.
The unbounded quantum statement is the analytic argument in the working notes.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from fractions import Fraction as F
import hashlib
import json
from math import isqrt
from pathlib import Path
from random import Random

ROOT=Path(__file__).resolve().parent

class CheckFailure(RuntimeError):
    pass

def require(ok: bool, text: str) -> None:
    if not ok:
        raise CheckFailure(text)

def d_sequence(n: int) -> list[F]:
    out=[F(4)]
    for _ in range(n): out.append(out[-1]-out[-1]*out[-1]/8)
    return out

def energy_ok(energy: F, others: F) -> bool:
    return others<=4 and 8*energy<=(4-others)**2

def low_ok(fs: list[F]) -> bool:
    return all(energy_ok(f,sum(fs[i+1:],F(0))) for i,f in enumerate(fs))

def high_ok(es: list[F]) -> bool:
    return all(energy_ok(e,sum(es[:i],F(0))) for i,e in enumerate(es))

def components_check() -> dict:
    vertex_count=component_count=loops_count=0
    for p in range(5):
        for q in range(5):
            den=2*3**max(p,q,1)
            vertices=[F(i,den) for i in range(den+1)]
            low=[F(1,3**(p-i)) for i in range(p)]
            high=[2-F(1,3**(j+1)) for j in range(q)]
            labels={v:('low',i) for i,v in enumerate(low)}
            labels.update({v:('high',j) for j,v in enumerate(high)})
            adj={v:[] for v in vertices}; loops={F(1):('broad',0)}
            for i,v in enumerate(vertices):
                if 2*v in labels: loops[v]=labels[2*v]
                for w in vertices[i+1:]:
                    if v+w in labels:
                        label=labels[v+w];adj[v].append((w,label));adj[w].append((v,label))
            unseen=set(vertices)
            while unseen:
                start=min(unseen); stack=[start]; comp=set();edges={}
                while stack:
                    v=stack.pop()
                    if v in comp:continue
                    comp.add(v);unseen.discard(v)
                    for w,label in adj[v]:
                        edges[tuple(sorted((v,w)))]=label
                        if w not in comp:stack.append(w)
                require(len(edges)==len(comp)-1,'off-diagonal label graph is a forest')
                cl=[(v,loops[v]) for v in comp if v in loops]
                require(len(cl)<=1,'at most one loop in a component')
                edge_labels=list(edges.values())
                require(len({a for a,_ in edge_labels})<=1,'low and high components stay disjoint')
                if cl:
                    typ,index=cl[0][1];loops_count+=1
                    if typ=='low':
                        require(all(a=='low' and j>index for a,j in edge_labels),'low loop has suffix labels')
                    elif typ=='high':
                        require(all(a=='high' and j<index for a,j in edge_labels),'high loop has prefix labels')
                    else:
                        require(all(a=='high' for a,j in edge_labels),'broad loop couples only to high levels')
                component_count+=1
            vertex_count+=len(vertices)
    return {'rational_atom_locations':vertex_count,'components':component_count,'one_loop_components':loops_count}

def optimization_check() -> dict:
    ds=d_sequence(12); allocations=sampled=transition=0
    for p in range(7):
        fs=[ds[p-i-1]**2/8 for i in range(p)]
        require(low_ok(fs),'optimal reverse-rank low energy allocation')
        require(sum(fs,F(0))==4-ds[p],'low energy total')
        for q in range(7):
            es=[ds[j]**2/8 for j in range(q)]
            require(high_ok(es),'optimal forward-rank high energy allocation')
            require(sum(es,F(0))==4-ds[q],'high energy total')
            for gamma in (F(1),F(4,3),F(2),F(3),F(4),F(5),F(9),F(100)):
                sharp=4-ds[p]+max(gamma,4-ds[q]+gamma*ds[q]**2/16)
                for u in [F(i,20) for i in range(41)]+[ds[q]/2]:
                    budget=min(4-ds[q],4-2*u)
                    scaled=[x*budget/(4-ds[q]) for x in es] if q else []
                    require(high_ok(scaled),'scaled high allocation remains feasible')
                    require(sum(scaled,F(0))+2*u<=4,'background shares high energy budget')
                    val=sum(fs,F(0))+sum(scaled,F(0))+gamma*u*u/4
                    require(val<=sharp,'finite-depth objective below endpoint maximum')
                    sampled+=1
                values=[]
                for u in (ds[q]/2,F(2)):
                    values.append(4-ds[p]+min(4-ds[q],4-2*u)+gamma*u*u/4)
                require(max(values)==sharp,'attaining background endpoint')
                allocations+=1
            if q:
                gamma=16/(4+ds[q])
                require(4-ds[q]+gamma*ds[q]**2/16==gamma,'exact finite-depth phase transition')
                transition+=1
    for n in range(2,13):
        p=n//2;q=n-p
        require(ds[p]+ds[q]==min(ds[i]+ds[n-i] for i in range(1,n) if i<len(ds) and n-i<len(ds)),
                'best no-background depth split is balanced')
    return {'energy_and_aspect_choices':allocations,'background_objective_checks':sampled,'transition_identities':transition}

def clique_size(budget: int) -> int:
    q=(1+isqrt(1+8*budget))//2
    require(q*(q-1)//2<=budget<(q+1)*q//2,'maximal integer clique size')
    return q

def nested_counts_check() -> dict:
    cases=0
    for p,q in ((1,1),(2,1),(1,2),(2,2),(3,3)):
        jmax=max(p,q)
        for scale in (4,8):
            exponent=2*3**jmax*scale; M=1<<exponent
            alphas=[F(1,3**(p-i)) for i in range(p)]
            deltas=[F(1,3**(j+1)) for j in range(q)]
            low=[1<<int(exponent*x) for x in alphas]
            high=[1<<int(exponent*(2-x)) for x in deltas]
            require(all((F(exponent)*x).denominator==1 for x in alphas+deltas),'integer powers realize rational rank exponents exactly')
            ranks=low+high
            require(all(a<b for a,b in zip(ranks,ranks[1:])),'all hierarchy ranks increase')
            require(ranks[-1]<M*(M-1)//2,'ranks fit in negative Schmidt eigenspace')
            for i,r in enumerate(low):
                prev=low[i-1] if i else 0; Q=clique_size(r-prev)
                groups=[(low[h]-low[h-1])//Q for h in range(i+1,p)]
                require(Q+sum(groups)<=M,'low arrowhead groups fit in original vertices')
                require(all(N>0 for N in groups),'low peripheral groups nonempty')
                require(Q*(Q-1)//2+prev<=r,'clique respects already nested low edges')
                cases+=1
            for j,r in enumerate(high):
                prev=high[j-1] if j else low[-1];Q=clique_size(r-prev)
                increments=[high[h]-(high[h-1] if h else low[-1]) for h in range(j)]
                groups=[inc//Q for inc in increments]
                require(Q+sum(groups)<=M,'high arrowhead groups fit')
                require(all(N>0 for N in groups),'high peripheral groups nonempty')
                require(Q*(Q-1)//2+prev<=r,'clique respects nested high edges')
                cases+=1
            reserved=1<<int(exponent*(1-deltas[-1]/2));Q=M-reserved
            increments=[high[h]-(high[h-1] if h else low[-1]) for h in range(q)]
            groups=[inc//Q for inc in increments]
            require(Q+sum(groups)<=M,'broad core plus all peripherals fit')
            require(all(N>0 for N in groups),'broad peripheral groups nonempty')
            require(all(Q*N<=inc for N,inc in zip(groups,increments)),'nested bipartite increments fit rank budgets')
            cases+=1
    return {'exact_large_integer_count_cases':cases,'scope':'Counts, not materialized huge graphs or finite-dimensional positivity certification'}

# Dense exact rational matrices, used only in small independent channel tests.
def eye(n):return [[F(i==j) for j in range(n)] for i in range(n)]
def transpose(A):return [list(row) for row in zip(*A)]
def mmul(A,B):
    Bt=transpose(B)
    return [[sum((x*y for x,y in zip(row,col)),F(0)) for col in Bt] for row in A]
def mtrace(A):return sum((A[i][i] for i in range(len(A))),F(0))
def pt(A,n):
    D=len(A);B=[[F(0)]*D for _ in range(D)]
    for i in range(D):
        a,b=divmod(i,n)
        for j in range(D):
            c,d=divmod(j,n);B[a*n+d][c*n+b]=A[i][j]
    return B

def positive_definite(A):
    B=[row[:] for row in A];N=len(B)
    require(B==transpose(B),'exact symmetric matrix')
    for k in range(N):
        if B[k][k]<=0:return False
        pivot=B[k][k]
        for i in range(k+1,N):
            for j in range(k+1,N):B[i][j]-=B[i][k]*B[k][j]/pivot
    return True

def projection_and_reflection_check() -> dict:
    rng=Random(280414); projection_tests=state_tests=0
    for m in range(2,9):
        n=m+2;D=m*n;R=m*(m-1)//2
        for _ in range(3):
            z=[rng.randrange(0,8) for _ in range(m)]
            if not any(z):z[0]=1
            ss=sum(v*v for v in z)
            pairs=sorted([F(z[i]*z[j],ss) for i in range(m) for j in range(i+1,m)],reverse=True)
            ev=[F(v*v,ss) for v in z]+pairs+[-v for v in pairs]+[F(0)]*(D-m*m)
            ev.sort(reverse=True)
            for r in range(D+1):
                S=sum(pairs[:r],F(0))
                lo=sum(ev[D-r:],F(0)) if r else F(0)
                hi=sum(ev[:r],F(0))
                require(lo>=-S and hi<=S+1,'two-sided rank-projection trace bounds')
                projection_tests+=1
    for m,n in ((2,2),(2,3),(3,3),(3,4),(4,4),(4,5)):
        D=m*n;coeff=[F(1,16*m),F(1,32*m),F(1,64*m)]
        ranks=[1,max(2,D//4),D//2];L=sum(coeff,F(0));mu=sum((c*r for c,r in zip(coeff,ranks)),F(0))/D
        sig=1-L*F(m-1,2)
        require(L<sig,'strict finite two-sided margin')
        vals=[sum((c for c,r in zip(coeff,ranks) if i<r),F(0))-mu for i in range(D)]
        require(sum(vals,F(0))==0,'exact centering')
        require(max(abs(v) for v in vals)<=L,'uniform relative operator contrast')
        v=[F((i%3)+1) for i in range(D)];vv=sum(x*x for x in v)
        U=[[F(i==j)-2*v[i]*v[j]/vv for j in range(D)] for i in range(D)]
        require(mmul(U,transpose(U))==eye(D),'rational Householder is unitary')
        Y=[[sum((U[i][h]*vals[h]*U[j][h] for h in range(D)),F(0)) for j in range(D)] for i in range(D)]
        Ypt=pt(Y,n)
        states=[]
        for sign in (1,-1):
            rho=[[ (F(i==j)+sign*Y[i][j])/D for j in range(D)] for i in range(D)]
            require(mtrace(rho)==1,'reflected density trace one')
            require(positive_definite(rho),'reflected state is positive definite')
            floor=sig-L
            residual=[[F(i==j)*(1-floor)+sign*Ypt[i][j] for j in range(D)] for i in range(D)]
            require(positive_definite(residual),'two-sided partial transpose exceeds analytic floor')
            require(mtrace(mmul(rho,rho))==F(1,D)+sum(x*x for x in vals)/(D*D),'exact centered purity')
            states.append(rho);state_tests+=1
        require(all(states[0][i][j]+states[1][i][j]==F(2*(i==j),D) for i in range(D) for j in range(D)),
                'reflection sums to twice maximally mixed state')
    return {'rank_projection_tests':projection_tests,'strict_rational_density_and_PT_checks':state_tests}

def moments_and_entropy_check() -> dict:
    rng=Random(100424);cases=0
    for D in range(10,110,3):
        ranks=sorted(rng.sample(range(1,D),4));coefs=[F(rng.randrange(1,8),40*D) for _ in ranks]
        T=sum(c*r for c,r in zip(coefs,ranks));mu=T/D
        S=sum(coefs[i]*coefs[j]*min(ranks[i],ranks[j]) for i in range(4) for j in range(4))
        vals=[sum(c for c,r in zip(coefs,ranks) if k<r)-mu for k in range(D)]
        require(sum(v*v for v in vals)==S-T*T/D,'nested flag centered second moment')
        # For alpha=2,3 the two Taylor formulas can be checked without logarithms.
        require(sum((1+v)**2-1-2*v for v in vals)==sum(v*v for v in vals),'quadratic divergence exact')
        rem=sum((1+v)**3-1-3*v-3*v*v for v in vals)
        eps=max(abs(v) for v in vals)
        require(abs(rem)<=eps*sum(v*v for v in vals),'cubic Taylor remainder controlled by contrast')
        cases+=1
    y=F(1,2);N=30
    lower=2*sum((y**(2*i+1)/F(2*i+1) for i in range(N)),F(0))
    upper=lower+2*y**(2*N+1)/(F(2*N+1)*(1-y*y))
    require(0<lower<upper<F(4,3),'rational enclosure proves log3 below four-thirds')
    gap_lo=4-3*upper;gap_hi=4-3*lower
    require(F(7,10)<gap_lo<gap_hi<F(71,100),'entropy separation has a strictly positive exact enclosure')
    require((3**2-1-2*2)-2*2*(2-1)==0,'spike and flat quadratic constants agree')
    require((3**3-1-2*3)-2*3*(3-1)==8,'third moment differs despite equal purity coefficient')
    return {'nested_moment_cases':cases,'entropy_gap_rational_lower':str(gap_lo),'entropy_gap_rational_upper':str(gap_hi)}

def negative_controls() -> list[dict]:
    results=[]
    require(not low_ok([F(2),F(1,2)]) and high_ok([F(2),F(1,2)]),'reversing low and high constraints is detected')
    results.append({'name':'use forward energies for low ranks','rejected':True,'diagnostic':'low suffix budget violated'})
    require(high_ok([F(2)]) and 2+2*2>4,'background is not an independent norm budget')
    results.append({'name':'ignore broad/high interaction','rejected':True,'diagnostic':'E+2u exceeds four'})
    # beta_low=2/3 and beta_high=4/3 yield a loop at 1/3 joined to 1.
    require(F(1,3)*2==F(2,3) and F(1,3)+1==F(4,3),'nonseparated labels share a loop component')
    require(F(0)*4-(-2)**2<0,'mixed arrowhead exceeds norm two')
    results.append({'name':'drop separation of the two rank ends','rejected':True,'diagnostic':'rational congruent PSD minor is negative'})
    D=9
    require(F(2,D)-F(3,D+2)<0,'generic APPT spike cannot be reflected')
    results.append({'name':'reflect an arbitrary APPT state without small contrast','rejected':True,'diagnostic':'reflected largest-spike eigenvalue is negative'})
    require(F(1,4)**2+F(1,3)**2 != (F(1,4)+F(1,3))**2,'nested cross terms cannot be dropped before the limit')
    results.append({'name':'discard finite nested cross terms','rejected':True,'diagnostic':'second moment changes'})
    return results

def run_checks() -> dict:
    report={'status':'PASS','scope':'Exact finite supporting calculations; not independent CI, Lean verification, or a finite proof of the analytic graph/APPT limit',
            'components':components_check(),'finite_depth_optimization':optimization_check(),
            'nested_counts':nested_counts_check(),'physical_reflection':projection_and_reflection_check(),
            'moments':moments_and_entropy_check(),'negative_controls':negative_controls()}
    names=['TWO_ENDED_GRAPH_LIMIT.md','FLAT_EXTREMIZERS.md','check_two_ended.py']
    report['source_hashes']={n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in names}
    return report

def main() -> None:
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--report',type=Path)
    args=p.parse_args();report=run_checks();text=json.dumps(report,indent=2)+'\n'
    if args.report:args.report.parent.mkdir(parents=True,exist_ok=True);args.report.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
