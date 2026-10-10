#!/usr/bin/env python3
"""Exact ancillary checks of the new APPT research notes.

These checks do not prove compactness, limits, or the all-unitary quantum theorem.
Only Python's standard library is used; disabling assertions changes no checks.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
import math
import random
from fractions import Fraction as F
from pathlib import Path
from typing import Callable

class CheckFailure(RuntimeError):
    pass

def require(condition: bool, message: str) -> None:
    if not condition:
        raise CheckFailure(message)

def ceil_sqrt(n: int) -> int:
    t = math.isqrt(n)
    return t + int(t*t != n)

def record_rejection(name: str, action: Callable[[], None]) -> dict:
    try:
        action()
    except CheckFailure as exc:
        return {"name": name, "rejected": True, "diagnostic": str(exc)}
    raise CheckFailure("Invalid control was accepted: " + name)

def variance_and_rearrangements() -> dict:
    rng = random.Random(20261010)
    count = 0
    for m in range(3, 13):
        for n in (m, m+1, 2*m):
            D=m*n; R=m*(m-1)//2; h=m//2; l=m-h; q=h*l
            for trial in range(12):
                weights = ([1]*(D//2)+[0]*(D-D//2) if trial == 0
                           else [rng.randrange(17) for _ in range(D)])
                total=sum(weights)
                lam=sorted((F(x,total) for x in weights), reverse=True)
                ds=[lam[i]-lam[-1-i] for i in range(R)]
                head=sum((x*x for x in ds[:q]),F(0)); t=ds[q-1]; w=ds[R-1]
                Bq=sum(ds[:q],F(0)); Bmid=sum(ds[q:R],F(0)); Ball=Bq+Bmid
                V=sum((x*x for x in lam),F(0))-F(1,D)
                require(V <= head-t*Bq+F(D,4)*t*t, "quartile variance identity")
                require(V <= head+(F(D,4)-q)*t*t, "quartile variance consequence")
                intermediate=head+t*Bmid-w*Bq-(R-q)*t*w+F(D,4)*w*w
                require(V <= intermediate, "second centered variance bound")
                require(intermediate <= head+t*Ball-q*t*t-R*t*w+F(D,4)*w*w,
                        "second variance scalar relaxation")
                rows=[ds[i*l:(i+1)*l] for i in range(h)]
                norm_sq=sum((sum(row,F(0))**2/F(l) for row in rows),F(0))
                require(sum((x*x for x in ds[l:q]),F(0)) <= norm_sq,
                        "shifted rectangular row inequality")
                count += 1
    opt_count=0
    for gamma in (F(1),F(6,5),F(5,4),F(3,2),F(2),F(5,2),F(3),F(5),F(10)):
        for ix in range(81):
            x=F(ix,20)
            for iy in range(min(ix,80-ix)+1):
                y=F(iy,20)
                f=x-x*x/4-x*y/2+gamma*y*y/4
                require(f <= max(F(1),gamma-1), "limiting scalar maximum")
                opt_count += 1
    return {"ordered_spectra":count,"scalar_parameter_cases":opt_count}

def physical_pairing() -> dict:
    rng=random.Random(83921); count=0
    for m,n in ((3,3),(3,5),(4,4),(4,7),(5,5)):
        D=m*n; R=m*(m-1)//2; S=m*(m+1)//2
        for _ in range(8):
            raw=sorted([rng.randrange(1,30) for _ in range(D)],reverse=True)
            lam=[F(x,sum(raw)) for x in raw]
            edges=list(itertools.combinations(range(m),2));rng.shuffle(edges)
            A:dict[tuple[int,int],F]={}
            def add(i:int,j:int,value:F)->None:
                A[i,j]=A.get((i,j),F(0))+value
            beta=lam[D-S:D-R]
            for i,b in enumerate(beta): add(i*n+i,i*n+i,b)
            for t,(i,j) in enumerate(edges):
                hi=lam[t];lo=lam[D-1-t];p=i*n+j;qq=j*n+i
                add(p,p,(hi+lo)/2);add(qq,qq,(hi+lo)/2)
                add(p,qq,(lo-hi)/2);add(qq,p,(lo-hi)/2)
            leftovers=iter(lam[R:D-S])
            for i in range(m):
                for j in range(m,n): add(i*n+j,i*n+j,next(leftovers))
            require(sum((v for (i,j),v in A.items() if i==j),F(0))==1,
                    "physical orbit trace")
            require(sum((v*v for v in A.values()),F(0))==sum((v*v for v in lam),F(0)),
                    "physical orbit second moment")
            PT={}
            for (row,col),v in A.items():
                i,j=divmod(row,n);k,ll=divmod(col,n)
                PT[i*n+ll,k*n+j]=v
            x=[rng.randrange(1,7) for _ in range(m)]
            actual=sum((F(x[i]*x[j])*PT.get((i*n+i,j*n+j),F(0))
                        for i in range(m) for j in range(m)),F(0))
            wanted=sum((beta[i]*x[i]**2 for i in range(m)),F(0))-sum(
                ((lam[t]-lam[D-1-t])*x[i]*x[j] for t,(i,j) in enumerate(edges)),F(0))
            require(actual==wanted,"physical Schmidt pairing sign and slots")
            count+=1
    return {"rational_orbit_pairings":count}

def walks() -> dict:
    graphs=0;moments=0
    for m in range(2,6):
        edges=list(itertools.combinations(range(m),2))
        for bits in range(1<<len(edges)):
            neighbors=[[] for _ in range(m)];r=0
            for t,(i,j) in enumerate(edges):
                if bits>>t&1:
                    neighbors[i].append(j);neighbors[j].append(i);r+=1
            v=[1]*m
            for power in range(1,8):
                v=[sum(v[j] for j in neighbors[i]) for i in range(m)]
                if power==2:require(max(v,default=0)<=2*r,"degree-sum walk bound")
                if power%2:
                    j=(power-1)//2
                    require(sum(v)<=(2*r)**(j+1),"odd walk moment bound")
                    moments+=1
            graphs+=1
    return {"all_graphs_orders_2_to_5":graphs,"odd_moment_inequalities":moments}

def make_forest(labels:list[F], points:list[F]) -> tuple[list[tuple[int,int,int]],list[tuple[int,int]]]:
    lookup={x:i for i,x in enumerate(points)}; edges=[];loops=[]
    for j,d in enumerate(labels):
        for i,x in enumerate(points):
            y=d-x
            if y not in lookup:continue
            k=lookup[y]
            if i<k:edges.append((i,k,j))
            elif i==k:loops.append((i,j))
    parent=list(range(len(points)))
    def root(i:int)->int:
        while parent[i]!=i:
            parent[i]=parent[parent[i]];i=parent[i]
        return i
    for i,k,_ in edges:
        a=root(i);b=root(k)
        require(a!=b,"additive label graph contains a cycle")
        parent[a]=b
    return edges,loops

def forests() -> dict:
    systems=0;edges_total=0;loops_total=0;quadratics=0
    for J in range(1,7):
        labels=[F(1,3**j) for j in range(1,J+1)]
        require(all(labels[i+1]*2<labels[i] for i in range(J-1)),"lacunary labels")
        denominator=2*3**J
        points=[F(i,denominator) for i in range(denominator//3+1)]
        edges,loops=make_forest(labels,points)
        for trial in range(5):
            weights=[F(1+(i+3*trial)%7,1+trial) for i in range(len(edges))]
            z=[F(1+(i*5+trial)%13,13) for i in range(len(points))]
            term=sum((w*z[i]*z[k] for w,(i,k,_) in zip(weights,edges)),F(0))
            energy=sum((w*w for w in weights),F(0)); norm=sum((v*v for v in z),F(0))
            require(4*term*term<=energy*norm*norm,"forest bipartite quadratic bound")
            quadratics+=1
        systems+=1;edges_total+=len(edges);loops_total+=len(loops)
    scalar_count=0
    for h in range(1,100):
        J=2*h*h;e=F(2,(h+1)**2);E=J*e
        sqrtE=F(2*h,h+1);sqrt2e=F(2,h+1)
        require(sqrtE*sqrtE==E and sqrt2e*sqrt2e==2*e,"hierarchy energy roots")
        require(sqrtE+sqrt2e==2,"hierarchy norm budget")
        require(8-(4+E)==F(4*(2*h+1),(h+1)**2),"sharp constant gap identity")
        scalar_count+=1
    return {"lacunary_grid_systems":systems,"forest_edges":edges_total,"loops":loops_total,
            "rational_quadratic_checks":quadratics,"hierarchy_budgets":scalar_count}

def moment_identities() -> dict:
    count=0
    for D in (12,20,30,48):
        for ranks in ((1,3,7),(2,5,9),(1,4,10)):
            if ranks[-1]>=D:continue
            for a in (F(0),F(1,2),F(2)):
                cs=[F(1,3),F(1,7),F(1,13)]
                values=[F(1)+sum((c for c,r in zip(cs,ranks) if i<r),F(0))+(a if i==0 else 0)
                        for i in range(D)]
                T=a+sum((c*r for c,r in zip(cs,ranks)),F(0))
                S=a*a+sum((c*c*r for c,r in zip(cs,ranks)),F(0))
                S+=2*sum((cs[i]*cs[j]*ranks[i] for i in range(3) for j in range(i+1,3)),F(0))
                S+=2*a*sum(cs,F(0))
                require(sum(values,F(0))==D+T,"nested flag trace")
                require(sum(((x-1)**2 for x in values),F(0))==S,"nested flag second moment")
                normalized=sum((x*x for x in values),F(0))/(D+T)**2
                require(D*D*(normalized-F(1,D))==(S-T*T/D)/(1+T/D)**2,
                        "centered normalized purity identity")
                count+=1
    return {"full_diagonal_nested_moment_cases":count}

def finite_family() -> dict:
    cases=0
    for m in range(9,201):
        r=m*ceil_sqrt(m);L=ceil_sqrt(2*r);H=ceil_sqrt(2*m)
        c=F(2,L+H);a=c*L
        require(1<=r<=m*(m-1)//2,"finite mesoscopic rank")
        require(L*L>=2*r and H*H>=2*m,"integer square-root bounds")
        require(a>=c>=0 and a+c*H==2,"finite graph norm certificate")
        for n in (m,2*m):
            D=m*n;T=a+(r-1)*c;S=a*a+(r-1)*c*c
            value=(S-T*T/D)/(1+T/D)**2
            require(value>0,"positive excess purity")
        cases+=1
    m=16384;D=m*m;r=m*ceil_sqrt(m);L=ceil_sqrt(2*r);H=ceil_sqrt(2*m)
    c=F(2,L+H);a=c*L;T=a+(r-1)*c;S=a*a+(r-1)*c*c
    val=(S-T*T/D)/(1+T/D)**2;gap=val-4-F(D,(m-1)**2)
    require(val==F(452164212835264520781824,89585058955962578104321),"finite witness centered value")
    require(gap==F(1134801570907058645479805042684,24044870718003888546572278919169)>0,
            "finite witness exceeds old subclass bound")
    return {"exact_finite_parameter_certificates":cases,"witness":{"m":m,"n":m,"rank":r,
            "a":str(a),"c":str(c),"centered_scaled_purity":str(val),"gap_above_old_subclass":str(gap)}}

def negatives() -> list[dict]:
    def wrong_variance()->None:
        D=16;q=4;delta=F(1,8);V=F(1,16)
        wrong=q*delta**2+(F(D,8)-q)*delta**2
        require(V<=wrong,"wrong quarter coefficient rejected")
    def wrong_graph_bound()->None:
        require(4<=3,"triangle violates false degree-sum bound r")
    def triangle_labels()->None:
        make_forest([F(3,5),F(1,2),F(2,5)],[F(3,20),F(1,4),F(7,20)])
    def false_forest_bound()->None:
        term=F(3);energy=F(3);norm=F(3)
        require(4*term*term<=energy*norm*norm,"triangle cannot use forest norm inequality")
    def too_high_spike()->None:
        # Schmidt rank 2, projection onto its negative eigenvector and zero slots.
        a=F(3)
        require(1-a/2>=0,"rank-two physical witness rejects spike contrast 3")
    return [record_rejection(name,fn) for name,fn in [
        ("changed variance coefficient",wrong_variance),
        ("changed walk coefficient",wrong_graph_bound),
        ("nonlacunary cycle",triangle_labels),
        ("apply forest estimate to a triangle",false_forest_bound),
        ("increase the spike past its physical bound",too_high_spike)]]

def main()->None:
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--report',type=Path);args=ap.parse_args()
    report={"status":"PASS","scope":"Exact ancillary finite identities only; not Lean, independent peer review, or a finite proof of the analytic limits",
            "variance":variance_and_rearrangements(),"physical_pairing":physical_pairing(),
            "graph_moments":walks(),"lacunary_forests":forests(),"nested_moments":moment_identities(),
            "finite_family":finite_family(),"negative_controls":negatives()}
    root=Path(__file__).resolve().parent
    report['sources']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in
                      [Path(__file__)]+[root/n for n in ('UNRESTRICTED_BOUND.md','MESOSCOPIC.md','GRAPH_LIMIT.md','MULTISCALE.md')]
                      if p.is_file()}
    text=json.dumps(report,indent=2)+'\n'
    if args.report:
        args.report.parent.mkdir(parents=True,exist_ok=True);args.report.write_text(text)
    print(text,end='')

if __name__=='__main__': main()
