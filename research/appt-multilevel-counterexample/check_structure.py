#!/usr/bin/env python3
"""Exact ancillary identities for phase rigidity and finite hierarchies.
Finite tests do not certify the analytic limits or all-unitary theorem.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
from random import Random
from check import require
ROOT=Path(__file__).resolve().parent

def psd(A):
    B=[list(row) for row in A];n=len(B)
    require(all(B[i][j]==B[j][i] for i in range(n) for j in range(n)), 'symmetric rational matrix')
    for k in range(n):
        p=B[k][k]
        if p<0:return False
        if not p:
            if any(B[k][j] for j in range(k+1,n)):return False
            continue
        for i in range(k+1,n):
            for j in range(k+1,n):B[i][j]-=B[i][k]*B[k][j]/p
    return True

def triangular(eta,m):
    rows=[];degree=[F(0)]*m;matrix=[[F(0)]*m for _ in range(m)];k=0
    for i in range(m-1):
        rr=[]
        for j in range(i+1,m):
            w=eta[k];k+=1;rr.append(w*w);degree[i]+=w;degree[j]+=w;matrix[i][j]=matrix[j][i]=w
        rows.append(sum(rr,F(0)))
    Q=sum((x*x for x in degree),F(0))/m
    T=sum(rows[1:],F(0));penalty=F(0)
    for t in range(1,m-1):
        kappa=F((m-1)**2,m*(m-t-1))
        require(degree[t-1]**2/m>=kappa*rows[t], 'weighted triangular row bound')
        penalty+=(kappa-1)*rows[t]
    require(Q-T>=penalty>=0,'nonnegative triangular saturation defect')
    return Q,T,matrix,degree

def phase_checks():
    checked=0;random_count=0;tail_count=0;rng=Random(417922)
    for m in range(3,29):
        R=m*(m-1)//2
        for _ in range(8):
            eta=sorted([F(rng.randrange(40),17) for _ in range(R)],reverse=True)
            triangular(eta,m);random_count+=1
    for m in (64,80,100,128):
        R=m*(m-1)//2
        for _ in range(4):
            eta=sorted([F(rng.randrange(100),13) for _ in range(R)],reverse=True)
            Q,T,_,_=triangular(eta,m)
            for theta in (F(1,8),F(1,4),F(3,8)):
                index=-(-(theta*m*m).numerator//(theta*m*m).denominator)
                tail=sum((x*x for x in eta[index-1:]),F(0))
                require(tail<=4*(Q-T)/theta,'quantitative subquadratic-rank concentration bound')
                tail_count+=1
    for m in range(3,13):
        for n in (m,4*m,6*m):
            D=m*n;R=m*(m-1)//2;S=m*(m+1)//2;h=m-1
            for rank in (1,R,D//2,D-1):
                families=[[F(1)+F(2,m-1)*int(i<rank) for i in range(D)]]
                if m>=4:families.append([F(2*m-5+2*int(i<rank)+4*(m-4)*int(i==0)) for i in range(D)])
                for raw in families:
                    tr=sum(raw,F(0));lam=[F(99,100)*v/tr+F(1,100*D) for v in raw]
                    b=lam[D-S];g=[(lam[i]-lam[-1-i])/b for i in range(R)]
                    w=g[-1];eta=[x-w for x in g];A=sum(eta,F(0));H=sum((x*x for x in eta[:h]),F(0))
                    Q,T,G,degrees=triangular(eta,m);u=F(4*h,m)
                    W=(sum((x*x for x in lam),F(0))-F(1,D))/(b*b)
                    C=max(F(8),4+F(D,h*h));alpha=2*A/m
                    slacks=[4-H,4-Q-u*w*A-h*h*w*w,Q-T,H+T+w*A+F(D,4)*w*w-W]
                    require(all(x>=0 for x in slacks),'all four physical purity defects nonnegative')
                    penalty=(h*h-F(D,4))*w*w if D<=4*h*h else (F(D,4)-h*h)*(F(4,h*h)-w*w)
                    require(C-W==penalty+(u-1)*w*A+sum(slacks,F(0)), 'exact phase defect decomposition')
                    B=[[G[i][j]+(w if i!=j else 0) for j in range(m)] for i in range(m)]
                    M=[[(2 if i==j else 0)-B[i][j] for j in range(m)] for i in range(m)]
                    require(psd(M),'physical rearranged graph bound')
                    yBy=sum((degrees[i]*B[i][j]*degrees[j] for i in range(m) for j in range(m)),F(0))/m
                    require(yBy>=0,'positive-vector quadratic term')
                    left=((2-h*w)*alpha-Q)**2
                    require(left<=(2-alpha-h*w)*(2*Q-yBy)<=2*Q*(2-alpha-h*w), 'critical matrix Cauchy-Schwarz obstruction')
                    z=(lam[R-1]+lam[D-R])/2
                    pa=[(lam[i]-z)/b-w/2 for i in range(R)]
                    pb=[(z-lam[-1-i])/b-w/2 for i in range(R)]
                    require(all(x>=0 for x in pa+pb),'paired centered excesses')
                    middle=lam[R:D-R]
                    md=sum((w*w/4-((x-z)/b)**2 for x in middle),F(0))
                    decomp=2*sum((x*y for x,y in zip(pa,pb)),F(0))+md+D*((z-F(1,D))/b)**2
                    require(slacks[3]==decomp,'exact spectral-centering defect')
                    a=m*w/2;X=[m*(v-z)/b for v in lam];Y=[min(a,max(-a,x)) for x in X]
                    require(sum((abs(x-y) for x,y in zip(X,Y)),F(0))/D==F(m,D)*A, 'empirical clipping cost')
                    require(sum((a*a-y*y for y in Y),F(0))/D==F(m*m,D)*md,'clipped second-moment defect')
                    checked+=1
    return {'arbitrary_sorted_weight_lists':random_count,'tail_bound_checks':tail_count,
            'SOS_or_projection_APPT_mixtures':checked,'rational_PSD_graph_tests':checked}

def forest_checks():
    vertices=0;components=0;loop_components=0
    for J in range(1,6):
        den=2*3**J;labels=[2*3**(J-i) for i in range(1,J+1)]
        adjacency={v:[] for v in range(den+1)};loops={}
        for i,label in enumerate(labels,1):
            for u in range(label//2+1):
                v=label-u
                if u==v:loops[u]=i
                else:adjacency[u].append((v,i));adjacency[v].append((u,i))
        seen=set()
        for root in adjacency:
            if root in seen:continue
            seen.add(root);stack=[root];part=[];edges=[]
            while stack:
                u=stack.pop();part.append(u)
                for v,j in adjacency[u]:
                    if u<v:edges.append((u,v,j))
                    if v not in seen:seen.add(v);stack.append(v)
            require(len(edges)==len(part)-1,'lacunary off-diagonal component is a tree')
            lp=[loops[u] for u in part if u in loops]
            require(len(lp)<=1,'at most one loop per lacunary component')
            if lp:
                require(all(j<lp[0] for _,_,j in edges),'loop component uses only preceding labels')
                loop_components+=1
            vertices+=len(part);components+=1
    return {'rational_atom_locations':vertices,'components':components,'one_loop_components':loop_components}

def hierarchy_checks():
    d=F(4);energies=[];optimal=[];arrow=0;inverse=0
    for j in range(1,11):
        previous=d;e=d*d/8;energies.append(e);Eprev=sum(energies[:-1],F(0));ell=previous/2
        require(Eprev+2*ell==4 and ell*ell==2*e,'active prefix spectral-radius budget')
        M=[[F(0)]*j for _ in range(j)];M[0][0]=4-2*ell
        ds=F(4)
        for i in range(1,j):
            M[i][i]=2;M[0][i]=M[i][0]=-ds/2;ds=ds-ds*ds/8
        require(psd(M),'optimal rational arrowhead is positive semidefinite')
        kernel=[F(1)]+[-M[i][0]/2 for i in range(1,j)]
        require(all(sum((M[i][k]*kernel[k] for k in range(j)),F(0))==0 for i in range(j)),'arrowhead quotient has exact eigenvalue two')
        arrow+=1;d=previous-previous*previous/8
        require(1/d-1/previous==1/(8*(1-previous/8)),'reciprocal deficit recursion')
        require(F(4,j+1)<=d<=F(8,j+2),'hierarchy depth bounds')
        optimal.append(4-d);inverse+=1
    rng=Random(827446);allocations=0
    for J in range(1,8):
        for _ in range(80):
            total=F(0)
            for j in range(1,J+1):
                inc=F(rng.randrange(101),100)*(4-total)**2/8
                require(8*inc<=(4-total)**2,'admissible rational prefix allocation')
                total+=inc
                require(total<=optimal[j-1],'greedy recursion bounds every energy prefix')
            allocations+=1
    return {'exact_optimal_arrowheads':arrow,'reciprocal_identities':inverse,
            'nonoptimal_feasible_allocations':allocations,
            'first_three_sharp_coefficients':[str(4+v) for v in optimal[:3]]}

def negatives():
    require((F(0)-3)**2>2*3*(2-1),'intermediate critical profile violates matrix bound')
    roots=(F(1,5),F(3,10));labels=(F(3,5),F(1,2),F(2,5))
    require(2*roots[0] in labels and 2*roots[1] in labels and sum(roots) in labels,
            'nonlacunary connected double-loop obstruction')
    require(8*F(2)>(4-F(2))**2,'single-level tests miss excessive second energy')
    for N in (2,10,100):
        require(F(1,N*N)*N==F(1,N) and F(1,N*N)*N*N==1,'vanishing first moment does not imply vanishing second moment')
    return ['r=1,Q=3 falsely saturates the scalar budget but fails matrix positivity',
            'nonlacunary two-loop component','individually allowed energies violate the prefix budget',
            'W1 convergence does not imply second-moment convergence']

def nested_graph_counts():
    import math
    cases=0;bad_budgets=0
    for J in range(1,4):
        for factor in (6,9,12):
            exponent=factor*3**J;M=3**exponent
            ranks=[3**(2*exponent-exponent//(3**i)) for i in range(1,J+1)]
            require(all(r<M*(M-1)//2 for r in ranks), 'nested ranks fit negative witness space')
            for j in range(J):
                prev=ranks[j-1] if j else 0
                q=(1+math.isqrt(1+8*(ranks[j]-prev)))//2
                while q*(q-1)//2>ranks[j]-prev:q-=1
                groups=[]
                for i in range(j):
                    old=ranks[i-1] if i else 0
                    size=(ranks[i]-old)//q;groups.append(size)
                    require(size>0 and q*size<=ranks[i]-old, 'each nested bipartite increment fits')
                    require(F(q*size,ranks[i])>=F(99,100), 'owned bipartite edge count approximates rank')
                require(q+sum(groups)<=M, 'central and peripheral vertex groups fit')
                require(q*(q-1)//2+prev<=ranks[j], 'clique and previous flag fit next rank')
                require(F(q*(q-1),2*ranks[j])>=F(99,100), 'central clique approximates target rank')
                if j:
                    qbad=(1+math.isqrt(1+8*ranks[j]))//2
                    require(qbad*(qbad-1)//2+prev>ranks[j], 'ignoring inherited rank gives an invalid flag')
                    bad_budgets+=1
                cases+=1
    return {'exact_large_integer_count_cases':cases,'invalid_unnested_budgets_rejected':bad_budgets,
            'scope':'Construction counts only; not materialized huge graphs or finite APPT certification'}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--report',type=Path);args=ap.parse_args()
    result={'status':'PASS','scope':'Exact finite ancillary identities; not proof of limits, all-unitary sufficiency, independent CI, or Lean verification',
            'phase_rigidity':phase_checks(),'lacunary_components':forest_checks(),
            'optimal_hierarchy':hierarchy_checks(),'nested_graph_counts':nested_graph_counts(),'negative_controls':negatives()}
    names=('PHASE_RIGIDITY.md','OPTIMAL_HIERARCHY.md','check_structure.py','check.py','MULTISCALE.md','SHARP_ASYMPTOTIC.md')
    result['source_hashes']={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in names}
    text=json.dumps(result,indent=2)+'\n'
    if args.report:args.report.parent.mkdir(parents=True,exist_ok=True);args.report.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
