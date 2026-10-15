"""Exact graph-code rank-two probes via an integer GF(3) Fourier transform.

This samples legitimate high-copy collective normal witnesses. Neither
normality nor graph-state structure is assumed for the full N0 target.
"""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import numpy as np, math,itertools,json,datetime,time
PRIVATE=Path('/mnt/d/math/tmp/breadth-quantum-20261015')
PUBLIC=Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015')
src=(PRIVATE/'finite_rank2_search.py').read_text();exec(src[src.index('def local_form'):src.index('def controls')])

def ternary_vectors(k,start=0,stop=None):
    if stop is None:stop=3**k
    ids=np.arange(start,stop,dtype=np.int64);arr=np.empty((len(ids),k),np.int16)
    for j in range(k-1,-1,-1):arr[:,j]=ids%3;ids//=3
    return arr

def weight_function(G):
    k=len(G);n=3**k;out=np.empty(n,np.int64);hist=np.zeros(k+1,np.int64)
    for s in range(0,n,100000):
        X=ternary_vectors(k,s,min(n,s+100000));Z=(X@G)%3
        wt=np.count_nonzero((X!=0)|(Z!=0),axis=1)
        out[s:s+len(X)]=np.array([(-1)**(k-int(w))*2**int(w) for w in wt],np.int64)
        hist+=np.bincount(wt,minlength=k+1)
    return out,hist

def integer_fourier3(values,k):
    # Exact Eisenstein arithmetic a+b*omega, omega^2+omega+1=0.
    a=values.reshape((3,)*k).copy();b=np.zeros_like(a)
    for axis in range(k):
        av=np.moveaxis(a,axis,0);bv=np.moveaxis(b,axis,0)
        a0,a1,a2=[v.copy() for v in av];b0,b1,b2=[v.copy() for v in bv]
        av[0]=a0+a1+a2;bv[0]=b0+b1+b2
        av[1]=a0-b1-a2+b2;bv[1]=b0+a1-b1-a2
        av[2]=a0-a1+b1-b2;bv[2]=b0-a1+a2-b2
    assert np.max(abs(b))==0 # even F(-x)=F(x) makes every transform real.
    return a.ravel()

def graph_state(G):
    k=len(G);X=ternary_vectors(k);phase=np.sum((X@np.triu(G,1))*X,axis=1)%3
    return np.exp(2j*np.pi*phase/3)/math.sqrt(3**k),X

def controls():
    rng=np.random.default_rng(15223);out=[]
    for k in [2,3,4]:
        G=np.triu(rng.integers(0,3,size=(k,k)),1);G=G+G.T
        f,hist=weight_function(G);F=integer_fourier3(f,k)
        anum=sum(int(hist[w])*(-1)**w*5**(k-w) for w in range(k+1))
        assert F[0]==anum
        u,X=graph_state(G);Pu=np.outer(u,u.conj());A=np.vdot(Pu,local_form(Pu,(3,)*k,.5)).real
        assert abs(A-anum/6**k)<1e-12
        maxerr=0
        for idx in [1,3**k-1,3**(k-1)]:
            b=ternary_vectors(k,idx,idx+1)[0];v=u*np.exp(2j*np.pi*((X@b)%3)/3)
            assert abs(np.vdot(u,v))<1e-12
            Pv=np.outer(v,v.conj());B=np.vdot(Pu,local_form(Pv,(3,)*k,.5)).real
            err=abs(B-int(F[idx])/6**k);assert err<1e-12;maxerr=max(maxerr,err)
        out.append({'k':k,'graph':G.tolist(),'direct_cross_checks':3,'max_error':maxerr,'MacWilliams_integer_identity':True})
    return out

def inspect_graph(G):
    k=len(G);f,hist=weight_function(G);F=integer_fourier3(f,k)
    a=int(F[0]);aa=sum(int(hist[w])*(-1)**w*5**(k-w) for w in range(k+1));assert a==aa and a>0
    # idx=0 is the same ray and omitted from the rank-two comparison.
    ix=int(np.argmax(abs(F[1:])))+1;bv=int(F[ix]);margin=a-abs(bv)
    return {'a_numerator':a,'largest_cross_numerator_signed':bv,'syndrome_index':ix,'minimum_A_minus_abs_B_numerator':margin,'exact_negative':margin<0,'zero_syndromes_count':int(np.sum(abs(F[1:])==a)),'stabilizer_weight_histogram':hist.tolist()}

start=time.monotonic();rng=np.random.default_rng(15151522)
results={'schema':'finite-normal-graph-code-exact-v1','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Legitimate normal rank-two graph-state Pauli pairs at finite copy numbers; no claim covering all normal or nonnormal operators, or arbitrary k. All Fourier arithmetic uses integers in Z[omega].','controls':controls(),'records':[]}
print(json.dumps({'event':'controls_passed','checks':results['controls']}),flush=True)
for k in range(2,5):
    edges=list(itertools.combinations(range(k),2));count=neg=zero=0;min_margin=None
    for labels in itertools.product(range(3),repeat=len(edges)):
        G=np.zeros((k,k),np.int16)
        for (a,b),g in zip(edges,labels):G[a,b]=G[b,a]=g
        rec=inspect_graph(G);count+=1;neg+=rec['exact_negative'];zero+=rec['zero_syndromes_count']
        min_margin=rec['minimum_A_minus_abs_B_numerator'] if min_margin is None else min(min_margin,rec['minimum_A_minus_abs_B_numerator'])
        if rec['exact_negative']:print('NEGATIVE',k,G.tolist(),rec,flush=True);break
    record={'k':k,'all_weighted_simple_graphs':True,'graphs_checked':count,'syndrome_pairs_checked':count*(3**k-1),'negative_graphs':neg,'zero_pair_count':zero,'minimum_numerator_margin':min_margin,'elapsed_seconds':time.monotonic()-start,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    results['records'].append(record);print(json.dumps(record),flush=True)

for k,number in [(5,2000),(6,500),(8,120),(10,80),(12,12),(14,4)]:
    count=neg=zero=0;best=None
    for trial in range(number):
        G=np.triu(rng.integers(0,3,size=(k,k),dtype=np.int16),1);G=G+G.T
        if trial==0:G=np.ones((k,k),np.int16)-np.eye(k,dtype=np.int16)
        if trial==1:
            G=np.zeros((k,k),np.int16)
            for a in range(k):G[a,(a+1)%k]=G[(a+1)%k,a]=1
        rec=inspect_graph(G);count+=1;neg+=rec['exact_negative'];zero+=rec['zero_syndromes_count']
        if best is None or rec['minimum_A_minus_abs_B_numerator']/rec['a_numerator']<best['minimum_A_minus_abs_B_numerator']/best['a_numerator']:
            best={'trial':trial,'graph':G.tolist(),**rec}
        if rec['exact_negative']:break
    record={'k':k,'all_weighted_simple_graphs':False,'graphs_checked':count,'syndrome_pairs_checked':count*(3**k-1),'negative_graphs':neg,'zero_pair_count':zero,'closest':best,'elapsed_seconds':time.monotonic()-start,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    results['records'].append(record)
    (PUBLIC/'GRAPH_CODE_EXACT.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(record),flush=True)
    if neg:break
results['closed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();results['complete_target_solved']=False
(PUBLIC/'GRAPH_CODE_EXACT.json').write_text(json.dumps(results,indent=2)+'\n')
