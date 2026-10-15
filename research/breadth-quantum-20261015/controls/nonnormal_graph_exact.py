"""Exact finite nonnormal graph-code probes via affine isotropic cosets.

The complete target remains all complex rank-two operators for all copies.
Graph pairs and all their Pauli pairs are only a structured probe.
"""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import numpy as np, math,itertools,json,datetime,time
PRIVATE=Path('/mnt/d/math/tmp/breadth-quantum-20261015')
PUBLIC=Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015')
exec((PRIVATE/'graph_code_exact.py').read_text().split('start=time.monotonic();rng=')[0])

def null3(A):
    A=np.asarray(A,dtype=np.int16).copy()%3;m,n=A.shape;r=0;piv=[]
    for j in range(n):
        candidates=np.flatnonzero(A[r:,j])
        if not len(candidates):continue
        rr=r+int(candidates[0]);A[[r,rr]]=A[[rr,r]]
        if A[r,j]==2:A[r]=(A[r]*2)%3
        for ii in range(m):
            if ii!=r and A[ii,j]:A[ii]=(A[ii]-A[ii,j]*A[r])%3
        piv.append(j);r+=1
        if r==m:break
    free=[j for j in range(n) if j not in piv];basis=[]
    for f in free:
        v=np.zeros(n,np.int16);v[f]=1
        for i,p in enumerate(piv):v[p]=-A[i,f]%3
        basis.append(v)
    out=np.array(basis,dtype=np.int16).reshape(len(free),n)
    assert not np.any((np.asarray(A[:r])@out.T)%3)
    return out

def weight_sum(xs,zs,k):
    weights=np.count_nonzero((xs!=0)|(zs!=0),axis=1)
    return sum((-1)**int(w)*5**(k-int(w)) for w in weights)

def direct_coset(G,H,x0,b):
    k=len(G);D=(G-H)%3;K=null3(D);coeff=ternary_vectors(len(K));hh=(coeff@K)%3
    a=weight_sum(hh,(hh@G)%3,k)
    xx=(hh+x0)%3;cc=weight_sum(xx,(xx@G+b)%3,k)
    return a,cc

def coset_fourier(G,H):
    k=len(G);K=null3((G-H)%3);r=len(K)
    C=np.concatenate([K,(K@G)%3],axis=1)
    B=null3(C);ell=len(B);n=3**ell
    assert ell==2*k-r
    f=np.empty(n,np.int64)
    for s in range(0,n,100000):
        X=ternary_vectors(ell,s,min(n,s+100000));v=(X@B)%3
        wt=np.count_nonzero((v[:,:k]!=0)|(v[:,k:]!=0),axis=1)
        f[s:s+len(X)]=np.array([(-2)**int(w) for w in wt],np.int64)
    F=integer_fourier3(f,ell)*((-1)**k)
    a=int(F[0]);assert a>0
    ix=int(np.argmax(abs(F)));cv=int(F[ix]);margin=a-abs(cv)
    assert a%3**(k-r)==0
    actual_a,_=direct_coset(G,H,np.zeros(k,np.int16),np.zeros(k,np.int16))
    assert actual_a==a//3**(k-r)
    return {'intersection_dimension':r,'fourier_dimension':ell,'cosets_checked':n,'a_numerator_scaled':a,'largest_cross_numerator_scaled_signed':cv,'closest_coset_index':ix,'minimum_numerator_margin_scaled':margin,'exact_negative':margin<0,'zero_coset_count':int(np.sum(abs(F)==a))},B,F

def controls_nonnormal():
    rng=np.random.default_rng(15318);rows=[]
    for k in [2,3,4]:
        G=np.triu(rng.integers(0,3,size=(k,k),dtype=np.int16),1);G+=G.T
        H=G.copy();H[0,1]=(H[0,1]+1)%3;H[1,0]=H[0,1]
        ug,X=graph_state(G);vh,_=graph_state(H)
        for trial in range(5):
            x0=rng.integers(0,3,size=k,dtype=np.int16);b=rng.integers(0,3,size=k,dtype=np.int16)
            c=(b+(G-H)@x0)%3
            if not np.any(b) or not np.any(c):continue
            u2=ug*np.exp(2j*np.pi*((X@b)%3)/3);v2=vh*np.exp(2j*np.pi*((X@c)%3)/3)
            A1=np.outer(ug,vh.conj());A2=np.outer(u2,v2.conj())
            a=np.vdot(A1,local_form(A1,(3,)*k,.5)).real
            aa=np.vdot(A2,local_form(A2,(3,)*k,.5)).real
            z=np.vdot(A1,local_form(A2,(3,)*k,.5))
            an,cn=direct_coset(G,H,x0,b)
            phase=np.exp(2j*np.pi*(2*np.dot(b-c,x0)%3)/3)
            assert abs(a-an/6**k)<1e-12 and abs(aa-a)<1e-12
            assert abs(abs(z)-abs(cn)/6**k)<1e-12
            # Record phase error but use the magnitude for determinant.
            rows.append({'k':k,'a':a,'a_exact_fraction':f'{an}/{6**k}','cross_abs':abs(z),'cross_exact_abs_fraction':f'{abs(cn)}/{6**k}','cross_phase_error':float(abs(z-phase*cn/6**k))})
        res,B,F=coset_fourier(G,H)
        # Directly compare integer coset sums with Fourier at arbitrary v.
        for trial in range(5):
            x0=rng.integers(0,3,size=k,dtype=np.int16);z0=rng.integers(0,3,size=k,dtype=np.int16);b=(z0-G@x0)%3
            an,cn=direct_coset(G,H,x0,b);sy=(B@np.r_[x0,z0])%3;idx=int(np.ravel_multi_index(tuple(sy),(3,)*len(B)))
            assert int(F[idx])==cn*3**(k-res['intersection_dimension'])
    return rows

start=time.monotonic();rng=np.random.default_rng(153333)
results={'schema':'finite-nonnormal-graph-coset-exact-v1','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Distinct graph-state Pauli pairs, legitimate complex nonnormal rank-two witnesses. Exact finite coset tests only; not all complex two-planes or arbitrary copies.','controls':controls_nonnormal(),'records':[]}
print(json.dumps({'event':'nonnormal_controls_passed','number':len(results['controls']),'max_phase_error':max(r['cross_phase_error'] for r in results['controls'])}),flush=True)
for k,number in [(3,27),(4,729),(5,500),(6,100),(8,30),(10,10),(12,3)]:
    edges=list(itertools.combinations(range(k),2));count=cosets=neg=zeros=0;best=None
    all_graphs=k<=4
    for trial in range(number):
        if all_graphs:
            labels=np.unravel_index(trial,(3,)*len(edges));G=np.zeros((k,k),np.int16)
            for (a,b),x in zip(edges,labels):G[a,b]=G[b,a]=x
        else:
            G=np.triu(rng.integers(0,3,size=(k,k),dtype=np.int16),1);G+=G.T
            if trial==0:G=np.ones((k,k),np.int16)-np.eye(k,dtype=np.int16)
        H=G.copy();H[0,1]=(H[0,1]+1)%3;H[1,0]=H[0,1]
        rec,B,F=coset_fourier(G,H);count+=1;cosets+=rec['cosets_checked'];neg+=rec['exact_negative'];zeros+=rec['zero_coset_count']
        ratio=rec['minimum_numerator_margin_scaled']/rec['a_numerator_scaled']
        if best is None or ratio<best['relative_margin']:
            best={'trial':trial,'G':G.tolist(),'H':H.tolist(),'relative_margin':ratio,**rec}
        if rec['exact_negative']:
            np.savez_compressed(PRIVATE/f'nonnormal-graph-negative-k{k}.npz',G=G,H=H,B=B,F=F);break
    record={'k':k,'all_weighted_G_but_one_fixed_edge_perturbation':all_graphs,'graph_pairs_checked':count,'all_cosets_checked':cosets,'negative_graph_pairs':neg,'zero_coset_total':zeros,'closest':best,'elapsed_seconds':time.monotonic()-start,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    results['records'].append(record)
    (PUBLIC/'NONNORMAL_GRAPH_EXACT.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(record),flush=True)
    if neg:break
results['closed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();results['complete_target_solved']=False
(PUBLIC/'NONNORMAL_GRAPH_EXACT.json').write_text(json.dumps(results,indent=2)+'\n')
