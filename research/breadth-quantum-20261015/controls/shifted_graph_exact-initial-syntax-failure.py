"""Exact phase-offset nonnormal graph-code Gram tests.

General Pauli character on the common stabilizer is retained. Omitting
this character would silently shrink the tested structured sector.
"""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
exec(Path('/mnt/d/math/tmp/breadth-quantum-20261015/nonnormal_graph_exact.py').read_text().split('start=time.monotonic();rng=')[0])

def fourier_eisenstein(values,k):
    a=values.reshape((3,)*k).copy();b=np.zeros_like(a)
    for axis in range(k):
        av=np.moveaxis(a,axis,0);bv=np.moveaxis(b,axis,0)
        a0,a1,a2=[v.copy() for v in av];b0,b1,b2=[v.copy() for v in bv]
        av[0]=a0+a1+a2;bv[0]=b0+b1+b2
        av[1]=a0-b1-a2+b2;bv[1]=b0+a1-b1-a2
        av[2]=a0-a1+b1-b2;bv[2]=b0-a1+a2-b2
    return a.ravel(),b.ravel()

def eisnorm(a,b):return int(a)*int(a)-int(a)*int(b)+int(b)*int(b)

def direct_shifted(G,H,x0,b,g):
    k=len(G);K=null3((G-H)%3);hh=(ternary_vectors(len(K))@K)%3
    out=[]
    for xx in [hh,(hh+x0)%3]:
        zz=(xx@G+(0 if np.array_equal(xx,hh) else b))%3
        wt=np.count_nonzero((xx!=0)|(zz!=0),axis=1)
        phase=(-xx@g)%3;counts=[sum((-1)**int(w)*5**(k-int(w)) for w in wt[phase==j]) for j in range(3)]
        out.append((counts[0]-counts[2],counts[1]-counts[2]))
    return out

def shifted_fourier(G,H,g):
    k=len(G);K=null3((G-H)%3);r=len(K)
    C=np.concatenate([K,(K@G)%3],axis=1);B=null3(C);ell=len(B);n=3**ell
    w0=np.r_[-g,np.zeros(k,np.int16)]%3
    f=np.empty(n,np.int64)
    for start in range(0,n,100000):
        Z=ternary_vectors(ell,start,min(n,start+100000));v=(Z@B+w0)%3
        wt=np.count_nonzero((v[:,:k]!=0)|(v[:,k:]!=0),axis=1)
        f[start:start+len(Z)]=np.array([(-2)**int(w) for w in wt],np.int64)
    aa,bb=fourier_eisenstein(f,ell);aa*=(-1)**k;bb*=(-1)**k
    A=int(aa[0]);assert int(bb[0])==0 and A>0
    # Squared norms can exceed int64 at large k; use object integers when
    # needed, so the determinant test never silently wraps.
    if max(int(np.max(abs(aa))),int(np.max(abs(bb))))>1000000000:
        aob=aa.astype(object);bob=bb.astype(object);ns=aob*aob-aob*bob+bob*bob
    else:ns=aa*aa-aa*bb+bb*bb
    ix=int(np.argmax(ns));cross2=int(ns[ix]);margin=A*A-cross2
    (dira,dirb),_=direct_shifted(G,H,np.zeros(k,np.int16),np.zeros(k,np.int16),g)
    assert dirb==0 and A==dira*3**(k-r)
    return {'intersection_dimension':r,'fourier_dimension':ell,'cosets_checked':n,'phase_offset':g.tolist(),'a_numerator_scaled':A,'max_cross_squared_numerator_scaled':cross2,'closest_coset_index':ix,'minimum_squared_numerator_margin_scaled':margin,'exact_negative':margin<0,'zero_coset_count':int(np.sum(ns==A*A))},B,aa,bb

def controls_shifted():
    rng=np.random.default_rng(1515032);rows=[]
    for k in [2,3,4]:
        G=np.triu(rng.integers(0,3,size=(k,k),dtype=np.int16),1);G+=G.T;H=G.copy();H[0,1]=(H[0,1]+1)%3;H[1,0]=H[0,1]
        ug,X=graph_state(G);vh,_=graph_state(H)
        for trial in range(6):
            x0=rng.integers(0,3,size=k,dtype=np.int16);b=rng.integers(0,3,size=k,dtype=np.int16);g=rng.integers(0,3,size=k,dtype=np.int16);c=(b+(G-H)@x0)%3
            if not np.any(b) or not np.any(c):continue
            u2=ug*np.exp(2j*np.pi*((X@b)%3)/3);v1=vh*np.exp(2j*np.pi*((X@g)%3)/3);v2=vh*np.exp(2j*np.pi*((X@(g+c))%3)/3)
            A1=np.outer(ug,v1.conj());A2=np.outer(u2,v2.conj())
            a=np.vdot(A1,local_form(A1,(3,)*k,.5)).real;z=np.vdot(A1,local_form(A2,(3,)*k,.5))
            (da,db),(ca,cb)=direct_shifted(G,H,x0,b,g);assert db==0
            assert abs(a-da/6**k)<1e-12
            assert abs(abs(z)-math.sqrt(eisnorm(ca,cb))/6**k)<1e-12
            rec,B,aa,bb=shifted_fourier(G,H,g);v=np.r_[x0,(G@x0+b)%3];sy=(B@v)%3;idx=int(np.ravel_multi_index(tuple(sy),(3,)*len(B)))
            assert eisnorm(aa[idx],bb[idx])==eisnorm(ca,cb)*3**(2*(k-rec['intersection_dimension']))
            rows.append({'k':k,'diagonal_error':abs(a-da/6**k),'cross_absolute_error':abs(abs(z)-math.sqrt(eisnorm(ca,cb))/6**k),'exact_Fourier_coset_norm_checked':True})
    return rows

start=time.monotonic();rng=np.random.default_rng(153315)
results={'schema':'finite-character-shifted-nonnormal-graph-exact-v1','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Complex distinct graph-state Pauli-pair witnesses retaining arbitrary chosen character on common stabilizer. Finite structured tests, not a general or all-copy proof.','controls':controls_shifted(),'records':[]}
print(json.dumps({'event':'shifted_controls_passed','number':len(results['controls'])}),flush=True)
for k,numgraphs,numchars in [(3,27,3),(4,729,9),(5,100,27),(6,20,81),(8,10,20),(10,4,10),(12,1,3)]:
    count=cosets=neg=zero=0;closest=None
    edges=list(itertools.combinations(range(k),2))
    for trial in range(numgraphs):
        G=np.zeros((k,k),np.int16)
        if k<=4:
            for (i,j),a in zip(edges,np.unravel_index(trial,(3,)*len(edges))):G[i,j]=G[j,i]=a
        else:
            G=np.triu(rng.integers(0,3,size=(k,k),dtype=np.int16),1);G+=G.T
        H=G.copy();H[0,1]=(H[0,1]+1)%3;H[1,0]=H[0,1]
        # One-edge perturbation gives K={h:h0=h1=0}; representative
        # characters g have first two coordinates zero.
        for character in range(numchars):
            if numchars==3**(k-2):g=np.r_[np.zeros(2,np.int16),ternary_vectors(k-2,character,character+1)[0]]
            else:g=rng.integers(0,3,size=k,dtype=np.int16)
            rec,B,aa,bb=shifted_fourier(G,H,g);count+=1;cosets+=rec['cosets_checked'];neg+=rec['exact_negative'];zero+=rec['zero_coset_count']
            relative=rec['minimum_squared_numerator_margin_scaled']/rec['a_numerator_scaled']**2
            if closest is None or relative<closest['relative_squared_margin']:
                closest={'graph_trial':trial,'G':G.tolist(),'H':H.tolist(),'relative_squared_margin':relative,**rec}
            if rec['exact_negative']:
                np.savez_compressed(PRIVATE/f'shifted-nonnormal-negative-k{k}.npz',G=G,H=H,g=g,B=B,a=aa,b=bb);break
        if neg:break
    record={'k':k,'weighted_G_graphs_requested':numgraphs,'characters_per_graph_requested':numchars,'all_characters_per_graph':numchars==3**(k-2),'graph_character_pairs_checked':count,'all_cosets_checked':cosets,'negative_pairs':neg,'zero_cosets':zero,'closest':closest,'elapsed_seconds':time.monotonic()-start,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    results['records'].append(record)
    (PUBLIC/'SHIFTED_NONNORMAL_GRAPH_EXACT.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(record),flush=True)
    if neg:break
results['closed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();results['complete_target_solved']=False
(PUBLIC/'SHIFTED_NONNORMAL_GRAPH_EXACT.json').write_text(json.dumps(results,indent=2)+'\n')
