from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
exec(Path('/mnt/d/math/tmp/breadth-quantum-20261015/switched_certificate.py').read_text().split('records=[];rng=')[0])
R=Rmatrix(3,3);cases={}
u=np.zeros(27,complex);u[[0,13,26]]=1;cases['GHZ3']=u/la.norm(u)
u=np.zeros(27,complex)
for p in itertools.permutations(range(3)):
    sg=(-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3));u[np.ravel_multi_index(p,(3,3,3))]=sg
cases['SU3_antisymmetric']=u/la.norm(u)
u=np.zeros(27,complex);u[[1,3,9]]=1;cases['qubit_W']=u/la.norm(u)
u=np.zeros(27,complex);u[[5,15,19]]=1;cases['cyclic_012']=u/la.norm(u)
u=np.zeros(27,complex)
for a,b in itertools.product(range(3),repeat=2):u[np.ravel_multi_index((a,b,(a+b)%3),(3,3,3))]=1
cases['qutrit_perfect_tensor']=u/la.norm(u)
records=[];rng=np.random.default_rng(153124)
for label,u in cases.items():
    for noise in [0.,.01,.1]:
        w=u+noise*(rng.normal(size=27)+1j*rng.normal(size=27));w/=la.norm(w)
        C,A,L=certificate(R,w);ev,ve=la.eigh(C,driver='evd')
        rec={'label':label,'noise':noise,'min':float(ev[0]),'null_count':int(np.sum(abs(ev)<1e-9)),'negative_count':int(np.sum(ev<-1e-9)),'min_positive':float(ev[ev>1e-9][0])}
        records.append(rec)
        if ev[0]<-1e-8:np.savez_compressed(PRIVATE/f'switched-structured-negative-{label}-{noise}.npz',u=w,R=R,C=C,witness=ve[:,0])
        print(json.dumps(rec),flush=True)
(PUBLIC/'SWITCHED_STRUCTURED.json').write_text(json.dumps({'schema':'strong-co-Choi-structured-control-v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Only a stronger sufficient co-Choi route. No actual rank-two counterexample or full theorem is implied.','records':records},indent=2)+'\n')
