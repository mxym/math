"""Portable exact controls for rejected sufficient routes and physical signs.
Usage: python exact_route_controls.py --output NEW_FILE.json
No old evidence is overwritten unless an explicit path is given.
"""
from pathlib import Path
import argparse,json,datetime,itertools
import sympy as sp
ap=argparse.ArgumentParser();ap.add_argument('--output',required=True);args=ap.parse_args()
target=Path(args.output);assert not target.exists(),'choose a new output file'
lam=sp.Symbol('lam',real=True)
def pt2(C,d=3):
    return sp.Matrix(d*d,d*d,lambda r,c:C[(r//d)*d+c%d,(c//d)*d+r%d])
def partial(C,slot,d=3):
    return sp.Matrix(d,d,lambda r,c:sum(C[(a*d+r if slot==0 else r*d+a),(a*d+c if slot==0 else c*d+a)] for a in range(d)))
def q2(C,l=lam,d=3):
    return sp.expand((C.H*C).trace()-l*sum((partial(C,j,d).H*partial(C,j,d)).trace() for j in [0,1])+l*l*sp.conjugate(C.trace())*C.trace())
P=sp.diag(1,0,0);I=sp.eye(3);H=sp.kronecker_product(I,P)-sp.kronecker_product(P,I)
K=sp.zeros(9)
for i in [1,2]:K[3*i,i]=K[i,3*i]=1
C=H+sp.I*K
assert C.rank()==2 and H.rank()==4 and H.eigenvals()=={sp.Integer(0):5,sp.Integer(-1):2,sp.Integer(1):2}
assert q2(H)==4-12*lam and q2(K)==4 and q2(C)==8-12*lam
records={'signature_route':{'H_inertia':[2,2,5],'H_rank':4,'actual_completion_rank':2,'QH':'4-12*lambda','QK':'4','QC':'8-12*lambda','endpoint_values':[-2,4,2],'interpretation':'rank4 Hermitian strong extension fails; actual complex rank2 completion is nonnegative'}}

def sw(i,j):
    S=sp.zeros(16)
    for x in itertools.product(range(2),repeat=4):
        y=list(x);y[i],y[j]=y[j],y[i];r=sum(x[a]*2**(3-a) for a in range(4));c=sum(y[a]*2**(3-a) for a in range(4));S[r,c]=1
    return S
A=(sp.eye(16)-sw(0,2)/2)*(sp.eye(16)-sw(1,3)/2);B=sw(2,3)*A*sw(0,1);w=sp.zeros(16,1);w[5]=w[10]=1
qa=(w.T*A*w)[0];qb=(w.T*B*w)[0];assert qa==sp.Rational(1,2) and qb==sp.Rational(5,2)
records['four_ray_route']={'vector':['0101','1010'],'coefficients':[1,1],'w_A_w':str(qa),'w_B_w':str(qb),'w_A_minus_B_w':str(qa-qb),'interpretation':'strong Loewner sufficient certificate only, not a four-ray product witness'}

# Independent physical sign control for the attributed canonical witness.
F=sp.zeros(9);Delta=sp.zeros(9)
for i,j in itertools.product(range(3),repeat=2):F[3*i+j,3*j+i]=1
for i in range(3):Delta[3*i+i,3*i+i]=1
rho=(Delta+sp.Rational(2,3)*(sp.eye(9)-F))/7
assert rho.trace()==1 and all(x>=0 for x in rho.eigenvals())
CC=sp.zeros(9)
for r in [1,2]:
    u=sp.zeros(9,1);v=sp.zeros(9,1);u[r]=u[3*r]=1/sp.sqrt(2);v[r]=1/sp.sqrt(2);v[3*r]=-1/sp.sqrt(2);CC+=u*v.T/sp.sqrt(2)
assert CC.rank()==2 and (CC.H*CC).trace()==1
psi=sp.zeros(81,1)
for a1,a2,b1,b2 in itertools.product(range(3),repeat=4):psi[(3*a1+b1)*9+3*a2+b2]=CC[3*a1+a2,3*b1+b2]
R=pt2(rho);val=sp.simplify((psi.T*sp.kronecker_product(R,R)*psi)[0]);assert val==-sp.Rational(1,882)
records['canonical_physical_negative']={'source':'https://arxiv.org/html/2608.08836v2','actual_density_trace':'1','actual_density_positive':True,'coefficient_rank':2,'vector_squared_norm':'1','two_copy_physical_expectation':str(val),'attribution':'Existing Tabia–Chen–Hsieh result, not a new major result here'}

# The anti/anti intermediate-memory recurrence, derived entry by entry.
V=sp.zeros(9,3)
for i in range(3):
    j,k=[x for x in range(3) if x!=i];V[3*j+k,i]=1/sp.sqrt(2);V[3*k+j,i]=-1/sp.sqrt(2)
def fs(slot):
    S=sp.zeros(81)
    for a1,a2,b1,b2 in itertools.product(range(3),repeat=4):
        x=[a1,a2,b1,b2];y=x.copy();y[slot],y[2+slot]=y[2+slot],y[slot];r=(3*a1+a2)*9+3*b1+b2;c=(3*y[0]+y[1])*9+3*y[2]+y[3];S[r,c]=1
    return S
E=sp.kronecker_product(V,V);F1=fs(0);F2=fs(1);out=sp.simplify(E.T*(sp.eye(81)-lam*(F1+F2)+lam**2*(F1*F2))*E)
formula=(1-lam/2)*sp.eye(9)+(lam**2-lam/2)*F
assert out==formula
records['anti_memory_recurrence']={'unnormalized_output':'(1-lambda/2)I+(lambda^2-lambda/2)F','endpoint_normalized_output':'I/9','gray_region_PPT_proof':'effective Werner lambda=lambda*(1/2-lambda)/(1-lambda/2)<=1/12<1/3 for0<=lambda<=1/2','scope':'one specific two-input-copy compression; no arbitrary-memory theorem'}

records['created_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();records['schema']='portable-exact-route-sign-controls-v1';records['complete_target_solved']=False
target.parent.mkdir(parents=True,exist_ok=True);target.write_text(json.dumps(records,indent=2)+'\n');print(json.dumps({'output':str(target),'exact_assertions_passed':True,'major_results':0}))
