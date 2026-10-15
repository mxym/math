"""Exact nonpositivity control for the orthogonal-map numerical probe."""
from pathlib import Path
import argparse,json,datetime,itertools
import sympy as sp
ap=argparse.ArgumentParser();ap.add_argument('--output',required=True);args=ap.parse_args();p=Path(args.output).resolve();assert not p.exists()
d=2;a=sp.Rational(3,4);beta=sp.Rational(1,3);I=sp.eye(d)
def L(X):return a*X.trace()*I-beta*(X+X.T)
out=sp.zeros(d*d)
for i,j in itertools.product(range(d),repeat=2):
    E=sp.zeros(d);E[i,j]=1;out+=sp.kronecker_product(L(E),L(E))/d
F=sp.zeros(d*d);omega=sp.zeros(d*d,1)
for i,j in itertools.product(range(d),repeat=2):F[d*i+j,d*j+i]=1
for i in range(d):omega[d*i+i]=1
formula=((d*a*a-4*a*beta)*sp.eye(d*d)+2*beta*beta*(omega*omega.T+F))/d
assert out==formula
w=sp.zeros(d*d,1);w[1]=1;w[2]=-1;val=(w.T*out*w)[0]/2;assert val==-sp.Rational(7,144)
record={'schema':'exact-orthogonal-map-negative-control-v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'d':2,'epsilon':'1/4','single_site_positive':True,'single_site_product_minimum':'1/12','input':'normalized two-use Bell state','output_antisymmetric_unit_vector_expectation':str(val),'two_copy_output_eigenvalues':{str(k):int(v) for k,v in out.eigenvals().items()},'scope':'An adversarial program sign control in dimension2, within a known map family. It is not a physical NPT state or an all-dimension theorem.','complete_target_solved':False}
p.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
