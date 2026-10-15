"""Discovery arithmetic only; exact formulas, uncertified high-precision roots.

No grid/root solve here proves the global phase diagram or uniqueness.
"""
import datetime as dt
import hashlib
import json
from pathlib import Path
import mpmath as m

m.mp.dps=90
q=lambda t:t/m.expm1(t)
s=lambda t:1+1/m.expm1(t)-1/t
g=lambda t:-m.log(q(t))-1+q(t)
gp=lambda t:s(t)*(1-q(t))
def W(K,k):
    u=K-k
    return 2*k*k/(3*u)+m.log(g(K)-g(k))-m.log(q(k))-m.log(m.expm1(g(K)))
def Wk(K,k):
    u=K-k
    return 2*k*(2*K-k)/(3*u*u)+s(k)-gp(k)/(g(K)-g(k))
def WK(K,k):
    u=K-k
    return -2*k*k/(3*u*u)+gp(K)/(g(K)-g(k))-gp(K)/(1-m.exp(-g(K)))

K,k=m.findroot((W,Wk),(m.mpf('.52'),m.mpf('.27')),tol=m.mpf('1e-75'),maxsteps=100)
assert 0<k<K<2
h=(-m.log(q(k))-g(K))/k
assert 0<h<1
row={'K':str(K),'c':str(K/2),'k':str(k),'L':str(2*k/K),'h':str(h),
 'r_cross':str(m.expm1(g(K))),'W':str(W(K,k)),'Wk':str(Wk(K,k)),
 'WK':str(WK(K,k)),'Wkk':str(m.diff(lambda t:Wk(K,t),k)),
 'admissibility_gap':str(-m.log(q(k))-g(K))}
out={'created_utc':dt.datetime.now(dt.timezone.utc).isoformat(),'decimal_digits':m.mp.dps,
 'scope':'One high-precision numerical solution of the two exact interior transition equations W=0,Wk=0. Not interval certification, exhaustive root count, uniqueness, global optimality, proof or Lean.',
 'formulas':{'W':'2 k^2/[3(K-k)] + log(g(K)-g(k)) - log(q(k)) - log(exp(g(K))-1)',
   'q':'k/(exp(k)-1)','g':'-log(q)-1+q','s':'exp(k)/(exp(k)-1)-1/k'},
 'candidate':row,'full_intermediate_phase_status':'Open here. No global transition uniqueness or absence of c-islands proved.'}
path=Path(__file__).with_name('CRITICAL_EQUATION_DISCOVERY.json')
path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(row,indent=2))
