"""Optional floating-point diagnostics only. Requires NumPy and SciPy."""
import numpy as np
from scipy.special import xlogy
from scipy.optimize import minimize
from itertools import combinations
w=np.exp(2j*np.pi/3)
x=np.arange(3)
M=[np.eye(3)]+[w**((a*x[:,None]**2+x[:,None]*x[None,:])%3)/np.sqrt(3) for a in range(3)]
seeds=[]
for i,j in combinations(range(3),2):
    for a in range(3):
        v=np.zeros(3,dtype=complex);v[i]=1;v[j]=-w**a;seeds.append(v/np.sqrt(2))
def theta(t):
    return M[:3]+[np.exp(1j*t*x)[:,None]*M[3]]
def entropy(b,z):
    p=abs(z@b.conj())**2
    return -xlogy(p,p).sum(axis=-1)
def score(z,S):
    return sum(entropy(b,z) for b in S)/4
for t in (0.1,0.01,0.001):
    S=theta(t);vals=[]
    for v in seeds:
        _,_,V=np.linalg.svd(v.conj()[None,:]);P=V[1:].conj().T
        def obj(y):
            z=v+t*(P@(y[:2]+1j*y[2:]));return (score(z/np.linalg.norm(z),S)-np.log(2))/t**2
        val=minimize(obj,np.zeros(4),method='BFGS',options={'gtol':1e-6}).fun
        vals.append(val*t**2)
    print("t, local minimum increment, standardized:",t,min(vals),min(vals)/(t*t*np.log(1/t**2)))
# Two identical qubit bases vs. the mutually unbiased pair: Haar integral via deterministic spherical Gauss x trapezoid.
# Try to verify variance differences directly without using (V1).
from numpy.polynomial.legendre import leggauss
z,wg=leggauss(200);ang=2*np.pi*np.arange(512)/512
xx=np.sqrt(1-z[:,None]**2)*np.cos(ang)
def hb(a):
    p=(1+a)/2;return -xlogy(p,p)-xlogy(1-p,1-p)
hz=hb(z)[:,None]
q1=hz**2;q2=((hz+hb(xx))/2)**2
observed=np.dot(wg,(q1-q2).mean(axis=1))/2
n=np.arange(2,20000,dtype=float)
pred=(1/12)*np.sum((2-4*np.exp2(-n))/(n*(n-1))**2)
if abs(pred-observed)>1e-7: raise RuntimeError((pred,observed))
print("qubit Haar variance gap, sphere quadrature vs. (V1):",observed,pred)
