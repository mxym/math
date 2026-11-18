"""Independent 80-digit checks from closed-form 2x2 rank-one pencils; no eigensolver, NumPy, or candidate source."""
from itertools import product
from mpmath import mp
mp.dps=80
M=mp.mpf
def require(c,msg):
    if not c: raise ArithmeticError(msg)
def envelope(a,b,c,p):
    # A=aP, B=bQ, with Tr(PQ)=c; the data are from the original rank-one operators.
    discriminant=mp.sqrt((a-b)**2+4*a*b*c)
    plus=(a+b+discriminant)/2
    minus=a*b*(1-c)/plus
    lhs=plus**p+minus**p
    s=(a**p+b**p)/2; u=c/mp.cosh(p*mp.log(a/b)/2)
    delta=mp.sqrt((1-u)*(1+u)); small=u*u/(1+delta)
    rhs=s*((1+delta)**(1/p)+small**(1/p))**p
    tol=M("1e-64")*max(1,lhs,rhs)
    require(lhs<=rhs+tol,"rank-one envelope")
    if p==2 or c==0 or c==1: require(abs(lhs-rhs)<=tol,"equality endpoint")
    if p>2 and c>0 and c<1: require(lhs<rhs,"strict at noncommutation")
    return min(lhs,rhs)
def laplace(s,t,c):
    # Removing the positive common factor 2 exp[-(s+t)/2], GT is Jensen's inequality
    # for d/dx twice of cosh(sqrt(x)) >= 0. Use both closed forms for independent agreement.
    lhs=(1-c)*mp.cosh((s-t)/2)+c*mp.cosh((s+t)/2)
    rhs=mp.cosh(mp.sqrt((s-t)**2+4*s*t*c)/2)
    e=(mp.exp(-s)+mp.exp(-t)+c*mp.expm1(-s)*mp.expm1(-t))-2*mp.exp(-(s+t)/2)*rhs
    d=2*mp.exp(-(s+t)/2)*(lhs-rhs)
    require(abs(e-d)<M('1e-70'),"GT independent formulas")
    require(d>=-M('1e-70'),"GT sign")
    if c not in (0,1) and s*t>0: require(d>0,"strict")
    return d
def main():
    trials=0
    for a,b,c,p in product(map(M,['0.007','0.7','1','3.9']),map(M,['0.02','0.7','1','2']),
              map(M,['0','1e-6','0.07','.5','.99999','1']),
              map(M,['2','2.001','2.5','2.97','3','3.95','4','4.1','7.7','8','17.3','31'])):
        envelope(a,b,c,p);trials+=1
    gt=0
    for s,t,c in product(map(M,['0','1e-4','.07','1','7','31']),map(M,['0','.002','.17','1.5','23']),map(M,['0','.013','.5','.999','1'])):
        laplace(s,t,c);gt+=1
    print('closed-form envelope comparisons:',trials,'; two-projector GT comparisons:',gt,'; precision:',mp.dps,'decimal digits')
if __name__=='__main__':main()
