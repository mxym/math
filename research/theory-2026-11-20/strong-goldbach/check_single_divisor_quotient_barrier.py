from fractions import Fraction as F
from itertools import product

def need(ok, desc):
    if not ok:
        raise ArithmeticError(desc)

# Check the linear identities for every independent formal evaluation symbol.
symbols = ['one','gam','b'] + [f'{h}{i}' for h in 'tzxy' for i in range(3)]
for symbol in symbols:
    z = {h:F(h==symbol) for h in symbols}
    G = z['gam']-z['b']
    def F1(p,i): return z['one']+G-z[f'{p}{i}']
    def J(*c): return 2*z['one']+z['gam']-sum(z[f'{p}{i%3}'] for p,i in c)
    D = J(('t',0),('t',1),('t',2))
    A = sum(J(('z',i),('z',i+1),('y',i+2)) for i in range(3))/3
    E = sum(J(('x',i),('t',i+1),('y',i+2)) for i in range(3))/3
    Fp = sum(F1('z',i) for i in range(3))/3
    Fpp = sum(F1('x',i) for i in range(3))/3
    need(-D-3*A+3*E-3*G+6*Fp-3*Fpp == z['one']-z['gam'],symbol)

# Each linear edge is checked at every corner of the full-dimensional box.
corners=0
for a,b,e1,e2 in product((F(119,1000),F(121,1000)),(F(645,10000),F(655,10000)),
                          (-F(25,100000),F(25,100000)),(-F(25,100000),F(25,100000))):
    w=1-a
    t=[w/3+e for e in (e1,e2,-e1-e2)]
    d=F(25,1000)
    M=F(499,1000)
    B=F(501,1000)
    need(a+b<M and w-b>F(813,1000),('giant',a,b))
    for i in range(3):
        for j in (1,2):
            Q=t[i]+j*d
            P=w-b-Q
            need(F(470,1000) <= P < M and F(317,1000)<Q<F(345,1000), ('macro',P,Q))
            need(b+P>B and b+Q<B and a+Q<M and a+b+Q>M and a+P>M, ('boxes',P,Q))
        for js in (t, [t[i]+d,t[(i+1)%3]+d,t[(i+2)%3]-2*d],
                   [t[i]+2*d,t[(i+1)%3],t[(i+2)%3]-2*d]):
            need(sum(js)==w and all(F(242,1000)<p<F(345,1000) and a+p<M
                                   and w-p>M for p in js),('triprime',js))
    corners+=1

box=F(2,1000)*F(1,1000)*F(5,10000)**2
bound=box/(19*150*F(1,1000))
need(bound == F(1,5700000000000) and bound>F(1,10**13),bound)
print(f'Exact cyclic identity on {len(symbols)} formal basis symbols; {corners} rational box corners.')
print('Uniform genuine averaged positive-part lower:',bound)
