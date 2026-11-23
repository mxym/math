from fractions import Fraction as Q

def req(ok, why):
    if not ok:
        raise ArithmeticError(why)

def G(t):
    z = abs(1-2*t)
    return 2*z**3-z**5

def loglo(v):
    x = (v-1)/(v+1)
    req(0 <= x < 1, 'log domain')
    return 2 * sum(x**(2*k+1)/(2*k+1) for k in range(7))

bits = 10**15
def down(x):
    return x.numerator*bits//x.denominator

ncell = credit = 0
P = 1000
step = Q(1,P)
for i in range(40,105):
    t0, t1 = i*step,(i+1)*step
    for j in range(i+1,170):
        v0, v1 = j*step,(j+1)*step
        s0,s1 = t0+v0,t1+v1
        X0,X1 = 1-s1,1-s0
        z = max(X1/5,v1)+Q('.0001')
        B = Q('.499')+v0/2
        E = B-t1-v1
        req(E>t1 and B-v1>Q('.4') and 5*z>X1 and z>v1,
            'factorability split, true quotient rank and ordered ownership')
        req(z < X0/4 and E/z < 4, 'valid prime geometry and linear ratio')
        if E <= 2*z:
            continue
        K3 = 16*t0*v0*X0*(5*(t0*t0+v0*v0+X0*X0)-3)
        up4 = (1-G(t1)-G(v1)-2*G(X1/2)+G(s0)
               +2*G((1+t0-v1)/2))
        K4 = (-up4)*4*z*(X0-z)/X1**2
        K5 = 1920*t0*v0*z*z*(X0-2*z)
        K6 = 3840*t0*v0*z**3*(X0-3*z)
        k = min(K3,K4,K5,K6)
        if k <= 0:
            continue
        ncell += 1
        coeff = k * 2*loglo(E/z-1)/E
        credit += down(coeff * step**2/(t1*v1))
Z = Q(credit,bits)
req(Z > Q('.0333'), 'actual negative-only prime rebate bound')
print(ncell, Z, float(Z))
