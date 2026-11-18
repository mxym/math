"""Finite algebra diagnostics of the Fourier coefficients and Hessian, not a limit proof."""
from fractions import Fraction as F

def req(ok,w):
    if not ok: raise ArithmeticError(w)
def b(k):return 1/F((k*k-1)**2)
def a(k):return b(k)/k**2
def ell(k):return F((-1)**(k-1),k)
def main():
    ncoeff=0; nmodes=0
    for k in range(2,65):
        fourier=(ell(k-1)+2*ell(k)+ell(k+1))/4
        req(fourier==F((-1)**k,2*k*(k*k-1)),('Fourier',k))
        s=k-2; moment=F(1)
        for d in [1,1,2,2,3,3]:moment/=s+d
        req(moment==a(k)==4*fourier**2,('Hausdorff',k));ncoeff+=1
    for n in range(4,33):
        for s in range(2,n-1):
            # Symmetric truncation of both signs, incl even n and s=n/2.
            J=6;constant=b(s)/2
            brack=[b(j*n-s)+b(j*n+s)-2*b(j*n) for j in range(1,J+1)]
            req(all(t>0 for t in brack),('strict curvature',n,s))
            plus=b(s)+sum(b(j*n+s) for j in range(1,J+1))
            minus=sum(b(j*n-s) for j in range(1,J+1))
            signed=(plus+minus)/2-sum(b(j*n) for j in range(1,J+1))
            req(signed==constant+sum(brack)/2 and signed>constant,('residues',n,s));nmodes+=1
    print('PASS:',ncoeff,'Fourier/moment identities;',nmodes,'finite residue curvature checks (including self-conjugate modes).')
if __name__=='__main__': main()
