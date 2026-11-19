"""Cross-check the five primitive branches against inverse Laplace residues, before numerical substitution."""
from fractions import Fraction as F
from collections import Counter,defaultdict
from itertools import product
import verify_poly as author

def even(c):return -1 if c%2 else 1

def Us(k,m):return {0:F(m==0)} if k==0 else {('U',k,m):F(1)}
def Vs(k,m):return {('V',k,m):F(1)}
def Ws(m):return {('W',m):F(1)}

def residues(m,a,b):
    # Laplace in L of simplex integral is 1/[s(s-2ia)(s-2ib)].
    # Phi real is E Re z^m exp(2i(b-c)beta). Imaginary constant and
    # odd single beta contributions cancel only after the m average.
    ans=defaultdict(F)
    def push(poly,x):
        for j,y in poly.items():ans[j]+=x*y
    seq=[0,a,b];C=Counter(seq)
    if len(C)==1:
        push(Ws(m),F(1,2))
    elif len(C)==3:
        for c in C:
            d,e=[v for v in C if v!=c]
            push(Us(b-c,m),F(-even(c),4*(c-d)*(c-e)))
    else:
        c=next(i for i in C if C[i]==2);d=next(i for i in C if i!=c)
        # Double node gives exp(2icL)( L/(2i(c-d)) - 1/(2i(c-d))^2 ).
        # Simple node gives exp(2idL)/(2i(d-c))^2.
        push(Us(b-c,m),F(even(c),4*(c-d)**2));push(Us(b-d,m),F(-even(d),4*(c-d)**2))
        push(Vs(b-c,m),F(-even(c),2*(c-d)))
    return {k:v for k,v in ans.items() if v}

def main():
    author.U,author.V,author.W=Us,Vs,Ws
    counts=Counter()
    for j,k,l in product(range(-8,9),repeat=3):
        M,A,B=j+k+l,-j+k+l,2*l
        given={k:v for k,v in author.triangle(M,A,B).items() if v}
        other=residues(M,A,B)
        if given!=other:raise ArithmeticError((j,k,l,given,other))
        counts[len(set([0,A,B]))]+=1
    if sum(counts.values())!=17**3:raise ArithmeticError('incomplete')
    print('Verified inverse-Laplace residue signs before putting in any actual Fourier coefficients:',dict(sorted(counts.items())))
    print('All 4,913 ordered frequency triples agree, including simple/double/triple poles.')
if __name__=='__main__':main()
