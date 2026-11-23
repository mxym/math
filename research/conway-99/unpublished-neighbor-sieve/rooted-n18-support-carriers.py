
from math import comb
def balanced(n,s,f):
 d,r=divmod(s,n);return (n-r)*f(d)+r*f(d+1)
for n,S,q in [(50,2,9),(51,5,9),(52,8,9),(53,11,8)]:
 v=balanced(n,8*n-(99-q),lambda t:comb(t,3))
 den=comb(q,3);m=(v+den-1)//den
 l=balanced(61,18*m,lambda t:comb(t,2))-4*comb(m,2)
 assert 4*l>24*S
 print(n,S,q,v,den,m,l,4*l,24*S)
