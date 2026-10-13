"""Exact ordered Q(sqrt(3)) and its complexification; standard library only."""
from fractions import Fraction as F

class R:
    __slots__=('a','b')
    def __init__(self,a=0,b=0):self.a=F(a);self.b=F(b)
    @staticmethod
    def coerce(x):return x if isinstance(x,R) else R(x)
    def __add__(self,y):
        y=R.coerce(y);return R(self.a+y.a,self.b+y.b)
    __radd__=__add__
    def __neg__(self):return R(-self.a,-self.b)
    def __sub__(self,y):return self+-R.coerce(y)
    def __rsub__(self,y):return R.coerce(y)+-self
    def __mul__(self,y):
        y=R.coerce(y);return R(self.a*y.a+3*self.b*y.b,self.a*y.b+self.b*y.a)
    __rmul__=__mul__
    def __truediv__(self,y):
        y=R.coerce(y);d=y.a*y.a-3*y.b*y.b
        if not d:raise ZeroDivisionError
        return self*R(y.a/d,-y.b/d)
    def __rtruediv__(self,y):return R.coerce(y)/self
    def __eq__(self,y):
        y=R.coerce(y);return self.a==y.a and self.b==y.b
    def __bool__(self):return bool(self.a or self.b)
    def sign(self):
        if not self.b:return (self.a>0)-(self.a<0)
        if not self.a:return (self.b>0)-(self.b<0)
        if self.a>0 and self.b>0:return 1
        if self.a<0 and self.b<0:return -1
        if self.a>0:return (self.a*self.a>3*self.b*self.b)*2-1
        return (3*self.b*self.b>self.a*self.a)*2-1
    def data(self):return [str(self.a),str(self.b)]
    def __repr__(self):return f'R({self.a},{self.b})'

class C:
    __slots__=('re','im')
    def __init__(self,re=0,im=0):self.re=R.coerce(re);self.im=R.coerce(im)
    @staticmethod
    def coerce(x):return x if isinstance(x,C) else C(x)
    def __add__(self,y):
        y=C.coerce(y);return C(self.re+y.re,self.im+y.im)
    __radd__=__add__
    def __neg__(self):return C(-self.re,-self.im)
    def __sub__(self,y):return self+-C.coerce(y)
    def __rsub__(self,y):return C.coerce(y)+-self
    def __mul__(self,y):
        y=C.coerce(y);return C(self.re*y.re-self.im*y.im,self.re*y.im+self.im*y.re)
    __rmul__=__mul__
    def __truediv__(self,y):
        if isinstance(y,C):return self*y.conj()/(y.re*y.re+y.im*y.im)
        y=R.coerce(y);return C(self.re/y,self.im/y)
    def __rtruediv__(self,y):return C.coerce(y)/self
    def conj(self):return C(self.re,-self.im)
    def __eq__(self,y):
        y=C.coerce(y);return self.re==y.re and self.im==y.im
    def __bool__(self):return bool(self.re or self.im)
    def data(self):return self.re.data()+self.im.data()
    @staticmethod
    def read(v):return C(R(v[0],v[1]),R(v[2],v[3]))

def positive_ldl(Z):
    """Exact L D L* identity with strictly positive ordered-field pivots."""
    n=len(Z);L=[[C() for _ in range(n)] for _ in range(n)];d=[]
    for j in range(n):
        if any(Z[i][j]!=Z[j][i].conj() for i in range(n)):raise ValueError('Not Hermitian')
        pivot=Z[j][j]-sum((L[j][k]*L[j][k].conj()*d[k] for k in range(j)),C())
        if pivot.im or pivot.re.sign()!=1:raise ValueError(('Nonpositive LDL pivot',j,pivot.data()))
        d.append(pivot.re);L[j][j]=C(1)
        for i in range(j+1,n):
            L[i][j]=(Z[i][j]-sum((L[i][k]*L[j][k].conj()*d[k] for k in range(j)),C()))/d[j]
    return L,d

def solve(A,b):
    """Square exact Gaussian solve over Q(sqrt(3))."""
    n=len(b);A=[list(row)+[v] for row,v in zip(A,b)]
    for j in range(n):
        p=next((i for i in range(j,n) if A[i][j]),None)
        if p is None:raise ValueError('Singular selected matrix')
        A[j],A[p]=A[p],A[j];pivot=A[j][j]
        A[j]=[x/pivot for x in A[j]]
        for i in range(n):
            if i!=j and A[i][j]:
                m=A[i][j];A[i]=[x-m*y for x,y in zip(A[i],A[j])]
    return [row[-1] for row in A]
