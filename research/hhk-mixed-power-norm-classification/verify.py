"""Fail-closed symbolic and rational checks for the mixed-power proof. No external inputs."""
import sympy as S
def need(c,msg):
    if not c: raise ArithmeticError(msg)
def zero(y): return S.simplify(S.expand(y))==0
q=S.Rational
x,y,h,l=S.symbols('x y h l',positive=True)
F=l*l-(x-y+h)*l+(x-y)*h-x*y
for lam,deriv in [(x,y/(x+y)),(-y,x/(x+y))]:
    need(zero(F.subs({l:lam,h:0})), 'characteristic root')
    need(zero(((F.diff(l)*deriv+F.diff(h)).subs({l:lam,h:0}))), 'simple eigenvalue derivative')
need(zero(x*y/(x+y)-y*x/(x+y)),'pair tangent')
print('PASS characteristic roots and tangents of both eigenbranches for every positive x,y.')
H=S.Matrix([[3,2],[2,0]]);c,m=S.symbols('c m', real=True)
E=S.Matrix([[0,2],[0,c]])
J=S.eye(2);P=(H+J)/5;Q=J-P
need(P*P==P and Q*Q==Q and P*Q==S.zeros(2) and H==4*P-Q,'spectral splitting')
g=(m*P-Q)*E
coeff=(4*(m+1)+(m-4)*c)/5
need(zero(g.trace()-coeff) and zero(coeff.subs(c,-(4*(m+1)+5)/(m-4))+1),'Schatten slope')
need(zero((P*E).trace()-(4+c)/5),'operator slope')
print('PASS fixed-B Schatten p slopes (including p=1, simple singular values 4,1) and operator slope.')
v=q(1,8);cc=-8;a=v**4
def mixed(t):
    B=S.Matrix([[q(3,2),2],[2,cc]])
    return S.diag(1,a**t)*B+B*S.diag(1,a**(1-t))
L=mixed(q(1,2)); R=mixed(q(3,4));t=q(79,20);G=t*t*J-R.T*R
need(L==S.Matrix([[3,q(65,32)],[q(65,32),q(-1,4)]]) and R==S.Matrix([[3,q(9,4)],[q(513,256),q(-65,64)]]),'exact matrices')
need((t*J-L).det()==q(-3481,25600)<0 and G[0,0]==q(4238311,1638400)>0 and G.det()==q(193986147,81920000)>0,'separating certificate')
print('PASS strict rational operator witness: 79/20 separates; exact determinant and both principal minors.')
