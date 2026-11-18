"""Check the determinants and squared trace-norm identity in PROOF.md exactly."""
import sympy as S
u,v,x=S.symbols('u v x', positive=True)
def need(q,msg):
    if not q: raise ArithmeticError(msg)
B=S.Matrix([[x,1],[1,x]]);D=S.diag(0,-1);T=S.diag(1,u);C=S.diag(1,v)
L=T*B+B*C*D; R=T*D*B+B*C
def simp(k):return S.factor(k.subs(x*x,1/(v-u)))
need(simp(S.expand(L.det())-(-1-u*(1-v)))==0 and simp(S.expand(R.det())-(1-v*(1-u)))==0,'determinants')
h=(R.T*R).trace()-(L.T*L).trace()
need(S.expand(h-2*(v-u))==0,'HS gap')
need(simp(S.expand(h+2*(R.det()+L.det())-4*u*(v-1)))==0,'nuclear gap')
print('PASS exact determinants and strict trace-norm gap polynomial 4α(β−1) for the specified positive definite B.')
