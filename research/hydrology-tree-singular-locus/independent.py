#!/usr/bin/env python3
"""Separately implemented symbolic diagnostics. Does not import exact.py."""
from __future__ import annotations
import argparse, hashlib, json
from pathlib import Path
import sympy as S


def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def model(n, edges, root, leak):
    f=S.symbols('f0:'+str(n-1)); r=S.symbols('r0:'+str(n-1)); ell=S.Symbol('ell')
    A=S.zeros(n)
    for i,(u,v) in enumerate(edges):
        A[v,u]=f[i]; A[u,u]-=f[i]; A[u,v]=r[i]; A[v,v]-=r[i]
    A[leak,leak]-=ell
    z=S.Symbol('z')
    P=A.charpoly(z).as_expr(); Q=A.minor_submatrix(root,root).charpoly(z).as_expr()
    C=S.Matrix(S.Poly(P,z).all_coeffs()[1:]+S.Poly(Q,z).all_coeffs()[1:])
    J=C.jacobian([ell]+list(f)+list(r))
    return A, J, f, r, ell, P, Q


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    examples=[]
    for leak in range(2):
        A,J,f,r,ell,P,Q=model(2,[(0,1)],0,leak)
        expected=r[0] if leak==0 else f[0]
        observed=S.factor(J.det(method='domain-ge'))
        require(S.expand(observed**2-expected**2)==0,'Two-store formula')
        examples.append({'name':f'path2-leak{leak}','determinant':str(observed)})
    for root in (0,1):
        for leak in range(3):
            A,J,f,r,ell,P,Q=model(3,[(0,1),(1,2)],root,leak)
            inward=(r[0]*r[1], f[0]*r[1], f[0]*f[1])[leak]
            expected=inward*(f[0]*r[0] if root==0 else
                (f[0]-r[1]+(ell if leak==0 else 0)-(ell if leak==2 else 0))**2)
            observed=S.factor(J.det(method='domain-ge'))
            require(S.expand(observed**2-expected**2)==0,'Three-store formula')
            examples.append({'name':f'path3-root{root}-leak{leak}','determinant':str(observed)})
    for which in range(3):
        edges=([(0,1),(1,2),(2,3)] if which==0 else
               [(0,1),(1,2),(1,3)] if which==1 else [(0,1),(0,2),(2,3)])
        A,J,f,r,ell,P,Q=model(4,edges,0,0)
        if which==0:
            expected=f[0]**2*f[1]*r[0]**3*r[1]**2*r[2]
        elif which==1:
            expected=f[0]**2*r[0]**3*r[1]*r[2]*(r[1]-r[2])**2
        else:
            collision=r[0]**2-r[0]*(r[1]+f[2]+r[2])+r[1]*r[2]
            expected=f[1]*r[0]*r[1]**2*r[2]*collision**2
        observed=S.factor(J.det(method='domain-ge'))
        require(S.expand(observed**2-expected**2)==0,'Four-store formula')
        examples.append({'name':f'tree4-{which}','determinant':str(observed)})
    # Positive rates are all distinct, but two non-isospectral branches share one eigenvalue.
    edges=[(0,1),(1,2),(0,3),(3,4)]
    A,J,f,r,ell,P,Q=model(5,edges,0,0)
    values=[33,27,39,80,75,48,70,90]
    subst=dict(zip(list(f)+list(r),values));subst[ell]=51
    M=A.subs(subst); J0=J.subs(subst); z=S.Symbol('z')
    B1=S.factor(M.extract([1,2],[1,2]).charpoly(z).as_expr())
    B2=S.factor(M.extract([3,4],[3,4]).charpoly(z).as_expr())
    require(len(set(values+[51]))==9 and min(values+[51])>0,'Rates not positive/distinct')
    require(S.expand(B1-(z+30)*(z+120))==0,'First branch spectrum')
    require(S.expand(B2-(z+30)*(z+210))==0,'Second branch spectrum')
    require(J0.det()==0,'Spectral collision not singular')
    require(J0.rank()==8,'Unexpected Jacobian corank')
    O=S.Matrix.vstack(*[(M**k)[0,:] for k in range(5)])
    require(O.rank()==4,'Unexpected observable dimension')
    require(S.gcd(S.Poly(P.subs(subst),z),S.Poly(Q.subs(subst),z)).as_expr()==z+30,
            'Wrong canceled transfer pole')
    boundary={
        'forward_rates':values[:4],'reverse_rates':values[4:], 'leak':51,
        'edges':edges, 'branch_polynomials':[str(B1),str(B2)],
        'jacobian_rank':8,'parameter_count':9,'observability_rank':4,
        'canceled_factor':'z + 30',
        'false_claim_all_positive_distinct_rates_implies_nonsingular':'REJECTED',
    }
    report={'status':'PASS','scope':'Symbolic finite identities and exact singular example; not a general proof',
            'sympy_version':S.__version__, 'symbolic_identities':len(examples),
            'identities':examples,'positive_spectral_collision':boundary}
    text=json.dumps(report,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
