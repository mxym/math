"""Typeset explicit inline notation from the analytic proof without changing its formulas."""
import re

PAIRS = {
 'm>=2':r'm\geq2', 'm>=3':r'm\geq3', 'n>=m':r'n\geq m', 'D=mn':r'D=mn',
 'K=m^2-2':r'K=m^2-2', 'c=2m(m+1)':r'c=2m(m+1)', 'D>=12m(S-1)':r'D\geq12m(S-1)',
 'm=2,3,4':r'm=2,3,4','m=2':r'm=2','m=3':r'm=3','2187/40':r'2187/40',
 'V_E':r'V_E', 'Theta(sqrt(n)(4/27)^n)':r'\Theta(\sqrt n(4/27)^n)',
 's_i>=0':r's_i\geq0', 'sum s_i^2=1':r'\sum_i s_i^2=1', 'lambda':r'\lambda',
 'h>=0':r'h\geq0','a_ij':r'a_{ij}','b_ij':r'b_{ij}','i<j':r'i<j','i<=j':r'i\leq j',
 's^T L_{a,b}s/2':r's^TL_{a,b}s/2','A=0':r'A=0',
 'e=(1,...,1)/sqrt(m)':r'e=(1,\ldots,1)/\sqrt m',
 'L_0=gI+(bar b-bar a)J':r'L_0=gI+(\bar b-\bar a)J',
 '2B':r'2B','A+B':r'A+B','epsilon':r'\epsilon','e-perpendicular':r'e^\perp',
 '(g-epsilon)I':r'(g-\epsilon)I','e,e':r'e,e','2h/m':r'2h/m',
 'u_k=(1/k,...,1/k,0,...,0)':r'u_k=(1/k,\ldots,1/k,0,\ldots,0)',
 'x_k>=0':r'x_k\geq0','k<D':r'k<D','x_D<0':r'x_D<0','h(u_D)=m/D':r'h(u_D)=m/D',
 'c_k=(m/D)/(m/D-h(u_k))':r'c_k=\frac{m/D}{m/D-h(u_k)}',
 'x_D>=0':r'x_D\geq0','x_k=c_k y_k':r'x_k=c_ky_k','y_D=1-sum_{k<D}y_k':r'y_D=1-\sum_{k<D}y_k',
 'prod c_k':r'\prod_{k<D}c_k','alpha D=m(m-1)n/2':r'\alpha D=m(m-1)n/2',
 'Dirichlet(1,...,1)':r'\operatorname{Dirichlet}(1,\ldots,1)',
 't=y_D':r't=y_D','Beta(1,D-1)':r'\operatorname{Beta}(1,D-1)',
 '(y_1,...,y_{D-1})/(1-t)':r'(y_1,\ldots,y_{D-1})/(1-t)','D-1':r'D-1',
 '(1-t)^{D-2}':r'(1-t)^{D-2}', 'D>=2m':r'D\geq2m','c_k<=2m':r'c_k\leq2m',
 'k<=D-S':r'k\leq D-S','c_k<=2/(m+1)<=2/3':r'c_k\leq2/(m+1)\leq2/3',
 'd_k=c_k':r'd_k=c_k','d_D=0':r'd_D=0',
 'J={1,...,R-1} union {D-S+1,...,D-1}':r'J=\{1,\ldots,R-1\}\cup\{D-S+1,\ldots,D-1\}',
 'Z=sum_{j in J}y_j':r'Z=\sum_{j\in J}y_j','epsilon<=cZ/D':r'\epsilon\leq cZ/D',
 'lambda_D>=1/(12D)':r'\lambda_D\geq1/(12D)','g>=1/(6D)':r'g\geq1/(6D)',
 'epsilon<=1/(12D)':r'\epsilon\leq1/(12D)', 'E Z^2=K(K+1)/[D(D+1)]':r'\mathbb EZ^2=K(K+1)/[D(D+1)]',
 "Z=(1-t)Z'":r"Z=(1-t)Z'", "Z'":r"Z'",'K(K+1)/[(D-1)D]':r'K(K+1)/[(D-1)D]',
 "t<6c^2(1-t)^2(Z')^2":r"t<6c^2(1-t)^2(Z')^2", "t<6c^2(Z')^2":r"t<6c^2(Z')^2",
 'Pr(t<u)<=min(1,(D-1)u)':r'\Pr(t<u)\leq\min(1,(D-1)u)','u>=0':r'u\geq0',
 '1-(1-u)^{D-1}<=(D-1)u':r'1-(1-u)^{D-1}\leq(D-1)u','[0,1]':r'[0,1]', 'y_D':r'y_D',
 'a>0':r'a>0','1+alpha=beta':r'1+\alpha=\beta','D-power':r'D\text{-power}',
 'R+S-1/2=m^2-1/2':r'R+S-1/2=m^2-1/2','D^{m^2-1}':r'D^{m^2-1}',
 'q_m^D':r'q_m^D','C_m':r'C_m','W=C_m sqrt(D) q_m^D(1+O_m(1/D))':r'W=C_m\sqrt Dq_m^D(1+O_m(1/D))',
 'Gamma(2)/Gamma(m+1)=1/m!':r'\Gamma(2)/\Gamma(m+1)=1/m!','Gamma(m)=(m-1)!':r'\Gamma(m)=(m-1)!',
 'K={lambda_max<=(beta/alpha)lambda_min}':r'\mathcal K=\{\lambda_{\max}\leq(\beta/\alpha)\lambda_{\min}\}',
 'K subset AS subset APPT':r'\mathcal K\subseteq\mathrm{AS}\subseteq\mathrm{APPT}',
 'AS=APPT':r'\mathrm{AS}=\mathrm{APPT}', 'E_i':r'E_i', 'E_i=t lambda_i':r'E_i=t\lambda_i',
 't^{D-1}':r't^{D-1}','u=e^{-x/alpha}':r'u=e^{-x/\alpha}',
 'V_AS/(sqrt(D)q_m^D)':r'V_{\rm AS}/(\sqrt Dq_m^D)','sqrt(2 pi alpha beta)':r'\sqrt{2\pi\alpha\beta}',
 'i,j':r'i,j', '|d_ij|<=2m':r'|d_{ij}|\leq2m', 'j<i':r'j<i', 'c_j<=2m':r'c_j\leq2m',
 'j>=i':r'j\geq i', 'm/j<=m':r'm/j\leq m', '(D-j)/(j+alpha D)<=1/alpha<=2':r'(D-j)/(j+\alpha D)\leq1/\alpha\leq2',
 'm/(D-m)':r'm/(D-m)','c_j=j/(j+alpha D)':r'c_j=j/(j+\alpha D)','c_j/j=1/(j+alpha D)':r'c_j/j=1/(j+\alpha D)',
 'O_m(1/D)':r'O_m(1/D)','1/D':r'1/D','Q_m':r'Q_m','Q_m(0)':r'Q_m(0)','Q_m(1)':r'Q_m(1)',
 'Pr_T(B|E)<=Pr_T(B)/Pr_T(E)':r'\Pr_T(B\mid E)\leq\Pr_T(B)/\Pr_T(E)',
 's=beta exp(a-x)-alpha':r's=\beta e^{a-x}-\alpha', 'Q_m(U)':r'Q_m(U)',
 'beta-alpha=1':r'\beta-\alpha=1', 'exp(a-b)=alpha/beta':r'e^{a-b}=\alpha/\beta',
 'beta(a+1)-alpha(b+1)=1':r'\beta(a+1)-\alpha(b+1)=1', '(m+1)/(m-1)':r'(m+1)/(m-1)',
}
for name in ['m','n','D','R','S','T','J','Z','U','i','j','k','y']:
    PAIRS.setdefault(name,name)


def render(text: str) -> str:
    parts=re.split(r'(\\\[[\s\S]*?\\\]|https://[^\s]+)',text)
    pattern=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(re.escape(k) for k in sorted(PAIRS,key=len,reverse=True))+r')(?![A-Za-z0-9_])')
    for i in range(0,len(parts),2):
        parts[i]=pattern.sub(lambda m:r'\('+PAIRS[m[0]]+r'\)',parts[i])
    result=''.join(parts)
    for before,after in [('converge to a and b, respectively',r'converge to \(a\) and \(b\), respectively'),
                         ('coupling to e has',r'coupling to \(e\) has'),
                         ('fixed b, Stirling',r'fixed \(b\), Stirling'),
                         ('For any bad event B,',r'For any bad event \(B\),'),
                         ('is independent of t,',r'is independent of \(t\),')]:
        result=result.replace(before,after)
    # Standardize an arrow macro without changing its mathematical meaning.
    result=result.replace(r'\Delta_D^\down',r'\Delta_D^{\downarrow}')
    before=re.findall(r'\\\[[\s\S]*?\\\]',text)
    after=re.findall(r'\\\[[\s\S]*?\\\]',result)
    expected=[s.replace(r'\Delta_D^\down',r'\Delta_D^{\downarrow}') for s in before]
    if after!=expected:
        raise RuntimeError('Displayed proof identity changed during typesetting')
    return result
