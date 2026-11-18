# Signed mean-value trace inequalities: two proofs of the exponential bound and a polynomial obstruction

Paulin, Mackey and Tropp asked for two one-sided trace inequalities in [Conjecture 13.4, pp. 3465–3466](https://tropp.caltech.edu/papers/PMT16-Efron-Stein-Inequalities.pdf#page=35). The **exponential inequality holds in every finite dimension**, with sharp coefficient. The **polynomial inequality as printed holds universally only at exponent $q=1$**: there are scalar counterexamples for every $q\ge2$. These are statements about the conjecture, not counterexamples to the paper's proved Efron–Stein theorems.

This is an AI-assisted research draft. A separate internal AI review checked the argument and supplied the elementary second proof below. There has been no external peer review, and no claim of global priority is made.

## 1. What was conjectured

Let $A,B,C$ be Hermitian matrices of the same finite size, $D=A-B$, and $s>0$. Write $X_\pm=(|X|\pm X)/2$, so that $X=X_+-X_-$, and define the signed quadratic expression

$$
V_{P,Q}(X)=\operatorname{Tr}(P X_+^2+Q X_-^2).
$$

The first assertion, with $P=e^A,\ Q=e^B$, is

$$
\operatorname{Tr} C(P-Q)\ \le\ \tfrac12\big(sV_{P,Q}(D)+s^{-1}V_{P,Q}(C)\big). \tag{E}
$$

The second, for each positive integer $q$, uses $U=|A|^{q-1}$ and $W=|B|^{q-1}$:

$$
\operatorname{Tr} C(A^q-B^q)\ \le\ \tfrac q2\big(sV_{U,W}(D)+s^{-1}V_{U,W}(C)\big). \tag{P}
$$

The left sides are signed scalar traces, not absolute values or operator inequalities. The power on the left of (P) is the ordinary power. There is no positive-semidefinite-input hypothesis on $A,B$.

## 2. Proof of (E) by measuring relative entropy

For arbitrary positive definite $P,Q$ define
$H=\log P-\log Q$ and $J=\operatorname{Tr}(P-Q)H$. The traces of $P,Q$ need not coincide. In an eigenbasis $v_i$ of a Hermitian test matrix $X$, let $x_i$ be its eigenvalues, and write $p_i=\langle v_i,Pv_i\rangle$, $q_i=\langle v_i,Qv_i\rangle$. These scalars are strictly positive. Data processing in this basis, applied in each direction, gives

$$
0\le \sum_i(p_i-q_i)\log(p_i/q_i)\le J. \tag{1}
$$

This is the measurement case of [Lindblad's relative-entropy monotonicity](https://doi.org/10.1007/BF01609396); a finite-dimensional proof valid for unnormalized inputs appears in §4.

Keep only the terms with $x_i(p_i-q_i)>0$ in $\operatorname{Tr}X(P-Q)$. On these terms, $w_i=\max(p_i,q_i)$ is **the weight selected by the sign of $x_i$**: it is $p_i$ when $x_i>0$ and $q_i$ when $x_i<0$. The sum of $w_ix_i^2$ over the retained indices is therefore at most $V_{P,Q}(X)$. Weighted Cauchy–Schwarz yields

$$
\big[\operatorname{Tr}X(P-Q)\big]_+^2
\le V_{P,Q}(X)\sum_i\frac{(p_i-q_i)^2}{\max(p_i,q_i)}
\le V_{P,Q}(X)J. \tag{2}
$$

Here the brackets denote the positive part of a real number. The second inequality uses (1) and the scalar bound $(a-b)^2/\max(a,b)\le(a-b)(\log a-\log b)$ for $a,b>0$, obtained by integrating $1/u$ between $a$ and $b$.

Apply (2) first with **$X=H$**. Its trace on the left is $J\ge0$, hence $J^2\le V_{P,Q}(H)J$. It follows that $J\le V_{P,Q}(H)$, also when $J=0$. A second application with **$X=C$** now gives

$$
\operatorname{Tr} C(P-Q)
\le \sqrt{V_{P,Q}(C)V_{P,Q}(H)}
\le \tfrac12\big(sV_{P,Q}(H)+s^{-1}V_{P,Q}(C)\big).
$$

For $P=e^A,\ Q=e^B$ we have precisely $H=A-B$, proving (E). Its constant is sharp: take the scalar $s=1$, $A=C=x>0$, $B=0$. The ratio of left to right in (E) is $(1-e^{-x})/x\to1$ as $x\downarrow0$.

## 3. A second, elementary proof without data processing

Keep the definitions of $H,J,V_{P,Q}$. Let $a_i,u_i$ and $b_j,v_j$ be the eigenvalues and orthonormal eigenvectors of $P$ and $Q$, respectively. For Hermitian $Y$, expand in both bases:

$$
\begin{aligned}
J &= \sum_{ij}|\langle u_i,v_j\rangle|^2
      (a_i-b_j)\log(a_i/b_j),\\
\operatorname{Tr}Y(P-Q) &= \sum_{ij}(a_i-b_j)
             \langle u_i,v_j\rangle\langle v_j,Yu_i\rangle .
\end{aligned}
$$

Cauchy–Schwarz, with weights $(a_i+b_j)/2$, gives

$$
|\operatorname{Tr}Y(P-Q)|^2
\le \tfrac12\operatorname{Tr}((P+Q)Y^2)\,K,\qquad
K=\sum_{ij}|\langle u_i,v_j\rangle|^2\frac{2(a_i-b_j)^2}{a_i+b_j}
\le J .
$$

The first factor follows by completeness of the two bases. The last inequality follows term by term because the average of $1/u$ between $a_i$ and $b_j$ is at least $2/(a_i+b_j)$ by convexity. There is no division by an eigenvector overlap.

In an eigenbasis of $X$, let $Y$ keep $x_i$ only when $x_i(p_i-q_i)>0$, and replace other eigenvalues by zero. Then $[\operatorname{Tr}X(P-Q)]_+\le\operatorname{Tr}Y(P-Q)$. On the surviving indices the endpoint weight selected by the sign is the larger of $p_i,q_i$, so $\operatorname{Tr}((P+Q)Y^2)/2\le V_{P,Q}(X)$. This gives (2) without (1). Substitute $H$ and then $C$ exactly as in §2.

## 4. Self-contained measurement argument for (1)

Write $D(P\Vert Q)=\operatorname{Tr}P(\log P-\log Q)$, without normalizing traces. On the Hilbert–Schmidt space set $\Delta(T)=QTP^{-1}$. The commuting positive left and right multiplication operators show that $\Delta>0$ and

$$
(-\log\Delta)(T)=-(\log Q)T+T\log P,\qquad
\langle P^{1/2},(-\log\Delta)(P^{1/2})\rangle_{\rm HS}=D(P\Vert Q).
$$

With $E_i=v_iv_i^*$, define the isometry $W e_i=E_iP^{1/2}/\sqrt{p_i}$. Its columns are orthonormal since $E_iE_j=0$ for $i\ne j$. Cyclicity of trace gives

$$
 (W^*\Delta W)_{ij}=\frac{\operatorname{Tr}(E_i Q E_j)}{\sqrt{p_ip_j}}
     =\delta_{ij}\frac{q_i}{p_i},\qquad W(\sqrt{p_i})_i=P^{1/2}.
$$

For $S>0$ and an isometry $W$, $(W^*S W)^{-1}\preceq W^*S^{-1}W$: in the splitting at the range of $W$, the upper block of the inverse is the inverse of the Schur complement, which dominates the inverse of the upper block. Applying this to $S=\Delta+tI$ and using

$$
-\log x=\int_0^\infty\big((x+t)^{-1}-(1+t)^{-1}\big)\,dt
$$

gives $-\log(W^*\Delta W)\preceq W^*(-\log\Delta)W$. Evaluation on $(\sqrt{p_i})_i$ yields $\sum p_i\log(p_i/q_i)\le D(P\Vert Q)$. Swap $P,Q$ in the same basis and add to obtain (1). No inverses at zero or common eigenbasis for $P,Q$ are needed.

## 5. The polynomial assertion: classification as printed

Take $A=0,\ B=-1$ as real scalars. Then $D=1$, and for every $q\ge2$ the weights in (P) are $U=0,\ W=1$.

| Exponent | Other parameters | Left side of (P) | Right side |
|:--|:--|--:|--:|
| Odd $q\ge3$ | $C=1,\ s=1$ | $1$ | $0$ |
| Even $q\ge2$ | $C=-1,\ s=q$ | $1$ | $1/2$ |

For $q=1$ both zeroth powers are identities. The assertion is then $\operatorname{Tr}CD\le(s\operatorname{Tr}D^2+s^{-1}\operatorname{Tr}C^2)/2$, which follows by expanding $\operatorname{Tr}(s^{1/2}D-s^{-1/2}C)^2\ge0$. This treats all positive integer exponents. The examples also show why the journal's subsequent statement about validity for scalars does not apply to (P) as printed. They do not settle a modified polynomial question with $A,B\succeq0$.

## 6. Prior work and scope

- The two assertions occur both in [Paulin–Mackey–Tropp's earlier report, Conjecture 7.3](https://tropp.caltech.edu/reports/PMT14-Deriving-Matrix-TR.pdf) and in their [2016 journal paper, Conjecture 13.4](https://doi.org/10.1214/15-AOP1054). Their proved unsigned mean-value inequalities are distinct from (E) and (P); this note does not derive a new probabilistic tail or moment bound.
- Relative-entropy data processing is classical. The use here is the sign-dependent selection of measured components, followed by the two substitutions in (2).
- [D. S. P. Salazar, *Quantum relative entropy uncertainty relation*, Phys. Rev. E **109**, L012103 (2024)](https://doi.org/10.1103/PhysRevE.109.L012103) already uses spectral-pair expansions and observable estimates in terms of symmetric quantum relative entropy for normalized density operators; see Eq. (3), Eqs. (8)–(18), and the Appendix. Those techniques are not claimed as new; that paper does not frame the sign-filtered inequality as (E).
- [De Huang and Joel A. Tropp, *From Poincaré inequalities to nonlinear matrix concentration*, Lemma 5.2](https://tropp.caltech.edu/papers/HT21-Poincare-Inequalities.pdf) gives an unsigned two-matrix functional-calculus estimate, not the signed three-matrix trace statement.
- The [author-hosted published text](https://lmackey.github.io/papers/matefronstein-aop16.pdf), [Caltech record](https://authors.library.caltech.edu/records/bg6h9-8vs77), [author publication list](https://tropp.caltech.edu/papers.html), and [arXiv record](https://arxiv.org/abs/1408.3470) were checked. A bounded search by title, DOI, conjecture name/number, and correction terms on 18 November 2026 located no erratum changing the quoted mathematical scope and no prior treatment resolving both assertions in precisely this form. This bounded search does not rule out an erratum or earlier work.

## Reproduction

The proof is analytic. As a finite check, run `python -B -O verify.py` (Python standard library). It checks (2) in 960 exact noncommuting two-by-two directional cases, including unequal traces, the specialization to $H$ in the underlying 40 matrix pairs, and the displayed scalar substitutions for $2\le q\le101$. Rational bounds from the power series for $\log 2=2\operatorname{artanh}(1/3)$ avoid floating-point comparisons. Finite checks are not used to infer the all-dimensional result.
