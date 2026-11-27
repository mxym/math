# Spectral covering for flat conditional quantum states

All logarithms are base 2 except ln. The error is normalized trace distance.
The inputs are classical, the outputs can be noncommuting, and every
conditional state has the form $\rho_x=P_x/r$, where $P_x$ is a projection
and the positive integer $r$ is common to all positive-probability inputs.
The alphabet is finite. Restrict the output space to the support of
$\rho=\sum_x p_x\rho_x$; it is finite dimensional even if the initial
ambient space is not. All logarithms of operators below are on their
supports, or are extended arbitrarily off those supports in weighted traces.

## 1. Model and results

Draw a table $X_1,\ldots,X_N$ of pairwise independent entries with common
law $p$. A separate deterministic site 0 represents an independent output
in state $\rho$. For two distributions $a,b$ on $\{0,\ldots,N\}$, form
the two output states by choosing the hidden position according to $a$ or
$b$, respectively; include the classical table in both states. Write
$w_i=a_i-b_i,\ c=\sum_{i=0}^N|w_i|/2,\ v=\sum_{i=1}^N w_i^2$. Include
position 0 in $c$, not in $v$. The achieved distance is
$$
 \Delta(a,b)=\frac12\mathbb E\|D_T\|_1,\qquad
 D_T=w_0\rho+\sum_{i=1}^N w_i\rho_{X_i}.
 \tag{1}
$$
The equality is by orthogonal classical table blocks, also for a table
index that encodes the entries and may contain additional randomness.

Uniform placement in $K$ sites versus the independent preparation has
$c=1,\ v=1/K$; write $\Delta_{n,K}$ for its distance in the product-source
case below. For a row of size $K$ against the full $M$-by-$K$ table,
$c=1-1/M,\ v=(1-1/M)/K$.

Let the single-copy eigenvalues of $\rho$ be $\lambda_j>0$, with
multiplicity. Define $Z=-\log(r\lambda_J)$, with $\Pr(J=j)=\lambda_j$,
and $D=\mathbb EZ,\ V=\operatorname{Var} Z$. At blocklength $n$, each
site has law $p^{\otimes n}$, individual conditional rank $r_n=r^n$,
average $\rho_n=\rho^{\otimes n}$, and $Z_n$ is the sum of $n$ i.i.d.
copies of $Z$. Site-wise pairwise independence is sufficient throughout.
Here $D=I(X:E)$ and $V=V(X:E)$, with the ordinary quantum information
variance, as shown below. Let $\Phi$ denote the standard normal CDF.

**Covering upper.** If $V>0$, attaining fixed error
$\varepsilon\in(0,1)$ is guaranteed in either experiment by
$$
 \log K\ \ge\ nD+\sqrt{nV}\,\Phi^{-1}(1-\varepsilon)+C_\varepsilon
 \tag{2}
$$
for all large $n$, with a constant depending on the ensemble and
$\varepsilon$, not on the number $M$ of rows. The bound applies even
when the projections $P_x$ do not commute. Section 2 gives a one-shot
bound. If $V=0$, $nD+O_\varepsilon(1)$ bits suffice.

**Matching ordinary uniform-placement bound.** Suppose for each $x$
the compressed operators $P_x E_\lambda P_x$, over the distinct spectral
projections $E_\lambda$ of $\rho$, commute on $\operatorname{ran}P_x$.
Call this the compatible-compression condition. It holds for all pure
conditional states, and if $[P_x,\rho]=0$ for each $x$, but does not
require the conditional states to commute with each other or with $\rho$.
For $V>0$, every fixed $C<\infty$, and every pairwise independent
table law as above,
$$
 \Delta_{n,K}=\Pr(Z_n>\log K)+O_C(n^{-1/2})
 \quad\text{if }|\log K-nD|\le C\sqrt n.
 \tag{3}
$$
Consequently, for the ordinary independent table, the least integer
$K_\varepsilon(n)$ at fixed error satisfies
$$
 \log K_\varepsilon(n)
   =nD+\sqrt{nV}\,\Phi^{-1}(1-\varepsilon)+O_\varepsilon(1).
 \tag{4}
$$
The lower bound also rules out smaller $K$ for any pairwise independent
table law. This is a statement about these prescribed random experiments,
not optimization over deterministic codebooks or arbitrary dependent
table laws. For $V=0$, (4) with its square-root term zero holds without
the compatible-compression condition.

## 2. The spectral-row upper bound

In (1), $\sum_i w_i=0$, so
$D_T=\sum_{i=1}^Nw_i(\rho_{X_i}-\rho)$. Matrix multiplication and pairwise
independence annihilate the distinct-site terms in the second moment,
including both orders of each noncommuting product. Because
$\rho_x^2=\rho_x/r$,
$$
 \mathbb E D_T^2=v(\rho/r-\rho^2).
 \tag{5}
$$
For a threshold $s>0$, let $H=\mathbf1_{\{\rho\ge sI\}}$, $L=I-H$.
The decomposition $D_T=HD_T+LD_TH+LD_TL$ gives
$\|D_T\|_1\le2\|HD_T\|_1+\|LD_TL\|_1$; the off-diagonal block uses
adjunction and contractivity of projection in trace norm. The light
compression has expected norm at most $2c\operatorname{Tr}(L\rho)$:
apply the triangle inequality to (1), noting that each positive
compressed state has mean trace $\operatorname{Tr}(L\rho)$.
An eigenbasis unit vector $e_j$ of $\rho$ gives the row norm
$\||e_j\rangle\langle e_j|D_T\|_1=\sqrt{\langle e_j,D_T^2 e_j\rangle}$.
The triangle inequality over heavy rows, Jensen, and (5) prove
$$
 \Delta(a,b)\le c\operatorname{Tr}(L\rho)
   +\sum_{\lambda_j\ge s}\sqrt{\,v(\lambda_j/r-\lambda_j^2)\,}.
 \tag{6}
$$
The sum includes multiplicities. If $v=0$, (1) is identically zero.

If $c\le1,\ v\le1/K$, choose $s=1/(Kr)$. Using
$\lambda_j\le1/r$, and dropping the $-\lambda_j^2$ only in the upper
bound, (6) is at most
$$
 \Pr(Z>\log K)
   +\mathbb E\!\left[2^{(Z-\log K)/2}\mathbf 1_{\{Z\le\log K\}}\right].
 \tag{7}
$$
For $n$ copies replace $r,\rho,Z$ by $r_n,\rho_n,Z_n$.

The first moment of the block log difference
$\log \rho_x-\log\rho$, evaluated under $\rho_x$, uses
$(\log\rho_x)P_x=-(\log r)P_x$. The same identity gives
$\operatorname{Tr}\rho_x(\log\rho_x) \log\rho
=\operatorname{Tr}\rho_x\log\rho\,(\log\rho_x)
=-(\log r)\operatorname{Tr}\rho_x\log\rho$. Thus the noncommuting
cross terms in the squared log difference give exactly the same second
moment as $-(\log r)I-\log\rho$ averaged against $\rho$. The
$\log p_x$ terms in the two c-q hypotheses cancel. This proves the
identities for $D,V$.

For $V>0$, Berry--Esseen implies $\Pr(Z_n\in I)\le
C_0(1+|I|)/\sqrt n$ for all intervals of finite length (with either
choice of endpoint inclusion). Decompose the second term of (7) into unit
slabs below $\log K$; its geometric weights sum to a finite constant,
so it is $O(n^{-1/2})$ uniformly in $K$. With
$t_n=nD+\sqrt{nV}\Phi^{-1}(1-\varepsilon)$,
Berry--Esseen also approximates the first term by the normal upper tail
with uniformly bounded $O(n^{-1/2})$ error. At a shift of a fixed
$C_\varepsilon>0$, the derivative of the normal CDF near the fixed
interior quantile reduces that tail by at least a fixed positive multiple
of $C_\varepsilon/\sqrt n$ for large $n$. This proves (2).
Alternatively use threshold $s=2^{-t}/r_n$ and $v\le2^{-t}$ for any
real $t\le\log K$. This shows explicitly that the guarantee continues
to hold for all larger $K$.

If $V=0$, $\rho$ is uniform on a support of some dimension $s_0$,
and $D=\log(s_0/r)$. At real threshold $\log K\ge nD$, (7) is at
most $2^{(nD-\log K)/2}$. Conversely the support of every uniform
empirical state has dimension at most $K r^n$, and the corresponding
support projector distinguishes it from the uniform $\rho_n$ with
distance at least $1-Kr^n/s_0^n$. This proves the assertion at $V=0$,
also for $D=0$ (in that case every conditional output equals $\rho$).

## 3. A regularized Gram test

Here is the key operator lemma for a covering converse. Let $u_c$ be
any finite family of unit columns, possibly dependent, with matrix $U$,
$F=UU^\dagger$ and Gram matrix $G=U^\dagger U$. Define the effect
$$
 T=f(F),\qquad f(g)=\frac{g}{g+(g-1)^2}\quad(g\ge0).
 \tag{8}
$$
Since $g+(g-1)^2=(g-1/2)^2+3/4$, $0\le T\le I$ and
$T\le(4/3)F$. Let $T^+$ denote the Moore--Penrose inverse; the
range of $T$ equals the range of $F$ and contains every $u_c$.
The Cauchy--Schwarz inequality for $T^{1/2}\psi$ and $(T^+)^{1/2}u_c$
gives
$$
 \langle\psi,T\psi\rangle
 \ge
 \frac{|\langle u_c,\psi\rangle|^2}{\langle u_c,T^+u_c\rangle}.
 \tag{9}
$$
Use a singular-value decomposition of $U$: $U^\dagger T^+U=h(G)$,
where $h(g)=g/f(g)=g+(g-1)^2$ for $g>0$ and $h(0)=0$.
Hence $h(G)\le G+(G-I)^2$, including zero modes. The diagonal entry is
at most $1+\sum_{d\ne c}|\langle u_c,u_d\rangle|^2$. In particular
$$
 \langle\psi,T\psi\rangle
 \ge|\langle u_c,\psi\rangle|^2
   \left(1-\sum_{d\ne c}|\langle u_c,u_d\rangle|^2\right).
 \tag{10}
$$
This compares $T$ with the **original** vector $\psi$; it does not
replace the original state by a noncommuting truncation. The empty
family gives $T=0$.

Under the compatible-compression condition choose an orthonormal basis
$\psi_{x,a}$, $1\le a\le r$, for each conditional support which
diagonalizes every compressed $E_\lambda$. The corresponding product
basis has the same property on each $n$-word support. Indeed every
spectral projection of $\rho_n$ is a sum of tensor products of
single-copy spectral projections, including when different products
give the same eigenvalue. Thus vectors of two different basis indices
for the same word obey
$$
 \langle \psi_{x,a}, L_s\psi_{x,b}\rangle=0\quad(a\ne b),
 \qquad
 L_s=\mathbf1_{\{-\log(r_n\rho_n)>sI\}} .
 \tag{11}
$$
Here and below $x,a$ now index product words; $1\le a\le r_n$.
Any two such spectral projections are nested, so (11) also shows that
truncations of those vectors at different thresholds are orthogonal.

Fix a real threshold $t$. Decide deterministically for every possible
pair $(x,a)$ whether to retain it and, if retained, a nonnegative
integer $j(x,a)$. Let
$\phi_{x,a}=L_{t+j(x,a)}\psi_{x,a}$,
$q'_{x,a}=\|\phi_{x,a}\|^2>0$, $u_{x,a}=\phi_{x,a}/\sqrt{q'_{x,a}}$
for retained pairs. Set $\phi,u,q'$ to zero for omitted pairs.
The variational characterization of trace distance allows a different
test for each classical table. Apply (8) to all its retained $u$ columns.
For column $(i,a)$, the squared overlap with the original vector is
$q'_{X_i,a}$. Different columns at the same site are orthogonal by
(11), so only distinct sites enter (10). Let
$$
 A=\mathbb E_X\frac1{r_n}\sum_{a=1}^{r_n}\phi_{X,a}\phi_{X,a}^\dagger,
 \qquad
 B=\mathbb E_X\sum_{a=1}^{r_n}u_{X,a}u_{X,a}^\dagger .
 \tag{12}
$$
Then (10) bounds the expected signal loss by
$(K-1)\operatorname{Tr}(AB)$: each of the $K(K-1)$ ordered distinct
site pairs factors by pairwise independence and is divided by $K$
in the empirical state. The null expectation is at most
$(4/3)K\operatorname{Tr}(\rho_n B)$ because $T\le(4/3)F$.
Consequently the one-shot lower bound is
$$
 \Delta_{n,K}\ge
 \mathbb E_{X,a}q'_{X,a}
  -(K-1)\operatorname{Tr}(AB)-\frac43 K\operatorname{Tr}(\rho_n B).
 \tag{13}
$$
The index $a$ is uniform conditional on $X$, independent between sites
if introduced in this notation; the actual test uses **all** retained
columns, not a random basis vector per site.

## 4. Averaging the variable cutoff

For a random basis pair $Y=(X,a)$ (on one copy choose $X\sim p$,
then $a$ uniform), let $Z$ conditional on $Y=(x,a)$ be the
measurement of $-\log(r\rho)$ in $\psi_{x,a}$. Its unconditional law
is the law in Section 1. On a product pair $Y^n$, the conditional
law of $Z_n$ is the sum of independent coordinate laws, even when
product eigenvalues coincide. Let $w=\mathbb E\operatorname{Var}(Z|Y)$.

Suppose $V>0,\ w>0$. Fix any $C<\infty$ and use
$|t-nD|\le C\sqrt n$. There is a set of good product pairs with
exponentially small complement, on which the conditional variance is
at least $nw/2$, and the conditional mean $m_Y$ satisfies
$|m_Y-t|\le\kappa n$ for a sufficiently small fixed $\kappa>0$.
These assertions follow by Hoeffding for bounded single-copy
conditional variances and means. Non-identically distributed
Berry--Esseen there gives, uniformly in the good pair and interval,
$$
 \Pr(Z_n\in I\mid Y^n)\le C_1(1+|I|)/\sqrt n .
 \tag{14}
$$
Put $q=\Pr(Z_n>t\mid Y^n)$. For clarity, the conditional tail
estimate needed to take logarithms is proved next.

Use the natural exponential change of measure on the conditional
independent variables, with log moment function
$\Psi(\theta)=\ln\mathbb E[e^{\theta Z_n}\mid Y^n]$. Let $R>0$
be the range of the single-copy $Z$ and let $C_0=R^2/4$. For
$0\le\theta\le1$, each normalized tilted density is at least
$e^{-R}$ relative to the untilted law. Expressing variance by two
independent copies shows
$c_0 n\le\Psi''(\theta)\le C_0 n$, with $c_0=e^{-2R}w/2>0$.
Take $\kappa=c_0/2$ and $b_n=2\sqrt{C_0n}$. For sufficiently
large $n$, there is a tilt $0\le\theta\le1$ whose mean is
$m'=\max(m_Y,t+2b_n)$, since the desired upward shift is at most
$\kappa n+2b_n\le c_0n$.
Here $\theta\le((t-m_Y)_++2b_n)/(c_0n)$.
Chebyshev under the tilt gives at least $3/4$ mass within $b_n$
of $m'$, and that interval lies strictly above $t$. Undoing
the tilt and using $\Psi(\theta)\ge\theta m_Y$ proves
$$
 0<q,\qquad
 -\log q\le C_2\left(1+\frac{(t-m_Y)_+^2}{n}\right).
 \tag{15}
$$
Indeed the reverse density is bounded below by
$\exp[-\theta(m'+b_n-m_Y)]$ on the interval. The conditional
mean has expectation $nD$ and variance $O(n)$, so
$\mathbb E[\mathbf1_{\mathrm{good}}(1-\log q)]=O(1)$.
This is the conditional tilt used in Wilde Appendix D and adapted
to pure-output packing in Appendix E; its use in (13) concerns
covering instead.

On a good pair choose $j=\lfloor-\log q\rfloor$, so
$2^{-j-1}<q\le2^{-j}$, and set $q_{\rm new}=\Pr(Z_n>t+j\mid Y^n)$.
Retain precisely those good pairs with $q_{\rm new}\ge q/2$.
For retained pairs $q'=q_{\rm new}>2^{-j-2}$. Else $q'=0$.
On a good pair, $q-q'\le 2(q-q_{\rm new})$, also when discarded.
By (14)--(15) and the exponentially small exceptional probability,
$$
 \mathbb E q'\ge\Pr(Z_n>t)-O(n^{-1/2}).
 \tag{16}
$$

The same cutoff controls **both** of the Gram corrections in (13).
Group the untruncated retained projectors by $j$ and let $A_j^0$
be their expected sum with weights $1/r_n$. These partial sums
satisfy $0\le A_j^0\le\rho_n$, so
$$
 A=\sum_{j\ge0}L_{t+j}A_j^0L_{t+j}
 \ \le\ \sum_{j\ge0}\rho_n L_{t+j}
 \ \le\ L_t\rho_n(1+(-\log(r_n\rho_n)-tI)_+).
 \tag{17}
$$
The last inequality counts the nonnegative integers $j<z-t$
at each eigenvalue $z>t$. Thus on a retained pair with index $j$
and conditional $u$, using $K\le2^t$,
$$
 \begin{aligned}
 Kr_n\langle u,(A+(4/3)\rho_n)u\rangle
 &\le (q')^{-1}
  \mathbb E\!\left[2^{t-Z_n}(7/3+Z_n-t)
                  \mathbf1_{\{Z_n>t+j\}}\mid Y^n\right] \\
 &\le \frac{C_3(1+j)}{\sqrt n}.
 \end{aligned}\tag{18}
$$
For the second line use (14) in the unit slabs
$(t+j+k,t+j+k+1]$, $k\ge0$. The factor above each slab is at
most $2^{-j-k}(10/3+j+k)$, while $1/q'<2^{j+2}$.
Averaging (18) and using (15) proves
$K\operatorname{Tr}[(A+(4/3)\rho_n)B]=O(n^{-1/2})$, because the
expectation over a **uniform** basis index $a$ cancels the $r_n$
in (18).

If $w=0$, the conditional law is a point mass almost surely. Each
corresponding basis vector is entirely in one average-state eigenspace.
Retain it unchanged exactly when $Z_n>t$, with $j=0$.
Now $A=L_t\rho_n,\ B=r_nL_t\rho_n,\ \mathbb E q'=\Pr(Z_n>t)$.
The Gram correction in (13), for $K\le2^t$, is bounded by
$(7/3)\mathbb E[2^{t-Z_n}\mathbf1_{\{Z_n>t\}}]=O(n^{-1/2})$ by
**unconditional** Berry--Esseen unit slabs, since $V>0$.

In both cases we have proved, uniformly in all $K\le2^t$ and
$|t-nD|\le C\sqrt n$,
$$
 \Delta_{n,K}\ge\Pr(Z_n>t)-O_C(n^{-1/2}).
 \tag{19}
$$
Taking $t=\log K$ and using (7) proves (3). To get (4), choose
$t=t_n-C_\varepsilon$ in (19); as in Section 2 the normal derivative
makes this tail strictly greater than $\varepsilon$ after subtracting
the uniform error, if the constant is large enough. This rules out
all $K\le2^t$, not only those within the Gaussian window; no monotonicity
assumption about varying table laws is needed. The upper bound follows
by rounding $2^{t_n+C_\varepsilon}$ upwards in (2). When $V>0$,
$D>0$ since $Z\ge0$ and is nonconstant, so this rounding is bounded
in logarithmic cost.

## 5. Coding consequence in Wilde's model

The one-shot argument for [Wilde, arXiv:2611.25496v1, Theorem 4.2]
(https://arxiv.org/html/2611.25496v1#S4) contains a mean Eve distance
equal to the row-versus-total instance of (1), by its Eqs. (4.23)--(4.30).
For the fixed reference alternative it is uniform placement versus
independent preparation instead. Equations (4.33)--(4.37) add the
reliability error and select a deterministic private codebook.
Likewise Theorem 5.1 and Corollary 5.2 compare against Eve's actual
state including the public table, and their sampling rule (5.16)
gives the same table marginal under every chosen site. Thus the
trace-distance terms are exactly (1), including when the table
family in Corollary 5.2 only has independent pairs. The Bob estimate,
fixed row partition, and $O(n)$ authenticated public bits are unchanged.

Under the hypotheses of Wilde's Theorem 6.1, if Eve's conditionals are
flat of a common rank, use (2) instead of (6.6) in that theorem's proof.
This removes precisely the covering $\tfrac12\log n$ from the
guaranteed rate, with the same joint-error criterion against Eve's actual
marginal and the same split tolerances. More explicitly, for fixed
$\varepsilon_B,\varepsilon_E>0$ with $\varepsilon_B+\varepsilon_E<1$,
there is a protocol/code there with
$$
 \log M\ge n(I_B-I_E)
     +\sqrt{nV_B}\Phi^{-1}(\varepsilon_B)
     +\sqrt{nV_E}\Phi^{-1}(\varepsilon_E)
     -b\log n-O(1),
$$
where $b=1/2$ in the general Bob case and $b=0$ when Bob meets
Wilde's existing commuting-pair or pure-output packing refinement.
There is no assertion here about optimal private/key rates, a converse
for row-versus-table coding, or fully quantum inputs. The converse
in Sections 3--4 concerns ordinary uniform placement alone.
