# A sharp broad-noise search window without a fixed-modulus assumption

The conclusion is an exact **statistical** threshold for a specified
broad-noise Ring-LWE observation model with independent uniform
public coefficients. The number of ideal directions may grow with
the modulus. A counting and moment argument shows that, in this
window, all proper ideals are collectively negligible at the optimum.
No runtime bound, solver, key-recovery procedure, or numerical
assessment of an actual cryptographic parameter is given.

## 1. Model and theorem

Let \(d\to\infty\) through powers of two and let \(q=q_d\ge3\)
be arbitrary odd integers, with no growth bound. Put
\(O_d=\mathbb Z[\zeta_{2d}]\), \(R_d=O_d/qO_d\), with the
coefficient identification \(R_d=(\mathbb Z/q)^d\) as an
additive group. Use the embedding \(u\mapsto u/q\) into
\(\mathbb T^d=(\mathbb R/\mathbb Z)^d\).
Let \(S\) be uniform on \(R_d^n\), with \(n=n_d\ge1\), and observe
\(m=m_d\ge1\) pairs \((A_i,B_i)\),
\[
 A_i\stackrel{\mathrm{iid}}{\sim}\mathrm{Unif}(R_d^n),\qquad
 B_i=(A_i S)/q+E_i,
\]
where the rows, hidden element and errors are mutually independent
before forming responses. Errors are iid with known product Haar
density \(p_b=f_b^{\otimes d}\),
\[
       f_b(t)=\sum_{k\in\mathbb Z}b^{k^2}e^{2\pi i kt},
          \quad 0<b<1 .
\]
For \(n=1\) this is the usual continuous spherical dual Ring-LWE
observation form in dyadic coefficient coordinates, with codifferent
\((1/d)O_d\): a canonical width \(s\) gives \(b=e^{-\pi d s^2}\).
The theorem only treats the broad-noise range
\[
                    \tau:=db^2\le c_0\log d
 \tag{1}
\]
for an absolute sufficiently small constant \(c_0>0\).

Write \(L_{q,b}(x)=\log(f_b(x)/f_{b^{q^2}}(qx))\) and put
\(C_q(b)=\mathbb E_{f_b}L_{q,b}\),
\(V_q(b)=\operatorname{Var}_{f_b}L_{q,b}\).
Let \(P_{\rm opt}(A)\) be the best possible success probability
of exact identification conditional on the realized public
matrix, with the stated uniform prior and no time restriction.

**Theorem.** Under (1), if
\[
 z_d=\frac{dm\,C_q(b)-dn\log q}{\sqrt{dm\,V_q(b)}}\longrightarrow
             z\in[-\infty,\infty],
 \tag{2}
\]
then \(P_{\rm opt}(A)\to\Phi(z)\) in \(L^1\) over the
public matrix, using \(\Phi(-\infty)=0,\ \Phi(+\infty)=1\).
The convergence permits arbitrary growing \(q,n\).
The scalar expansions \(C_q(b)\sim b^2,\ V_q(b)\sim2b^2\)
hold uniformly in \(q\ge3\). In (2) the exact mean is used;
replacing it by \(b^2\) without a separate centering check
is not part of the theorem.

## 2. Ideal Fourier estimates

For a nonzero ideal \(J\le R_d\), including \(J=R_d\),
let \(g_J=P_Jp_b\) be the average of \(p_b\) under translation
by \(J/q\). Its Fourier support is the annihilator
\[
 I_J=\{u\in O_d: \langle u,v\rangle_{\mathrm{coeff}}\equiv0
                    \pmod q\text{ for all }v\in J\},
\]
where the coefficient dot product equals
\(\operatorname{Tr}(u\bar v)/d\).
This set is an ideal: multiplication by \(a\in O_d\) is
adjoint to multiplication by \(\bar a\). It contains \(qO_d\);
by perfect finite duality \([O_d:I_J]=|J|\), so it is
proper. Every nonzero element \(u\in I_J\) has
\(|N(u)|=[O_d:uO_d]\ge |J|\). The canonical norm
and arithmetic–geometric mean at the embeddings give
\[
 |N(u)|\le (\|u\|_{\mathrm{coeff}}^2)^{d/2},
       \qquad \|u\|_{\mathrm{coeff}}^2\ge |J|^{2/d}.
 \tag{3}
\]
The first bound uses orthogonality of the dyadic power basis
in canonical coordinates and counts both embeddings in every complex pair.

Here is an elementary uniform small-coefficient estimate.
Let \(b'>0\) be sufficiently small and keep \(I_J\) fixed
when changing the nome. With \(x=(b')^2\),
\(\theta(x)=\sum_{t\in\mathbb Z}x^{t^2}\),
\[
      \sum_{u\in I_J\setminus\{0\}}x^{\|u\|_{\mathrm{coeff}}^2}
            \le C\frac{(d x)^3}{d}e^{C dx}.
 \tag{4}
\]
Indeed take any maximal ideal \(\mathfrak p\supset I_J\)
with odd residue characteristic \(\lambda\mid q\).
The image of \(\zeta_{2d}\) in its residue field has exact
order \(2d\), since its \(d\)-th power is \(-1\).
Each signed monomial of coefficient squared norm 1 and
each signed binomial of squared norm 2 is therefore outside
\(\mathfrak p\). For a vector in \(\mathfrak p\) having
some coefficient nonzero mod \(\lambda\), mark and delete
such a coefficient \(c\). For each remaining vector and
marked value there is at most one way to restore its
position, because the first \(d\) powers of the root
are all distinct in the residue field. If \(c=\pm1\),
the remaining squared norm is at least 2. If every
coefficient is divisible by \(\lambda\), count that part
separately. The resulting upper bound is
\[
 2x(\theta(x)^d-1-2dx)
       +\Big(\sum_{|c|\ge2}x^{c^2}\Big)\theta(x)^d
       +\theta(x^{\lambda^2})^d-1.
\]
For \(x\) small, \(\theta(x)=1+2x+O(x^4)\) and
\(\theta(x)^d\le e^{C dx}\). Thus the bracket is
\(O(((dx)^2+dx^4)e^{C dx})\), and the last term is
\(O(d x^9 e^{C dx})\). This proves (4) uniformly, including
when \(dx\to0\).
This marked-position estimate is also used in the
[one-error alignment note](ring-lwe-dyadic-ideal-information-alignment.md).
There it does not by itself control exponentially many directions.

An extra fixed Fourier tilt allows (3) to be retained:
\[
 \sum_{u\in I_J\setminus\{0\}} (b')^{2\|u\|_{\rm coeff}^2}
       \le C\frac{(d(b')^2)^3}{d}\,e^{C d(b')^2-|J|^{2/d}}.
 \tag{5}
\]
Indeed multiply each summand by \(e^{\|u\|_{\rm coeff}^2}\),
use its lower-bound penalty from (3), and apply (4) at
\(x=e(b')^2\). Increase the absolute constant to absorb
the fixed tilt.

## 3. A dimension-independent fixed moment

Circle heat hypercontractivity is classical; see [Weissler](https://www.sciencedirect.com/science/article/pii/0022123680900427).
We include a short non-sharp smoothing proof to access a
higher-than-second moment without an \(L^\infty\) theta bound.
Fix an even integer \(p=2k\ge2\).
For a constant \(c=c_p\in(0,1)\) small enough, the circle
heat convolution \(T_c\) with multipliers \(c^{j^2}\) satisfies
\[
       \|T_c^{\otimes d}h\|_p\le\|h\|_2
 \tag{6}
\]
for real \(h\) on \(\mathbb T^d\).
In dimension one write \(h=a+h_0\) with zero-mean \(h_0\)
and \(\|h_0\|_2=u\).
By Cauchy–Schwarz on the Fourier series,
\(\|T_c h_0\|_\infty\le\delta u\), where
\(\delta=(\sum_{j\ne0}c^{2j^2})^{1/2}\to0\) as \(c\to0\).
Expand the even power of \(a+T_ch_0\) and discard the
vanishing linear term. For \(j\ge2\), bound the terms by
\(\binom{2k}j |a|^{2k-j}\delta^j u^j\).
Each odd monomial is at most the average of its two
adjacent even monomials, and the first such odd index is 3.
Their sum is at most a constant depending on \(k\) times
\(\delta^2\sum_{j=1}^k |a|^{2k-2j}u^{2j}\).
For small enough \(c\) this fits under
\((a^2+u^2)^k-|a|^{2k}\), proving (6) in dimension one.
The product inequality follows by iteration and Minkowski:
\(L^p_y(L^2_x)\) is bounded by \(L^2_x(L^p_y)\) for \(p\ge2\),
so the two coordinate operators can be bounded successively.

Use (6) with \(p=34\), large \(d\) so that \(b/c<1\),
and \(h=P_Jp_{b/c}-1\).
Fourier multipliers give \(T_c^{\otimes d}h=g_J-1\).
Equations (5) and Parseval imply, with absolute \(C,K\),
\[
 \|g_J-1\|_{34}^2
       \le C\frac{\tau^3}{d}\,e^{K\tau-|J|^{2/d}} .
 \tag{7}
\]
Under \(E\sim p_b\), the mean of \(g_J(E)^{32}\)
is \(\int g_J^{33}\), since \(g_J\) is invariant under
the averaging group. Expanding around 1, the linear term
vanishes, and all terms of orders 2 through 33 are bounded
in absolute value by a constant times \(\|g_J-1\|_{34}^2\)
for large \(d\). We choose \(c_0\) small enough that
\(K c_0<1/4\), so the norm in (7) tends uniformly to zero.
In particular uniformly in all \(J\ne0\),
\[
 \log\mathbb E_{p_b}\,g_J(E)^{32}
        \le C\frac{\tau^3}{d}\,e^{K\tau-|J|^{2/d}} .
 \tag{8}
\]

## 4. Counting directions by index

For proper ideals \(J\subsetneq R_d\), write
\(\Lambda_J=[R_d:J]\). Each is a product of
residue-field norms according to its prime-ideal factors.
Every norm of a prime ideal above an odd rational prime
\(p_0\) is \(p_0^{f(p_0)}\equiv1\bmod 2d\), since the
residue field contains the exact-order root used in
Section 2. There are at most \(d\) prime ideals over any
\(p_0\), and for \(O_d\) their residue degrees are all
\(\operatorname{ord}_{2d}(p_0)\).
Norms belonging to different rational primes are distinct,
as they are powers of distinct primes.
In particular \(\Lambda_J\ge2d+1\) for proper \(J\).

The sum over all ideals \(J\le R_d\), including zero and
full, of \(\Lambda_J^{-u}\) is bounded above by
\[
 \prod_{\mathfrak p\mid qO_d}(1-N\mathfrak p^{-u})^{-1},
 \tag{9}
\]
as follows by lifting to the ideals of \(O_d\) containing
\(qO_d\) and summing the corresponding bounded geometric
series over the exponents. This works for prime powers
and composite \(q\); it is not an assumption that \(q\)
splits completely. For \(u=3\), the logarithm of
the right-hand side is
\[
  O\left(d\sum_{j\ge1}(1+2dj)^{-3}\right)=O(d^{-2}).
\]
For \(u=3/4\), the number \(\omega(q)\) of distinct
rational primes in \(q\) is at most \((\log q)/\log3\).
Since the possible residue norms are distinct across
those primes, their sum weighted by norm to the power
\(-3/4\) is bounded by the first \(\omega(q)\) terms of
the progression \(1+2dj\). The logarithm in (9) is therefore
\[
 O\left(d\sum_{j\le\omega(q)}(1+2dj)^{-3/4}\right)
                      = O((d\log q)^{1/4}).
 \tag{10}
\]
Constants in these two count bounds are absolute.

## 5. The common-noise shortcut at the threshold

First suppose (2) holds for finite \(z\).
The scalar Fourier expansion of the numerator and denominator
of \(L_{q,b}\) gives uniformly for \(q\ge3\)
\[
 L_{q,b}=2b\cos(2\pi t)+O(b^2),\quad
 C_q(b)\sim b^2,\quad V_q(b)\sim2b^2.
\]
For the mean one uses
\(C_q=D(f_b\Vert1)-D(f_{b^{q^2}}\Vert1)\);
the same subgroup averaging identity is used in the
[fixed-modulus result](ring-lwe-fixed-odd-modulus-threshold.md).
It follows from (2) that \(dm b^2\sim dn\log q\), i.e.
\(m(db^2)\sim nd\log q\), and \(\sqrt{dm V_q(b)}\)
is asymptotic to \(\sqrt{2nd\log q}\). In this section \(K\)
is the absolute moment constant in (7)–(8).

For each \(J\ne0\) define
\(\Delta_J=\sum_i\log g_J(E_i)\) on the same sample of errors.
For a proper nonzero \(J\), let \(u_J=n\log\Lambda_J\).
The moment cost from (8) for \(m\) errors is at most
\[
       C n \tau^2\log q\,e^{K\tau-|J|^{2/d}}.
\]
Uniformly in all proper \(J\), this is \(o(u_J)\).
To see this, if \(|J|\le q^{d/2}\), then
\(u_J\ge(n d/2)\log q\) and the ratio is
\(O(\tau^2e^{K\tau}/d)=o(1)\). Otherwise \(|J|^{2/d}>q\).
If \(q\ge2K\tau\), the displayed cost is
\(O(n\tau^2\log q\,e^{-q/2})=O(n)\), whereas
\(u_J\ge n\log(2d+1)\).
If \(q<2K\tau\), then \(q=O(\log d)\). For every odd
prime \(p_0\mid q\) the residue degree in this range is
\(f=2^{\log_2 d+2-v_2(p_0^2-1)}\ge4d/(p_0^2-1)\),
by successive squaring as in the fixed-base calculation:
\(v_2(p_0^{2^t}-1)=v_2(p_0^2-1)+t-1\) for \(t\ge1\).
This formula is in its stable range uniformly since \(p_0=O(\log d)\).
Thus \(u_J\ge c n d/q^2\) for any proper direction.
Here the ratio is at most \(C\tau^2 q^2\log q\,e^{K\tau}/d=o(1)\).
By Markov's inequality and independence of the errors,
\[
       \Pr(\Delta_J>u_J/8)\le e^{-3 u_J}
\]
for all sufficiently large \(d\), uniformly.
The sum of these failure probabilities is \(O(d^{-2})\),
because \(n\ge1\) and (9) for \(u=3\) after subtracting the
full ideal term. Thus we have controlled all the proper
directions at once even if their unweighted count is huge.

For the full ideal \(\mathrm{all}=R_d\), the averaged noise
is a product of \(f_{b^{q^2}}(q t)\) densities. Therefore
\(|\Delta_{\mathrm{all}}|\le C m d b^{q^2}=o(n)\)
deterministically. Indeed \(m d b^2\sim nd\log q\) and
\(\log q\, b^{q^2-2}\le C b^7\) whenever \(q\ge3,\ b\le1/2\);
under (1), \(d b^7=o(1)\).
On the simultaneous event just established, for each proper
\(J\ne0\) the actual information sums therefore satisfy
\[
 T_J:=\sum_i\log(p_b(E_i)/g_J(E_i))
 \ \ge\ T_{\mathrm{all}}-u_J/4 .
 \tag{11}
\]
Let \(\gamma_d=(d\log q)^{3/8}\). On the event in (11)
and \(T_{\mathrm{all}}>nd\log q+\gamma_d\), an aggregate
expected-posterior comparison error is bounded by
\[
 \sum_{J\ne0} |J|^n e^{-T_J}
     \le e^{-\gamma_d}\sum_{J\le R_d}\Lambda_J^{-3n/4}
     =o(1),
 \tag{12}
\]
by (10). More explicitly, conditional on the true
hidden element and the errors, each likelihood ratio
for a different hidden hypothesis, averaged over uniform
independent rows \(A_i\), equals \(e^{-T_J}\) where \(J\)
is the ideal generated by its difference coordinates.
There are at most \(|J|^n\) such differences for a given
\(J\). The expected true posterior mass is a lower bound
on optimal success (the maximum of a probability vector
is at least its squared norm); its loss is at most the
sum of those ratios. This proves the averaged lower
bound
\[
        \mathbb E_A P_{\rm opt}(A)
          \ge\Pr(T_{\mathrm{all}}>nd\log q+\gamma_d)-o(1).
 \tag{13}
\]
This is an unrestricted statistical bound, not a way
to evaluate the optimum with a polynomial amount of work.

For the pointwise upper bound, uniformize by the full
ideal, which makes the response law independent of the true
hidden element for each fixed \(A\). The true-to-reference
log likelihood is \(T_{\mathrm{all}}\) and the reference
success is \(|R_d|^{-n}\). The elementary
change-of-measure bound gives for each \(A\)
\[
        P_{\rm opt}(A)
         \le \Pr(T_{\mathrm{all}}>nd\log q-\gamma_d)+e^{-\gamma_d}.
 \tag{14}
\]
Now \(T_{\mathrm{all}}\) is the sum of \(dm\) independent
scalar copies of \(L_{q,b}\). One centered summand is
\(O(b)\), compared with total standard deviation
asymptotic to \(\sqrt{2dm}\,b\).
The triangular-array CLT applies; also
\(\gamma_d\to\infty\) and
\(\gamma_d=o(\sqrt{nd\log q})\).
Both probabilities in (13)–(14) tend to \(\Phi(z)\).
The deterministic upper bound and average lower bound
squeeze the \(L^1\) distance as in the fixed-modulus proof.

For \(z_d\to-\infty\), use (14) with a cutoff \(\gamma\to\infty\)
that is negligible relative to the growing threshold gap.
That gap goes to infinity: when the expected information is
at most half the threshold it is at least \(nd\log q/2\);
otherwise the total standard deviation is of order at least
\(\sqrt{nd\log q}\). Chebyshev's inequality then gives limit
zero. For \(z_d\to+\infty\), compare with a shorter prefix:
for any fixed \(z_0\in\mathbb R\), choose an integer
\(m_0\le m\) with \((d m_0 C_q(b)-dn\log q)/
\sqrt{d m_0 V_q(b)}\to z_0\). This is possible by taking
\(m_0\) nearest to the solution for real \(m_0\).
Since \(d C_q(b)=O(\log d)\), rounding changes the center
by \(O(\log d)=o(\sqrt{nd\log q})\), and the exact positive root
is asymptotic to \(n\log q/b^2\to\infty\).
The standardized expression is strictly increasing in
positive \(m_0\), so the rounded choice is at most \(m\)
eventually. Optimal success cannot decrease when more
public rows and their responses are available.
The finite-window lower bound then gives
\(\liminf\mathbb E_A P_{\rm opt}(A)\ge\Phi(z_0)\),
and \(z_0\to\infty\) gives \(L^1\) convergence to 1.

## 6. Scope

The [sample model and cyclotomic residue theory of LPR](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf)
and the broader [PRS reduction](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf)
do not supply this information window; their hardness
reductions refer to different specified error families
and are not a consequence of this result. The
[usual entropy interpretation of the scalar mod-lattice channel](https://arxiv.org/abs/2206.10443)
is also not new here. The point is that we can combine
a fixed heat moment, norm divisibility, and a weighted
ideal count to control all competing directions, without
fixed-base stabilization or a bound on how \(q\) grows.
The bound is an exact asymptotic statistical statement
only in \(db^2\le c_0\log d\), not an estimate for general widths,
a classical polynomial-time result, or a concrete
security recommendation. The companion checker only
verifies elementary finite arithmetic identities on
synthetic inputs.
