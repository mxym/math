# A calibrated cutoff lift that confines negative rank-four terms to a near-half prime

This note uses the literal two-free completion in
[the full free-branch subtraction](../full_free_hb_splice/Proof.md).
Its change of cutoff is evaluated at the same fixed target and in the same
two-tag covariance. It does not import a triple-convolution distribution result,
and does not assert a sign of the full covariance.

Let \(N=2x\) be a prescribed large even integer, \(Y=\sqrt x,\ L=\log x\),
\(z=\exp(L/(\log L)^2)\), and \(R_z(y)=1_{P^-(y)>z}\). Use \(d,e\in[.65Y,.8Y]\),
\(k\in[Y,1.1Y]\), with \((dek,N)=1\); all physical \(y=N-ek\) lie in
\([x,3x/2]\). The slope weight \(\beta(e)\) counts the literal prime tags
\(p_2p_3\mid e\) in the bands \(p_2\in[x^{.029},x^{.031}]\),
\(p_3\in[x^{.075},x^{.078}]\). As in the full cutoff calculation put
\[
 K(y)=R_z(y)\sum_{\substack{rs=y\\r>x^{.505}}}\mu(r)\log s,\qquad
 F_U(y)=-R_z(y)\sum_{\substack{s c a=y\\ca>x^{.505}\\a>U(s)}}\mu_2(c)\log s,
 \qquad \mu_2=\mu*\mu.
\]
The wider previously proved cutoff is
\[
 T(s)=
 \begin{cases}
 x^{.674}s^{-1/4}&x^{.13}\le s\le x^{.32},\\
 \min(x^{.766}s^{-1/2},\,x^{.918}/s)&\text{otherwise}.
 \end{cases}
\]

Fix \(0<\eta<.01\), independent of \(x\). Write
\[
 v_1=.495-\eta,\qquad v_2=.495-\eta/8,\qquad
 \alpha_1=.505+\eta/4,\qquad \alpha_2=.505.
\]
Define the lifted free cutoff by
\[
 T^\uparrow(s)=
 \begin{cases}
   \max(T(s),x^{\alpha_1})&s\le x^{v_1},\\
   \max(T(s),x^{\alpha_2})&x^{v_1}<s\le x^{v_2},\\
   T(s)&s>x^{v_2}.
 \end{cases}                                                       \tag{1}
\]

**Theorem.** For every fixed \(A\) the change from \(F_T\) to \(F_{T^\uparrow}\)
has arbitrarily small logarithmic error on the literal tagged rows:
\[
 \sum_{\substack{k\\(k,N)=1}}
  \left|\sum_{\substack{e\\(e,N)=1}}
       \beta(e)(F_T-F_{T^\uparrow})(N-ek)\right|
       \ll_{\eta,A} xL^{-A}.                                        \tag{2}
\]
It may therefore be made in either leg of the exact covariance, with
the same opposite true divisor-weight envelope and error
\(O_{\eta,A}(x^{3/2}L^{-A})\) as in the original removal.
The surviving score \(K-F_{T^\uparrow}\) is zero on squarefree
semiprimes and nonnegative on squarefree triprimes. It is also
nonnegative on **every squarefree rank-four integer**
\(y\in[x,3x/2]\) whose largest true prime factor satisfies
\[
                          P^+(y)\le x^{.495-\eta}.                   \tag{3}
\]
In particular any negative rank-four contribution remaining in this
precise ledger must contain a genuine prime above that bound.

The statement about ranks is after **this large-free-slot removal alone**.
Further removals of other finite-convolution branches, even when
algebraically disjoint and analytically negligible in the whole row,
can change signs on ranks three and four. The nonnegative statements
are not inherited by arbitrary further subtractions.

## 1. The actual lifted band is a zero-mean two-free block

A lift is only possible on the \(T(s)=x^{.918}/s\) piece. Indeed the
first old cutoff on \(s\le x^{.304}\) is at least \(x^{.614}\);
the old annulus on \(x^{.13}\le s\le x^{.32}\) is at least
\(x^{.594}\); both exceed either new floor. On the remaining pieces
where a change occurs, \(s>x^{.918-\alpha_i}\), of exponent
greater than .410 for all specified \(\eta\). Thus on the
\(i\)-th change the difference in (2) is exactly
\[
 -R_z(y)\!\!\sum_{\substack{s c a=y\\ s\text{ in the }i\text{-th band}\\
                         x^{.918}/s<a\le x^{\alpha_i}}}\!\!
                  \mu_2(c)\log s .                                 \tag{4}
\]
The raw \(ca>x^{.505}\) condition is automatic because
\(s\le x^{v_2}\) and \(ca=y/s\ge x/s\).
Both shifts leave \(a\) and \(s\) polynomially long, and
\(c<y/x^{.918}\le1.5 x^{.082}\).
The sequence \(F_{T^\uparrow}\) is still an exact selected
unique-free-variable branch in the original finite Möbius identity:
its cuts are only larger than those already audited for \(F_T\).

For (4), open the literal modulus \(Q=kp_2p_3\), \((Q,N)=1\).
The interval for \(y=N-ek\) is
\(J_k=[N-.8Yk,N-.65Yk]\), and the residue is \(N\bmod Q\).
Use the same two-free argument as in Sections 2 and 3 of the
full cutoff proof. For clarity all relevant features persist:
keep \(c\) fixed and its true rough/unit indicators, expand the two
independent roughness indicators on \(a,s\) by the subpower
Bonferroni divisors, and apply the composite rectangular
Kloosterman completion to the two genuinely free integer variables.
The new upper \(a\le x^{\alpha_i}\) and the two \(s\)-endpoints
are independent box cuts. The event \(a s>x^{.918}\) remains
the physical endpoint \(y>c x^{.918}\).
The largest power error over \(Q\) and \(c\) is still
\[
 x^{.082+o(1)}(x^{.6092})^{3/2}=x^{.9958+o(1)}.
\]
The other completion error is controlled by polynomial lengths of \(a,s\).
The log-fine endpoint and factorial errors satisfy the same true
divisor-moment bounds; an added independent endpoint is covered by
one more relative-width strip in the free \(a\) coordinate.
One can use the unit restriction \((c,QN)=1\) exactly as in that proof;
possible target-unit violations in the other two rough factors
are paid on the original rough terms before any expansion.
These estimates hold in the absolute sum over \(k,p_2,p_3\).

Let \(W_z(Q)=\prod_{p\le z,\ p\nmid Q}(1-1/p)\).
On the \(i\)-th changed \(s\)-interval the exact main term per
actual modulus has the form
\[
 -\frac{\varphi(Q) W_z(Q)^2}{Q^2}
   \int_{J_k}\int_{\substack{s\text{ in the }i\text{-th band}\\
                          s>x^{.918-\alpha_i}}}
      \frac{\log s}{s}
        \sum_{\substack{y/(s x^{\alpha_i})\le c<y/x^{.918}\\
                        (c,QN)=1}}
                      \frac{\mu_2(c)R_z(c)}{c}\,ds\,dy .             \tag{5}
\]
In particular the original reduced-unit constant is unchanged.
The lower endpoint in the first band is at least \(x^{3\eta/4}\)
and in the second at least \(x^{\eta/8}\), using \(y\ge x\).
The upper endpoint is at least \(x^{.082}\).
Thus the uniform rough harmonic \(\mu_2/c\) estimate applies
to both prefixes separately, at **fixed** \(\eta\).
A real or exact integer endpoint changes no estimate.
This makes (5) \(O_{\eta,A}((x/Q)L^{-A})\).
The sum of \(1/Q\) over physical labels is \(O(1)\), giving (2).
As before the absolute original row is pointwise \(O(YL^C)\)
by Shiu, and any fixed divisor polynomial in \(k\) is paid by
log clipping and its higher moments. This gives the covariance claim.
No estimate here is uniform as \(\eta\) tends to zero with \(x\).

## 2. Exact rank signs and pairing of negative singleton labels

For any raw divisor pair \(rs=y,\ r>x^{.505}\) with \(s>1\),
the free choice \(a=r,\ c=1\) remains admissible.
Under the old cutoff this follows from \(rs=y>x^{.918}\).
Under a new floor \(r=y/s\) is at least \(x^{.505+\eta}\)
in the first band and \(x^{.505+\eta/8}\) in the second.
In particular neither lift touches this choice.

It suffices to consider rough \(y\), since both terms vanish otherwise.
For squarefree \(y\), normalize all weights by \(L\), write
\(t=\log y/L\), and for a divisor \(s\mid y\) write \(u=\log s/L\).
Writing its complementary \(r=y/s\) as the set of its prime factors,
the exact contribution of the \(s\)-label to the residual is
\[
 u\left((-1)^{\omega(r)}+
      \sum_{\substack{c\mid r\\
              \log c/L<t-u-\log T^\uparrow(s)/L}}
                    (-2)^{\omega(c)}\right) .                      \tag{6}
\]
The strict inequality comes from \(a>T^\uparrow(s)\);
the \(c=1\) choice is always present. If \(r\) has one prime,
(6) is zero. If \(r\) has two primes, at most one proper
positive-log \(c\) can be accepted, since the free cutoff is
greater than \(\sqrt r\). Its contribution is therefore
either \(2u\) or zero. This proves the semiprime and triprime
statements (the \(s=1\) term is zero).

Now let \(y=p_1p_2p_3p_4\) satisfy (3), and write
\(u_i=\log p_i/L\), so \(u_i\le v_1\).
There is no nonzero triple-complement \(s\)-label because its
remaining single prime would not exceed \(x^{.505}\).
Each singleton \(s=p_i\) is raw-admissible.
In (6) its signless constant cancels, the single-prime \(c=p_j\)
terms have weight \(-2u_i\) each, and the two-prime \(c\) terms
have nonnegative weight. The three-prime \(c=r\) term cannot
occur. Drop all the nonnegative two-prime \(c\) terms to get
a lower bound. Draw a directed charge \(i\to j\) for each of
the remaining negative terms, namely whenever
\[
 u_i+u_j<t-\log T^\uparrow(p_i)/L .
\]
Because \(u_i\le v_1\), (1) implies that the right side is at
most \(t-\alpha_1\). For all sufficiently large \(x\),
\(t\le1+\log(3/2)/L<1+\eta/8\), so
\[
 w=u_i+u_j<t-\alpha_1<.495-\eta/8=v_2 .
\]
The physical paired label \(s=p_i p_j\) is raw-admissible, since
its complementary exponent \(t-w>\alpha_1>.505\).
Moreover \(T^\uparrow(p_i p_j)\ge x^{.505}\).
Its remaining two genuine primes are each at most
\(x^{v_1}<x^{.505}\), so no one of them can be the proper
free factor \(a\). Consequently (6) for this pair is exactly \(2w\).
It pays \(-2u_i\) if only \(i\to j\) occurs, and pays both
\(-2u_i-2u_j\) if the reverse charge occurs as well.
Every edge is accounted for using its own unordered pair,
with no duplication. All other pair labels are nonnegative
by the two-prime case of (6).
This proves (3) on the actual integers with the actual cutoffs.

## Scope

The negative rank-four set is not shown small once it has such a prime.
All higher ranks remain, and a genuine near-half prime can still change
the sign via the different outer-divisor choices in (6).
The theorem narrows the support to which a further signed estimate
must apply. It does not give a favorable sign on an arbitrary
reflection or a lower bound for binary Goldbach.

