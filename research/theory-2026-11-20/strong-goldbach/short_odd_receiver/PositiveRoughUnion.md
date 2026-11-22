# Signed opposite-arm transfer when at least one positive arm is very rough

Use the same actual \(H\), caps and parameters in
[the bilateral rough debit](BilateralRoughDebit.md), and hence in
[the exact short odd receiver](Proof.md). In particular
\(\chi\leq\psi\), \(v=.498\), \(k=(1-.0001)^{-1}\), and
\(\alpha=1-.001 k\).
At an even target \(N\), write \(L=\log N\), \(x+y=N\),
\(x\in NJ\) for a fixed central interval of positive length,
\(M=|J|N\mathfrak S(N)\), and retain the actual target-unit mask
\((x,N)=1\) throughout. Set \(a=.150\).
Let \(\mathcal A\) be the rows for which **at least one** arm
has \(H(n)>0\) and \(P^-(n)>N^a\); no rank, sign or roughness
condition is imposed on its opposite arm.

**Theorem.** At every sufficiently large even target,
\[
          \sum_{(x,y)\in\mathcal A} H(x)H(y)
                                    \geq -.349M+o(M).          \tag{1}
\]
Also the rows with an actual prime factor \(>N^{.502}\) on either
arm have \(o(M)\) **absolute** cost, even with arbitrary least
factor and arbitrary other prime powers.

Consequently the actual residual outside the union (and outside the
discarded giant rows) has signed weight at most
\[
                 R_J-\bigl\{1-(.001k)^2-.349\bigr\}M+o(M).
                                                               \tag{2}
\]
Every adverse row of this residual has a genuine least factor
\(\le N^{.150}\) on its **positive** arm, and there is no giant
\(>N^{.502}\) on either arm. The positive and negative contributions
on the arbitrary opposing arm in (1) are both retained.
Neither (1) nor (2) is a bound for the signed residual from below.
There is no addition of the earlier bilateral \(.645M\) estimate:
its adverse rows already intersect the union in (1).
The quartic half-zero score is a different score and is not used.

## 1. One rough-positive leg, with all its actual opponents

By [Proof, Theorem 2](Proof.md) nonsquarefree rows can be
discarded at \(o(M)\) absolute cost. Put
\[
 P(n)=1_{\{n\ {\rm squarefree},\,P^-(n)>N^a\}}[H(n)]_+,
 \qquad P=P_2+P_4+P_5+P_6+P_{\rm err}.
\]
Here \(P_j\) is its true rank-\(j\) part; \(P_{\rm err}\) is
the rank-three part, uniformly \(O_J(1)\) by the bilateral
debit's exact cofactor geometry. Primes have \(H=0\) and ranks
above six are impossible. The pointwise \(O_J(1)\) score
errors within the individual rough ranks will only be dropped
in genuine rough-versus-rough products after paying the rough
pair count \(O(M/L^2)\). On the arbitrary opposite arm all of
\(H\) is retained.

True rank product distribution gives, in both orientations,
\[
 \langle P,H\rangle
    =\alpha\mathfrak S(N)\!\!\sum_{\substack{x\in NJ\\(x,N)=1}}\!\!P(x)
                       -\langle P,\Pi\rangle+o(M),           \tag{3}
\]
with \(1-J\) in place of \(J\) under reflection.
For this use [WholeMarkPrimeTransfer, §1](../nearfull_high_vaughan/WholeMarkPrimeTransfer.md)
on the true squarefree products of bounded rank at any fixed
strictly subroot level, including \(.4997\).
A label of maximal size is a genuine prime factor and its
coefficient can be divided by \(\log r/L\), bounded
away from zero and with bounded variation in that slot.
The other slots have divisor-bounded product coefficients.
Use a log-fine mesh in the individual target-log angles and
the true central spatial argument (or a finite majorant mesh
followed by refinement). The exact \(P/L\) is piecewise
Lipschitz uniformly in \(N\) on these compact sets of angles;
the only hard mark cut on this source is at the **individual**
factor angle \(v\), already retained in its factor window.
A positive part preserves the Lipschitz bounds. One may count
labelled tuples with their actual rank factorial; repeated
primes \(>N^a\) then have power-small cost by the true square
rows and crossed divisor moments. Physical spatial and score
mesh errors are bounded by these same moments, as are the
reduced-model errors with their extra reciprocal totient
harmonic. Thus all cutoffs are on true products and
arbitrary-log summed error is available for each completed
absolute modulus sum with its fixed divisor-power weights.

To obtain (3), open \(A_F-B-C_\psi\) on the opposite arm
exactly as in [Proof, §§1–2](Proof.md), with \([q,e^2]\)
for its squarefree term. The physical proper-prime-power and
squarefree expansion errors there are allowed with this
bounded-log source. In the reduced principal keep the actual
source mask \(Nx\); the single-leg zeroth and first moments,
including the distinguished actual prime in \(C_\psi\),
are precisely the one-variable computations of that proof.
The coefficient is \(\alpha\mathfrak S(Nx)\).
Since \(x\) has at most six macro factors, this equals
\((\alpha+o(1))\mathfrak S(N)\), uniformly here.
The genuine opposite prime term is \(\Pi_F\);
replacing it by \(\Pi\) costs \(o(M)\) by the following genuine
sieve upper and the \(O_J(1/L)\) actual multiplier error.

Use the fixed relative sieve level \(Q_0=N^D,\ D=.499\).
Exactly as in [BilateralRoughDebit, §3](BilateralRoughDebit.md),
true product distribution gives
\[
 \langle P,\Pi\rangle\leq \Bigl(\frac2D+o(1)\Bigr)
            \mathfrak S(N)\sum_{x\in NJ,(x,N)=1}P(x).         \tag{4}
\]
Indeed the true prime exceeds \(N^{D/2}\), the dimension-one
upper sieve has \(s=2\), and the factor \(L\) of the prime
weight cancels the \(L^{-1}\) model. Its reduced density is
\(1/(p-1)\) only for \(p\nmid Nx\), and zero otherwise; no
opposite composite is assigned prime weight in (3).
Use \(P_a=I_2+I_{4,+}+6I_5+I_{6,+}\) of the bilateral proof.
Its ordinary upper \(P_a<.03874925\) gives a two-orientation
lower \(-2(2/D-\alpha)P_a M+o(M)\) in (3).

## 2. The real positive overlap: a matched pair of factor labels

The key is to price \(P_5\) as receiver without paying its
maximum pointwise weight \(6L\) times a generic rough density.
Put \(b=.440\). On an actual squarefree rank-five \(y\) of the
required floor, the ten genuine pair-product target angles
\(t_{pq}=\log(pq)/L\) have sum \(4\log y/L\leq4\).
Consequently
\[
   \sum_{\{p,q\}\subset\{p:p\mid y\}}(b-t_{pq})_+
                \geq10b-4=.4.
\]
Together with its rank-five score cap \(6L+O_J(1)\), this permits
the nonnegative receiver majorant
\[
 P_5(y)\leq
      \frac{6+O_J(L^{-1})}{10b-4}\,L\,
      1_{\{P^-(y)>N^a\}}
      \sum_{\substack{p<q,\;pq\mid y\\p,q\ {\rm prime},\ p,q>N^a}}
                            \bigl(b-\log(pq)/L\bigr)_+ .      \tag{5}
\]
The ten-slot inequality is used on true rank-five rows only;
the right side may be positive on other ranks, as befits an upper.

At fixed distinct actual \(p,q\) with \(t=\log(pq)/L<b\),
upper-sieve \(y/(pq)\) at
\[
           D_{pq}=N^D/(pq),\qquad z_{pq}=\sqrt{D_{pq}} .
\]
Indeed all its true prime factors on the retained receiver
are above \(N^a>z_{pq}\), since
\((D-2a)/2=.0995<a\). The minimum residual level has the
fixed reserve \(D-b=.059\).
The genuine modulus is \(p q d\leq Q_0\), with \(d\) the
ordinary upper sieve divisor, and all the \(d\)-primes are
below both \(p,q\). An actual contributing prime pair has
\((pq,N)=1\); the actual source progression remains at
residue \(N\), and in its reduced term also requires \((x,pq)=1\).
After imposing the genuine labels, the quotient tested
prime has conditional density \(1/(\ell-1)\) for
\(\ell\nmid Nx pq\), zero at target or source primes.
There is no tested prime dividing \(pq\).
The two labelled primes contribute the outside denominator
\(1/\varphi(pq)=(1+o(1))/(pq)\) uniformly. The model
\(\mathfrak S(Nx)/\mathfrak S(N)=1+o(1)\) holds on all
true sources used here; omitting \((x,pq)=1\) only
enlarges the resulting positive upper. The singular factor
for the variable cutoff is uniform as in the earlier
rough count. Target prime labels are also dropped only
for the positive upper.

Thus a genuine nonnegative bounded-rank source \(Z\) of
this same floor, tested against (5), satisfies
\[
  \langle Z,P_5\rangle\leq (B_5+o(1))\mathfrak S(N)
                          \sum_{x\in NJ,(x,N)=1} Z(x),
 \qquad
 B_5=\frac{12}{10b-4}\int_{2a}^{b}
 \frac{\log((t-a)/a)}{t}\frac{b-t}{D-t}\,dt .                 \tag{6}
\]
This is a bound after summing the actual labelled pairs,
not a separate error claim for each \(p,q\).
The modulus multiplicity of all \(p,q,d\) is bounded by
a fixed divisor power; varying level, weights and
prime-label windows remain within its coefficient.
The same arbitrary-log product discrepancy therefore pays
the whole sieve error, using the same source as in (3).
The sieve principal before the weight in (5) is
\(2\mathfrak S(N)/(pq(D-t)L)\) times the unopposed source
mass. Finally the integral arises from the genuine
unordered two-prime reciprocal harmonic:
for fixed total angle \(t\),
\[
   \frac12\int_a^{t-a}\frac{ds}{s(t-s)}
                             =\frac{\log((t-a)/a)}t .
\]
The diagonal does not contribute to the true pair summation
and is power-small in its positive completion.
In particular there is no extra ordering factor in (6).

Write \(I_4=I_{4,+}, I_6=I_{6,+}\) and \(p_5=6I_5\).
An upper for the part of \(\langle P,P\rangle\) involving
\(P_5\) is \(B_5(p_5+2(I_2+I_4+I_6))M+o(M)\).
For the remaining overlap use:
* On its significant physical support \(P_2/L\leq1\)
  and both genuine factors have target angle at least
  \(v-o(1)\). The linear upper sieve at \(Q_0\) and
  \(z=N^{D/2}\) is therefore valid, costing \(2/D\)
  with a rough source. In terms with \(P_4\) or \(P_6\)
  as the other arm, take that other arm as source.
* On significant support \(P_4/L\leq1\) and
  \(P_6/L\leq10\), each with the floor \(a\).
  Use the floor-\(a\) dimension-one sieve with the
  bound \(A_a(D)=2D^{-1}(1+(D/a-3)^2/4)\).
  Take \(P_6\) as source in each \(4,6\) mixed term.
* The \(O_J(1)\) errors on true rough rows, including
  rank three, cost \(o(M)\) by the actual two-rough count.

By reflection, these collar-only overlaps cost at most
\[
               \frac2D(I_2+2I_4+2I_6)
                     + A_a(D)(I_4+2I_6+10I_6)              \tag{7}
\]
in units of \(M\). All terms in (6)–(7) are a positive upper
on the genuine overlap; no independent two-rank
distribution is assumed.

The exact signed union with nonsquarefree rows discarded is
\(\langle P,H\rangle+\langle H,P\rangle-\langle P,P\rangle\).
The overlap is literally positive and is subtracted
**once**. Equations (3)–(7) give the lower in (1).
The [exact checker](check_positive_rough_union.py) gives
\(B_5<1.652\), and the resulting debit is \(<.349M\).

## 3. Absolute deletion on all actual prime giants above .502

This part uses the same \(H\), but imposes **no** rough floor.
After paying squares as above, write \(n=rm\) with a true
prime \(r>N^{1-v}=N^{.502}\). It is unique. A prime \(n\)
itself has \(H=0\); otherwise \(m>1\) is squarefree.
For any \(d\mid m\),
\(\log(dN/n)/L\leq1-\log r/L<v\), so these arguments
are all affine. Any divisor containing \(r\) lies outside
the supports. Every eligible smaller mark \(p\mid m\)
has its \(P_F\) terms cancelled exactly by \(B\), since
its actual remaining product label divides \(m\), of
angle \(<v\), hence has cap one.
An ineligible factor \(p\leq U\) occurs in neither mark
sum. The sole true \(r\)-mark therefore contributes the
full affine signed divisor sum on \(m\).
It is zero when \(m\) has at least two prime factors.
The companion \(C_\psi\) sum is then also zero: it is
the full signed sum of an additive function of the
distinct true primes of \(m\), with \(\psi=1\) on all
these divisors. If \(m=p\) is a single genuine prime,
the exact formula instead gives
\[
             H(rp)=k(\log p)\bigl(1-\log(rp)/L\bigr).
\]
Write \(E'(rp)=k\log r\log p/L\) on those squarefree
semiprimes and \(0\) elsewhere. The displayed error is
\(O_J(E'(n)/L)\), since \(\log r>.502L\).

To pay this uniformly even for very small \(p\), apply
the same corrected two-form Henriot bound as in
[Proof, §3](Proof.md) on \(x,N-x\), not at fixed \(p\).
On the indicated semiprimes,
\[
                       E'(n)\leq kL
                           \prod_{\ell\mid n}\frac{\log\ell}{L}.
\]
The product is a genuine nonnegative multiplicative
envelope (the same value at each positive prime power,
zero at target primes). Its rough Euler insertion has
bounded cost because
\(\sum_{\ell\leq N}\log\ell/(\ell L)=O(1)\).
The other arm retains the full integrated \(H\)-envelope.
Thus \(\langle E',|H|\rangle,\langle |H|,E'\rangle\ll M\)
and the giant cohort costs \(o(M)\) absolutely.
This removes all such rows, including those with arbitrary
ineligible actual smaller factors. Equation (2) now follows
from the exact full identity and (1), with no other
regional lower inserted.
