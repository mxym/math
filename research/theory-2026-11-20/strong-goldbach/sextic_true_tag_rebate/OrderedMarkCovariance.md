# Paid true mark removals in the degree-six detector

Use the genuine fixed-target \(N,L,J,M,\Pi,R_J\) and the squarefree
own-log profile \(F,H\) in [the degree-six proof](Proof.md).
For the wider-bank option first use the actual bank \(B=\{p\text{ prime}:N^{.010}<p\le N^{.016}\}\);
write \(k(n)=\#\{p\in B:p\mid n\}\). Define
\[
 A_j(n)=\binom{k(n)}j H(n)\quad(j=1,2),\qquad A=A_1-A_2.
\]
Let \(a=.010,\ b=.016\), and let \(T_E=\sum_{\ell\in E}t_\ell\)
for genuine mark angles \(t_\ell\in(a,b]\). The two ordinary
signed constants are
\[
 m_j=\frac1{j!}\int_{(a,b]^j}
       \sum_{E\subseteq[j]}(-1)^{|E|}F'(T_E)\,
                             \prod_{\ell=1}^j\frac{dt_\ell}{t_\ell},
 \qquad
 (m_1,m_2)=(.4246009303\ldots,.0186958367\ldots).
\]
The physical pairing is still on actual target units.
The marks are not model prime labels.

**Theorem A (wider bank).** Uniformly through the even targets,
\[
 \langle A_i,A_j\rangle=m_i m_j M+o(M)\quad(i,j\in\{1,2\}),\qquad
 R_J\ge .509M+\langle H-A,H-A\rangle+o(M).                       \tag{1}
\]
Here \(H-A=\tfrac12(k-1)(k-2)H\) pointwise. It is exactly zero
on every actual arm with one or two bank primes, has the same
sign as \(H\) everywhere else, and is amplified at four or more.
The remainder covariance, including all its high multiplicities,
is not estimated. This subtraction is **not** added to the
rough \(Q\) or negative \(W\) corrections in the preceding proof.\n\nThe separate narrower-bank option in §4 does pay the entire\nrough-correction overlap and gives a single jointly compensated\nscore. Neither option is added to the other.

## 1. Physical marked-product tails and the product-angle diagonal

An \(i\)-tag product \(P\mid x\) and a \(j\)-tag product \(Q\mid y\)
are products of actual distinct primes of the stated band,
each unordered subset counted once. On the actual target units
\((P,Q)=1,\ (PQ,N)=1\); otherwise the pair is absent.
Use the literal free lattice
\[
      x=P(u_0+Qv),\quad y=Q(v_0-Pv),\quad Pu_0+Qv_0=N .
\]
Its central length is \(\asymp_J N/(PQ)\gg_J N^{.936}\).
The two displayed quotient forms are primitive (each constant is
a unit at the opposite leading coefficient), with resultant \(N\).
Their roots are distinct off \(PQN\), coincide at primes of \(N\)
and are removed by the actual unit mask there, and have one root
at each prime of \(PQ\). Multiplicative Fourier weights as in
[the half-zero proof, §2](../halfzero_detector/Proof.md) apply
by corrected Henriot on these **actual quotient forms**. The
leading-prime ratios in the root product are uniformly bounded
and tend to one, since \(P,Q\) have at most four polynomial
prime factors. The coefficients and form sizes are polynomial
in the free length, with fixed power margin. At fixed \(P,Q\)
one may bound the extracted phase factors of their marks by
\(2^{i+j}\). Repeats of a named prime are removed by actual
\(p^2\mid x\) or \(p^2\mid y\), power-small with fixed divisor
weights. The resulting absolute contribution is
\(O_J(M/(PQ))\), with the same multiplicative rank and tiny-factor
tail gains and smooth taper errors as in the half-zero proof.
After the real finite rank and positive floor cut, own-log
to target-log costs \(o(M)\) as there.

In particular, writing \(\beta=\log P/L,\ \alpha=\log Q/L\),
\[
 \sum_{|\beta-\alpha|\le\eta}
   \sum_{\substack{x\in NJ,(x,N)=1\\P\mid x,\ Q\mid N-x}}
                 |H(x)H(N-x)|=O_J(\eta M)+o_\eta(M).              \tag{2}
\]
Use the above uniform true fiber bound and genuine reciprocal
prime harmonics for each of the at most four actual tags. At
fixed \(\eta\), their bounded log-angle densities on \([a,b]\)
give the \(O(\eta)\) mass of this sum-of-angles collar (condition
on all but one angle); this upper may omit cross-prime restrictions
in the *positive reciprocal harmonic*, not in the fiber.
The statement follows by fixed angle rectangle covers and PNT
first. Thus it is the full product-angle diagonal which is
negligible, rather than just equality of two integer labels.

## 2. Genuine factored distribution away from that diagonal

Consider a fixed product-angle box with \(\beta>\alpha+\eta\).
In the source \(x=Ph\), retain fixed finite rank, positive
actual least-factor floor, and its exact \(H(x)\) weight;
take their limits using §1. For each actual choice of a
named source \(i\)-tag subset, group its one or two actual
primes into the short input \(P\), and the other genuine
prime factors into \(h\). On log-fine multiplicative boxes
for the separate prime slots, the signed angular source
weight is frozen with arbitrarily small log error.
Use factorial normalization on ordered slots within the
two groups, rather than making the tag unique. Short and
long supports are dyadic after harmless padding. Repeated
slots have actual polynomial prime squares and contribute
power-small; endpoint cells lie in actual integer strips
\(O(NL^{-C}+1)\), costed with crossed divisor moments as in
[the true Fouvry comparison, §1](../quartic_tiny_opponent/Proof.md).
The sizes of all these costs allow any fixed requested log
accuracy. This retains the physical central windows rather
than replacing their residues.

The grouped short coefficient, including for \(i=2\),
satisfies Fouvry's prime-like congruence condition (1.3).
For \(i=1\) this is maximal prime Siegel--Walfisz with the
actual arbitrary auxiliary excluded primes. For \(i=2\),
in one box fix the first genuine prime, omit it if it is
not a unit at the test modulus or auxiliary \(d_0\), and
apply maximal prime Siegel--Walfisz to the second in the
literal reduced class. Its characteristic scale is
polynomial in \(N\); two endpoints give any fixed
subinterval, including an additional cut on the group
product if needed. Omitted auxiliary primes cost at most
\(\omega(d_0)\) times the count of the first prime. This
has fixed power slack relative to the grouped scale,
since each tag has a fixed positive exponent; large
\(\omega(d_0)\) are harmless in the permitted
\(\tau(d_0)^{O(1)}\) multiplier. The reduced principal
includes precisely the genuine source weight on units
at \(d_0\) and the test modulus. For moduli above a
chosen log power the trivial reduced-class bound suffices:
each integer in the short group has at most two ordered
representations by its genuine primes, so this is the
usual \(O(P_{\rm scale}/q+1)\) and totient model bound.
The same estimates apply before and after separating
the signed long source coefficient, which is only
divisor-bounded. No new distribution for arbitrary
semiprime sources at all over-root moduli is claimed.

On the receiving arm \(y=Qv\), its \(j\) tags have angles
\(t_\ell=\log q_\ell/L\) with \(T_{[j]}=\alpha\).
Open the exact short divisor score on \(v\):
\[
   f_Q(w)=\sum_{E\subseteq[j]}(-1)^{|E|}F_\delta(w+T_E).
\]
Here \(F_\delta\) is the fixed smooth sub-half taper in the
degree-six proof; \(\delta\downarrow0\) is allowed by §1.
The central prime atom vanishes on this arm. The actual
modulus is \(Qd\) with \(d\le N^{.5}\). To use independent
\(Q,d\) coefficients restore terms with \((Q,d)>1\), which
have genuine \(q_\ell^2\mid y\) and contribute power-small
on the actual rows. In the reduced model use
\(\sum_{q_\ell\in B}\varphi(q_\ell^2)^{-1}\ll N^{-.01+o(1)}\)
with the remaining divisor harmonics. Entirely squareful
nonmarked exceptions can be removed by the real tail limits.
The factors \(F_\delta(w+T_E)\) separate by Fourier
inversion of \(F_\delta\): the characters in \(w=\log d/L\)
and in the named angles are independent, with finite
absolute frequency norm. If several named tuples give
the same \(Q\), their multiplicity is bounded by \(2!\)
and their phase sums are part of the \(Q\)-coefficient
only. Real spatial logarithms can be kept by localization.

Apply [Fouvry's actual moving-residue
Theorem (1.4), C.1, p. 619](https://www.numdam.org/article/ASENS_1987_4_20_4_617_0.pdf)
with short group angle \(\beta\), first modulus slot the
\(d\)-dyad, and second modulus group the true \(Q\) at
angle \(\alpha\). The strict rails in this box are
\[
 -\beta+2(.5)+\alpha\le1-\eta,\qquad
 \tfrac32\beta+\tfrac74(.5)+2\alpha
                  \le .875+3.5(.032)=.987 .
\]
The product of the actual long and short source scales
is \((1+o(1))x\) in the fine boxes, so its printed scale
\(X=4UV\) is \(>N\) for the actual central windows. The
literal residue is \(N\), not a fixed small integer.
Log-fine boxes and dyadic intervals cost fixed log powers.
This pays the actual weighted discrepancy for precisely
these separated product moduli with arbitrary log accuracy.
On the reversed angle ordering use the other physical arm
as the source in the reflected interval, with the same argument.

The remaining reduced principal is
\(1/\varphi(Qd)\) on the exact mask \((Qd,Nx)=1\).
Complete the signed \(d\)-harmonic with its \(NxQ\) mask:
its first-log moment is \(-\mathfrak S(NxQ)\), zeroth
moment zero. On the finite-rank compact retained source
all added factors are polynomial, so
\(\mathfrak S(NxQ)/\mathfrak S(N)=1+o(1)\).
The omitted \(Q\)'s sharing a prime with that actual
source or target have power-small reciprocal mass at
any fixed positive floor. The resulting mark coefficient
is the negative angular integral of \(f_Q'(0)\) with
the true \(1/\varphi(Q)\) weight, and \(1/j!\) is the
subset normalization. The ordinary source mark model
is the same signed coefficient at order \(i\): direct
integer CRT on that arm at \(Pd\le N^{.532}\), with
actual unit inclusion–exclusion, gives power-small
floors and signed \(\mu(d)/d\) moment
\(-NP/\varphi(NP)\); after its outside
\(\varphi(N)/(NP)\) the true weight is \(1/\varphi(P)\).
This is the argument of §4 of the degree-six proof
at the one- or two-mark order, and works also on any
fixed product-angle interval.

Consequently each separated box has, at scale \(M\),
the product of its two signed angular derivative
integrals with actual subset weights. Pay the omitted
physical angle diagonal by (2) while the model diagonal
has vanishing mass on shrinking rectangles. First taking
\(N\to\infty\) at fixed meshes/floors/tapers, then their
improvements, proves the matrix scalar products in (1).
In particular \(\langle A,A\rangle=(m_1-m_2)^2M+o(M)\).

## 3. True prime comparison and the compensated identity

The ordinary signed model gives \(M_{A_j}=-m_jM+o(M)\).
For a genuine marked-prime cross
\(\langle\Pi,A_j\rangle\), no unproved over-root prime
distribution is used. Use ordinary prime BV with the
literal modulus \(Qd\) after shortening each term
\(F(w+T_E)\) by the explicit \(\Phi_{\alpha-T_E+\delta}
(w+T_E)\) of the [degree-six proof, §3](Proof.md).
For \(E=[j]\), the shift is already \(\alpha\) and just
the usual taper is needed, at negligible limiting cost.
Otherwise \(\Phi_h\) as defined there gives the exact
cap \(d\le N^{.5-\alpha-\delta}\), so all joined moduli
are strictly sub-root. Keep the actual reduced mask
\(NQ\) and the outer \(1/\varphi(Q)\). The zeroth and
first signed moments give \(-m_j\) with endpoint
corrections \(\Phi_h'(T_E)\).
Since \((.5-T_E)/(\alpha-T_E)\ge .5/.032\),
each correction is \(<10^{-5}\), directly from the
exponential linear formula for \(g_j\) in that proof
(use \(z-1\ge14.625\)). True powers, repeats and own logs
are handled by the marked envelopes as there. The argument
works on both true prime orientations.

Write
\(D(t)=44\cdot50t^{8/3}+112\cdot83t^{14/3}\).
The explicit Cauchy--Plancherel seam transform norms
used in that proof remain \(<50,<83\) for widths up to
\(.033\), as the [rational checker](check_ordered_marks.py)
verifies. The ordinary **absolute** marked errors on
the physical residual angular measure have the same
upper \(10/(2\pi c)\) times the sum \(D(\alpha-T_E)\),
with \(c=1-\alpha>0\); shifting the profile changes
only its Fourier phase. Use the genuine \(3.446\)
angular prime upper on bounded-rank and positively
rough actual pieces, then the absolute marked tails.
For two tags these estimates are the explicit
integral upper
\[
 \frac{3.446\cdot10}{2\pi(1-2b)2}
  \int_{(a,b]^2}
      [D(t+s)+D(t)+D(s)]\,\frac{dt\,ds}{ts},
\]
with the small endpoint corrections just discussed.
The corresponding single-tag upper uses
\(3.446\cdot10/(2\pi(1-b))\int_a^b D(t)dt/t\).
With the real endpoint corrections both are \(<.109\)
and \(<.054\), respectively. The checker integrates
positive increasing powers by outward rational rectangles
with actual logarithmic harmonic bounds, and computes the
two ordinary derivative integrals exactly. Hence
\[
 |\langle\Pi,A_j\rangle+m_jM|,\ 
 |\langle A_j,\Pi\rangle+m_jM|
       \le e_jM+o(M),\qquad (e_1,e_2)=(.054,.109).
\]
The genuine finite-product transfer (3) of the first
note applies also to each signed \(A_j\) against \(H\);
extend from the compact finite ranks using the actual
tails, since \(\binom{k}{j}\) is bounded (each tag exceeds
\(N^{.01}\)). Therefore both \(\langle A,H\rangle\) and
\(\langle H,A\rangle\) have absolute value at most
\(.163M+o(M)\). Finally use the literal algebra
\[
 \langle H,H\rangle=\langle H-A,H-A\rangle+
              \langle A,H\rangle+\langle H,A\rangle-\langle A,A\rangle
\]
and \(\langle H,H\rangle=R_J-M+o(M)\).
Since \(0<m_1-m_2<.406\),
\(1-2(.163)-(.406)^2>.509\), giving (1).
No sign or independence assumption has been used on the remaining
genuine score, or on any overlap with the separately defined \(Q,W\).

## 4. A narrower bank with the entire rough overlap paid

For this **separate option**, use the actual band
\(B_0=\{p\ {\rm prime}:N^{.010}<p\le N^{.012}\}\).
Write \(k_0(n)=\#\{p\in B_0:p\mid n\}\),
\(A^0=(k_0-\binom{k_0}{2})H\), and let
\[
 Q_{\rm rough}=[-H]_+1_{P^->N^{.1251}},\qquad
 H_C=H+Q_{\rm rough}-A^0.
\]
This is the full rough correction from the degree-six base proof,
including every actual negative rank-four through rank-seven row.

**Theorem B (jointly paid option).** Uniformly through even \(N\),
\[
                   R_J\ge .572M+\langle H_C,H_C\rangle+o(M).      \tag{3}
\]
In particular \(H_C\) vanishes on every negative rough arm and on
every actual arm with one or two \(B_0\)-marks. The two row predicates
are disjoint on the same arm. The multiplier on the remaining
tagged arms is still \((k_0-1)(k_0-2)/2\); it is nonnegative,
and amplifies the score when \(k_0\ge4\).
No sign is established for this genuinely remaining covariance.
This is different from the rough-only residual or the wider option
of Theorem A, so their threshold coefficients are not cumulative.
With the narrower mark correction omitted, the rough receiver price
below also improves the rough-only bound on the **same** residual
\(H+Q_{\rm rough}\) to \(R_J\ge .929M+\langle H+Q_{\rm rough},H+Q_{\rm rough}\rangle+o(M)\).

### 4.1. Actual rough receiver against a finite-product source

For each \(R_j=Q_{\rm rough}1_{\omega=j}\), \(4\le j\le7\),
we construct a genuine upper
\(\langle Z,R_j\rangle\le U_j M_Z+o(M)\) on any fixed
nonnegative compact prime-product source \(Z\) of positive floor,
in either spatial orientation. Let
\(r=.1251,\ \theta=.499\), and retain the true target-angle
notation; these agree with own angles on the fixed ranks
up to \(O_J(1/L)\). Write \(s\) for a sum of two mark angles.

In rank four, first use the **sign** of the true score to
justify a two-least opening. If all four own angles are
\(\le c=.4005\), their square sum is at most
\(c^2+(1-c-2r)^2+2r^2<11/35\): a convex maximum
on this box-constrained simplex puts as much surplus as
possible in the first coordinate, then the second.
The rank-four score is then nonnegative. Thus any negative
rank-four row has largest *target-log* angle \(>.4\) for all
large \(N\), with fixed slack from the own-angle condition.
Its two **actual least** angles \(u\le v\) therefore have
\(s=u+v\le .4\), because the sum of the three smaller is
\(\le .6\). Let \(z\le w\) be the two remaining angles,
with \(z\ge v\ge s/2\) and \(w>.4\).
For the majorization we can add \(1-\log n/L=O_J(1/L)\)
to the largest angle, so \(z+w=1-s\) and all the preceding
inequalities survive. This changes the bounded normalized
score by \(O_J(1/L)\). The exact quartic-in-angles rank-four
formula of the [degree-six base, §2](Proof.md) now gives
\[
 \frac{R_4(n)}L\le uv\,G_4(s)+o(1),\quad
 G_4(s)= \max_{V_{\min}(s)\le V\le V_{\max}(s)}
                           [V(C(s)-3360V)]_+,
\]
where
\[
 C(s)=1680[r^2+(s-r)^2+(1-s)^2]-528,\quad
 V_{\min}(s)=(s/2)(1-3s/2),\quad V_{\max}(s)=.4(.6-s).
\]
Indeed the actual remaining product \(V=z(1-s-z)\) lies in
this interval: \(s/2\le z\le 1-s-.4<(1-s)/2\), where the
product is increasing. The square sum of the two named least
angles is at most \(r^2+(s-r)^2\). The quadratic maximum is
evaluated at \(C(s)/6720\) clamped to the displayed interval.

For ranks \(5,6,7\) the bounds per true pair of sum \(s\) are
\[
 \begin{split}
 q_5(s)&=(s-r)^2+(1-s-2r)^2+3r^2,\\
 G_5(s)&=(10080\sqrt{q_5(s)}-1056/\sqrt{q_5(s)})((1-s)/3)^3,\\
 G_6(s)&=40320((1-s)/4)^4,\\
 G_7(s)&=2112((1-s)/5)^2+80640\cdot7((1-s)/5)^5 .
 \end{split}
\]
The normalized negative score is at most \(u v G_j(s)+o(1)\)
for **any** true named pair \(u,v\).
For rank five, maximize the two marked squares and the other
three squares separately under the true floor \(r\), then use
the monotone exact coefficient from the degree-six base and
AM--GM on the remaining product. Rank six is a constant
times the full product. Rank seven uses
\(2112\prod_{i\le4}u_{(i)}+80640\cdot7\prod_{i\le7}u_{(i)}\),
by the exact \(b_7''(0)\) bound. The product of the least four
is at most the actual marked pair times the two smallest of
the other five, whose product is at most \(((1-s)/5)^2\).

In rank \(j=5,6,7\), use all actual unordered pairs weighted
by \((c_j-s)_+\) and divide by \(\binom j2 c_j-(j-1)>0\),
where \((c_5,c_6,c_7)=(.461,.375,.303)\).
The sum of all pair angles is \((j-1)\log n/L\le j-1\),
so this is a pointwise bound, not a repetition of the full score.
In rank four use just the two actual least labels proved above;
we may then drop their least-status in the upper sieve.
All these opened marks have actual product \(h=pq\) below
\(N^{.499}\). Upper-sift the literal quotient at exponent
\((\theta-s)/2<r\) with level exponent \(\theta-s\).
The actual quotient primes exceed \(r\). At the true
joined moduli \(hd\le N^{.499}\), apply the genuine reduced
product-BV and linear-sieve calculation in
[the quartic receiver proof, §1](../halfzero_detector/CompensatedDebit.md),
with actual unit mask \(Nx\) and parameter 2.
Omit primes of the mark from the upper sieve, a true
enlargement with model change \(1+o(1)\).
The total upper weight is then
\((1+o(1))2\mathfrak S(N)/(h(\theta-s)L)\).
After \(uv\) cancels the true unordered pair harmonic,
the remaining angle density is \((s/2-r)ds\).
Uniform \(o(1)\) errors on the normalized score are
harmless under these same positive upper weights on
the compact rough ranges. Thus the required receivers are
\[
 U_4=2\int_{2r}^{.4}G_4(s)\frac{s/2-r}{\theta-s}\,ds,\qquad
 U_j=\frac{2}{\binom j2c_j-(j-1)}
       \int_{2r}^{c_j}G_j(s)(s/2-r)\frac{c_j-s}{\theta-s}ds
                           \quad (j=5,6,7).
\]
Their [rational outward checker](check_joint_rough_marks_v4.py)
gives \(U_4<.150\) and \(\sum_j U_j<.852\).
These are genuine conditional uppers against actual product
sources, not independent two-rank occupancies.

The same bounds also improve the **entire rough-only debit**.
Apply each receiver to the sources \(R_i\) themselves and
reflect, giving the positive upper
\(\langle R_i,R_j\rangle\le
 \min(m_i U_j,m_j U_i)M+o(M)\) for each ordered pair, with
\(m_i\) the ordinary upper in the degree-six base.
Reusing its two signed mixed estimates (3), one obtains
\[
  \langle Q_{\rm rough},H\rangle+\langle H,Q_{\rm rough}\rangle
    +\langle Q_{\rm rough},Q_{\rm rough}\rangle
     \le (2\sum_i m_i+\sum_{i,j}\min(m_iU_j,m_jU_i))M+o(M)
     <.071M+o(M).
\]
This counts every ordered overlap once, and also proves the
rough-only improvement stated after Theorem B.

### 4.2. The whole actual adverse marked source

We need only the ordinary mass of \(Z=[-A^0]_+\), because
the remaining part of \(A^0\) is nonnegative when paired
against \(Q_{\rm rough}\). Pointwise
\[
 [-A^0]_+\le k_0[-H]_++\binom{k_0}{2}[H]_+ .
\]
The true signed ordinary one-mark model on this narrower band
is \(-m_1^0 M\), \(m_1^0=.1436884815\ldots\), by the same CRT
as in §2. In the proof of the ordinary positive one-mark mass
in [the degree-six base, §4](Proof.md), the three upper bounds
\(.01817,.02177,.04576\) for ranks 2, 3, and \(\ge9\) were
linear in the band width after all \(dt/t\) tag factors were
cancelled. Their other majorants remain valid for the narrower
band, giving here \(.2(.01817+.02177+.04576)\).
Together this prices \(M_{k_0[-H]_+}/M\).

At least two such true marks imply no positive score in ranks
\(\le7\). Rank two is impossible, and rank three has two small
labels and a giant. Its second difference is nonpositive
because \(F''<0\) in the actual interval of total small
angles \(\le .024+o(1)\). Ranks 4–7 have the negative signs
on any one tag in the base proof; larger even ranks vanish.
For odd \(s\ge9\), use the smallest-product bound in that
proof. After designating two different actual tags \(t,u\),
a product of the least \(j\) angles is at most
\((tu)^{1/2}\) times the product of the least \(j-1\)
angles among the \(s-2\) non-designated labels:
it is at most either of the two products using one
named mark and those same \(j-1\) other labels.
Hence the true joint tag harmonic, unordered, is bounded by
\(2(\sqrt{.012}-\sqrt{.010})^2\) times the residual weighted
integral. Apply the ordered-ratio estimate in the base proof
with \((j-1,\ell)=(3,4),(5,2)\), since the residual rank
starts at 7; sum the two exact geometric tails over odd ranks.
The checker gives an upper \(.004148\) for the ordinary positive
two-mark mass. This and the one-tag calculation give
\(M_{[-A^0]_+}<.167M+o(M)\) in each orientation.

Apply §4.1 to this actual source restricted to fixed finite
ranks and positive floor, with its true positive-part and
all tag masks (finite-angle Jordan approximations suffice).
Remove the restrictions by the actual paired Fourier tails
and ordinary source tails: the polynomial in \(k_0\) is
bounded since its actual tag angles exceed \(.010\), and
\(Q_{\rm rough}\le|H|\). This yields the needed two **genuine**
overlap bounds
\[
 \langle Q_{\rm rough},A^0\rangle,\ \langle A^0,Q_{\rm rough}\rangle
               \ge -(.852)(.167)M+o(M)>-.143M+o(M).
\]

### 4.3. Close the complete signed accounting

Sections 1–3 apply with \(b=.012\) unchanged. Its exact
two-order signed coefficient \(m_1^0-m_2^0\) is \(<.142\);
its prime absolute seam costs are \(<.014,.011\),
respectively (the same arithmetic and rational integrals
with the actual narrower endpoints). Hence
\(|\langle A^0,H\rangle|,|\langle H,A^0\rangle|
 \le .025M+o(M)\) and
\(\langle A^0,A^0\rangle\le .142^2 M+o(M)\).
Use every term of the actual expansion
\[
\begin{split}
 \langle H,H\rangle={}&\langle H_C,H_C\rangle
   -\{\langle Q_{\rm rough},H\rangle+\langle H,Q_{\rm rough}\rangle
                         +\langle Q_{\rm rough},Q_{\rm rough}\rangle\}\\
 &+\langle A^0,H\rangle+\langle H,A^0\rangle
   +\langle Q_{\rm rough},A^0\rangle+\langle A^0,Q_{\rm rough}\rangle
   -\langle A^0,A^0\rangle .
\end{split}
\]
The braces are paid by the entire \(.071M\) rough debit
in §4.1; the other terms have just been priced.
The retained coefficient is at least
\(1-.071-2(.025)-2(.143)-.142^2=.572836>.572\).
Combining with the original true degree-six calibration gives (3).
