# A true short compensation leaving the stable odd-rank receiver

Let \(N\) be an individual large even target, let \(J\Subset(0,1)\)
be a fixed interval of positive length, write \(L=\log N\),
\(x\in NJ\), \(y=N-x\), and \(M=|J|N\mathfrak S(N)\).
Put \(\Pi(n)=1_{n\ {\rm prime}}\log n\) and
\[
 \langle X,Y\rangle=\sum_{\substack{x\in NJ\\(x,N)=1}}X(x)Y(y),
 \qquad R_J=\langle\Pi,\Pi\rangle .
\]
All pairings use these actual target units.

Use the wide affine parameters of
[the same-score semiprime sector](../same_T_semiprime_sector/Proof.md):
\[
   \lambda=.0001,\quad U=N^\lambda,\quad k=(1-\lambda)^{-1},
   \quad \rho=.999,\quad v=.498,\quad b=.4996.
\]
The fixed \(F(t)=(1+kt)C(t)\) is affine through \(.4992\)
and vanishes from \(b\) on, with \(0\le C\le1\).
Keep the original genuine composite prime marks
\[
 P_F(n)=\sum_{\substack{r\mid n,\ r\ {\rm prime}\\ U<r<n}}
        (\log r)\sum_{d\mid n/r}\mu(d)
                           F(\log(dN/n)/L).
\]
Keep \(B\) as the subscore on the literal marks \(r\le N^v\)
with each summand multiplied by \(\chi(\log(rd)/L)\).
The fixed smooth cap \(\chi\in[0,1]\) is one on an interval
\([0,v+c_\chi]\) with some fixed \(c_\chi>0\), and zero from
\(.499\) on. This includes the original cap one through \(.4985\)
and the separate [tag-union variant](../literal_tag_union/Proof.md)
with its \(K\) fixed first; no signed credit from either previous
\(T\)-score is applied to the new score below.

Choose a fixed smooth \(\psi\in[0,1]\), one through \(.4988\)
and zero from \(.4992\) onward, with \(\int_0^\infty\psi(t)\,dt=.499\).
For instance choose a smooth reflection-symmetric transition
about \(.499\), meaning \(\psi(.499+s)+\psi(.499-s)=1\)
throughout the transition. Define the actual short compensator
\[
 C_\psi(n)=k\,\mu^2(n)\sum_{q\mid n}\mu(q)\psi(\log q/L)
        \left(\log q-\frac1L\sum_{p\mid q}(\log p)^2\right),
 \qquad H(n)=P_F(n)-B(n)-C_\psi(n).                             \tag{1}
\]
Here \(\mu^2(n)\) is the actual squarefree indicator and every
\(p\) in the inner sum is a distinct genuine prime. In particular
\(H\) has no weight on a central prime.

**Theorem 1.** Write \(\delta=1-\rho=.001\). At every sufficiently
large even target,
\[
              \langle H,H\rangle
                    =R_J-\{1-(k\delta)^2\}M+o(M).               \tag{2}
\]
There is no remaining genuine high-prime cross in (2).
This is an identity, not a lower bound on the binary atom.

**Theorem 2.** The contribution to \(\langle H,H\rangle\) of rows
with a nonsquarefree integer or a prime factor \(>N^\rho\)
on either arm is \(o(M)\), also in absolute value. Call a central
squarefree integer \(n\) stable if every actual prime factor exceeds
\(U\), and every nonempty proper subset of its prime factors has
sum of own-log angles outside \([.4978,.5022]\).
If \(n\) is stable and has no factor \(>N^\rho\), and if
\({\cal A}_n=\{A:\sum_{p\in A}\log p/\log n<1/2\}\), then
\[
                 H(n)=L\sum_{A\in{\cal A}_n}(-1)^{|A|}
                              +O_{J,\lambda}(1).                \tag{3}
\]
Consequently rows with a stable **even** rank on either arm,
or a stable arm with a factor of own-log angle \(>1/2\),
can also be discarded at \(o(M)\) absolute cost.
The stable bulk which remains consists of odd-rank squarefree
composites with all prime factors below own half on both arms.
There are additionally the actual ineligible small-mark rows
and the actual subset-angle collars; they are not equated to the
stable bulk. At fixed ranks and a fixed positive angle floor
the latter have the genuine quantitative bound in §4.
No sign of the stable odd correlation or total seam is asserted.

## 1. Squarefree forms and literal modulus sizes

Let \(A_F\) be the actual short log-minus-mark score in
[the two-endpoint identity](../nearfull_high_vaughan/JointGiantEndpointDerivative.md):
\[
 A_F(n)=\sum_{d\mid n}\mu(d)F(\log(dN/n)/L)
          \left(\log(n/d)-
             \sum_{\substack{j\mid n/d\\j\le U}}\Lambda(j)\right).
\]
On central \(n\) one has \(P_F=A_F-\Pi_F\) apart from genuine
proper prime powers \(>U\) dividing \(n\), where
\(\Pi_F(n)=F(\log(N/n)/L)\Pi(n)\). The physical exceptional set
has \(N^{1-\lambda/2+o(1)}\) integers, with all pair weights
bounded by fixed divisor powers and log factors.
Thus it has \(o(M)\) absolute effect on the pairings under study.
Write \(Z=A_F-B-C_\psi\), so \(H=Z-\Pi_F\) up to these errors.

Expand \(\mu^2(n)=\sum_{e^2\mid n}\mu(e)\) in \(C_\psi\),
retaining \(e\le N^\epsilon\) with \(\epsilon=.00015\).
The omitted physical support is at most
\(N\sum_{e>N^\epsilon}e^{-2}=O(N^{1-\epsilon})\), with the
same divisor-weight qualification. The actual modulus for
\(C_\psi\) is \([q,e^2]\), **not** \(qe^2\) counted with
coprime density. Its size is \(\le N^{.4992+2\epsilon}=N^{.4995}\).
For the additive-square term open the actual distinguished
prime \(p\mid q\), put \(q=pd\), and retain \((p,d)=1\), since
\(\mu(q)\ne0\). This does not add a new factor to the modulus
and its choices at fixed modulus have divisor-power multiplicity.
The \(A_F\) moduli are \(d\) or \(dj\le N^{.4997}\), and
the \(B\) modulus is \(rd\le N^{.499}\).
All crossed floor sums are power-small: on target units,
opposite product moduli are coprime and individually
coprime to \(N\). Opening target units adds \(\tau(N)=N^{o(1)}\)
to actual integer CRT floors, and the total modulus product
ceiling is \(N^{.9994}\), including the fixed divisor powers.
Genuine prime crosses use ordinary weighted prefix BV at these
strictly sub-root ceilings with the same physical multiplicities.
Keep the true spatial factors while applying each model.

Only in the principal, restore the full square divisor \(e\)-sum
on a \(C_\psi\)-leg by absolute completion. With \(q\) squarefree,
the added local factor in \(1/[q,e^2]\), relative to \(1/q\),
is \(1/p\) when \(p\mid(e,q)\), and \(1/p^2\) when \(p\mid e\)
but \(p\nmid q\). In the reduced prime principal the corresponding
factors relative to \(1/\varphi(q)\) are \(1/p\) and
\(1/[p(p-1)]\). These give, by Rankin with exponent \(1/4\),
an \(O(N^{-\epsilon/4+o(1)})\) absolute tail uniformly
in all polynomial \(q\); at \(p\mid q\) the correction product
is at most \(2^{\omega(q)}=N^{o(1)}\).
Coprimality constraints can be dropped only in this upper tail
bound. The remaining positive divisor harmonics cost fixed log
powers. After this completion all squarefree conditions in the
principal can be used as exact local factors.

## 2. First moments with the completed squarefree conditions

We give the local computations to check that squarefree
conditioning neither changes the singular-series normalization
nor introduces an unevaluated rank weight. Write \(s,t\) for
the two signed divisor exponents near \(1\). At a prime
\(p\nmid N\) outside any fixed mark label, let \(i_x,i_y\)
be the respective squarefree flags, each \(0\) or \(1\).
The local factor before the two inverse zetas is
\[
 1-\frac{i_x+i_y}{p^2}
     -\left(1-\frac{i_x}p\right)p^{-s}
     -\left(1-\frac{i_y}p\right)p^{-t}.                          \tag{4}
\]
The two removable square roots are disjoint modulo \(p^2\),
since \(p\nmid N\). If \(p\) belongs to one actual squarefree
Möbius divisor, that arm may hit \(p\) but may not hit \(p^2\)
when its flag is one; the other arm is then a \(p\)-unit.
This gives each of the last two terms. At \(s=t=1\) (4)
equals \(1-2/p\), irrespective of the two flags.
At \(p\mid N\), target units give local factor one, with the
usual separate \(\varphi(N)/N\) density.

If \(p\) belongs to a fixed \(A_F\) or \(B\) mark on one arm,
factor out its actual marked denominator and keep the same-arm
Möbius divisor eligible to contain \(p\), with the other
arm a unit. Its factor at \((1,1)\) becomes \(1-1/p\), as
in the ordinary marked CRT. If \(p\) is the fixed
distinguished prime on \(C_\psi\)'s additive-square term,
the same-arm Möbius variable excludes it, but its squarefree
flag gives the \(1-1/p\) factor at the assigned root.
Thus the correction at either type of single fixed mark is
the familiar \(c(p)=(p-1)/(p-2)\). Fixed marks on opposite
arms sharing a prime are incompatible; these cases are omitted
from the actual principal.

For a genuine-prime cross with \(C_\psi\), at \(p\nmid N\)
the one-variable local factor before the inverse zeta is
\[
             1-\frac1{p(p-1)}-p^{-1-s_0}
\]
with \(s_0\) near \(0\). The first correction excludes
the actual \(p^2\)-class among reduced residues; if the
Möbius divisor contains \(p\), the allowed probability is
\((1-1/p)/(p-1)=1/p\), giving the last term. At zero
the factor is \(1-1/(p-1)\), just the usual local density.
At a fixed distinguished \(p\) on this arm the same-arm
Möbius variable excludes \(p\) and the outside factor
is \(1/p\); its remaining local correction is \(c(p)\).
The \(p\mid N\) rule is unchanged.

The signed harmonic completions now work as in
[the short joint calculation, §2](../nearfull_high_vaughan/JointGiantEndpointDerivative.md).
For explicitness, after factoring the inverse zeta(s),
the Euler products away from the target and actual fixed
labels have coefficient norms absolutely bounded on the
two slightly earlier abscissae
\(1-1/(10\log L)\), or on the corresponding
one-variable abscissa. This follows directly from (4)
and its single-arm analogue: only \(O(p^{-2+O(1/\log L)})\)
errors remain at each unmarked prime. Exceptional local
factors cost a fixed power of \(\log L\) by splitting the
polynomial label's prime divisors at \(L^2\).
This also supplies uniform completions when the opposite
Möbius divisor is held fixed first: after factoring out
its reciprocal denominator its primes just join the
polynomial masks. Complete each free signed divisor one
at a time at \(S_0=\exp((\log L)^4)\), using the ordinary
zero-free-region Mertens tails convolved with those
absolute coefficient norms and bounded profile variations.
The log moments on the complete short box are then
actual derivatives of the Euler products. In particular
any zeroth moment on either free variable is zero,
and the \((1,1)\) signed first/first coefficient with
target density is \(\mathfrak S(N)\) with the stated
mark corrections. The one-variable first log moment in a
prime cross is \(-\mathfrak S(N)\), with its stated
correction. All higher fixed moments have
\((\log L)^{O(1)}\) bounds. Sharp polynomial endpoints
may be retained in the tails; the profiles vanish or
are smooth past their supports.

The first-log coefficient of \(A_F\) after its signed
mark and free-log harmonic is \(k-1-k\lambda=0\).
The possible short \(j\)-log harmonic with its marked
\(c(p)\) factors differs from \(\lambda L\) by \(O(\log L)\).
For \(B\) the coefficient is \(k(v-\lambda)\), with its
actual cap identically one through the completed short
box for every \(r\le N^v\). For \(C_\psi\)'s ordinary
\(\mu(q)\log q\) term the coefficient is \(k\psi(0)=k\).
For its additive-square term, opening \(q=pd\) flips
\(\mu(q)\) to \(-\mu(d)\), so the first coefficient at the
fixed distinguished \(p\), before its reciprocal harmonic,
comes from
\[
       k(\log p)^2 L^{-2}\psi'(\log p/L).
\]
The zeroth moment vanishes and the next terms cost \(o(1)\)
after absolute prime log harmonics and the completed
higher moments. The leading derivative is supported
strictly between \(.4988\) and \(.4992\), so any coincidence
with an \(A_F\) short mark or a \(B\)-mark is absent there;
a \(C_\psi\)-to-\(C_\psi\) coincident distinguished \(p\)
costs the square-reciprocal tail. Off this derivative
support the marked coefficients are already negligible
by the same completion and the next Taylor orders.
PNT on the genuine prime \(p\) gives the integrated
additional coefficient
\[
       k\int_0^\infty t\psi'(t)\,dt
                   =-k\int_0^\infty\psi(t)\,dt .
\]
The local \(c(p)\) factors here change the coefficient by
\(o(1)\). Thus \(C_\psi\)'s first-log coefficient is
\[
                     a=k(1-.499)=k(\rho-v).
\]
This calculation uses the literal additive prime squares,
not a substitution of \((\log q)^2\) for them.

The signed first-log coefficient for \(Z=A_F-B-C_\psi\)
is therefore \(-\alpha\), with
\(\alpha=k(v-\lambda)+a=k(\rho-\lambda)=1-k\delta\).
Its genuine prime cross is \(+\alpha M+o(M)\);
its integer CRT self-pairing is \(\alpha^2 M+o(M)\).
The \(F(\log(N/n)/L)\) spatial factor of a true
\(\Pi_F\) may be replaced by 1 after evaluating each
genuine prime principal. On the binary atom itself this
replacement costs \(o(M)\) by the usual prime-pair
upper sieve. Now
\[
  \langle H,H\rangle=\langle Z-\Pi_F,Z-\Pi_F\rangle+o(M)
          =R_J+(\alpha^2-2\alpha)M+o(M),
\]
which is (2). No \(E\times E\) or \(E\times\Pi\) estimate
is needed for this calibration.

## 3. Physical clipping of squares, high prime arms, and stable ranks

The Fourier envelopes for \(P_F,B\) are those of
[the wide actual rank tail](../nearfull_high_vaughan/WideJointGiantFiniteAngles.md)
and the smooth cap version of
[the true prime-rank pressure](../nearfull_high_vaughan/WideNoHighPrimeRankPressure.md).
They also apply to \(C_\psi\). For its log-\(q\) summand
use the profile \(t\psi(t)\). For the other summand, after
Fourier inversion at \(t\), the exact unsigned bound inside
the integral is a sum over \(p\mid n\) with weight
\((\log p/L)^2\) multiplying the product
\(\prod_{p'\mid n,\ p'\ne p}|1-e^{it\log p'/L}|\).
Allocate this one selected weight to the degree-one term
in
\[
               W_t(n)=\prod_{p\mid n}
                  \bigl(|1-e^{it\log p/L}|+\log p/L\bigr),
\]
using \((\log p/L)^2\le \log p/L\).
The remaining \(\mu^2(n)\) mask can only reduce the absolute
bound. Thus \(H\) has an envelope \(L\) times integrated
multiplicative \(W_t\)'s with fixed Schwartz profiles
(and their convolution for the actual cap).
Corrected Henriot on the true primitive forms \(x,N-x\)
gives the same \(O(M)\) positive two-leg bound, a genuine
tail \(O_{\theta,F,\chi,\psi,J}(\theta^{-K}M)\) at rank
\(>K\) on either arm for any fixed \(\theta>1\), and
a small-factor cost \(O_{F,\chi,\psi,J}(\eta M)\) for a
true factor \(\le N^\eta\) on either arm. The last claim
uses the actual \(x=pv'\) or \(y=pv'\) extraction and
resets all powers of \(p\) on that leg, extracting
\(W_t(p)\) only once even when the factor repeats.
The actual harmonic of these extracted weights is
\(O(\eta(1+|t|))\). As usual, for fixed \(\eta\) the
remaining nonsquarefree integers involve true \(p^2\)
with \(p>N^\eta\), giving \(O(N^{1-\eta})\) rows,
power-small even with divisor weights. Letting \(\eta\)
be arbitrarily small after the fixed profiles proves
the asserted \(o(M)\) total absolute square contribution.

A physical high row has unique prime \(r>N^\rho\).
Since all its low summands are either in \(B\) or zero,
\(P_F(n)-B(n)=-E(n)\) exactly there, where
\(E(rm)=k(\log r)\Lambda(m)/L\) for \(m>1\).
For squarefree \(n=rm\), every \(d\mid m\) is inside
the full plateau of \(\psi\), while no \(d\) containing
\(r\) appears. The \(C_\psi\) coefficient on \(d\mid m\)
is additive in its distinct factors. Therefore if \(m\)
has at least two primes the full Möbius sum of this
additive function is zero, as is \(E\). If \(m=1\)
the true prime row has \(H=0\). If \(m\) is a prime,
\(C_\psi(rm)=-k\log m(1-\log m/L)\), hence
\[
              H(rm)=k\log m\,\frac{L-\log(rm)}{L}
                                  =O_J(E(rm)/L).
\]
This accounts for **all** genuine higher-rank high rows,
not just the prime-versus-semiprime part. For completeness,
\(\langle E,|H|\rangle\ll M\): fix \(m\) in \(E\),
a true prime power \(\le N^\delta\), keep \(r\) as a true
prime and majorize it by a rough weight in the corrected
Henriot bound on \(r,N-mr\), of length \(\asymp_J N/m\).
The additional leading prime of \(m\) has bounded factor
\(c(m)\). The result is \(O(M/m)\) before the outside
\(k\Lambda(m)/L\), whose \(1/m\) harmonic is \(O(1)\).
This proves the \(o(M)\) high clipping; if one also keeps
nonsquarefree \(m=p^j,j\ge2\), their same harmonic is
\(O(1/L)\). Reflection treats the other orientation.

On a stable squarefree non-high composite put
\(\theta_p=\log p/L\), \(u=\log n/L=1-\kappa\), and
\(t_A=\sum_{p\in A}\theta_p\).
Since \(\kappa=O_J(1/L)\), stability gives the **same**
short-subset family for \(F\), the \(B\)-cap, and \(\psi\):
below own half the parameters lie in their full plateaux
(or affine part for \(F\)); above own half all such terms
are zero. When a product \(rd\) corresponds to a short
subset, its mark is \(r\le N^v\) automatically.
All prime marks are eligible, and a mark on a composite
automatically satisfies \(r<n\). At a short subset \(A\),
aggregate the \(P_F\)-terms by their divisor, which gives
the normalized coefficient
\((u-t_A)(1+k\kappa+k t_A)\).
Aggregate the \(B\)-terms by their actual product \(rd\):
the sign of the divisor after removing the marked prime
is \(-(-1)^{|A|}\), and its normalized unsigned weight
sums to
\[
                 t_A(1+k\kappa+k t_A)
                           -k\sum_{p\in A}\theta_p^2.
\]
It follows that \(P_F-B\) has, after the
\((-1)^{|A|}\) sign, normalized coefficient
\[
                 u(1+k\kappa+k t_A)-k\sum_{p\in A}\theta_p^2 .
\]
Subtracting \(C_\psi\) removes the last term and
\(k t_A\), leaving \(u(1+k\kappa)+k(u-1)t_A\).
This proves (3); the rank is bounded already by
\(1/\lambda\) from the actual eligible marks.
If the rank is even, each subset and its complement
have the same sign and exactly one is short. Thus the
short sum is half the full zero Möbius sum. If any factor
has own-log angle \(>1/2\), the short subsets are exactly
the subsets omitting that factor; their sum is zero
on every composite. Primes were already separately
zero. In these discarded stable sectors \(H(n)=O(1)\)
rather than \(O(L)\). The genuine \(U\)-rough condition
on that arm, written with a factor \(L\), and the same
two-leg positive envelope on the other arm cost \(O(M)\)
by corrected Henriot. Dividing by \(L\) proves the claimed
\(o(M)\) absolute deletion, uniformly on the stable set.

## 4. Explicit surviving seam and odd cases

For any fixed \(\eta_0>0\) and integer \(K\), restrict both
arms to actual squarefree ranks at most \(K\) and all prime
factors \(>N^{\eta_0}\). For a true subset-angle collar
\([1/2-h,1/2+h]\) with fixed \(0<h<.05\) on either arm,
the absolute contribution is
\[
                              \ll_{\eta_0,K,J} h M+o(M).         \tag{5}
\]
Here the bounded profiles and \(k\) can be used pointwise;
no constant needs to be uniform in \(K,\eta_0\).
To see (5), majorize that arm by \(L\) times the literal
compact fixed-rank angular collar source. Designate its
actual largest prime factor as the long prime input for
the [true product BV](../nearfull_high_vaughan/WholeMarkPrimeTransfer.md),
with the other genuine prime-product coefficient bounded
and the angular gates covered by a finite positive mesh.
Its unopposed \(L\)-weighted mass is \(O_{\eta_0,K,J}(hN)\):
the prime-product angular integrals have bounded density
on this compact region, and any nonempty proper subset
sum is a nonconstant linear form in the simplex coordinates.
Ordinary PNT in the genuine largest prime and reciprocal
harmonics in the other factors give this exact source
upper in the mesh limit. For the actual opponent use the
linear-sieve upper on its \(N^{\eta_0}\)-rough gate,
decreasing the tested exponent to a smaller fixed
positive number if necessary. It gives \(O_{\eta_0}
(\mathfrak S(Nx)/L)\) in the real reduced principal,
with true product BV for the actual short moduli.
Since the source is of fixed rank with macro factors,
\(\mathfrak S(Nx)=(1+o(1))\mathfrak S(N)\) there.
The other score is pointwise \(O_K(L)\).
This proves (5) for the actual fixed target and both
orientations. It is not a two-sided angular asymptotic.

In particular the absolute rank and tiny-factor tails
can be taken as small as desired for the **fixed**
profiles, followed by a finite angular problem with
(5) and the explicit ineligible-mark set \(P^-(n)\le U\).
The latter has the true bound \(O_{F,\chi,\psi,J}(\lambda M)\)
from the extracted-factor estimate in §3. This note
does not let the profile widths tend to zero after the
rank and tiny cutoffs; there is no uniform seam deletion.
The stable odd bulk includes two opposite signs:
on a stable squarefree triprime with no giant the
normalized leading score is \(1-3=-2\); on the open
stable rank-five cell with all angles close to \(1/5\)
it is \(1-5+10=6\). These are literal angular
configurations, not claimed simultaneous occupancy
opposite each other at every target. An estimate on
the signed odd bulk together with the actual remaining
seams is still required to get a binary lower.
