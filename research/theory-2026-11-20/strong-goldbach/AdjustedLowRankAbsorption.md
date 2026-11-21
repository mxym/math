# A same-row centered shift absorbs all reflected ranks through seven

Use the original \(C(m),W_s(q),U,V,Q_0,H\) and whole adjusted quotient coefficient \(D_B(q)\) from [AdjustedTriprimePositiveBudget.md](AdjustedTriprimePositiveBudget.md). In particular \(N=2x,\ L=\log x,\ x^{.10}<s<x^{.14}\) with \(s\) prime, \(n=sq\in(x/2,x]\), \(m=N-n\), \((n,N)=1\), and \(H=\exp(L^\sigma)\) with fixed \(0<\sigma<1\). We keep the two **actual** quotient families:
* \(\mathcal Q_1\) consists of the one-small-prime triples \(q=a_q P Q\), \(x^{.010}<a_q<x^{.070}\), \(P,Q<x^{.501}\), \(a_qP>x^{.501}\), with distinct primes and unique marked \(P\) on the physical support.
* \(\mathcal Q_2\) consists of the unordered genuine distinct prime triples \(q=P Q R\) with all three factors below \(x^{.358}\).

On their physical supports \(D_B(q)/\log q\) is exactly \(j=1,2\), respectively, not an average. One may use either profile separately; an additional fixed gate on the marked \(P\) in \(\mathcal Q_1\) is also allowed. In all cases the admissible \(q\) test, before the central \(sq\) product cut, is an independent \(1\)-bounded sequence on the integer \(q\).

Let \(\epsilon_0=1/200\). For fixed \(0<\epsilon<\epsilon_0\), \(0<\rho<1/2\), put \(Z=x^\epsilon\) and define the bounded-variation, flat-then-power function
\[
 f_\rho(u)=
 \begin{cases}
 1,&0\le u\le\rho,\\
 ((1-u)/(1-\rho))^6,&\rho<u<1,\\
 0,&u\ge1.
 \end{cases}
\]
The exact reflected shift is
\[
 \begin{split}
 S_U(m)&=\sum_{\substack{d\mid m\\d\le U}}\mu(d),\qquad
 G(m)=\sum_{d\mid m}\mu(d)\, f_\rho(\log d/\log Z),\\
 E(m)&=C(m)+\frac{\log m}{2}\{S_U(m)-G(m)\}.
 \end{split}
\tag{1}
\]
For each of the two genuine profiles, the full signed sums with \(C\) and with \(E\) differ by \(O_A(xL^{-A})\) for every fixed \(A\). This shift is identically zero at a **prime** \(m\). Given any \(\xi>0\), one can choose fixed \(\epsilon,\rho>0\), in that order, such that for all sufficiently large even \(N\),
\[
 \boxed{\quad
 \sum_{\substack{(s,q)\text{ in the original physical row}\\
            q\in\mathcal Q_j,\ \Omega(m)\le7}}
       W_s(q)\frac{D_B(q)}{\log q}\,(E(m))_+
       \ \le\ \xi M_N ,\qquad j=1,2.
       \quad}
\tag{2}
\]
Here \(\Omega\) **counts prime factors with multiplicity**, so (2) includes squareful \(m\) in these ranks. It is a uniform fixed-target statement. It does not retain a previous negative reserve for \(C\) without re-evaluation on the new \(E\), extend to \(\Omega(m)\ge8\), or estimate the complementary quotient profiles. In particular this is a reduction of two selected signed components, not the full \(.010M_N\) upper or a Goldbach proof.

## 1. The exact whole null on each actual quotient family

The discrepancy for the first short term of (1), and for the \(G\)-term, is controlled by [Maynard's generalized BV, Lemma 8.9](https://ora.ox.ac.uk/objects/uuid%3A39a52f47-3770-4ddd-b7a2-b2a4f7300931/files/srj4305733) on the independent product of the actual \(s\)-prime factor and the \(1\)-bounded \(q\)-mask of \(\mathcal Q_j\). Use it as in [FullScaleConvolutionBV.md](FullScaleConvolutionBV.md), §1. Both factors have polynomial length in dyadic boxes, and \(s\) supplies SW with the auxiliary coprimality condition. The exact factor \((n,N)=1\) is imposed separately on the two source factors; it removes only \(O(L)\) prime values from \(s\) and so preserves SW on that factor. The coefficient on \(q\) is not asserted SW. The true modulus is \(d\le U=\sqrt x/H^4\) or \(d\le Z\). The subpower gap \(H^4\) accommodates the log-level reserve for any desired error. The residue is \(N\bmod d\); if \((d,N)>1\) there is no physical term.

As in the cited full-scale BV note, use relative log-fine Cartesian meshes for \(sq\in(x/2,x]\); the test \(W_s(q)\log(2x-sq)\) separates to arbitrary log precision, or use \(W_s(q)=1-5t+8t^2-4t^3,\ t=\log s/\log(sq)\), and ordinary partial summation. Boundary strips have \(O(xL^{-J})\) physical product integers with the usual divisor-moment bound; increasing the mesh parameter \(J\) and the theorem log reserve pays their weighted cost. The centered errors therefore cost \(O_A(xL^{-A})\). This treatment does not call a prime test on a factor of \(q\) that depends on an independent \(s\)-test within the accepted box.

In the reduced principal fix the actual source row \(n=sq\). The exact mask is \((d,Nn)=1\). The constant harmonic moments
\[
        \sum_{\substack{d\le Y\\(d,Nn)=1}}\frac{\mu(d)}{\varphi(d)}
                  =O_A(L^{-A})
         \qquad (Y\ge x^c,\ c>0\text{ fixed})
\tag{3}
\]
are uniform here by the finite coprime \(\mu/\varphi\) lemma used in the cited notes (e.g. Huang–Li, [Lemma 1](https://arxiv.org/abs/2005.03811)). For \(G\), the portion \(d\le Z^\rho\) is an entire constant moment; on \(Z^\rho<d\le Z\), partial summation with the bounded variation of \(f_\rho(\log d/\log Z)\) uses only polynomially long endpoints in (3). The shift therefore has zero principal to arbitrary log precision. At a true prime \(m\) near \(x\) both \(S_U\) and \(G\) equal \(1\); \(C(m)=E(m)=0\) exactly. All these null operations are performed on the whole \(m\)-support under each selected \(q\)-mask, not after imposing a rank cutoff.

## 2. A uniform actual upper sieve for bounded-rank reflected \(m\)

All prime factors of actual \(q\in\mathcal Q_j\) exceed \(x^{.010}\). For an upper bound we may instead only sieve \(q\) at \(z_q=x^{.002}\), dropping the special \(q\)-factorization and retaining the true central relation \(m+sq=N\). In \(\Omega(m)\le7\), fix \(F\), the full product (with powers) of those prime factors of \(m\) at most \(x^{\epsilon_0}\). Then \(F\le x^{.035}\), and the remaining \(t=m/F\) has a nonempty product of at most seven primes \(>x^{\epsilon_0}\). For all such \(F\) and any fixed number of these large labels there is the uniform upper
\[
 \#\{(s,t):\ Ft+s q=N,\ Ft\in[x,3x/2),\
                   t\text{ such a prime product},\
                   q\text{ is }z_q\text{-rough on unit support}\}
 \ \ll\ \frac{\mathfrak S(N)x}{F L^2}
       +O_A\!\left(\frac{x}{F L^{A}}\right).
\tag{4}
\]
The labels in (4) can be counted with ordered multiplicity, which only enlarges the bound.

To verify (4), omit \(F\) with \((F,N)>1\), since those physical rows are empty. Take upper linear-sieve weights \(\lambda_d^+\) with \(D=x^{.004}\), using the primes below \(z_q\) that do not divide \(FN\). This is the ordinary dimension-one sieve at ratio \(\log D/\log z_q=2\). The actual sieve condition \(d\mid q\), including integrality, is exactly
\[
                             t\equiv N\overline F\pmod {s d}.
\]
Indeed \(s>x^{.10}>P^+(F d)\), \(s\nmid N\) on the retained support, and \((d,FN)=1\). Both the residue and the multiplier \(F\) are therefore reduced. The modulus \(s d\le x^{.144}\) has a unique designated \(s\) when nonzero here because \(d\le x^{.004}<s\). The ordinary generalized BV on the actual product \(t\) at scale \(x/F\ge x^{.965}\) has fixed power slack to \(x^{.144}\), including arbitrary reduced residues. If there is only one large prime label use ordinary prime BV. If there are two or more, choose one genuine prime slot for SW, and group the rest into its independent divisor-bounded product; both slots have polynomial lengths after the ordinary dyad and relative mesh localization of the true central \(t\)-interval. The sum of errors times \(|\lambda_d^+|\le1\) is \(O_A((x/F)L^{-A})\) uniformly in \(F\). This does not require a SW theorem for a coefficient on the exact rough quotient \(q\).

In the principal term \((t,d)=1\) is automatic because every \(t\)-prime is \(>x^{\epsilon_0}\). Only \((t,s)=1\) is retained for the source. Thus for each true \(s\), the nonnegative upper sieve factor is
\[
         \sum_d \frac{\lambda_d^+}{\varphi(d)}
             \ll \prod_{\substack{p<z_q\\p\nmid FN}}
                                \left(1-\frac1{p-1}\right)
             \ll \mathfrak S(N)/L.
\]
The first inequality uses the uniform dimension-one local product, since removing primes dividing \(FN\) only improves its interval upper bound; \(2\mid N\) removes the exceptional prime \(2\). The second is the ordinary Mertens comparison with the Goldbach singular series: the at most seven extra prime divisors of \(F\) contribute a uniformly bounded factor (each odd Euler multiplier is at most \(2\)). One may now bound the source at each \(s\) by all of its \(t\)-products, and \(\sum_s1/\varphi(s)\ll1\) on the fixed polynomial band. The count of these \(t\)-products is \(O(x/(F L))\): condition on all but the largest true prime, use ordinary PNT upper in its admissible interval at scale at least \(x^{\epsilon_0}\), and sum the other polynomial prime reciprocal ranges, each of \(O(1)\) harmonic mass. This proves (4).

Consequently for any nonnegative multiplicative-label weight \(V(F)\) with \(V(F)\) bounded by a fixed log power, the sum weighted by \(V(F)\) in (4) admits the right side summed with \(V(F)/F\). We will only need such weights. In particular \(\sum_F1/F\ll(1+\log L)^6\) over the small product types that occur, allowing multiplicities (there are at most six small slots because the large product is nonempty).

## 3. Exact midpoint algebra and cutoff errors of negligible total

Start by removing \(m\) with any prime square \(p^2\mid m,\ p>x^{\epsilon_0}\) from (2). Their number is \(O(x^{1-\epsilon_0})\) by summing the bound \(O(x/p^2)\) on multiples; the number of eligible \(s\) at each \(m\) is bounded, since \(s\) divides \(N-m\) and \(s>x^{.10}\). On \(\Omega(m)\le7\) the weighted cost is \(O(L)\) per row and hence \(o(M_N)\). On the remaining support write \(R=\operatorname{rad}(m)\), \(T=\log(m/R)\). Every repeated prime is a factor of \(F\), so \(T\) depends only on \(F\). The harmonic sum \(\sum_F T/F\ll(1+\log L)^5\), since each repeated prime-power slot may be summed using \(\sum_p\log p/p^2<\infty\) and the other slots use ordinary prime reciprocals.

Let
\[
 C_U'(m)=\sum_{\substack{d\mid m\\d>U}}\mu(d)\log(m/d).
\]
By \(\sum_{\ell\mid a}\Lambda(\ell)=\log a\), the only terms switched off in the literal \(C(m)\) relative to \(C_U'\) have \(\ell\le\max(V,Q_0/U)=H^2\). On \(\Omega(m)\le7\), there are boundedly many such pairs and each has size \(O(\log H)\), so
\[
                              C(m)=C_U'(m)+O(\log H).
\tag{5}
\]
Whether \(m\) is squarefree is not needed for (5). Define for the squarefree \(R\)
\[
 C_*(R)=\sum_{\substack{d\mid R\\ d>\sqrt R}}\mu(d)\log(R/d),
 \qquad S_*(R)=\sum_{\substack{d\mid R\\d<\sqrt R}}\mu(d).
\]
The radical \(R>1\) and there is no exact divisor at \(\sqrt R\). Moreover \(G(m)=G(R)\) because only squarefree divisors have nonzero \(\mu\). Since \(\sum_{d\mid R}\mu(d)=0\),
\[
 C_U'(m)+\tfrac12\log m\,S_U(m)
         =\sum_{\substack{d\mid R\\d>U}}\mu(d)(\tfrac12\log m-\log d).
\]
Compare this to the identical expression with \(\sqrt R,\log R\). A cutoff crossing has \(|\log d-\frac12\log m|\ll\log H+T+1\); all other differences cost \(O(T)\) per term. With (5) this proves the pointwise relation
\[
 E(m)= C_*(R)+\tfrac12\log R\bigl(S_*(R)-G(R)\bigr)
                         +O(\log H+1+T).
\tag{6}
\]
Its whole weighted error on these ranks is \(o(M_N)\) by (4), since \((1+\log H)(1+\log L)^6/L=o(1)\) and the \(T\)-moment is as just stated. There is no pointwise prime-pair estimate in this argument: the second \(1/L\) for the error is the genuine \(q\)-rough upper sieve in (4).

The sign at the exact midpoint in (6) is as follows. For \(R\) composite and squarefree, \(\sum_{d\mid R}\mu(d)\log d=0\), and complementing \(d\mapsto R/d\) gives:
* If \(\mu(R)=-1\), \(C_*(R)=-\tfrac12\log R\, S_*(R)\), so the first two terms of (6) become precisely \(-\tfrac12\log R\, G(R)\).
* If \(\mu(R)=+1\), \(S_*(R)=0\), and those terms are \(C_*(R)-\tfrac12\log R\,G(R)\).

The case \(R\) prime need not be evaluated by the composite moment. If \(m\) is not prime itself and \(R\) is prime, then \(m\asymp x\) and \(\Omega(m)\le7\) force a repeated base \(>x^{\epsilon_0}\), already removed. Actual prime \(m\) has \(E(m)=0\) as in §1.

## 4. Even rank two, four and six, and all flat-taper leakage

For an even squarefree radical of rank \(r\), set \(t_i=\log p_i/\log R\), \(\sum_i t_i=1\). The continuous normalized extension of its exact counterpart is
\[
 {\cal C}_r(t)=\frac12\sum_{I\subseteq[1,r]}(-1)^{|I|}
                         \min\!\left(\sum_{i\in I}t_i,\ 1-\sum_{i\in I}t_i\right).
\tag{7}
\]
This just pairs complementary divisors, which have the same sign when \(r\) is even. Actual squarefree \(R\) has no midpoint ties; extension to the closed simplex is only for bounding. If one exponent is set to \(0\) and its mass transferred to another, (7) vanishes at the new point by cancellation of that bit, and each summand changes by at most the transferred mass. Hence
\[
                     |C_*(R)|\le 2^{r-1}\log p_{\min}.
\tag{8}
\]
Also \({\cal C}_2\le0,\ {\cal C}_4\le1/2,\ {\cal C}_6\le1/4\). For rank two use the direct negative shorter log. For rank four with all exponents \(<1/2\), the triple-divisor terms sum to \(-1\) and the three complementary pair partitions contribute at most \(3/2\). For rank four or six with an exponent \(>1/2\), all major divisors include that bit and the full signed log moment on the remaining composite is zero; extend by continuity at equality.

Here is the finite elementary certificate for rank six when all \(t_i\le1/2\):
\[
 {\cal C}_6=-1+\!\sum_{i<j}\min(t_i+t_j,1-t_i-t_j)
     -\!\sum_{\text{10 unordered triple partitions}}
                   \min(t_I,1-t_I).
\tag{9}
\]
The quintuple terms give \(-1\). A pair and its complementary quadruple have the same positive sign, and a triple and its complementary triple have the same negative sign, giving (9). Order \(0\le t_1\le\cdots\le t_6\). Two disjoint pairs cannot both have weight \(>1/2\), by summing their four exponents. If there is a long pair not containing \(6\), then \(45\) is long and the long-pair graph is exactly the triangle on \(4,5,6\), since any other edge would be disjoint from a triangle edge. Otherwise it is empty or a star at \(6\) whose neighbors are \(j,j+1,\ldots,5\) for some \(j\). On each of these closed polytopes (ordering, sum, cap, and the indicated linear pair constraints), the pair sum in (9) is linear and minus the triple minima is convex. Its maximum is therefore at a vertex. The [rational certificate](check_even_rank_six_center.py) gives the complete checked maxima in order: \(1/4\) for the empty and all five star cases, \(0\) for the triangle. It enumerates rank-five independent active inequalities with the total-sum equation; every vertex occurs that way, even when extra inequalities are active. No primality or numerical approximation is assumed in this bound.

When no prime of \(R\) is \(\le Z\), \(G(R)=1\) and every odd or even case in (6) is nonpositive for these ranks. In the other cases, the even positive \(C_*\) can be bounded by (8), paying
\[
 \ll \frac{\mathfrak S(N)x}{L^2}
   \sum_{\substack{F\text{ small types}\\p_{\min}(F)\le Z}}
                 \frac{\log p_{\min}(F)}F
 \ \ll M_N\,\epsilon\,\bigl(1+\log(\epsilon_0/\epsilon)\bigr)^6.
\tag{10}
\]
To see the harmonic bound, use \(\log p_{\min}1_{p_{\min}\le Z}\le
\int_0^{\epsilon L}1_{\log p_{\min}>v}\,dv\); allowing repeats with reciprocal factors only enlarges the factor sums. For \(k\le6\) small slots,
\(\sum_{e^v<p\le x^{\epsilon_0}}1/p\ll1+\log(\epsilon_0 L/v)\), interpreting \(v=0\) by integration. This follows from the ordinary uniform harmonic upper, also for \(v<\log 2\) by its trivial \(\log\log x\) bound. Integrate the \(k\)-th power. The double logarithm term from squaring an upper bound is not being absorbed into an unspecified \(\epsilon\)-dependent sieve constant; the constants in (4) stayed at the fixed cutoff \(\epsilon_0\).

It remains to pay the defect \(G_-(R)=\max(0,-G(R))\), for either parity. If \(p_1,\dots,p_k\) are the distinct prime factors of \(R\) at most \(Z\), \(k\le6\), set \(u_i=\log p_i/\log Z\) and note
\[
         G(R)=\sum_{I\subseteq[1,k]}(-1)^{|I|}
                                  f_\rho\!\left(\sum_{i\in I}u_i\right).
\]
For the unflattened \(f_0(u)=(1-u)_+^6\), the finite difference is nonnegative through order six: successive integration writes it as the box integral of \((-1)^k f_0^{(k)}\ge0\) almost everywhere. For the flattened taper, \(\|f_\rho-f_0\|_\infty\ll\rho\) and its Lipschitz bound is absolute uniformly in \(0<\rho<1/2\). Comparing to \(f_0\) and pairing by the smallest-prime bit respectively gives
\[
                   G_-(R)\ll \min(\rho,\min_{i\le k}u_i)
                         \qquad(k\ge1),
\tag{11}
\]
and the defect is zero for \(k=0\). Each \(F\)-factor between \(Z\) and \(x^{\epsilon_0}\) has harmonic cost \(O(1+\log(\epsilon_0/\epsilon))\). For the \(k\) defect factors, use
\(\int_0^\rho(\sum_{Z^v<p\le Z}1/p)^k\,dv\ll
\rho(1+|\log\rho|)^k\), by the same harmonic upper. Repeated fixed powers only reduce the harmonic mass, up to a fixed multiplicity depending on rank. Apply (4) weighted by \((\log x)G_-\), and obtain the uniform bound
\[
 \ll M_N\,\rho(1+|\log\rho|)^6
                   (1+\log(\epsilon_0/\epsilon))^6
\tag{12}
\]
for the positive defect. Errors from (4) after summing the harmonic label weights have arbitrary log reserve. Choose \(\epsilon\) small first in (10), then \(\rho\) small in (12), then \(x\) large for the \(o(M_N)\) errors of §3. The factors \(W_s(q)\) and \(D_B(q)/\log q\) are bounded with the actual signs in both families. This proves (2).

**Uncontrolled support.** The same algebra at an odd squarefree midpoint removes \(C_*\) identically, but (11) with this exponent of taper is limited to at most six small labels, and the bounded-rank upper sieve accounting in this proof has fixed rank. Starting at even rank eight, (7) can already exceed \(1/2\): at eight equal exponents, its continuous value is \(5/2\), hence on nearby strict profiles with all factors \(>Z\) the new midpoint term is still positive. Thus neither the high-rank positive budget, the full signed upper, nor binary Goldbach follows from this absorption.

## Related reductions

The parallel [coupled fixed-rank detector](all_fixed_ranks/Proof.md) uses the quadratic weight on the squarefree joint product and different zero-mean tags. This note instead uses the literal adjusted quotient profiles, the original reflected Vaughan coefficient, and multiplicity rank on its reflected argument. Compare also [Arneth’s October cubic minorant](https://zenodo.org/records/23477014) and [Pham’s October reflected-prime programme](https://www.preprints.org/manuscript/202610.3061), neither of which supplies the unestimated full signed remainder here. No priority claim is made.
