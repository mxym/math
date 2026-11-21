# Paying the actual rough-reflected triprime-quotient debit from its own mean

This is a fixed-target upper on an explicit broad portion of the **actual** added positive debit in [HigherQuotientReflectedSourceSwitch](HigherQuotientReflectedSourceSwitch.md), including every reflected rough rank on that portion. Its cost is bounded by \(0.866\) of that very correction's negative mean. On the narrower actual coupled source of [CoupledQRShortPart](CoupledQRShortPart.md), its pre-existing positive part on the same reflected sector can also be paid, with total charge \(<0.927\) of the single mean. This does not control other quotient shapes or the smaller-reflected-factor complement. No Goldbach bound is claimed.

## The actual ledger and charge

Keep \(N=2x\), \(L=\log x\), \(M_N=\mathfrak S(N)x/(2L)\), \(n=sq=N-m\in(x/2,x]\), the original \(C(m)\), \(W_s(q)\), and the high quotient chart \(v=saQ\) of the first cited note:
\[
 \log_x s\in(.138,.139),\quad \log_x a\in(.068,.069),\quad
 \log_x Q\in(.297,.298),\qquad b=n/v.
\]
All displayed labels here except \(b\) are true primes. The exact centered adjustment subtracts \(\frac13 W_s(q){\cal R}(b)1_{\omega_E(m)=1}C(m)\) on this whole chart and adds back its signed mean. Here \(E=(x^{.311},x^{.321})\), and the old Selberg square \({\cal R}\) has divisor cutoff \(x^{.025}\). The mean is \(-(\rho+o(1))M_N\), where, writing \(h_I=\log(\sup I/\inf I)\) for an exponent interval \(I\),
\[
\begin{split}
 h_E&=\log(.321/.311),\quad h_a=\log(.069/.068),\quad h_Q=\log(.298/.297),\\
 J_s&=\int_{.138}^{.139}(1-t)(1-2t)^2\,dt/t,\qquad
 \rho=\frac{40}{3}J_s h_a h_Q\,h_E^2(1-h_E)>0 .
\end{split}                                                               \tag{1}
\]
In particular this is only one credit in the original signed identity, not a credit assigned separately to every chamber.

Consider the actual \(b\) that are squarefree products of three true primes, with at least one prime \(b_2\) in \(B_2=(.164,.16524)\) and at least one prime \(b_3\) in \(B_3=(.16525,.167)\), the intervals again denoting log exponents. No assertion is made about all triprime \(b\), much less all composite \(b\). The third actual factor \(r=b/(b_2b_3)\) is \(\asymp x^{\vartheta}\) for some \(.161<\vartheta<.168\) for all large \(x\), by the physical product constraints and these bands (a fixed-relative factor is immaterial). In particular all three exceed \(x^{.025}\), so \({\cal R}(b)=1\) on the literal rows. Multiple choices of marked pair are allowed only in the nonnegative upper below, not in the definition of the original adjustment.

Let \(D_N^{\rm rough}\) be the **added positive weight** on these actual rows with \(P^-(m)>x^{.138}\) and exactly one \(E\)-mark:
\[
 D_N^{\rm rough}=\frac13\sum_{\rm stated\ actual\ rows}
                    W_s(q)(-C(m))_+ .
\]
As throughout, \((n,N)=(m,N)=1\). The claim is
\[
 D_N^{\rm rough}\le (.866\,\rho+o(1))M_N.                                  \tag{2}
\]
On the narrower six-prime source \(\mathcal B\) of the second cited note, in the ledger \(B'=D_B(q)/\log q+2F_2(s,q)/3\) (without \(F_1\)), the **pre-existing** positive part \(W_s(q)(B'C(m))_+\) on this same reflected rough sector costs at most \((.061\,\rho+o(1))M_N\). Thus adding both algebraic charges uses strictly less than \(.927\) of (1); the known mean cannot be used again at full strength.

## All rough ranks of the reflected side

Discard squareful \(m\) among these rough rows at power-small cost, since a squared prime is \(>x^{.138}\) and the divisor-opening bound is \(O(x^{.862}+\sqrt{x})\); weights and possible physical prime-label multiplicities are \(x^{o(1)}\). For \(m=p u\), \(p\in E\), the integer \(u\) has at most four true prime factors because \(5(.138)>.689\). There is no prime \(m\) on this marked physical range. For all these squarefree \(m\),
\[
 C(m)=-\sum_{d\mid m,\,d\le U}\mu(d)\log(m/d),\qquad U=\sqrt x/H^4 .
\]
Indeed in the original reassembly the \(T_2,T_3\) terms require a prime factor of size at most \(H^2\), which is absent, and \(\Lambda(m)=0\).

* Rank 2: \(m=p P\) with genuine prime \(P\); only the unit and \(p\) are short. Here \(C(m)=-\log p\).
* Rank 3: if all singles are short, no pair can be short since \(m>U^2\), and \(C(m)=\log m\). If one single \(P\) is long, both others are short (two long factors together with \(p\in E\) cannot fit the size of \(m\)). Only the pair complementary to \(P\) can also be short. It gives \(C=0\) if short and \(+\log P\) otherwise. Hence no added positive weight.
* Rank 4: all singles are short on this rough sector (each non-marker is \(<1.5x^{.689-2(.138)}\)). There are no short triples. Put \(a_1\le a_2\le a_3\le a_4\) for the four actual prime logs, of sum \(\log m\). An upper bound on the short weighted pair sum uses, in each of the three complementary pair choices, the smaller log pair; both complementary divisors cannot be short. The sum of the three smaller logs is \(a_1+a_2+a_1+a_3+\min(a_1+a_4,a_2+a_3)\), at least \(\log m\) since \(a_4<\frac12\log m\). Thus their total \(\log(m/d)\) is at most \(2\log m\), canceling the negative unit/singleton sum. Therefore \(C\ge0\) with the exact cutoff \(U\), even if it excludes some of the shorter pairs.
* Rank 5: all singles are short, no four-prime product is short, and the short triples only decrease the sum being negated. Summing all ten possible pairs, not just the short ones, bounds \((-C)_+\le -3\log m+(10-4)\log m=3\log m\). Every non-marker prime is \(<x^{.276}\) for sufficiently large \(x\), since each exceeds \(x^{.138}\), and \(.689-3(.138)=.275\).

Here the deformation by \(H\) is harmless by *exact* inclusion and sign, not an assumption that every nearest half divisor stays on the same side. Thus the added debit is bounded by the nonnegative tests \((\log p)/3\) on the true reflected semiprimes, and \(\log m\) on the true reflected five-prime products, with no other surviving rough ranks.

## Actual coupled upper by opening the opposite source

For the upper, retain the actual primes \(s,a,b_2,b_3\) and drop the actual requirements \(Q,r\) on
\[
                        F=n/(sa b_2b_3).
\]
Dropping those requirements is only a **nonnegative inclusion**, not a source asymptotic on the genuinely restricted rows. For a literal triprime \(b\) in the asserted bands, \(F=Qr\) is a true product of two polynomial primes, both exceeding \(R'=x^\delta\), \(\delta=.017\). Insert the new optimal nonnegative Selberg square \({\cal R}'(F)\) with divisor cutoff \(R'\) and the density \(g(\ell)=1/(\ell-1)\) at primes \(\ell\nmid N\), exactly as in §3 of the first cited note. It is identically one on the actual \(F=Qr\). If multiple choices of \(b_2,b_3\) exist, sum them in this upper only. For each fixed permissible pair every tuple on the original chart maps to at least one of these upper-source tuples, because the old actual \(Q\) (size near \(x^{.2975}\)) is unique among the original three \(b\) primes (all near \(x^{.165}\)).

The source \(m\) is now **literally** \(p\times P\) for rank 2, or \(p\times(p_1p_2p_3p_4)\) for rank 5 with each \(p_i\in(x^{.138},x^{.276})\), distinct and taken unordered. The first factor \(p\) is a genuine independent SW prime in \(E\). The long coefficient is otherwise valid arbitrary bounded prime-product support, with the physical product interval imposed by fine rectangles; \(\log p/L\) is an allowed SW multiplier by prime prefix partial summation. The factor \(\log m/L\) in rank 5 and \(W_s((N-m)/s)\) are smooth and separated by the same fine rectangles (the actual \(s\) in the weight is retained). All these source primes are distinct, and the exact source coprime mask \((m,N)=1\) separates as usual. Expand \({\cal R}'\) as a sum over \(d\mid F\), \(d<x^{.034}\), with the log- and divisor-bounded coefficients of the optimal square. The independent modulus slots for [Lichtman Proposition 5.2](https://arxiv.org/html/2309.08522#S5) with actual residue \(N\) are
\[
 q_1=s b_2,\qquad q_2=b_3 d,\qquad q_3=a .
\]
The factors of \(q_1\) have two disjoint bands; \(b_3\) is the unique prime factor of \(q_2\) in its band, because \(d<x^{.034}\). Thus these coefficients act independently. The worst upper exponents for the four rails, with \(\theta=7/32\), are respectively
\[
 -.00676,\qquad .981,\qquad 1.98699,\qquad 1.866568125 .
\]
For example \(q_1\le x^{.30424}\), \(q_2\in[x^{.16525},x^{.201}]\), \(q_3\le x^{.069}\), and first-source scale \(x^{[.311,.321]}\), so the first exponent is \(.30424-.311\), while the fourth uses \(2\theta(.321+.069-.16525)\). All inequalities have fixed slack. The product-scale source/stated SW definitions, factor-mesh separations and divisor clipping are as in [HigherQuotientReflectedSourceSwitch](HigherQuotientReflectedSourceSwitch.md): coefficients on the long slot and \(q_2\) are clipped/rescaled at a high log power, with arbitrary log reserve from the physical divisor moments and the harmonic divisor moments of the principal terms. One needs no unrelated \(\Lambda(m)\) estimate at \(x^{.57}\). Every modulus with a nonunit factor of \(N\) is excluded by the actual unit condition, and the target residue is \(N=2x\).

For rank 2 the source factors cannot divide its modulus because of lengths. For rank 5 the bound on the principal may drop the mask \((m,q_1 q_2 q_3)=1\), but **only before evaluating the signed Selberg coefficient by pulling out a common main**: each polynomial modulus prime \(s,a,b_2,b_3\) can be excluded directly from the source via a uniform power-small error in its unprogressioned prime-product main, by \(O(x/p_{\rm modulus})\) integers before divisor powers. There are only four such primes. The \(d\) primes are \(<x^{.034}\), hence never divide a source factor. The same deletion applies to the source factor exclusions at primes dividing \(N\) (at most \(O(L)\), and only polynomial ones matter). The sums of the absolute modulus coefficients divided by \(\phi(q_1q_2q_3)\) are log-bounded, so these errors are negligible. This makes the main factor independent of \(d\); no termwise signed inequality in its coefficients is used. Also \(d\) is coprime to each label \(s,a,b_2,b_3\) by sizes and the four labels are in disjoint bands. The exact Selberg quadratic sum is \(1/G_{R'}\sim\mathfrak S(N)/(\delta L)\), uniformly in target by the Euler product calculation of the first cited note. Orientation of the inequality was decided on the physical square, which is nonnegative.

For rank 2, fixing actual \(p\) and using prime PNT for \(P\) on fixed-relative product intervals with weight \(\log p\) gives the density
\[
 I_2=\int_{.311}^{.321}\frac{dt}{1-t}=\log(.689/.679)
\]
in the physical \(m\) variable, up to \(o(1)\) uniformly on fine relative intervals or via prefix partial summation. For rank 5 with weight \(\log m\), fix any three of the \(p_i\) along with \(p\) and use PNT for the remaining true prime at scale \(x^\xi\), \(\xi\ge.138\). The density bound is
\[
 B_5=\frac{h_E\,\log(.276/.138)^3}{24(.138)}
       =\frac{h_E\,\log(2)^3}{24(.138)} .
\]
In detail, count all ordered distinct \(p_i\) and divide by \(4!\). The first three free labels contribute the three bounded harmonic prime sums and the fourth logarithmic denominator is at least \((.138)L\). The factor \(\log m=(1+o(1))L\) cancels it. Positive upper prefix or fine rectangles give the same bound against \(W_s\ge0\), since its variation is uniform and the physical interval is central. These inequalities are for the principal after the residue transfer, not upper sieve estimates pretending that any actual source cofactor is prime.

Lastly sum \(s,a,b_2,b_3\) with their reciprocal totient weights and the physical \(W_s\). The \(s\)-sum tends to \(J_s\) because \(W_s((N-m)/s)=W(\log_x s)+O(1/L)\) uniformly for central \(m\), and the other three labels give \(h_a h_{B_2}h_{B_3}\) by PNT. The physical \(m\)-length is \(x/2\). Thus exactly on the normalization of (1),
\[
 D_N^{\rm rough}\le
 \left[\frac{J_s h_a h_{B_2}h_{B_3}}{\delta}
               \left(\frac{I_2}{3}+B_5\right)+o(1)\right]M_N.              \tag{3}
\]

## Exact budget and scope

Dividing the coefficient in (3) by the one negative mean \(\rho\) gives
\[
 \frac{h_{B_2}h_{B_3}(I_2+3B_5)}
      {40\delta\,h_Q h_E^2(1-h_E)}<.866 .
\]
For the pre-existing part on \(\mathcal B\), on its whole exact source profile the original no-\(F_1\) value is
\[
 B'=-\frac23-\frac{3\log a+2\log b}{\log q},\qquad |B'|<2.1.
\]
This is the same exact short-list evaluation in the first cited note, strict on all the narrower six-prime bands. The size bound also follows immediately from \(a<x^{.0686}\), \(b\le x/(s a Q)<x^{.4958}\), and \(q>.5x^{.8614}\). To pay its actual old positive part, use (3) with its two narrower \(b\) bands \(B_2^\flat=(.16512,.16524)\) and \(B_3^\flat=(.16525,.16545)\), and multiply that coefficient by \(3(2.1)\). Keeping the broader \(J_s,h_a\) on this upper only makes the charge larger. The resulting ratio to \(\rho\) is \(<.061\). These two caps count different algebraic weights: the broad bound is just the **added increment**, and the narrow one just the **prior positive part**. They use a single known mean, with a remaining fraction \(>.073\) before any other debit. The companion rational checker certifies both inequalities including the logarithms.

This accounts for a real, whole rough-reflected sign sector at each fixed \(N\), including the earlier reflected semiprime witness and the near-equal reflected five-prime adverse witness when they occur on these actual triprime quotient rows. It does not give a lower count on those genuine rows. It leaves all \(m\) with a factor \(\le x^{.138}\) (as well as the other quotient shapes, or pre-existing positives outside the narrow sector) unbounded here. Neither the earlier exact-one C correction nor the stronger q-mixture is being claimed uniformly good on the full ledger.
