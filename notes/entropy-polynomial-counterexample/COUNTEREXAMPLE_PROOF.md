# A counterexample to the entropy polynomial root conjecture

8 October 2026

## Result and scope

Wakhare's entropy polynomial root conjecture, Conjecture 2 of *Iterated Entropy Derivatives and Binary Entropy Inequalities*, is false. The coprime parameter pair

\[
(k,r)=(11,10)
\]

gives at least four distinct roots in \((0,1)\). The proof below uses only rational and integer arithmetic and the intermediate value theorem.

This does **not** refute the associated binary-entropy inequality. Ho's 2026 proof of that inequality is a separate result. Nor does it resolve Frankl's union-closed sets conjecture.

## 1. The conjecture as stated

For integers \(k>r\ge1\), Wakhare defines

\[
h_{k,r}(x)=\sum_{j=0}^{k-1}x^{rj}
  \sum_{v=0}^{j}\frac{(-1)^{j-v}}{v+1}
       \binom{rv+k}{k}\binom{k}{j-v},
\]

and

\[
p_{k,r}(x)=\alpha_{k/r}k(1-x^r)^k h_{k,k}(x)
-r(1-x^k)^k h_{k,r}(x),
\]

where \(\alpha_s>0\) is determined by

\[
\alpha_s(1+\alpha_s)^{s-1}=1.
\]

Conjecture 2 asserts that \(p_{k,r}\) has exactly two roots in \((0,1)\), counting multiplicity. These are equations (1.3)–(1.4) in the [arXiv v2 text](https://arxiv.org/html/2312.14743v2) and the same definitions in the [published article, Journal of Approximation Theory 307 (2025), 106143](https://doi.org/10.1016/j.jat.2025.106143).

For \((k,r)=(11,10)\), write \(\alpha=\alpha_{11/10}\). Equivalently,

\[
\alpha^{10}(1+\alpha)=1.
\]

The function \(z\mapsto z^{10}(1+z)\) is strictly increasing for \(z>0\), so this determines a unique positive \(\alpha\).

## 2. Two short coefficient lists

Set

\[
\begin{aligned}
P(t)={}&1+352705t+60632419t^2+1227099358t^3\\
&+6330005947t^4+10701243741t^5+6330005947t^6\\
&+1227099358t^7+60632419t^8+352705t^9+t^{10},
\end{aligned}
\]

and

\[
\begin{aligned}
Q(t)={}&11+1939817t+289126442t^2+5380098482t^3\\
&+25959010187t^4+41238382790t^5+22851341183t^6\\
&+4098130058t^7+181139618t^8+831413t^9-t^{10}.
\end{aligned}
\]

Substitution in the defining binomial sum gives exactly

\[
h_{11,11}(x)=P(x^{11}),\qquad
h_{11,10}(x)=\frac1{11}Q(x^{10}).
\]

All coefficients of \(P\) are positive. For \(0<t<1\), the constant and final terms of \(Q\) already give \(11-t^{10}>0\), and its other coefficients are positive. Thus \(P,Q\) are positive at every argument used below.

Define

\[
R(x)=\frac{10(1-x^{11})^{11}Q(x^{10})}
{121(1-x^{10})^{11}P(x^{11})}.
\]

The denominator is positive for \(0<x<1\), and

\[
p_{11,10}(x)=11(1-x^{10})^{11}P(x^{11})\,[\alpha-R(x)].
\]

Consequently its sign is the sign of \(\alpha-R(x)\).

## 3. A rational interval for \(\alpha\)

The following two integer computations are exact:

\[
117^{10}\cdot242-125^{11}=-90074807210933370467<0,
\]

\[
937^{10}\cdot1937-1000^{11}
=10474898608767871728104442364513>0.
\]

Strict monotonicity therefore gives

\[
\frac{117}{125}<\alpha<\frac{937}{1000}.
\]

## 4. Five exact signs

Direct integer arithmetic gives the following strict inequalities. Their cleared-denominator certificates are printed in Section 6.

| \(x\) | Certified inequality | Sign of \(p_{11,10}(x)\) |
|---|---|---|
| \(1/5\) | \(R(x)<919/1000<117/125\) | \(+\) |
| \(2/5\) | \(R(x)>1131/1000>937/1000\) | \(-\) |
| \(3/5\) | \(R(x)<935/1000<117/125\) | \(+\) |
| \(2/3\) | \(R(x)>938/1000>937/1000\) | \(-\) |
| \(4/5\) | \(R(x)<928/1000<117/125\) | \(+\) |

Since \(p_{11,10}\) is a polynomial with real coefficients, it is continuous. The intermediate value theorem gives a root in each of the four disjoint intervals

\[
\left(\frac15,\frac25\right),\quad
\left(\frac25,\frac35\right),\quad
\left(\frac35,\frac23\right),\quad
\left(\frac23,\frac45\right).
\]

These are four distinct roots in \((0,1)\). Therefore the assertion of exactly two roots, even counting multiplicity, is false. The parameter pair is coprime, so imposing \(\gcd(k,r)=1\) would not rescue the conjecture. \(\square\)

No assertion that the number of roots is *exactly* four is needed or made.

## 5. Reproduction without floating-point arithmetic

The accompanying `verify_small_counterexample.py`:

1. Reconstructs both coefficient lists directly from the conjecture's binomial sums, using rational arithmetic.
2. Verifies the two integer signs isolating \(\alpha\).
3. Computes the five rational comparisons below using integers only.
4. Checks the alternating signs and the ordering of the five sample points.

The file `small_exact_certificate.json` records every numerator, denominator, and positive residual. Neither numerical root approximation nor numerical optimization is used in the proof. The earlier \((20,19)\) certificate is retained separately as an independently checked larger example.

## 6. Cleared-denominator integer certificate

Write \(P(t)=\sum_{j=0}^{10}p_jt^j\) and \(Q(t)=\sum_{j=0}^{10}q_jt^j\), with the coefficient lists in Section 2. Define their homogeneous evaluations

\[
\mathcal P(a,b)=\sum_{j=0}^{10}p_j a^{11j}b^{11(10-j)},\qquad
\mathcal Q(a,b)=\sum_{j=0}^{10}q_j a^{10j}b^{10(10-j)}.
\]

For integers \(0<a<b\), put

\[
N(a,b)=10(b^{11}-a^{11})^{11}\mathcal Q(a,b),
\]

\[
D(a,b)=121b(b^{10}-a^{10})^{11}\mathcal P(a,b).
\]

Then \(N,D>0\) and \(R(a/b)=N(a,b)/D(a,b)\). The five comparisons are precisely the positivity of these integers:


919D(1,5)-1000N(1,5) =

466874824750036867317284944431757160910291473920298358488270615396787783588172636108068732797424906336057540553684974786517014172859649275824805705028730880 > 0.

1000N(2,5)-1131D(2,5) =

42538194776507513458711885524826212893895489706184796164361512069476994269276907091882743610132255592931201086393400144305699712531157889439015076159529241505 > 0.

935D(3,5)-1000N(3,5) =

5251637910449814865586327498595497343364916127740768684705104599199185256340399027956110708767358049927938282779151210248609234143827247884850356820630516531200 > 0.

1000N(2,3)-938D(2,3) =

880081075869492581391345270291752622515553720814680080811186606457767956959351946751016842608896901672363281250 > 0.

928D(4,5)-1000N(4,5) =

1213682038859153402457303598743302574162634821418226521799031957011114963599358661651488660016203235762863004128345364061271715446024425596394854034905941742192560 > 0.

## References and provenance

- Tanay Wakhare, *Iterated Entropy Derivatives and Binary Entropy Inequalities*, Journal of Approximation Theory **307** (2025), 106143; [DOI](https://doi.org/10.1016/j.jat.2025.106143), [arXiv:2312.14743v2](https://arxiv.org/abs/2312.14743v2). The target is Conjecture 2, not Conjecture 1.
- Boon Suan Ho, *A generalization of Boppana's entropy inequality*, [arXiv:2601.19327](https://arxiv.org/abs/2601.19327), January 2026. Its Theorem 1 proves the associated entropy inequality for all real exponents greater than one; this counterexample does not conflict with that result.

The parameter search was exploratory. The final refutation is the finite exact certificate above. No prior published counterexample was identified in the source search, but that negative search is not a claim of exhaustive novelty verification.
