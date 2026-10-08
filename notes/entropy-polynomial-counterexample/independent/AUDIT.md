# Independent exact audit: Wakhare's two-root conjecture

Audit date: 2026-10-08 UTC.

## Verdict

**The stated Conjecture 2 is false.** The admissible coprime pair `(k,r)=(11,10)` gives a polynomial with at least four distinct roots in `(0,1)`. The independently checked pair `(20,19)` gives a second example. Both conclusions follow from exact integer sign certificates and the intermediate value theorem. No floating-point result, root solver, assumed numerical precision, or imported coefficient recurrence is used.

This audit independently transcribed the published finite sum. It did not read, import, or reuse the parent investigator's or the first investigator's scripts or certificates. The proposed parameter pairs and rational sampling points were supplied; independence concerns the reconstruction and verification, not discovery credit.

## 1. Source and scope audit

Primary sources:

1. [Wakhare, arXiv:2312.14743v2](https://arxiv.org/html/2312.14743v2), dated 14 January 2025. Conjecture 2, equations (1.3) and (1.4), in the Introduction; [PDF](https://arxiv.org/pdf/2312.14743v2), printed page 2. The scale parameter is defined in (1.1), printed page 1; the equivalent equation for `alpha_(k/r)` appears explicitly as (6.1), printed page 11.
2. [Publisher article](https://www.sciencedirect.com/science/article/pii/S0021904525000012), Journal of Approximation Theory 307 (May 2025), article 106143, DOI [10.1016/j.jat.2025.106143](https://doi.org/10.1016/j.jat.2025.106143).
3. [Ho, arXiv:2601.19327v1, Theorem 1](https://arxiv.org/html/2601.19327v1), 27 January 2026, for the distinct entropy-inequality result.

The publisher's indexed primary text includes the entire Conjecture 2: the parameter domain, both defining formulas, and the root-count assertion agree with arXiv v2. Direct opening of the publisher URL returned a tool error; the journal PDF was not obtained. Thus the journal comparison here is against the publisher's returned indexed article text, not a byte-for-byte PDF comparison. The arXiv PDF's extracted text independently confirms the formulas and page locations. PDF screenshots failed to fetch; no visual-PDF inspection is claimed.

The conjecture's domain is all integers `k>r>=1`; it is not restricted to `r=1`, `k/r>=2`, or integer ratios. Both examples also satisfy `gcd(k,r)=1`, so imposing the coprimality mentioned in the subsequent reduction theorem would not remove them.

The previously suggested DOI ending `106093` is not the publisher's identifier and must not be used for this paper.

## 2. Exact definitions audited

For integers `k>r>=1`, define

\[
h_{k,s}(x)=\sum_{j=0}^{k-1}x^{sj}\sum_{v=0}^j
 \frac{(-1)^{j-v}}{v+1}\binom{sv+k}{k}\binom{k}{j-v}.
\]

The polynomial under test is exactly

\[
p_{k,r}(x)=\alpha k(1-x^r)^k h_{k,k}(x)
-r(1-x^k)^k h_{k,r}(x),\qquad \alpha=\alpha_{k/r}.
\]

In particular, the first entropy polynomial is `h_(k,k)`, not `h_(k,k-r)`. The subscript on alpha is the ratio `k/r`, not the integer `k`.

The scale equation is

\[
\alpha^r(1+\alpha)^{k-r}=1,\qquad 0<\alpha<1.
\]

On the positive axis, `t^r(1+t)^(k-r)` is strictly increasing. Its values at zero and one are respectively zero and `2^(k-r)>1`. Consequently alpha is the unique positive solution in `(0,1)`. Raising the original positive-root equation to its `r`th power introduces no ambiguity in this domain. No negative or complex algebraic root is selected.

## 3. Integer denominator clearing

Let `L=lcm(1,...,k)` and define integer coefficients and evaluations

\[
C_{s,j}=\sum_{v=0}^j(-1)^{j-v}\frac{L}{v+1}
\binom{sv+k}{k}\binom{k}{j-v},\qquad
H_s(a,b)=\sum_{j=0}^{k-1}C_{s,j}a^{sj}b^{s(k-1-j)}.
\]

For positive integers `0<a<b`,

\[
h_{k,s}(a/b)=\frac{H_s(a,b)}{Lb^{s(k-1)}}.
\]

Set `d=k^2+kr-r` and

\[
A=k b^{k-r}(b^r-a^r)^kH_k(a,b),\quad
B=r(b^k-a^k)^kH_r(a,b).
\]

Then, **exactly**,

\[
Lb^d p_{k,r}(a/b)=\alpha A-B.
\]

All denominators cleared here are strictly positive. The scripts verify `A>0` and `B>0` at every test point. Dividing both integers by their positive greatest common divisor changes no sign or ratio.

Let `R=B/A`. By strict monotonicity of the scale function,

\[
\operatorname{sgn}(p_{k,r}(a/b))
=\operatorname{sgn}\{1-R^r(1+R)^{k-r}\}
=\operatorname{sgn}\{A^k-B^r(A+B)^{k-r}\}.
\]

Thus the sign is an integer computation. This is the main certificate. No approximation to alpha occurs in it.

## 4. Primary counterexample: k=11, r=10

Here `L=27720`, `d=221`. The freshly reconstructed coefficient arrays `C_(11,j)` and `C_(10,j)`, in increasing `j`, are:

```
C11 = [27720, 9776982600, 1680730654680, 34015194203760,
       175467764850840, 296638476500520, 175467764850840,
       34015194203760, 1680730654680, 9776982600, 27720]
C10 = [27720, 4888338840, 728598633840, 13557848174640,
       65416705671240, 103920724630800, 57585379781160,
       10327287746160, 456471837360, 2095160760, -2520]
```

The exact integer `A^11-B^10(A+B)` is respectively positive, negative, positive, negative, positive at

\[
1/5,\quad2/5,\quad3/5,\quad2/3,\quad4/5.
\]

For a compact independently verified presentation of the same sign certificate, all of the following are strict rational bounds:

| x | Lower bound for R=B/A | Upper bound for R=B/A | sign p(x) |
|---|---:|---:|---:|
| 1/5 | 918/1000 | 919/1000 | + |
| 2/5 | 1131/1000 | 1132/1000 | - |
| 3/5 | 934/1000 | 935/1000 | + |
| 2/3 | 938/1000 | 939/1000 | - |
| 4/5 | 927/1000 | 928/1000 | + |

Moreover, `936/1000 < alpha < 937/1000`. This bound is proved by the exact integer identities

```
936^10 * 1936 - 1000^11 = -773736702328927599581634494464
937^10 * 1937 - 1000^11 = 10474898608767871728104442364513
```

Each interval for `R` is checked by the two integer inequalities `1000B-nA>0` and `(n+1)A-1000B>0`. These are rigorous rational enclosures, not reported decimal estimates. The full residuals and main integer certificates are in `small_integer_certificate.json`.

Since `p_(11,10)` is a real polynomial, it is continuous. Opposite nonzero signs at the endpoints yield at least one root in each of the four pairwise disjoint open intervals

\[
(1/5,2/5),\quad(2/5,3/5),\quad(3/5,2/3),\quad(2/3,4/5).
\]

Those four roots are distinct and lie strictly in `(0,1)`. Every root has multiplicity at least one, so the number counted with multiplicity is at least four. This contradicts the conjectured count of two.

## 5. Second independently verified example: k=20, r=19

Here `L=232792560`, `d=761`. The exact integer `A^20-B^19(A+B)` has signs `+,-,+,-,+` at

\[
1/5,\quad2/5,\quad11/20,\quad13/20,\quad3/4.
\]

Accordingly, four distinct roots occur in the four open intervals between consecutive listed sample points.

An auxiliary exact rational certificate gives `965/1000<alpha<966/1000` and these strict bounds for `R`, in the same point order:

```
(951/1000, 952/1000)
(1187/1000, 1188/1000)
(924/1000, 925/1000)
(979/1000, 980/1000)
(962/1000, 963/1000)
```

Complete coefficient arrays and full integer signs are in `integer_certificate.json`; the enclosure residuals are in `compact_certificate.json`.

## 6. What this establishes and what it does not

- This is a complete counterexample to the universally quantified Conjecture 2 as published and as stated in arXiv v2.
- It establishes **at least four distinct roots**, not exactly four. It does not establish their multiplicities or exclude further roots.
- It does not give the smallest counterexample, an infinite family, or a classification.
- It does not refute Conjecture 1, the entropy inequality. Wakhare's stated reduction is the implication `Conjecture 2 => Conjecture 1`; failure of the sufficient condition does not negate the inequality. Ho's 2026 Theorem 1 concerns that inequality for real exponents greater than one and is consistent with this counterexample. This audit checked its statement, not its entire proof or Lean development.
- No external contact, upload to a public mathematical repository, or git publication was performed.

## 7. Limited public-priority check

Searches on 2026-10-08 included the paper title with `counterexample` and `correction`, `Wakhare "Conjecture 2" counterexample`, and `entropy "p_{20,19}"`. The primary arXiv record still lists v2 as its latest version. The checked Ho paper discusses the entropy inequality and does not claim this root-count counterexample. No public counterexample or erratum was located in this limited search.

**Novelty is not certified.** Search failure cannot rule out an unindexed note, unpublished result, discussion, differently phrased example, or earlier counterexample. The mathematical counterexample and public-priority status are separate conclusions.

## 8. Reproduction

Use Python 3.11 or later; all dependencies are from its standard library.

```
python3 verify_small_integer.py
python3 verify_integer.py
```

The scripts reconstruct coefficients from the defining binomial sum on every run and regenerate their certificates. All assertions passed in this audit. `run_small_output.txt` and `run_output.txt` contain the audit run summaries. The scripts neither access the network nor read another investigator's certificate.
