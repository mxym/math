# Exactly half the primes above the square root force a common multiplier

Let \(N\) be even and let \(A\) be the multiplicity matrix of a nontrivial
[Bożek exceptional autonomous component](https://arxiv.org/abs/1909.09900):
all labels are distinct odd primes coprime to \(N\), and every \(N-x\)
is composite with all factors in the component. The support is strongly
connected, oriented from each input to its factors. Suppose there are
\(2t\) labels, \(t\ge2\), and \(\dim\ker(I-A)=t-1\). Write \(S\)
for the labels at most \(\sqrt N\) and \(R\) for the others.

**Theorem.** If \(|S|=|R|=t\), then there is an even integer \(h>0\)
such that
\[
 W=1+hN,\qquad \operatorname{rad}(W)=\prod_{s\in S}s,\qquad
 v_s=1+hs\mid W,\qquad R_s=\frac{W/v_s-1}{h}.
\]
The \(R_s\)'s are the distinct labels of \(R\). This holds at every
height; no smoothness, arity bound, asymptotic restriction, or fixed
seed is assumed. The result generalizes the exact part of the
[weight-zero/weight-one balanced result](PrimeOrbitBalancedReturn.md);
it does not give that result's additional subpower bound on \(h\).

### The outside graph must be acyclic

Each row has at most one outside target with multiplicity one, since
two factors above \(\sqrt N\) would exceed \(N\). If it has such a
target, its remaining cofactor \(v\) satisfies \(3\le v<\sqrt N\)
and is supported on \(S\). Restriction of a fixed vector \(Aw=w\)
to \(S\) is injective: a vector zero there propagates zero along
the single outside successor from any retained row, and then along
all outside paths. Every outside label can be reached this way by
strong connectivity (take the last retained vertex on a path).
Thus the image of the fixed space in the retained coordinates has
dimension \(t-1\).

If there is an outside cycle, sum the fixed-vector equations along
that cycle. The differences of successive outside coordinates cancel,
leaving a nonzero linear relation on \(S\) with nonnegative coefficients
(the sum of the cofactor exponents). The image of the fixed space is
exactly the hyperplane of this relation. A retained row with no outside
target would impose a second relation whose coefficient at its own
vertex is \(+1\), whose other coefficients are nonpositive, and
with at least one negative coefficient; the loop is forbidden because
each label is coprime to \(N\). This relation cannot be a multiple
of the first one. Hence, if a cycle exists, every retained input
directly supplies an outside target. The targets are distinct:
a common larger prime would divide the nonzero difference of two
smaller inputs. They therefore exhaust \(R\).
Each outside target now already has a smaller retained input, and
cannot have another smaller input by the same congruence argument.
Every outside arc would therefore strictly decrease, contradicting
the cycle.

### The first-return equations force all outside paths to have length one

The first-return matrix on \(S\) is
\(K=A_{SS}+A_{SR}(I-A_{RR})^{-1}A_{RS}\), since the outside block is
nilpotent. It is irreducible, by breaking each path at its retained
visits, and its row sums are at least two: each outgoing factor,
with multiplicity, extends to at least one first-return path.
Schur elimination gives \(\dim\ker(I-K)=t-1\). Therefore \(K-I\)
has rank one and is strictly positive: its column and row lines
are the positive right and left Perron lines of \(K\), with
positive nonzero eigenvalue \(\rho(K)-1\). Write \(K-I=ab^\mathsf T\)
with positive integral vectors \(a,b\), taking the primitive integral
vector on the column line so that \(\gcd_s a_s=1\).
Set \(W=\prod_{s\in S}s^{b_s}>1\).

Starting at \(x_0=s\), follow the unique outside successor
while there is one, ending at \(x_i\) after \(i\) outside
arcs. Write \(N-x_{j-1}=v_jx_j\). Set \(V_0=1,C_0=0\), and
\(V_j=v_jV_{j-1}, C_j=V_{j-1}-C_{j-1}\). Successive substitution gives
\(x_j=(C_jN+(-1)^j s)/V_j\) and \(0\le C_j<V_j\).
The terminal complement \(N-x_i\) is entirely supported on \(S\).
The retained factors accumulated by the first return are exactly
the product of the cofactors and that terminal complement, so
\[
 W^{a_s}=\frac{V_i(N-x_i)}s=\frac{(V_i-C_i)N}s+(-1)^{i+1}.
\]
In particular \(s\mid(V_i-C_i)\), since \(s\nmid N\). This
excludes \(i=0\), where \(V_0-C_0=1\). Hence all retained inputs
directly supply different outside targets, exhausting \(R\).
The congruences \(W^{a_s}\equiv\pm1\pmod N\) and \(\gcd_s a_s=1\)
give \(W\equiv\pm1\pmod N\), so \(W\ge N-1\).

For an outside path of length one or two, \(V_i<N\), and
\(W^{a_s}<N^2/3+1<(N-1)^2\) for \(N\ge4\); hence \(a_s=1\).
If any outside edge exists, follow a path to a last edge \(y\to z\)
where \(z\) has no outside successor. The two retained inputs that
directly target \(y,z\) then have lengths two and one, respectively.
They give \(a_s=1\) but opposite signs modulo \(N\) for \(W\),
impossible. Thus all lengths are one and all \(a_s=1\).

The formula at length one gives \(W=1+hN\) with
\(h=(v_s-1)/s\) the same positive integer for all \(s\). It is
even because each cofactor is odd. Since \(v_s=1+hs\) is
coprime to \(s\) and divides \(sW\), it divides \(W\). The
factorization \(N-s=v_s R_s\) then gives \(W=(1+hs)(1+hR_s)\).
The strictly positive exponents \(b_s\) give the radical equality.

### Application to six-label orbits at \(F\)-rich centers

Fix a finite prime set \(F\), \(\epsilon>0\), and a prescribed
odd prime \(p\) coprime to even \(N\), with \(N_F\ge N^{1/2+\epsilon}\)
as in [moving-seed independence](PrimeOrbitMovingSeed.md).
A **terminal, six-label forward orbit** from \(p\) with all
complements composite must have at least four labels at most
\(\sqrt N\), for every sufficiently large such \(N\), without
an arity cap.

Indeed the corank is two by the cited independence and feedback
bounds. There are at least three retained labels by the injective
restriction argument above (which works for any retained set
containing all labels at most \(\sqrt N\)); if there were exactly
two, the image would be two-dimensional, so an outside cycle would
contradict the nonzero constraint above, while in the acyclic
case \(I-K\) has a nonzero Perron eigenvalue and nullity at most one.
With exactly three retained labels there are three outside labels,
and \(p\) is among the retained for large \(N\). Write the other
retained labels \(q<r\). Both grow to infinity on any candidate
sequence by the [two-seed lower bound](PrimeOrbitMultiSeedMinimal.md):
a fixed second seed in the same terminal component would require at
least seven labels. The above multiplier makes every \(1+hs\) for
\(s\in\{p,q,r\}\) supported on that same set, contradicting the
[three-prime moving multiplier lemma](PrimeOrbitSixSmoothExclusion.md),
which itself does not require \(N\) to be smooth.

Under a fixed arity cap a whole six-orbit is terminal by
[the three-factor rank and bounded-arity theorem](EACSixThreeFactorRank.md).
Without an arity cap, the argument does not exclude a nonterminal
six-orbit or the case of four or more retained labels. Nor is
any bound on the size of a general counterexample orbit asserted.

**Dated comparison (through November 21, 2026).** The original graph
framework is Bożek's. The earlier [asymptotically balanced statement](PrimeOrbitBalancedReturn.md)
and [two-retained result](EACTwoRetained.md) are the nearest local precedents.
[Kelanemer's 2026 exponent-matrix work](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460)
has a related terminal-component framework, but only its indexed
abstract was accessible; there is no priority or comprehensive
nonoverlap claim. [Pham October 2026 v1](https://www.preprints.org/manuscript/202610.3061)
and the [November almost-prime sieve](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf)
concern different additive estimates rather than this exact factor-closure theorem.
