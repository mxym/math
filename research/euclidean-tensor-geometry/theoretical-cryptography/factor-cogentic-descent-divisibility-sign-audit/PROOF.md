# Exact audit of the ancestor-determinant guard

## 1. Fixed source and notation

The audited source is the PDF `paper.pdf` at Google Research commit
`4a7bc8ab0bc770e71a259b7966c500496b99010a` (paper blob
`19f36b2f189ed41ec8e112b92aa9b88a96c6bd1e`).

For a history of distinct primitive pairs
\[
\mathbf a_t^*=(a_t^*,b_t^*)\qquad(0\le t<r),
\]
the paper uses
\[
D_{t_1,t_2}:=
 |b_{t_1}^*a_{t_2}^*-a_{t_1}^*b_{t_2}^*|,
 \qquad
R_{\rm anc}:=\prod_{0\le t_1<t_2<r}D_{t_1,t_2}.
\]
The geometric filters make every displayed determinant in this product
nonzero.

## 2. What Lemma 4.4 requires and uses

Lemma 4.4(1), “Local second-moment concentration across all descent levels,”
assumes
\[
q\nmid R_{\rm anc}. \tag{L}
\]
The proof later invokes (L) explicitly: since \(q\nmid R_{\rm anc}\), at most
one ancestor index \(t_0\) can satisfy
\(q\mid\Delta_{t_0}(\mathbf a_1)\). This yields
\[
v_q(P_{\rm anc}(\mathbf a_1))\in\{0,1\}
\]
outside one exceptional candidate and is then used to choose the
\(q^{1-s}P_{\rm anc}\) shift. Thus (L) is not a decorative hypothesis.

## 3. What the printed algorithm checks

Definition 4.5, in the `AlgNode` pre-check, instead says to verify
\[
q\mid D_{t_1,t_2}
\quad\text{for every }0\le t_1<t_2<r. \tag{A}
\]
When \(r\ge2\), (A) implies
\[
q\mid\prod_{t_1<t_2}D_{t_1,t_2}=R_{\rm anc},
\]
which is the negation of (L). Consequently:

* a history admitted by the printed guard (A) is outside the stated scope of
  Lemma 4.4;
* a good history satisfying (L) is rejected by the printed guard (A).

This is an exact logical contradiction, not an asymptotic or constant-factor
issue.

## 4. Why the intended repair is nondivisibility

Lemma 4.4 defines
\[
Y_{\rm forb}(\mathbf a)
  =R_{\rm anc}\prod_{t<r}
      \Delta_t(\mathbf a)y_{t,1}^*y_{t,2}^*.
\]
Lemma 3.6(3) puts every prime divisor of \(Y_{\rm forb}\) into the bad-prime
set. Hence, if an accepted parent does not trigger the bad-child event, every
candidate child prime \(q\) satisfies \(q\nmid R_{\rm anc}\).

This is exactly the assertion used in Lemma 4.6 when it says that every such
candidate child satisfies every hypothesis of Lemma 4.4(1). Therefore the
surrounding proof consistently points to the corrected guard
\[
q\nmid D_{t_1,t_2}
\quad\text{for every ancestor pair}. \tag{A'}
\]
Since \(R_{\rm anc}\) is their product, (A') is equivalent to (L).

## 5. Scope of the conclusion

The fixed v1 does not prove Lemma 4.6 for the algorithm literally printed in
Definition 4.5. Replacing the single `\mid` by `\nmid` in that pre-check
removes this exact incompatibility and agrees with the rest of the displayed
argument.

This audit does not certify all remaining estimates, does not claim that the
global \(L_N[1/3,105]\) theorem is false after correction, and does not address
implementations or real cryptographic targets.
