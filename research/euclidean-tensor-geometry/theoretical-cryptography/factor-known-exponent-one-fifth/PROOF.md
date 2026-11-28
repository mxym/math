# Proof

Let
\[
 \vartheta=\frac1{4\sqrt e}<\frac15
\]
and choose a fixed
\[
 0<\eta<\frac15-\vartheta. \tag{1}
\]

Write
\[
 \mathcal H(Y)=
 O\!\left(
 \frac{Y^{1/5}\log^{16/5}Y}{(\log\log Y)^{3/5}}
 \right) \tag{2}
\]
for the rigorous deterministic complete-factorization bound of
Harvey and Hittmeir, with the finitely many small values absorbed into
the implied constant.

## Case 1: \(N\le E\)

Apply the Harvey--Hittmeir algorithm directly to \(N\). This returns the
complete prime factorization in \(\mathcal H(N)\) bit operations.
Since \(X=\min\{N,E\}=N\), this is the first term of the asserted bound.

## Case 2: \(E<N\)

Apply the same algorithm to \(E\). This deterministically returns the
complete prime factorization
\[
 E=\prod_i r_i^{S_i} \tag{3}
\]
in \(\mathcal H(E)\) bit operations.

Now invoke the factored-advice theorem at repository commit
\[
 \texttt{46afa65c4e8fd9999822dcdd8bfd492522cff0b7}.
\]
Its hypotheses hold because the original input supplies
\(\lambda(N)\mid E\), and (3) is now known. If
\[
 P_E(N)=\max\bigl(\{p:p\mid N,\ p\nmid E\}\cup\{1\}\bigr),
\]
that theorem gives complete factorization of \(N\) in
\[
 P_E(N)^{\vartheta+\eta}
 \operatorname{poly}_{\eta}(\log N+\log E). \tag{4}
\]
Every residual prime satisfies \(p-1\mid E\), so
\[
 P_E(N)\le E+1. \tag{5}
\]
Combining (2), (4), and (5), the second case costs
\[
 \mathcal H(E)
 +(E+1)^{\vartheta+\eta}
 \operatorname{poly}_{\eta}(\log N+\log E). \tag{6}
\]

## Combining the branches

The algorithm compares the two supplied integers and chooses the
appropriate branch. With \(X=\min\{N,E\}\), (6) and Case 1 give
\[
 \mathcal H(X)
 +(X+1)^{\vartheta+\eta}
 \operatorname{poly}_{\eta}(\log N+\log E). \tag{7}
\]
Because \(\vartheta+\eta<1/5\), (7) is
\[
 X^{1/5+o(1)}
 \operatorname{poly}(\log N+\log E). \tag{8}
\]

If \(E=N^{\tau+o(1)}\), then
\(X=N^{\min\{1,\tau\}+o(1)}\), and substitution in (8) gives
\[
 N^{\min\{1,\tau\}/5+o(1)}. \tag{9}
\]

No step constructs \(E\); the theorem only exploits the supplied
multiple.

## Finite verifier

The checker does not reprove either analytic complexity theorem. It
tests their arithmetic interface on exact bounded examples, including
nontrivial multiples of \(\lambda(N)\):

* factoring the supplied multiple and reconstructing it exactly;
* stripping every prime of \(N\) that also divides \(E\);
* squarefreeness and injectivity of the residual full signatures;
* prime-conductor local-order witnesses for every residual pair;
* complete residual refinement by all factored-\(E\) chains;
* both comparison branches \(E<N\) and \(N\le E\);
* the strict numerical inequality
  \(1/(4\sqrt e)<1/5\).
