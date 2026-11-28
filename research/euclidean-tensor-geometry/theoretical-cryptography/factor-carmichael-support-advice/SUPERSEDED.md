# Supersession note

The theorem in PROOF.md is valid, but its
\(P_{\mathcal S}(N)^{1/(4\sqrt e)+\varepsilon}\) dependence is weaker
than the smooth-subgroup argument already present in Źrałek's proof.

## Input conversion

The support advice gives the completely factored polynomial-length
multiple
\[
 E=\prod_{r\in\mathcal S,\ r\le N}r^{\lfloor\log_rN\rfloor},
 \qquad \lambda(N)\mid E.
\]
Primes from \(\mathcal S\) are divided out first. The remaining integer
is squarefree; call the largest remaining prime \(P\).

## Geometric scale search

On a current composite block \(D\), use geometrically increasing bounds
\(y\). For every ordinary base \(2\le b\le y\), the factorization of
\(E\) lets us compute \(\operatorname{ord}_D(b)\) by prime-factor
stripping. A difference among the local order valuations gives a
Fermat--Euclid gcd split.

If no split occurs, every prime \(p\mid D\) sees the same local orders.
Thus, with
\[
 A=\operatorname{lcm}_{2\le b\le y}\operatorname{ord}_D(b),
\]
we have \(A\mid p-1\) and
\[
 A=\#\langle2,\ldots,y\rangle_p\ge\Psi(p,y).
\]
This is the step used in Źrałek, arXiv:0707.4102v5, Lemma 8.3.

For \(p>y\), the standard lower bound
\[
 \Psi(p,y)>p^{1-\log\log p/\log y}
\]
gives
\[
 \frac pA<
 \exp\!\left(\frac{\log p\,\log\log p}{\log y}\right).
\]
At
\[
 \log y=(1+o(1))\sqrt{\log P\,\log\log P},
\]
the right-hand side is at most \(y\), uniformly for \(p\le P\).
Therefore some \(p\mid D\) is \(p=1+mA\) with \(m\le y\). Testing those
candidates splits \(D\). If \(p\le y\), ordinary trial division already
finds it.

The algorithm does not need to know \(P\): double the scale
geometrically until a split occurs, then recurse. There are only
\(O(\log N)\) split nodes, so the total deterministic cost is
\[
 \exp\!\left((1+o(1))
 \sqrt{\log P\,\log\log P}\right)\operatorname{poly}(B).
\]

This is a direct adaptation of a published proof to the support-to-\(E\)
conversion. It supersedes the old Burgess bound but is not an
independent novelty claim. The historical proof remains in place.
