# Proof

Let \(K=\mathbb F_Q\), \(Q\ge2\), and \(k,\ell\ge1\). A function \(K^k\to K\) is called **balanced** if every fiber has cardinality \(Q^{k-1}\); this is the source's definition of a permutation polynomial in \(k\) variables. Put
\[
 \sigma_\ell(x_1,\ldots,x_k)=\sum_{i=1}^k x_i^\ell,\qquad
 d=\gcd(\ell,Q-1).
\]

**Theorem.** For any function \(f:K\to K\), the composite \(f\circ\sigma_\ell\) is balanced if and only if \(d=1\) and \(f\) is bijective.

**Proof by free orbits.** Since \(K^\times\) is cyclic of order \(Q-1\), the subgroup of roots of \(u^\ell=1\) has order \(d\). On \(K^k\setminus\{(0,\ldots,0)\}\), let a root \(u\) multiply the first nonzero coordinate of the tuple, leaving all others unchanged. The first nonzero coordinate remains at the same index, so this is a group action. It is free because a nonzero coordinate cannot be fixed by multiplication by \(u\ne1\), and it preserves \(\sigma_\ell\) and hence every fiber of its composite with \(f\). The only excluded tuple is the zero tuple, in the fiber of \(f(0)\). Thus the exact integer congruence for all \(b\in K\) is
\[
 \#(f\circ\sigma_\ell)^{-1}(b)\equiv [b=f(0)]\pmod d .
\]
If \(d>1\), any \(b\ne f(0)\) gives a contradiction to balance: \(Q^{k-1}\equiv1\pmod d\), since \(d\mid Q-1\). If \(d=1\) then \(x\mapsto x^\ell\) permutes \(K\); for every \(s\in K\) and every choice of \(k-1\) input coordinates, there is exactly one remaining coordinate giving \(\sigma_\ell=s\). Therefore the fiber of \(f\circ\sigma_\ell\) at \(b\) has size \(Q^{k-1}\# f^{-1}(b)\), proving the theorem.

In the setting of the conjecture, \(q=p^m\) and \(Q=p^e\) have the same characteristic and \(f\) is the polynomial \(g_{n,q}\) evaluated on \(K\). The proof imposes no divisibility relation between \(m\) and \(e\) and works for every \(n\) in the source. If desired, the two conditions also make each one-variable slice bijective, so here the balanced PP and local PP conditions agree. This last observation uses the theorem and the definitions, not a general assertion that a multivariate PP is local.

## Independent additive-character proof and a mixed-power extension

Let \(A\) be any finite abelian group with additive notation, and \(h:A\to A\) any function. Set \(c(a)=\#h^{-1}(a)\). The fiber sizes of the map \((x_1,\ldots,x_k)\mapsto \sum_i h(x_i)\) are the \(k\)-fold additive convolution \(c^{*k}\): expand the count according to the values \(h(x_i)\). For a complex character \(\chi\), write \(\widehat c(\chi)=\sum_{a\in A}c(a)\chi(a)\). Summing over \(a,b\) with \(\chi(a+b)=\chi(a)\chi(b)\) gives
\[
 \widehat{c^{*k}}(\chi)=(\widehat c(\chi))^k.
\]
If the sum map is balanced, the left side is zero at every nontrivial character. Over \(\mathbb C\) an element with zero \(k\)-th power is zero, so by character orthogonality \(c\) is constant. Its sum is \(|A|\), hence \(c(a)=1\) and \(h\) is bijective. Conversely \(c\equiv1\) clearly gives uniform convolutions. A postmap \(f:A\to A\) must itself be surjective if the composite is balanced, as every fiber is nonempty, and hence bijective; applying it merely relabels the fibers. Taking \(h(x)=x^\ell\) recovers Conjecture 5.23 independently of the orbit divisibility.

For completeness this gives a useful variant for *different* exponents. Let \(a_i\ne0\) in \(K\), and \(\ell_i\ge1\). The diagonal sum \(\sum_i a_i x_i^{\ell_i}\) over \(K\) is balanced if and only if at least one exponent \(\ell_i\) is coprime to \(Q-1\). For the forward implication suppose each \(d_i=\gcd(\ell_i,Q-1)>1\). For each input summand its pushforward count is
\[
 c_i=\mathbf 1_{\{0\}}+d_i\mathbf 1_{a_i(K^\times)^{\ell_i}},
\]
and at every additive character the transform is \(1+d_i\sum_{z\in a_i(K^\times)^{\ell_i}}\chi(z)\), which cannot be zero. Indeed, the sum of roots of unity is an algebraic integer, whereas \(-1/d_i\) is a rational noninteger. The product of the transforms is then nonzero at any nontrivial character, precluding uniformity. The reverse implication follows by fixing the other coordinates and using the coprime coordinate to hit every value exactly once. This variant is an elementary consequence, not a separate priority claim.
