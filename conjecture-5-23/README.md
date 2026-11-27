# Fernando–Kousik Conjecture 5.23

The conjecture holds for all of its parameters. For \(Q=p^e\), \(q=p^m\), and \(k,\ell\ge1\), the polynomial
\[
 g_{n,q}^{(\ell)}(x_1,\ldots,x_k)
 =g_{n,q}(x_1^\ell+\cdots+x_k^\ell)
\]
has exactly \(Q^{k-1}\) preimages of every element of \(\mathbb F_Q\) if and only if both \(\gcd(\ell,Q-1)=1\) and \(g_{n,q}\) permutes \(\mathbb F_Q\).

The [proof](PROOF.md) applies to any univariate postmap in place of \(g_{n,q}\). For \(d=\gcd(\ell,Q-1)>1\), multiplication by the \(\ell\)-th roots of unity on the first nonzero coordinate shows that every output fiber except possibly that of the zero tuple has cardinality divisible by \(d\). The required size \(Q^{k-1}\) is \(1\) modulo \(d\), a contradiction. A second proof by additive characters applies even to sums of copies of an arbitrary map on a finite abelian group.

This answers Conjecture 5.23 and Remark 5.24 of the [source](https://arxiv.org/pdf/2606.01037v1#page=17). It does not classify the univariate \(g_{n,q}\) or answer the eight questions in its §6.

## Reproduce

    sh replay.sh | diff -u RESULTS.txt -

Python 3.10+, no dependencies or downloaded data. The checker compares finite tuple enumeration with histogram convolution, reconstructs \(g_{n,q}\) independently from its defining identity, and checks the mod-\(d\) obstruction and mixed-exponent examples. These are finite checks of an analytic argument.
