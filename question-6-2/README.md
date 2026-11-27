# Fernando–Kousik Question 6.2: the only extension is e = 3

For \(q=4\), \(e>2\), and \(n=1+4^{e-2}+4^{e-1}+2\cdot4^e\), the polynomial in [Question 6.2 of Fernando and Kousik](https://arxiv.org/pdf/2606.01037v1#page=17) permutes \(\mathbb F_{4^e}\) **if and only if \(e=3\)**.

[The proof](PROOF.md) derives and simplifies the polynomial from its definition to \(y^8+y^5+y\operatorname{Tr}_{4^e/4}(y)\) after a bijective Frobenius change of input. Even extensions contain an explicit collision already over \(\mathbb F_4\). In odd extensions \(e\ge9\), a two-trace character count proves that a pair of distinct trace-zero inputs collides. Exact finite certificates cover \(e=3,5,7\). The \(e=3\) case was already listed in the source and its predecessor; the result proves that no other extension works.

## Reproduce

    sh replay.sh | diff -u RESULTS.txt -

Python 3.10+, no external data. The two checkers use different arithmetic implementations. One checks the small fields, collisions and trace-sieve arithmetic; the other computes the literal translation sum in a polynomial quotient ring without using the derived formula. The large-\(e\) assertion is analytic, not an enumeration cutoff.
