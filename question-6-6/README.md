# Fernando–Kousik Question 6.6: every allowed extension works

The polynomial in [Question 6.6 of Fernando and Kousik](https://arxiv.org/pdf/2606.01037v1#page=17) permutes \(\mathbb F_{4^e}\) for **every even \(e>2\)**, with no further restriction.

In fact, put \(e\ge2\), \(a\ge0\), and \(n_{e,a}=1+2\cdot4^a+2\cdot4^{e-1}+4^e+2\cdot4^{e+a}\). Then
\[
 g_{n_{e,a},4}\text{ permutes }\mathbb F_{4^e}
 \quad\Longleftrightarrow\quad
 e\text{ is even and }\gcd(2a+1,e)=1.
\]
Question 6.6 is \(a=e/2-1\), where the gcd is automatically 1. Theorem 3.4 in the source already gives the positive range for \(a=2\) and \(e>3\); their Example 3.5 is the same parameter as Question 6.6 at \(e=6\).

[The proof](PROOF.md) derives the polynomial independently from its defining translation sum. The two equal terms in the printed formula cancel in characteristic two. On each nonzero trace fiber the resulting map is a rescaled affine binary linearized trace sum whose kernel is explicit. This answers Question 6.6, not the other questions of §6.

## Reproduce

    sh replay.sh | diff -u RESULTS.txt -

C++17 compiler and POSIX shell. Set the temporary directory to a writable executable location if needed. The checker enumerates all inputs for \(e=4,6,8,10\) in two distinct polynomial bases each, and compares with the literal defining sum in a formal quotient ring at all inputs for \(e=4,6\) and deterministically sampled inputs for \(e=8,10\). It also tests odd extension, nontrivial kernels and the effect of deleting one copy of a repeated term. These computations are not used in the analytic proof.
