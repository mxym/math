# Fernando–Kousik Question 6.8: precisely e = 4

For \(q=4\), \(e\ge3\), and \(n=1+2\cdot4+4^2+2\cdot4^3+2\cdot4^{e+1}\), the polynomial from [Question 6.8 of Fernando and Kousik](https://arxiv.org/pdf/2606.01037v1#page=18) permutes \(\mathbb F_{4^e}\) **if and only if \(e=4\)**.

[The proof](PROOF.md) starts with the literal defining translation sum. On the target field its value is \(x^{32}+t^2(1+(x+x^4)^9)\) with \(t=\operatorname{Tr}_{4^e/4}(x)\). This matches the displayed formula as a polynomial function; the proof distinguishes it from the formal polynomial before reduction. Odd extensions are excluded on the ground subfield. For even \(e\ge10\), a two-trace character count sends a nonzero-trace input into the image of the zero-trace layer. Exact finite certificates handle \(e=4,6,8\). The positive \(e=4\) instance was previously listed; the contribution is the exclusion of every other extension.

## Reproduce

    sh replay.sh | diff -u RESULTS.txt -

Python 3.10+, without external inputs. The checker gives complete enumeration in two polynomial bases for \(e=4,6,8\). An independent carryless verifier evaluates the literal defining sum in a quotient ring, checks both complete \(e=4\) tables and the collision witnesses, and distinguishes the formal polynomial from the displayed representative on a different field. The proof for large \(e\) does not rely on enumeration.
