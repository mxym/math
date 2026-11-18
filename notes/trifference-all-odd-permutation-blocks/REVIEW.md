# Independent internal review

**Result: PASS for the stated lower bounds.** Independent AI-assisted review and separately implemented integer checks; this is not human peer review or formal certification.

### Conditional count: only two parity masks

The input words all have the same profile up to permutations of rows and letters. Thus it suffices to fix the first word $x=(0,0,0,1,\ldots,q-1)$ and multiply its number of compatible ordered pairs by the block size $S$. Let $a_i,b_i\in\{-1,1\}$ be two sign masks for the other two words. Write $U=\sum_i a_i$, $V=\sum_i b_i$, $W=\sum_i a_i b_i$. In a row where the fixed first symbol is $i$, the signed sum over allowed pairs equals

$$
L_i=a_i V+b_i U+W-2a_i b_i.
$$

This is the union of the conditions that one letter agrees with $i$ or the other two agree; the all-equal case was counted three times. Taking the signed character projection onto odd counts for each of the two remaining words yields

$$
D/S=4^{-q}\sum_{a,b}\left(\prod_i a_i b_i\right)L_0^3\prod_{i=1}^{q-1}L_i.
$$

The independent checker groups **only the singly occurring letters** by their four possible sign pairs and sums over the sign pair of letter 0 separately. It does not import the original three-mask or parity-state implementations. It reproduces all sixteen $q=4,\ldots,19$ bad-triple counts. At $q=9$ the exact values are $S=59875200$ and $D=458769821652172800$. For $q=3,n=5$ the conditionally counted pairs also agree with raw enumeration of the words.

### Permutations by coloring nontrivial cycles

Fix the first permutation as identity. Given the second permutation $\sigma$, the third permutation $\tau$ must, at each moved point $i$ of $\sigma$, choose either $i$ or $\sigma(i)$. Thus $\tau$ maps each nontrivial $\sigma$-cycle into itself; injectivity forces a uniform choice around that cycle. On the fixed points of $\sigma$ the remaining permutation is unrestricted. If there are $f$ fixed points and $c$ other cycles, exactly $f!2^c$ third permutations work.

Let $g_m$ count derangements of $m$ letters with each cycle one of two colors. Then $g_0=1$, $g_1=0$, and $g_m=(m-1)(g_{m-1}+2g_{m-2})$: either insert the distinguished letter after an existing letter, or make a two-cycle with it and choose its color. Hence the number of suitable ordered pairs for fixed first word is $q!\sum_{m=0}^q g_m/m!$. Dividing by $(q!)^2$ gives the with-replacement failure probability. This nonnegative count proves the same finite gaps independently of the alternating coefficient formula. The independent program checks all 236 alphabets $20,\ldots,255$, then checks the exact guards in the analytic tail.

### Quantifiers and diagnostics

* The deletion argument is a first-moment argument for the number of bad **index** triples. It needs no independence between distinct triples, no Janson estimate, and no second-moment assumption. The draws are independent across block positions, so the probability for any given triple is $F^k$. Retaining at least three indices excludes repeated surviving words automatically.
* Padding by at most $n-1$ unused coordinates is harmless for a fixed $n,q$. No diagonal passage with changing $q$ is required. The large-alphabet limit applies to an explicit achievable expression and implies only a liminf lower bound on the true gap.
* The ternary conversion contributes a factor of four, in addition to the length-11 block and factor of two from alteration. Both the stated decimal threshold and the comparison with the exact Yuan–Zhu value pass without rounding. The independent check also exhausts the $\binom 93=84$ triples of Tetra symbols.
* Neither the block of all odd words nor the permutation block is assumed to be a three-hash code. Only the outer code after deletion must have the separation property.
