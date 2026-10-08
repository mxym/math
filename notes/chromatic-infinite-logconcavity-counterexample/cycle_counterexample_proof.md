# Cycles refute infinite log-concavity for chromatic coefficients

## Result

The absolute coefficient sequence of the chromatic polynomial of the cycle C17 is not 3-log-concave. More generally, this holds for every cycle C_n with n >= 17. Therefore Conjecture 21 of Tewodros Amdeberhan and Victor H. Moll, *Infinite log-convexity*, is false.

The same statement appears earlier as Conjecture 13.1 in Tewodros Amdeberhan, *Theorems, Problems and Conjectures*, arXiv:1207.4045v7 (August 25, 2022), Section 13, page 14: https://arxiv.org/pdf/1207.4045 . Hence this result also refutes that formulation.

A smaller example is C12, which fails on the fifth iteration. The simpler three-iteration certificate for C17 is sufficient for the disproof.

## Target and convention

Amdeberhan and Moll's Conjecture 21 asserts infinite log-concavity for the absolute coefficient sequences of all chromatic polynomials. Their paper lists the cycle polynomial explicitly on page 8 and states the conjecture on page 9.

- Journal record: https://combinatorialpress.com/ojac-articles/issue-17-2022/infinite-log-convexity/
- Paper: https://combinatorialpress.com/article/ojac/vol17/305.pdf

For a finite sequence a=(a_0,...,a_N), extend it by zeros outside this range and define

    L(a)_k = a_k^2 - a_{k-1}a_{k+1},    0 <= k <= N.

The length and endpoints are retained. This is the explicit convention on page 2 of Petter Brändén, *Iterated sequences and the geometry of zeros*, cited as reference [9] by Amdeberhan and Moll:
https://arxiv.org/pdf/0909.1927

Amdeberhan’s earlier Section 13 also explicitly imposes the left boundary a_(-1)=0. The Amdeberhan–Moll journal introduction does not spell out the boundary convention. The counterexample also admits a variant that avoids using any out-of-range coefficient at all; see below.

## A short exact certificate

The chromatic polynomial of the cycle C_n is

    chi(C_n;q) = (q-1)^n + (-1)^n(q-1).

For completeness, delete an edge of C_n and contract the same edge. The resulting graphs are a path on n vertices and C_(n-1), respectively, giving

    chi(C_n;q) = q(q-1)^(n-1) - chi(C_(n-1);q).

Starting with chi(C_3;q)=q(q-1)(q-2), induction gives the displayed formula.

Thus its absolute coefficients, in ascending degree, are

    a_0=0, a_1=n-1, a_k=C(n,k) for 2 <= k <= n.

For n=17 the initial coefficients needed are

    a_0,...,a_5 = 0, 16, 136, 680, 2380, 6188.

Write b=L(a), c=L(b), d=L(c). Direct integer arithmetic gives

    b_0,...,b_4 = 0, 256, 7616, 138720, 1456560;
    c_1=65536;
    c_2=7616^2 - 256*138720 = 22491136;
    c_3=138720^2 - 7616*1456560 = 8150077440.

Consequently

    d_2 = 22491136^2 - 65536*8150077440
        = -28272276537344 < 0.

This is a finite, explicit counterexample to Conjecture 21. No numerical approximation or unproved theorem is involved.

## An infinite family

The same calculation can be made symbolically. For n>=5,

    b_1 = (n-1)^2,
    b_2 = n(n-1)^2(n+4)/12,
    b_3 = n^2(n-2)(n-1)^2(n+1)/144,
    b_4 = n^2(n-3)(n-2)^2(n-1)^2(n+1)/2880.

A second application gives

    c_1 = (n-1)^4,
    c_2 = n^2(n-1)^4(n+2)/16,
    c_3 = n^3(n-2)^2(n-1)^4(n+1)(n^2+n+18)/51840.

It follows by subtraction and factorization that

    (L^3(a))_2
       = -n^3(n-1)^8(n+4)Q(n)/103680,

where

    Q(n)=2n^4-12n^3-327n^2-412n+36.

Set n=u+17. Then

    Q(u+17)=2u^4+124u^3+2529u^2+17370u+6615.

Every coefficient on the right is positive. Therefore Q(n)>0 for every real n>=17, in particular for every integer n>=17. All other factors outside the minus sign are positive, proving that every C_n with n>=17 fails 3-log-concavity.

The accompanying verifier checks the polynomial identity over Q[n] using exact rational polynomial arithmetic written with Python's standard library; it does not rely on a symbolic-algebra package.

## A boundary-independent variant

If one instead applies the local rule only where both neighbors are present and deletes the two endpoints at each iteration, take

    G = C17 disjoint union K1.

Adding an isolated vertex multiplies the chromatic polynomial by q. Its coefficient sequence is the above one shifted by one position. The same negative value occurs at degree 3 after three applications of the local rule. It depends only on the original coefficients at degrees 0 through 6, all of which exist. In particular, degree 3 remains in the valid range after three rounds of deleting endpoints. Thus this 18-vertex graph refutes the claimed universal property even under the endpoint-deleting interpretation.

Similarly, C12 disjoint union three isolated vertices gives a 15-vertex, five-iteration certificate entirely inside the original coefficient range.

## Smaller-cycle certificate

For C12 the absolute coefficient sequence is

    (0,11,66,220,495,792,924,792,495,220,66,12,1).

After four applications of L, the entries at degrees 1, 2, and 3 are

    45949729863572161,
    1505318939996586804452286,
    54746933663864342589859620161140.

Their middle square minus the product of its two neighbors is

    -249621701601023742801969101519201265582387397744.

The verifier confirms all entries in the preceding four iterates are nonnegative. We make no claim that C12 is a smallest counterexample among all graphs.

## Verification artifacts

- `verify_cycle_counterexample.py`: dependency-free exact proof checks, including a separate deletion–contraction calculation of the cycle polynomials.
- `exact_certificates.json`: complete initial and iterated sequences for C12 and C17, plus the symbolic factorization and shifted positivity certificate.
- `status_search_20261008.md`: sources and the scope/limits of the public-status search.


## Appendix: complete classification of cycles

Under the standard zero-extension convention, the absolute chromatic coefficient sequence of C_n is infinitely log-concave **if and only if 3<=n<=11**.

The negative direction for n>=17 was proved above. For n=12 the fifth-iterate certificate was given above. For n=13,14,15,16, the entry at degree 2 in the fourth iterate is, respectively,

    -3618341131654935620812800,
    -199158562975246657489530096,
    -2734560032125157358883149375,
    -25982668618402950000000000000.

For the positive direction use the following elementary invariant. Say a nonnegative sequence is 3-factor log-concave when a_i^2 >= 3a_(i-1)a_(i+1) at every index, with zero extension. If b=L(a), then

    (2/3)a_i^2 <= b_i <= a_i^2,
    b_(i-1)b_(i+1) <= a_(i-1)^2 a_(i+1)^2 <= a_i^4/9,

so b_i^2 >= 4b_(i-1)b_(i+1), and in particular b is again nonnegative and 3-factor log-concave. Induction proves infinite log-concavity from any 3-factor iterate, provided all preceding iterates were nonnegative.

For 3<=n<=11, the following table specifies an iterate j at which the sequence is 3-factor log-concave. The last column is the minimum exact slack b_i^2-3b_(i-1)b_(i+1) over 2<=i<=n-1 for b=L^j(a). The omitted index i=1 has the automatically positive slack b_1^2 since b_0=0; the two endpoints are also automatic.

| n | j | minimum slack |
|---|---|---|
| 3 | 0 | 3 |
| 4 | 1 | 28 |
| 5 | 2 | 25825 |
| 6 | 2 | 90846 |
| 7 | 2 | 271656 |
| 8 | 3 | 711608924160 |
| 9 | 3 | 4029124698225 |
| 10 | 3 | 19225238518750 |
| 11 | 3 | 79738750726206 |

All preceding iterates are nonnegative. The exact verifier checks every entry and every inequality, stores the certifying sequences, and verifies the four negative values for n=13,...,16. Thus this classification requires only finitely many transparent integer computations in addition to the symbolic n>=17 proof and the invariant lemma.
