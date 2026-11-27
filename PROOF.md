# Four affine forms always have a bounded-degree certificate

## 1. Statement and scope

Let m≥2 and let g_1,…,g_m be nonzero real affine-linear forms on the n-variable Boolean cube C={0,1}^n; nonzero constants are also allowed. Put Z_i={x∈C:g_i(x)=0}. Assume ∪_i Z_i=C and ∩_i Z_i=∅. Thus the forms obey both the pointwise product-zero and no-common-zero assumptions in Kothari et al., Conjecture 1. A certificate is a tuple p_i of real multilinear polynomials such that ∑_i p_i=1 pointwise on C and p_i|_(Z_i)=0. Its degree is the largest degree of a nonzero p_i.

This is equivalent to the original reduced-product formulation: from h_i take p_i to be the unique multilinear representative of h_i g_i on C. Conversely, for a given p_i define a function h_i on C equal to p_i/g_i where g_i≠0, and 0 on Z_i, and interpolate it on C. Then the multilinearization of h_i g_i is precisely p_i. This equivalence does not bound the degree of h_i itself.

**Theorem.** For m≤4 there is always a certificate of degree at most min(n,80), even with each p_i taking values only in {0,1}. There are families with m=5 affine forms requiring unbounded certificate degree. Consequently the exact least number of affine forms for an unbounded-degree counterexample is five. The lower-bound family is the five-form example of Rajagopalan–Saurabh; its exact optimum, and that of their three-quadratic example, are verified in Section 4.

## 2. Localization of a minimal affine zero cover

Choose an inclusion-minimal subset I⊆{1,…,m} whose zero sets cover C; such a subset exists because the family is finite. Write k=|I|. No nonzero affine form vanishes everywhere on a Boolean cube, so k≥2. For each i∈I, the product of the other chosen forms is nonzero as a function on C, by minimality. Its real multilinearized degree is at most k−1 and its support is contained in Z_i, since the chosen zero sets cover C.

A nonzero multilinear function of degree at most d on the n-cube has nonzero fraction at least 2^(−d). Here is a brief proof for completeness. For actual degree d>0 choose a variable in some degree-d term and slice at its two values: the difference is nonzero of degree at most d−1. On every lower-dimensional point where this difference is nonzero, at least one slice is nonzero. Induction on d gives the fraction bound, and degree 0 is constant. Applying this to the product shows
```
           |Z_i| / 2^n ≥ 2^(1−k)      (i∈I).                     (1)
```

Let ℓ_i be the number of variables whose coefficients in g_i are nonzero. Its density of zeros is at most
```
           b(ℓ_i) = C(ℓ_i,floor(ℓ_i/2)) / 2^ℓ_i.                (2)
```
Indeed flip the variables with negative coefficients so that all ℓ_i relevant coefficients are positive. Among subsets of those coordinates, equal weighted sums form an antichain. A uniformly random maximal chain encounters at most one member, and encounters each particular t-subset with probability 1/C(ℓ_i,t). Summing implies the claimed central-binomial bound. Irrelevant coordinates leave the density unchanged.

The sequence b(ℓ) is nonincreasing: b(2s−1)=b(2s) and b(2s+1)=b(2s)(2s+1)/(2s+2). Direct comparison at the boundary gives the largest possible ℓ_i from (1)–(2):
```
       k                         2        3        4
       largest ℓ with b(ℓ)≥2^(1−k)        2        8       40.
```
For k=4 the comparison is C(40,20)≥2^37 and C(41,20)<2^38; the k=2,3 comparisons are C(2,1)/4≥1/2>C(3,1)/8 and C(8,4)/2^8≥1/4>C(9,4)/2^9. No estimate of these thresholds depends on n.

Let J be the union of the coordinates occurring in the chosen forms. Each coordinate in J occurs in at least two of them. Otherwise let t occur only in g_i within I. By minimality some assignment avoids all Z_j with j∈I\{i}. Both its original and its t-flipped version still avoid those sets, so coverage forces both to lie in Z_i, contrary to the nonzero coefficient of x_t. Hence
```
          |J| ≤ (1/2) Σ_(i∈I) ℓ_i ≤ 2, 12, 80
          for k=2,3,4 respectively.                            (3)
```
The underlying high zero-density observation and the Littlewood–Offord step are the k=3 argument already used by Rajagopalan–Saurabh. The localization here keeps only a minimal cover and treats the unused forms afterwards; the shared-coordinate observation gives (3).

## 3. The certificate and the unused form

If k=2, each chosen zero set occupies at most half the cube by (2) (a chosen form cannot be a nonzero constant). Since they cover, their zero sets are disjoint. Define p_i=1 when g_i≠0 and 0 otherwise for the two chosen forms, and set all other p_i=0. Exactly one chosen form is nonzero at each vertex, so this is a certificate depending on only the coordinates J.

If k≥3 and m≤4, there is at most one unused form. For each assignment z∈{0,1}^J examine the values of all chosen forms, which are fixed throughout that fiber. If one is nonzero, choose the least-indexed such form. If they are all zero, there must be an unused form (by the no-common-zero condition); it is unique, and is nonzero at every vertex of the fiber. Choose it. Define p_i as the indicator that this rule chose i on the assignment to J. A multilinear polynomial for each such indicator is the sum of indicators of its assigned patterns on J, each a product of |J| literals. Thus degree≤|J| and p_i vanishes where g_i does. Equation (3) proves the theorem. In particular no condition on the variable count of an unused form is needed.

More generally, for any finite number of affine forms, this minimal-cover argument localizes the remaining certificate problem. On every J-fiber where all chosen forms vanish, the restricted unused forms have no common zero, and the product-zero condition is not required of them. Any global certificate restricts to one supported on those unused forms there. Conversely certificates on these fibers can be glued by the same J-pattern indicators, adding at most |J| to their largest reduced product degree; on the other fibers one chosen form is enough. This explains why one unused form is harmless, while two may carry the existing high-degree separation. This observation is not a claim to have classified optimal certificate degrees for m≥5.

## 4. The exact degree in the published examples

For n≥2 use variables x_1,…,x_n,y_1,…,y_n and let u=Σ x_i, v=Σ y_i. Put U=u and V=u+v−(n+1). Their zero sets are disjoint since u=0 implies u+v≤n. Write Z_U and Z_V for those zero sets.

The following known separator bound is Kothari et al., Fact 7, and was reused by Rajagopalan–Saurabh. A function on this cube with values 1 on Z_U and 0 on Z_V has multilinear degree at least n. To verify it, symmetrize its polynomial over all permutations of x-coordinates and, independently, y-coordinates. Each monomial with i x-variables and j y-variables averages to the polynomial C(u,i) C(v,j)/[C(n,i) C(n,j)], so the resulting polynomial P(u,v) has no larger total degree and agrees on the two symmetric zero sets. If deg P<n, P(0,t)−1 vanishes for t=0,…,n, so is identically zero. But P(s,n+1−s) has n distinct roots s=1,…,n and value 1 at s=0, impossible for degree less than n. On the other hand the indicator of Z_U, Q(x)=∏_(i=1)^n(1−x_i), itself provides a separator of degree n.

**Five affine forms (Rajagopalan–Saurabh, Proposition 26).** The family is
```
             x_1, x_2, x_1−x_2, U, V.
```
The first three zero sets cover the cube (both binary coordinates equal, or at least one is zero). On Z_U the first four vanish, but V never vanishes. Thus the full family covers with no common zero. In any certificate p_5 must equal 1 on Z_U and 0 on Z_V, so its degree is at least n. This is the already published lower bound. It is attained by p_5=Q, p_4=1−Q, all others zero: Q vanishes on Z_V, and 1−Q vanishes on Z_U. This proves that the optimum is exactly n.

**Three quadratics (Rajagopalan–Saurabh, Theorem 6).** Put t=x_1+x_2 and use
```
             U t,    U(t−1),    V(t−2).
```
Coverage follows because t∈{0,1,2}. At a common zero of the first two, U=0 (t and t−1 cannot both vanish), which forces t=0 and V≠0; hence the third form is nonzero. All three reduced polynomials have degree two for n≥2. On Z_U the first two vanish, and on Z_V the third vanishes. Therefore p_3 is again a separator, of degree at least n. Define p_3=Q, p_1=1_(t≥1)=x_1+x_2−x_1 x_2, and p_2=1−p_1−p_3. The supports are respectively u=0, t≥1, and t=0 with u≠0. On each of these parts the associated third, first and second form is nonzero, so the three p_i form a certificate of degree at most n. Thus the published lower bound is exact also for this family.

No general conclusion about higher-degree polynomials, or about the unmultiplied degree of the h_i, is asserted.
