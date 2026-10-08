# The unique runner-up among homogeneous simplex product–join recursions

**Companion result to entry 005, October 7, 2026.** This note strengthens the
complete independent-arity classifications published in
[the first exact proof](PROOF.md) and the
[parallel shorter-tail proof](../unbalanced-homogeneous-projection-recursion/paper.md).
The assertion is about fixed integer arities and simplex seeds, not arbitrary
operation trees. It is AI-assisted mathematical work; no independent human
referee or literature-wide novelty certification is asserted.

## 1. Sharp second-place classification

For each positive integer triple (m,k,p), let T_p denote any p-simplex, let
K_0=T_p and K_(j+1)=(K_j^m)^{*k}. For the projection-body ratio
R(K)=|Pi K|/|K|^(dim K-1), put
\[
\Lambda_{m,k,p}=\lim_{j\to\infty}R(K_j)^{1/\dim K_j}.
\]
Both cited first-place notes establish the existence of this limit and
identify (m,k,p)=(2,2,5) as its unique global maximizer.

**Theorem (unique second place, with a uniform third-place gap).**
For every triple of positive integers other than
(2,2,5) and (2,2,6),
\[
\boxed{\log\Lambda_{m,k,p}<L_2:=\frac{10479}{10000}=1.0479.}
\tag{1}
\]
On the other hand,
\[
\boxed{
L_2<\log\Lambda_{2,2,6}
<\frac{131}{125}
<\log\Lambda_{2,2,5}.
}
\tag{2}
\]
Hence **(2,2,6) is the unique runner-up**, and the infinite family has a
positive, explicitly certified gap between second place and every lower place.

The strict separation in (1), and the first inequality in (2), are **new**
relative to the two earlier first-place classifications. The previous
first-place theorem supplies the latter two inequalities in (2).

## 2. The same universal bound at a smaller threshold

We recall the exact formula, including its full scope, to make the threshold
change auditable. For m,k>=2 put
\[
T=mk,\qquad c=\frac{k-1}{T-1},\qquad
A_p=\log\bigl((p+1)p^p/p!\bigr),\qquad
q=\frac{k-1}{2}\log(m/k).
\]
For every integer J>=0,
\[
\log\Lambda_{m,k,p}
<\frac{
  A_p+\sum_{j=0}^{J-1}T^{-j-1}\log D_j
  +T^{-J}\left(\frac{C+Jq}{T-1}+\frac{q}{(T-1)^2}\right)
}{p+c},
\tag{3}
\]
where
\[
d_j+c=(p+c)T^j,\quad a_j=((p+1)k^j)^{-1},\quad
D_j=k a_j^{k-1}\frac{g(Td_j+k-1)}{g(md_j)^k},
\]
\[
g(n)=n^n/n!,\qquad
C=\tfrac12\log k+(k-1)\left[
1+\tfrac12\log(2\pi m(p+c))-\log(p+1)
\right]+\frac{k}{12mp}.
\]
These formulas and their strict Robbins--Stirling derivation appear in the
first [independent-arity proof](PROOF.md), Sections 2--3. The recurrences
and upper bound do not depend on the threshold used later.

In this note only, set
\[
L=L_2,\qquad \epsilon=L-1=479/10000,\qquad
\delta_p=Lp-A_p,
\]
and
\[
h_{m,k,p}=-\epsilon+
\tfrac12\log(2\pi m(p+c))-\log(p+1),
\]
\[
E_{m,k,p}=
\frac{\log k}{2(T-1)}
+\frac{k}{12mp(T-1)}
+\frac{c}{2(T-1)}\log(m/k).
\]
The J=0 bound in (3) is less than L **if and only if**
\[
\boxed{\delta_p>c\,h_{m,k,p}+E_{m,k,p}.}
\tag{4}
\]
This follows by expanding C and using c=(k-1)/(T-1), exactly
as in Section 3 of the first proof. The parameter-space decomposition
below certifies (4) outside a small exceptional finite core.

## 3. Exhausting three infinite tails

All analytic estimates used here are stated and proved in
[PROOF.md, Sections 4--5](PROOF.md). They are algebraic in L and
apply without alteration after replacing the specific slack
6/125 by the new rational \epsilon=479/10000.
For clarity, the strict new endpoint tests are specified here.

**Seed gap.** For every integer p=1,...,31, the exact checker
bounds
\[
\delta_p>\frac3{20}.
\tag{5}
\]
For real p>=32, Robbins gives
\[
\delta_p>\phi(p):=\epsilon p-\log(p+1)
+\frac12\log(2\pi p)+\frac1{12p+1}.
\]
Its derivative satisfies
\[
\phi'(p)\ge\epsilon-\frac1{33}
-\frac{12}{385^2}>0\quad(p\ge32),
\]
and the exact checker verifies \phi(32)>2/3. Hence
\[
\delta_p>2/3\quad(p\ge32).
\tag{6}
\]

**Large product arity.** For m>=32, all k>=2, p>=1, the elementary
bound in PROOF.md, Lemma 5.1, gives
\[
c h+E\le
\frac{\frac12\log(\pi m)-\epsilon}{m}
+\frac1{4(m-1/2)}
+\frac1{12m(m-1/2)}
+\frac{\log m}{2m(2m-1)}.
\tag{7}
\]
The right side decreases for m>=32; its value at 32 is rigorously less
than 3/20. Combine this with (5)--(6).

**Large seed dimension.** For 2<=m<=31, k>=2, p>=32,
\[
h\le\frac12\log\frac{62\pi}{33}-\epsilon<17/20,\qquad
E<1/6+1/1152+1/25.
\]
Since c<=1/2, the total is less than 2/3, proving (4)
with (6).

**Large join arity.** For 2<=m<=31, p<=31, k>=32,
the logarithmic slope q is nonpositive. Put
\[
H_{m,p}=-\epsilon+
\frac12\log\bigl(2\pi m(p+1/m)\bigr)-\log(p+1).
\]
When (m>=3 or p>=8), the same monotonicity argument as in
PROOF.md, Lemma 5.3, bounds
\[
c h+E\le
\frac{\max(0,H_{m,p})}{m}
+\frac{\log32/64+1/(12mp)}{m-1/32}.
\tag{8}
\]
For m=2,p<=7, the stronger one-level inequality
from PROOF.md, Lemma 5.4, applies. All 923 regular and seven
exceptional rational comparisons are **rechecked at L=L_2**, not
inferred from success at L=1.048.

Thus every positive-integer parameter outside
2<=m,k<=31 and p<=31 satisfies \log\Lambda<L,
except possibly the pure-product / pure-join boundary arities.
These also satisfy the stronger bound: m=1 gives limit e,
and k=1 gives A_p/p<L by (5)--(6).

## 4. Finite core and exactly two survivors

For 2<=m,k<=31, 1<=p<=31, evaluate the J=0 upper
bound of (3) for every m>=3 or p>=8, with exact rational logarithmic
intervals; these give 27,690 strict exclusions.
For m=2,p<=7 use the J=3 restart, excluding all 208
triples outside the set
\[
\{(2,2,5), (2,2,6)\}.
\]
The values of \log\Lambda are not estimated by floating point:
the checker encloses every \log x using finite rational atanh sums
and an analytic remainder; \pi has a rational Machin-series enclosure;
g(n) uses exact factorials for n<=20 and Robbins bounds for n>=21.
All signed terms use correctly directed endpoints.

The accompanying [exact executable certificate](check_second.py)
checks 27,690+208+930 = 28,828 strict finite/endpoint inequalities,
plus analytic cutoff inequalities for each infinite parameter region.
No inference from a finite grid to an infinite domain is made without
the displayed monotonicity or convexity argument.

## 5. Certified strict runner-up lower bound

It remains to distinguish the two surviving triples.

For the (2,2,6) orbit, recurrence (2.1) gives
\[
d_j=\frac{19\,4^j-1}{3},\quad
a_j=\frac1{7\,2^j},\quad R_{j+1}=R_j^4D_j .
\]
The elementary central-binomial inequality used in
[005 v5, Section 9](../../preprints/005-simplex-product-optimum/v5/paper.md)
says
\[
\frac{g(2q+1)}{g(q)^2}>
2\sqrt{3q+1}\qquad(q\ge1).
\]
With q=2d_j, this yields
\[
D_j>4a_j\sqrt{6d_j+1}
=\frac47\sqrt{38-4^{-j}}
\ge\frac47\sqrt{37}>3,
\tag{9}
\]
the last strict inequality being the integer comparison 16*37>9*49.

For any J>=0, the exact limiting series gives
\[
\log\Lambda_{2,2,6}>
\frac{3\log R_J+\log3}{3d_J+1}.
\tag{10}
\]
Take J=5, when d_5=6485. We determine a rigorous *lower* interval for
\log R_5, with no huge factorials or floating-point logarithms:
\[
\log R_0=\log 7+\log g(6),
\]
\[
\log R_{j+1}
=4\log R_j+\log2-\log7-j\log2
+\log g(4d_j+1)-2\log g(2d_j).
\tag{11}
\]
Each \log g(n) is bounded from both sides by exactly the same
proved factorial-log intervals as the upper certificate. The independent
reconstruction in check_second.py certifies the **strict rational
inequality**
\[
\boxed{3\,\underline{\log R_5}+\underline{\log3}
>L_2(3\cdot6485+1).}
\tag{12}
\]
Combining (10) with (12) proves the first inequality in (2).

Finally, the earlier first-place classification (or its replayed J=3
bound at p=6) gives
\[
\log\Lambda_{2,2,6}<131/125,
\]
while the 005 v5 exact integer witness proves
\[
\log\Lambda_{2,2,5}>\log(14267/5000)>131/125.
\]
This yields the strict first/second/third ordering claimed in (1)--(2).
\(\square\)

## 6. Reproducibility and trust boundary

Run, from repository root:

~~~sh
python3 notes/independent-arity-simplex-recursions/check_second.py
python3 -O notes/independent-arity-simplex-recursions/check_second.py
python3 notes/independent-arity-simplex-recursions/check.py
python3 notes/unbalanced-homogeneous-projection-recursion/checker.py
~~~

The ordinary and optimized runner-up reports must be byte-identical.
The runner-up program is a separate complete frozen checker using
standard-library integer and Fraction arithmetic, not a numerical
optimization output. The earlier upper-bound proofs and the 005 v5
geometric and lower-endpoint inputs remain explicit dependencies.
The two first-place classifications offer different tail partitions;
this new result is *not* being counted as a second discovery of
the already-completed first-place theorem.

No theorem here concerns nonhomogeneous operation trees or non-simplex
seeds, and no first-in-literature or human peer-review claim is made.
