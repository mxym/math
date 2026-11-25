# An explicit quadratic defect bound for all odd periodic twelve-cycle dimensions

Yongxian Zhang. AI-assisted proof development and internal checks; no external peer review claimed.

In the shared-site complex periodic twelve-cycle model of [Gesmundo–Landsberg–Walter](https://arxiv.org/html/1801.09106#S1.SS4), let F12(q) be the maximum odd-even flattening rank with common physical and bond dimension q. Write q=2r+1. Then
```
F12(q) >= q^6 - 30r^2 + r.
```
The proof is uniform in r: its finite-field arithmetic concerns signed multiset types involving at most five opposite classes, not a limited scan of dimensions. It does not determine F12(q) in general. Accordingly the upper bound for q congruent to 3 mod 4 remains q^6-1 as in GLW Theorem I.3, and the lower bound below may have a quadratic gap. For dimension three use the separate exact rank 728 witness.

## Base and mixed blocks

Index the physical and virtual symbols by 0 and r opposite pairs {a,-a}. Put
```
A_0 = E_00,             A_a = E_(0,a) + c_a E_(-a,0),  a != 0
```
with independent nonzero complex parameters c_a. At the base every closed virtual walk with core labels uses a unique dimer tiling of the interleaved noncore sites: a dimer consists of the outgoing a and returning -a steps at the same leaf, giving c_(-a), and each zero is a hub monomer. Starting at any specified zero fixes the tiling; if the tiling is impossible the trace is zero.

Relabel the column words by global sign negation. Every dimer includes one odd and one even position, so M preserves the signed multiset of noncore labels in the relabeled columns. The rotation R of both length-six words commutes with M. On each eigenspace of R use input orbit sums weighted by successive powers of a sixth root, keeping exactly the orbits on which those weights are well-defined; the matrix output is evaluation at each least representative. Rotation and column sign relabeling commute.

For a mixed block (at least one zero), let n≤5 count noncore labels. Its signed multiset up to class relabeling and sign flips is uniquely described by a sorted list of pairs (a,b) with a≥b≥0 and a+b>0, recording multiplicities of the two signs in each used class, summing to n. The script `check-base.py` enumerates exactly those profiles, computes the full rotation blocks via the dimer formula modulo 1009, and verifies their ranks. With the sole exceptions below the entire block is invertible at its modular evaluation:
```
profile                             rank defect at most
((1,1),)                                         5
((2,2),)                                        20
((1,1),(1,1))                                   60
```
No symbolic upper bound on these exceptional generic ranks is needed. These modular values give the stated lower bounds in characteristic zero: over a field containing sixth roots, the computations are a decomposition of matrices with integral entries, so full rank and total-rank lower bounds lift by a single nonzero integral minor. All finitely many per-instance minor conditions can be imposed at once with generic c because each is nonzero on its own after class relabeling. Thus mixed base blocks cost at most 25r + 60 binom(r,2) dimensions in total.

For zero-core words there are only the two possible global dimer alignments. In each rotation orbit the block is a scalar multiple of I plus a scalar multiple of R or its inverse. The two coefficients are the products of the c's of opposite signs in that multiset. They agree identically iff the signed multiset is balanced (equal multiplicity of the two signs in each class). In nonbalanced multisets generic c make every block invertible. In balanced multisets only the -1 sector is singular, and its entire block is zero. All balanced words have even rotation period (either 2 or 6); if the period divided 3, repeating a word of odd length three twice could not give balanced counts. There are three balanced profiles, specified by the multiplicities of sign pairs:
* three copies of one pair: 20 words per class, exactly two of period 2; the defect is (20-2)/6+2/2=4 per class;
* two copies of one pair plus one of another: 180 words per ordered pair of different classes, all period 6; defect 30 per profile;
* one copy of each of three distinct pairs: 720 words, defect 120 per unordered triple of classes.

## Quadratic perturbation

Add to each noncore slice t times arbitrary diagonal loops at both leaves of its own opposite class. Add to the core slice t times arbitrary tilted returns from every leaf to the hub. A factor of t is a mark in that leaf's class. At degrees at most two every contributing closed walk visits the hub (a trace confined to a leaf for all 12 steps would have degree 12). During each hub excursion all noncore sites have the same class; a loop increases its noncore count by one and a tilt decreases it by one. In the whole word, the parity of the noncore count in each class equals the parity of its number of marks. The difference of row and column counts in each class has magnitude at most the number of its marks: unmarked dimers are balanced, while a marked excursion has a contiguous run of noncore positions (possibly followed by a tilted zero return), whose alternating difference has magnitude at most one. These bounds also hold along chains joined by a base inverse because that inverse preserves the multiset.

Work in the rotation -1 sector. Retain every zero-core balanced block of the second and third profiles (call their direct sum K). Omit the four zero-core coordinates per class of the first profile. In all remaining nonzero base blocks choose base minors of size at least the guaranteed rank and omit any unused coordinates. The resulting submatrix has an invertible base complement B_0 and the retained null coordinates K. All first-order entries on K×K vanish by the parity rule. The leading Schur coefficient there is
```
H = M_2[K,K] - M_1[K,B] B_0^(-1) M_1[B,K].
```
This formula applies to row and column indexed pivot sets separately. In fact any first-order intermediate reached from K has exactly five noncore labels in the relabeled convention. A tilt deletes one signed label. For a loop, the affected three-site excursion has its opposite-signed endpoints on the same parity and its single middle loop on the other parity, so after column sign relabeling the counts differ by deleting whichever of the endpoint signs is not retained. Thus only the signed multisets obtained by deleting one letter from K are possible. Their base blocks are full (all n=5 profiles passed), so B includes each of those entire blocks. The reversed direction has the same support statement, by transposing the original alternating matrix and rotating one word.

At degree two the marks must lie in the same class in any K-to-K entry, since all class counts of both endpoints are even. A difference between two distinct six-label profiles would require changing at least two classes; hence H is block diagonal on balanced zero-core signed multisets. It is local to the classes of each profile. In a Schur chain the intermediate is a single deletion and cannot introduce a different class. In a direct trace a leaf excursion necessarily starts with a noncore label of that leaf's class, so no hidden outside class can occur.

The companion `check-jet.cpp` computes these local H matrices exactly over F_1009, using sparse trace arithmetic through degree two and the full -1 blocks of the deletion profiles for B. For the second and third cases, H sizes are 30 and 120 with determinants 111 and 793 respectively. The B denominators are nonzero modulo 1009, so these certify that the corresponding complex rational determinant functions are not identically zero. (The program reports zero for the omitted one-class trial, which is not a claimed universal obstruction.) Local nonvanishing holds simultaneously generically, by taking the intersection of finitely many nonempty algebraic open sets. Therefore the retained submatrix has determinant with nonzero leading coefficient in t after the two powers of t per K coordinate; choose a complex t avoiding the zeros. The total remaining defect is at most
```
25r + 60 binom(r,2) + 4r = 30r^2-r.
```

Replay with `python3 check-base.py` and `c++ -std=c++17 -O3 check-jet.cpp -o check-jet; ./check-jet`. The output logs identify the verified profiles, their sector defects, and the local jet determinants. No finite-field maxima or formal-verified status is claimed.
