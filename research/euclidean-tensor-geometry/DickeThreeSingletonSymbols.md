# Dicke entropy formula for three singleton symbols

**Yongxian Zhang.** Research note (AI-assisted proof development and verification).

For k≥5, let S consist of permutations of (0^{k−3},1,2,3). Write L=k(k−1)(k−2), and h for the entropy of ((k−3)/k,1/k,1/k,1/k). Then the asymptotic induced matching number, and asymptotic subrank for every tensor with this support over every field, both equal exp(h) when h uses natural logarithms.

Use natural logs throughout (convert the theorem's base-2 logs by multiplying inequalities by ln 2). The standard slice-rank argument and full-rank collision argument are identical to [the two-singleton note](DickeTwoSingletonSymbols.md). For k=5,6 [the previous exact finite verification](dicke-order-six/README.md) covers both types (2,1,1,1) and (3,1,1,1). Below let k≥7. Encode the three singleton symbols by products of two of three distinct primes, with a different prime omitted for each symbol; encode 0 by 0. Then reducing differences modulo an omitted prime isolates its singleton symbol. Subtract the constant sum of all symbol encodings from the encoding on the last party to satisfy tightness.

For any collision set in higher-order CW with rational difference rank r≥1 and some fixed shared coordinate, induce three equivalence partitions as in [the two-singleton note](DickeTwoSingletonSymbols.md). In each partition sum of class sizes minus one is ≤r. The shared coordinate has singleton class in every partition because the difference reduction has zero there. For each pair of words, their ordered triple U of singleton equivalence classes agrees. Under any allowed collision law Q each individual singleton position is uniform. Therefore
 H(Q) ≤ ln L + H(Y|U(Y)) ≤ ln L + 3(r+1)ln(r+1)/k.
The target CW estimate is H(Q) ≤ ln L + r(ln L−h)/(k−2), and the full rank r=k−2 is handled using the entropy h of the common coordinate exactly as before.

If r≤k−4, monotonicity of (r+1)ln(r+1)/r reduces the comparison of these two bounds to r=k−4. Using ln L−h=ln(k−1)+ln(k−2)+(k−3)ln(k−3)/k and abbreviating t=k−3, the comparison rearranges to
 (t+3)[ln(1+2/t)+ln(1+1/t)] ≥ 6 ln t/(t−1).
For t≥4 the left is at least (t+3)[2/(t+2)+1/(t+1)]≥3. The right is at most 2 ln 4<3 by monotonicity of ln(t)/(t−1).

For r=k−3 write x=k−2≥5. The excess of the naive bound 3x ln x/k over the target term, multiplied by k, is
 B=3 ln x/x − ((x−1)/x)[(x+2)ln(1+1/x)+(x−1)ln(1−1/x)] < 3 ln x/x.
Indeed the bracket is positive, since its two terms sum to at least (x+2)/(x+1)−1>0 by the usual bounds a/(1+a)≤ln(1+a)≤a.

Suppose at least one equivalence partition does not have any class of size x (the maximum allowed). Among such partitions the convex sum of |C|ln|C| is at most (x−1)ln(x−1)+2ln2: total deficit sum(|C|−1) is at most x−1 and each deficit ≤x−2, so it is maximized by deficits x−2 and 1. This saves at least
 Δ=x ln x−(x−1)ln(x−1)−2ln2
   ≥ ln x+1−1/x−2ln2 ≥ 3 ln x/x.
The last inequality holds at x=5 and continues because (1−3/x)ln x+1−1/x−2ln2 is increasing for x≥5. Uniform singleton positions make the actual entropy saving Δ/k.

In the remaining case each partition has a class of size x, omitting the same fixed shared coordinate and one other coordinate. Any pair of these large classes intersects in at least x−1 positions. Condition on a triple of classes drawn as U(Y), let g count how many are large, and temporarily allow independently chosen positions from the classes. If two chosen classes are large, the event their positions coincide has fraction at least (x−1)/x² of the allowed product. If three are large, the union of the forbidden equality events has fraction at least [3x(x−1)−2x]/x³: each equality contributes at least x(x−1) triples, and any pairwise intersection (and the triple intersection) is the common-position set of size at most x, so subtract twice its size. Thus the valid number of tuples is at most the product of class sizes times 1−δ_g, where δ_g≥binom(g,2)(x−5/3)/x² (also holds trivially for g≤1). The conditional entropy bound by log support saves at least δ_g, using −ln(1−δ_g)≥δ_g. Each of the 3 index pairs is jointly in its large classes with probability at least 1−4/k by the union bound and uniform singleton locations. Averaging the savings gives at least (k−4)(3x−5)/(kx²), which covers B/k because
 (k−4)(3x−5)/x²=(x−2)(3x−5)/x² ≥ 3 ln x/x
for x≥5 (left increasing and right decreasing; check at 5). This gives the target at r=k−3.

Therefore every collision-rank case in higher-order CW attains the target and the entropy formula holds in this family. The proof requires the structural validity of the existing finite certificates for k=5,6; the dimension-free bound resolves all larger orders. No claim on the unrestricted Dicke conjecture.
