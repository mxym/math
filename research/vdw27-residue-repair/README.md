# W(2,7): baseline and a local repair obstruction

Research checkpoint, 10 October 2026. **No new van der Waerden bound or exact value is claimed. This is not a completion release.**

The known W(2,7)>3703 residue construction is reconstructed in BASELINE.md. The earlier remote blob was only an unattached checkpoint; this directory makes the record reachable from the repository.

## Finite local theorem

Let C color positions 1,...,3704 as follows. Set C(1)=1 and C(i)=0 for other i congruent to 1 modulo 617. At the remaining positions let C(i)=1 exactly when i-1 is a nonzero quadratic residue modulo 617.

Every coloring of 1,...,3704 without a monochromatic seven-term arithmetic progression differs from C in at least six positions.

### Proof

The progression E={2+617j:0<=j<=6} has color 1 in C. Any valid coloring D must change some v in E to 0. For each such v the explicit certificate in verify.cjs supplies five progressions P_1,...,P_5 through v. Every other vertex of these progressions has color 0 in C, and the five sets P_j minus {v} are pairwise disjoint. As D(v)=0, D must change at least one vertex in each of those five sets to 1. These changes are distinct and different from v. Thus D differs at at least six positions. This is a finite, elementary certificate proof; the checker verifies every assertion about all 35 progressions.

## Reproduction and audit

Run `node verify.cjs`. The checker uses BigInt modular exponentiation for Euler's criterion, independently of the original square-enumeration construction. It also enumerates all 1,140,833 progressions in the first 3703 positions (zero violations), verifies all petals, and rejects a deliberately corrupted certificate.

Expected certificate conclusion: minimum Hamming distance at least 6 from this one specified length-3704 template. There is **no assertion** that distance 6 is attainable, that other templates fail, or that W(2,7)=3704. No Lean, CI or external review is claimed.

## Research consequence

One-bit repair and, more generally, radius-five repair of this particular extended coloring cannot improve the known bound. Any constructive continuation around it must change at least six bits. This small obstruction is a search diagnostic, not a major solution or a claimed new literature result.

## Source

Herwig, Heule, van Lambalgen and van Maaren, *A New Method to Construct Lower Bounds for Van der Waerden Numbers*, Table 1 and Section 4.2, attributes the bound to Rabung: https://www.cs.utexas.edu/~marijn/publications/waerden.pdf .
