# Real two-step paths to 3 in planted dyadic factor graphs

Written corollary, 2026-11-24. Work on the actual prime-label graph at \(N=2^k\), with a directed edge \(u\to v\) if \(v\) is prime and divides \(N-u\). A common endpoint below is an actual directed claim about the indicated labels, not a bound on the size of one terminal component.

Use the exact planted square-root window \(I=(a\sqrt N,b\sqrt N]\) with \(0<a<b<1\), the notation \(L=\log N\), and \(B_0\) of the [planted P4 theorem](PrimeOppositeSquareRootPlantedP4.md).

## Actual high children from the original two-level profile

Keep exactly the construction in [the two-level dictionary](DyadicTwoLevelPlantedDictionary.md). Thus \(T=\log\log N\), \(d=\prod_{3\le\ell\le cT,\ \ell\ {\rm prime}}\ell\); the second dictionary is
\[
 V=\{v\ {\rm prime}:2cT<v\le5cT,\ v\nmid d-1\}.
\]
Its profile gives \(p\to3\) for every selected root once \(N\) is large. Each row with no quotient prime at or below \(\sqrt N\) has a single quotient prime \(q=(N-p)/d>\sqrt N\). Such \(q\)'s are distinct over their roots because the root window has width \(<\sqrt N<q\) and all parents of \(q\) are in one class modulo \(q\). Each genuine high row has \(q\to v\) for all \(v\in V\), by the exact valuation property.

Among primes in \((2cT,5cT]\), the fixed residue \(v\equiv N\bmod3\) has \((1.5c+o(1))T/\log T\) members by the prime number theorem in the two reduced mod-3 classes. At most \(\log(d-1)/\log(2cT)\le(c+o(1))T/\log T\) distinct primes in the whole interval can divide \(d-1\). Thus \(V\) contains at least \((.5c+o(1))T/\log T\) primes \(v\equiv N\bmod3\). Every such \(v\) has the genuine edge \(v\to3\). Consequently each high rank-one quotient prime has that many internally disjoint length-two paths \(q\to v\to3\). If this high branch supplies a fixed positive fraction of \(B_0\) roots, it supplies \(\gg B_0\) different high labels that really reach 3. Any vertex or component reachable from 3 is therefore also reachable from all these labels.

## A separate all-odd-exponent result and even-exponent dichotomy

Keep \(3\mid d\) and deliberately impose the exact quotient class \(r\equiv-1\bmod3\), leaving the other admissible profile residues unchanged. This is always allowed: \(r\) is a unit modulo 3, and \(N-dr\equiv N\not\equiv0\bmod3\). For example, in the above CRT construction change the \(3\)-part of \(r\) alone; the local conditions on the other primes and on \(V\) are independent. The P4 theorem still supplies at least \((3/40+o(1))B_0\) actual prime roots. This variant does not claim the original avoidance of \(3\) by a high quotient against all parities.

If \(k\) is odd, \(N\equiv-1\bmod3\), and \(Q\equiv-1\bmod3\) guarantees a genuine factor \(q\mid Q\) satisfying \(q\equiv N\bmod3\). If \(k\) is even, \(N\equiv1\bmod3\). In that case a quotient with no prime factor congruent to \(N\bmod3\) must have all factors \(-1\bmod3\), hence an odd rank since \(Q\equiv-1\bmod3\). It has rank at most four, so its rank is one or three.

For either parity, whenever a root supplies a factor \(q\equiv N\bmod3\), choose one such true factor for that root. Its size is at least \(N^{.05}\) and less than \(N\), and \(p\to q\to3\) are actual edges. There is no risk of \(N-q=1\): indeed \(q\le (N-p)/d\le N-p\) and \(p\to\infty\). If at least a fixed positive fraction of \(B_0\) roots supply such a factor, they supply \(\gg N^{.05}\) distinct such labels. To count them, if at least half of these chosen factors lie below \(N^{.4}\), the [uniform two-form bound](PrimeOppositePlantedLargestLabelSupply.md) at \(K=N^{.02}\) applies to each one even though it is not necessarily largest: \(q\ge N^{.05}>K\) is the only required lower size, and it is an actual divisor of \(Q\). At most \(1300B_0/q\) roots are assigned to each label, giving positive reciprocal mass and hence \(\gg N^{.05}\) labels. If at least half lie above \(N^{.4}\), the same true CRT bound gives \(\gg N^{.4}/L^2\) labels. Thus:

* For every sufficiently large **odd** \(k\), some admissible exact profile supplies \(\gg N^{.05}\) distinct actual first-level labels which have the directed edge to 3.
* For every sufficiently large **even** \(k\), on this exact profile either \(\gg B_0\) actual prime roots have quotient rank at most three, or \(\gg N^{.05}\) distinct actual first-level labels have the directed edge to 3. To see the dichotomy, separate the supplied rows into those with a directed label and the rest, and use whichever contains at least half.

The odd/even conclusion about directed labels does not require that they are the largest factors. Conversely the many-largest-label proof has no unconditional directed claim for those specific largest labels. No implication about the number reachable from a single root, the size of a terminal component, or an unconditional three-factor bound is asserted.
