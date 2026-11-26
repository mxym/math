# Reconstructing arbitrary-width heavy path masses with a common residue

**Yongxian Zhang.** AI-assisted proof development and internal mathematical checks; no external peer review claimed.

**Theorem.** Fix cutoff \(h\ge1\), precision \(d\ge1\), and an integer divisor \(g>d\). Suppose a tree has a heavy path skeleton on \(q\ge2\) blocks with masses \(s_v\ge\max(h+d+1,2d+1)\). Suppose that for some integer \(M>q\), every \(s_v\) has the form
\[
s_v=g(1+M a_v),\qquad a_v\in\mathbb Z_{\ge0}.
\]
Then the ordinary chromatic symmetric function determines the weighted path skeleton and each rooted block series through deficit \(d\), up to path reversal, among all ordinary trees. No bound on the width of the mass range is required. If the mass word is nonpalindromic, the smaller size condition \(s_v\ge h+d+1\) suffices. At cutoff two take \(d=1\) to obtain full reconstruction; at general cutoff use the bounded-branch threshold \(d\ge\sum_{j\le h}j b_j\).

Block masses can repeat arbitrarily, and the common residue does not encode any individual vertex label or leaf tag. For example one can take \(h=2,g=2,M=q+1\) and any \(a_v\ge1\); the block masses then are even, potentially equal or arbitrarily far apart. Each block may be any mixture of single leaves and two-vertex branches consistent with its mass.

## 1. Unmarked mass order via block count

Use the top high homogeneous layer of the ordinary unsigned \(U\)-polynomial as before to recover the number and multiset of heavy block orders. Put all low variables to zero to obtain the ordinary weighted cut polynomial of the skeleton. For any one-edge split of this weighted skeleton, if one side has intact mass \(W\), its number of skeleton vertices is exactly the representative in \([0,q]\) of the residue of \(W/g\) modulo \(M\), because each vertex contributes \(1\) and \(q<M\). The splits with a side of one vertex identify the leaf edges. If \(q\ge3\), there are two such splits and any rival skeleton therefore has two leaves, so is a path. If \(q=2\) the shape is forced directly.

The weighted path cut polynomial is the L-polynomial of its mass word \(\eta\). By [Billera–Thomas–van Willigenburg](https://arxiv.org/abs/math/0405434), equal L-polynomials are obtained precisely by reversing factors of the irreducible composition-product factorization. Now any \(\eta=\alpha\circ\beta\) with \(\operatorname{len}(\beta)\ge2\) and some \(\alpha_i>1\) contains the actual endpoints \(\beta_{\rm first},\beta_{\rm last}\) and also the merged part \(\beta_{\rm first}+\beta_{\rm last}\). Modulo \(gM\), the intact parts have residue \(g\), whereas the merged part would have residue \(2g\). This is impossible. It follows that at most one irreducible factor is nonsymmetric: otherwise separate after the first such factor, making the left product contain a part \(>1\) and the right product have length at least two (composition cannot shrink a part or reduce the length of either input). Reversing that sole possible factor coincides with reversing the entire word. Consequently the mass word is recovered up to reversal.

## 2. Recovering the block series

Once the mass word is aligned, the palindrome case is exactly the [two-deficit argument](StanleyPalindromicTwoDeficit.md): two independently marked components of low deficits \(k,l\le d\) have total mass loss at most \(2d\), and their residues individually determine the deficits. The resulting bivariate products and three-part cuts synchronize the signs of all prefix versus suffix products. That argument uses no relative size bound on the masses after the path and its weights have been reconstructed.

Suppose instead the mass word is nonpalindromic. Apply the [one-mark comparison](StanleyNonpalindromicHeavyPaths.md). As there, write \(J\) for proper prefix masses, \(N\) for the total mass, and call a mass paired if both it and its complement lie in \(J\), asymmetric if exactly one does. At the first differing degree between two candidates with the same mass word, let \(\delta_a\) be the leading difference of the prefix series at a paired mass \(a\); elsewhere put it zero. All asymmetric side series are individually read from two-part cuts. Then \(\delta_{N-a}=\delta_a\), and for any asymmetric \(b\), a nonzero \(\delta_a\) satisfies \(\delta_{(a+b)\bmod N}=\delta_a\). This follows from the three-part coefficient with \(a,b\) intact and \(N-a-b\) marked (or their complement indices when the sum wraps), as proved in the companion note. Thus translating a nonzero \(a\) repeatedly by any asymmetric prefix mass \(b\) visits paired prefix masses with the same nonzero value.

The common congruence now precludes such an orbit. For each proper prefix mass \(x\), let \(k(x)\in\{1,\ldots,q-1\}\) be its prefix vertex count, so
\[
x/g\equiv k(x)\pmod M,\qquad N/g\equiv q\pmod M.
\]
Take an asymmetric prefix mass \(b\) with \(k(b)=j\), and iterate \(x\mapsto x'=x+b-Nw\) on the orbit starting at a nonzero \(\delta_x\), with \(w\in\{0,1\}\) the wrap indicator. All \(x,x'\) have nonzero \(\delta\) and hence are paired. The congruences give
\[
k(x')\equiv k(x)+j-qw\pmod M.
\]
If there is no wrap, then \(x'>x\), so both \(k(x')-k(x)\) and \(j\) lie in \([1,q-1]\). If there is a wrap, then \(x'<x\), so both \(k(x')-k(x)\) and \(j-q\) lie in \([1-q,-1]\). In either case the interval has length less than \(M\), so the congruence is an actual equality. Summing \(x'=x+b-Nw\) over a full orbit of \(m\) steps shows \(N\sum w=mb\); summing the equalities for \(k\) shows \(q\sum w=mj\). Thus existence of a single nonzero difference forces \(b/N=j/q\) for **every** asymmetric prefix mass \(b\).

Because the word is nonpalindromic there is such a prefix mass \(b\). The prefix \(b'\) at complementary index \(q-j\) is asymmetric too: its complement has residue \(j\) modulo \(M\) after division by \(g\), so if its complement were in \(J\) it would have to equal \(b\), the unique prefix with that count. This is excluded by the asymmetry of \(b\). But the proportionality from the orbit, applied to \(b'\), forces \(b'=N-b\), a contradiction. Thus no first difference exists. Finally dividing consecutive prefix products gives the individual block series, and the standard cutoff-two or bounded-branch criterion reconstructs the rooted blocks.

The same theorem holds with a common residue \(r\) instead of 1, provided its additive order \(M/\gcd(M,r)\) exceeds \(q\): component counts are still decoded uniquely, the merged endpoint residue \(2r\) differs from \(r\), and the orbital congruence for counts can be interpreted modulo the additive order of \(r\).

## Scope

This is a second untagged criterion, not a reduction of every weighted heavy skeleton to this case. It replaces near-equal masses by equal residues carrying only component vertex count, still permitting unbounded diameter and arbitrarily repeated rooted blocks. It does not handle arbitrary weighted branching cores, all caterpillars of unbounded branch order, or unrestricted Stanley reconstruction.

[Independent finite checks](stanley-marked-path-verify.js) are supplementary; the proof does not use them. See also the [separated interval-mass version](StanleySeparatedHeavyPaths.md).
