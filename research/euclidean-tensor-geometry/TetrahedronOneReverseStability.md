# Stability for the one-reversed-link tetrahedron family

The one-reversed-link family of the companion density theorem also satisfies a quantitative stability theorem on its given partition. With all transversals present, let \(F=6abc+3(a^2b+b^2c+c^2a)\) be the cyclic template's ideal weighted density and \(D\) the original probability that three independent samples form an edge. Write \(\Delta=F-D\). The probability of disagreement with the standard cyclic construction using the **given** partition is at most \(10\sqrt{\Delta}\). In particular a sequence approaching \(5/9\) is close to the standard template, and the existing mass penalty forces a balanced partition in the limit. The order \(\sqrt{\Delta}\) is sharp when the partition must stay fixed. [Original proof and notation](TetrahedronOneReverseLinkEnergy.md).

Keep the original notation. The switched A-pair graph \(Q\) has density \(s\), square degree mean \(\mathbb E d^2\), and triangle density \(t\). Let \(f\) be the AAB deficit away from \(Q\), \(g\) the BBC deficit, \(\bar h\) the CCA deficit, \(o\) the AAC density, and \(i_A,i_B\) the internal triple densities.

Two improvements fit the existing link-energy proof.

1. Call an A triple Q-hit if one of its pairs belongs to \(Q\). If the first two and last two of four independent A samples are both \(Q\)-pairs, every one of the four contained triple positions is Q-hit. At least one is missing by tetrahedron-freeness, also when a draw repeats, since a triple with repeated vertices cannot be an edge. The event has probability \(s^2\). By the union bound, the probability of a Q-hit triple missing internally is at least \(s^2/4\). Thus subtract \(s^2/4\) when bounding the density of Q-hit internal triples. This avoids needing a cycle in \(Q\).
2. For each B vertex, the graph of missing AAB pairs outside \(Q\) has some density \(p\). A triple contains one of its edges with probability \(3p-3\mathbb E d_p^2+t_p\le3p-2p^2\), by inclusion–exclusion, \(t_p\le\mathbb E d_p^2\), and Jensen. Every internal A triple with no Q-pair must hit this graph for each such B vertex. Average to replace its earlier \(3f\) bound by \(3f-2f^2\). The same argument on the missing BBC graph for every C vertex replaces \(3g\) by \(3g-2g^2\) for internal B triples.

The stronger inequalities are therefore
\[
i_A/3\le f-\tfrac23 f^2+s-\mathbb E d^2+t/3-s^2/12,\qquad
i_B/3\le g-\tfrac23 g^2.
\]
Substitute in the existing link-energy estimate to get
\[
\Delta\ge 3a^2(b-a)(s+f)+3b^2(c-b)g
 + a^3\big(t/2+s^2/4+2f^2\big)+2b^3g^2.
\]
There is no positivity issue when a part is empty. Its weighted terms vanish and the surviving internal deficits are controlled exactly as above.

To bound total edit, let \(X=a^2b(s+f)+b^2cg\) and \(Y=a^2c o\). The crude inequalities \(i_A\le3(s+f),\ i_B\le3g\) and mass order \(a\le b\le c\) give \(a^3i_A+b^3i_B\le3X\). The exact excess identity implies \(ac^2\bar h\le Y+\Delta/3\). The total probability of edits is at most \(3(X+Y+ac^2\bar h)+a^3i_A+b^3i_B\le6(X+Y)+\Delta\). This is an upper bound for edits of the simple template even with sampling repetitions, because repetitions can only overcount missing forward types. Now \(o\le s\) and the displayed penalties give
\[
X+Y\le\left[2\sqrt a(b+c)+(\sqrt a b+\sqrt b c)/\sqrt2\right]\sqrt\Delta.
\]
Use \(a+b+c=1\), \(\sqrt a(1-a)\le2/(3\sqrt3)\), and \(\Delta\le1\); the resulting constant is at most \(6(4/(3\sqrt3)+1/\sqrt2)+1<10\). The existing repair step for a missing-transversal fraction \(\delta\) extends the stability to \(O(\sqrt{(5/9-D)_+}+\delta^{1/4})\) edits. The repair itself costs \(O(\sqrt\delta)\) and the repaired density is within \(O(\sqrt\delta)\) of the old one.

### A sharp disturbance on a small subset of one part

At balanced masses split A into \(A_0,A_1\) with internal fractions \(x,1-x\). Reverse exactly the cross-pairs \(A_0A_1\), with every C extension present and no B extension. Keep AAB on pairs within either subpart, keep BBC, and delete CCA when the A singleton is in \(A_0\). Add precisely internal A triples with one \(A_0\) and two \(A_1\) vertices. Keep ABC complete.

For distinct vertices, exclusivity rules out a tetrahedron of type AABC. On two A and two C vertices, the only case with AAC uses one \(A_0\), whose CCA triples are absent. An internal A triple has a cross-pair missing its B extensions and a same-subpart pair missing C extensions. Four A vertices cannot have all four triples with exactly one \(A_0\). The other types inherit the usual absent cyclic-template types. The stated color-type rules are preserved under blow-up.

In the blow-up limit, \(s=o=2x(1-x)\), \(f=g=0\), \(\bar h=x\), and \(i_A=3x(1-x)^2\). Thus \(\Delta=(2x^2-x^3)/9\), and given-partition edit probability is \((6x-6x^2+x^3)/9\), by counting removed AAB and CCA and added AAC and AAA. This proves partition-fixed sharpness. Moving \(A_0\) to B would absorb all first-order changes, so this example gives no lower bound of that order if repartition is allowed.

### Status and comparison

A bounded July–November search found no matching one-reverse stability inequality. The ordinary \(K_4^{(3)}\) conjecture is still open. Jeong et al.'s v2 concerns the unrestricted density upper bound. The November even-zycle stability result concerns different forbidden hypergraphs, and unrestricted tetrahedron conjectural maximizers include diverse constructions. [Unrestricted upper bound v2](https://arxiv.org/abs/2609.27495v2) · [Even zycles](https://arxiv.org/abs/2611.16654) · [Razborov’s Fon-der-Flaass interpretation](https://arxiv.org/abs/1008.4707)

