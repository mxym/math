# Marked root 2-neighbors and true 42/44-set populations

Work at rank 42 on the two-type face where the only occurring selected unit types are neutral squared norms 18 and 24, except where scope is explicitly noted. Write \(G_{a,t}\) for raw positively charged labels, \(N_t\) for raw oriented neutral labels. At rank 42, the graph has exactly one actual Hoffman coclique \(C\) on this face. It is convenient to use \(c=-1_C\). The even rank-44 graph mark lattice \(U\) has determinant 49 and anisotropic seven-part; here \(U\) and \(U^*\) realize precisely the graph charges \(0,\pm3\), with zero seven-class for \(U\). Evaluations are \(b_i+a/9=(y,u_i)\), so \(7y^2=t-11a^2/9\). Set \(d_i=(3I-A)e_i\), so \(d_i\cdot b=7b_i+2a\) and \(d_i^2=23\).

## Marked 2-neighbors

The actual vector \(v_x=3u_x\) has squared norm 28. The condition \((z,v_x)\equiv0\pmod2\) cuts an index two sublattice \(U_0\) of \(U\), since \((3u_z,v_x)=1\) for any nonneighbor distinct from \(x\). The union \(U_0+\mathbb Z(v_x/2)\) is an odd integral lattice, denoted \(O_x\), of the same determinant. The other companion \(U'_x\) is obtained by adjoining \(a_0+v_x/2\) to \(U_0\) for any \(a_0\in U\) of odd pairing with \(v_x\); it is even. Outside the prime two there is no change, so \(U'_x\) has level seven and the same anisotropic residual seven-plane. For \(U^*\) and \(U'^*_x\) the same local descriptions apply at two because the lattices are unimodular there.

For a newly adjoined half-vector \(z=p/2\) the necessary and sufficient dyadic condition for \(p\) is \(p\equiv v_x\bmod2U\), together with the right parity of \(z^2\); the labeling of the odd/even cosets is exactly that parity because \(v_x^2/4=7\). For dual fields use \(U^*\), which equals \(U\) locally at two. The graph marks \(u_i\) span locally at two and \(U\) is self-dual there. Thus pairing congruences with all \(u_i\) characterize the dyadic condition. The parity pattern is (charge-zero p) odd on all 84 distance-two sites and even on the root and its 14 neighbors, or (charge-three p) odd on the closed star and even outside. The latter follows because the charge offset \(1/3\) is odd. For charge three, let e count exterior entries congruent to two modulo four. The 15 odd squares contribute seven modulo eight, while the remaining squares contribute \(4e\). The odd neighbor's raw cost is seven modulo eight, hence e is even; the even neighbor's raw cost is three modulo eight, hence e is odd. The sum on the fourteen neighbors is two modulo four by the eigen-equation and the full sum is three modulo four. Thus the root value is one modulo four in the first case and three modulo four in the second.

Let \(B_x\) count the oriented flat neutral fields with signs \(\pm1\) on all 84 outside sites and zero on the closed star. Equivalently, each is the difference between two 42-site shores, each inducing degree four outside the root star and each meeting each near arm in six sites. Then
\[
 [q^{3/2}]\Theta_{O_x}
 =B_x+2G_{1,23}(b_x=-1)+2G_{2,22}(b_x=0),
 \qquad [q^{1/2}]\Theta_{O_x}=0.
\]
For neutral \(p\) at \(p^2=4\) the parity needs cost at least 84, while it has raw cost 28. At \(p^2=12\) it has cost 84, and parity forces exactly the flats. Charge three gives respectively raw costs 39 and 95. Raw 39 is impossible because an integer array of mass \(-33\) with only 15 odd locations has squared norm at least \(66-15=51\), by \(k^2\ge 2|k|-\mathbf1_{k\text{ odd}}\). At raw 95 put \(f=(b-d_x)/2\), integral of charge one, with \(f_x=(b_x-3)/2\) and \(f^2=(53-7b_x)/2\). Parity gives \(b_x\equiv1\bmod4\): \(b_x=1\) gives \(G_{1,23}\) with \(f_x=-1\), and \(b_x=-3\) gives \(G_{1,37}\) and \(f+d_x\in G_{2,22}\) with zero at \(x\). Larger positive values have cost below the charge-one minimum; smaller negative values give \((f+d_x)^2<22\). Each construction is invertible and the opposite charge doubles it. The odd norm-three coefficient therefore counts an exact graph family, not a formal residual class.

## The exact first coefficients of the even companion

Put \(X'_j=\#\{z\in U'^*_x:7z^2=2j\}\) and \(Y'_j=\#\{z\in U'_x:z^2=2j\}\); subscripts refer to different cusps. For the new half-coset \(p=2z\) of the dual, the raw cost is \(8j\) (charge zero) or \(8j+11\) (charge three). In charge zero, the parity forces \(p_x\equiv2\bmod4\): the sum on the near star is 0 mod 4 by the eigen-equation, so the number of near entries congruent to 2 mod 4 is even, and the 84 odd squares contribute 4 mod 8. Thus \(\sum p_i^2\ge104\), since the root square is at least four and the near entries must have absolute sum at least eight, with squared sum at least sixteen. This elementary bound also works if the root entry has magnitude larger than two. At equality orient \(p_x=-2\); then \(-(p+d_x+\mathbf1)/2\) is a charge-four all-nonpositive unit label of cost 44, with a \(-1\) at \(x\). Its inverse has the desired raw norm and parity. At raw cost 112 the same formula gives exactly the labels \(G_{4,46}(b_x=-1)\), because \(p_x=-2\) still follows from the bound when \(|p_x|\ge6\), and the affine inverse has norm 112 by the translation formula. Both neutral inverse counts take the two orientations of \(p\).

For the new charge-three sector let \(f=(b-d_x)/2\). It now has cost \((4j+11-7b_x)/2\), and \(b_x\equiv3\bmod4\). For \(b_x\ge7\) and \(j\le14\), its cost is below 21. If \(b_x\le-5\), adding \(d_x\) to \(f\) gives charge two at cost at most \(2j-6\); this is below 22 through \(j=13\), with only the case \(j=14,b_x=-5\) attaining 22, then \(f+d_x\) has a negative unit at \(x\). The case \(b_x=3\) gives \(G_{1,2j-5}(f_x=0)\), hence empty up to \(j=13\) on this face. The case \(b_x=-1\) gives \(G_{1,2j+9}(f_x=-2)\). Through \(j=11\) it vanishes: the short charge-one norms up to 21 are absent; \(G_{1,23}\) has no negative exception; \(G_{1,25}\) is absent; \(G_{1,27}\) has only the unique positive double of its norm18 translate; and a negative double at costs 29 or 31 switches to the absent \(G_{2,28}\) or \(G_{2,30}\). At \(j=12,13,14\) the same case contributes respectively the negative double slots of \(G_{1,33},G_{1,35},G_{1,37}\).

The inherited dual half (the actual intersection with \(U^*\)) consists of original vectors with even pairing with \(v_x\), i.e. even \(b_x\) in charge zero and odd \(b_x\) in charge three. Consequently
\[
\begin{aligned}
&X'_1=\cdots=X'_8=X'_{10}=0,\qquad X'_9=N_{18}(b_x=0),\\
&X'_{11}=N_{22}(b_x\text{ even})+2G_{3,33}(b_x\text{ odd}),\\
&X'_{12}=N_{24}(b_x\text{ even})+2G_{3,35}(b_x\text{ odd})+2G_{1,33}(b_x=-2),\\
&X'_{13}=2G_{4,44}(b_x=-1)+2G_{1,35}(b_x=-2),\\
&Y'_2=N_{28}(b_x\text{ even})+2G_{3,39}(b_x\text{ odd})+
       2\big[G_{4,46}(b_x=-1)+G_{1,23}(b_x=0)+G_{1,37}(b_x=-2)+G_{2,22}(b_x=-1)\big].
\end{aligned}
\]
Here and only here the literal primal shell at \(j=14\) equals \(X'_{14}\) by anisotropy; corresponding marked graph fields are of zero seven-class. For \(j<14\) use all eligible dual labels. The coefficient at \(j=13\) has no inherited terms because raw neutral norm 26 and raw \(G_{3,37}\) both vanish. The reverse parity maps use no assumptions on the graph beyond those stated.

The standard rank-44 determinant-49 [Fricke relation](rank36-coclique-tangent.py) on a rootless scaled dual with \(X'_1,\ldots,X'_6=0\) is
\[
Y'_2=1000-8X'_7+25X'_8+11X'_9+8X'_{10}+3X'_{11}+X'_{12}.
\]
Subtract this row from the same relation on \(U\), using the first-coefficient dictionary. This gives the following exact equation at every graph vertex \(x\):
\[
\begin{aligned}
2[\,G_{4,46}(-1)+G_{1,23}(0)+G_{1,37}(-2)+G_{2,22}(-1)\,]={}&
N_{28}(\mathrm{odd})+2G_{3,39}(\mathrm{even})-11N_{18}(\ne0)\\
&-3N_{22}(\mathrm{odd})-6G_{3,33}(\mathrm{even})
-N_{24}(\mathrm{odd})-2G_{3,35}(\mathrm{even})+2G_{1,33}(-2).
\end{aligned}
\]
All parenthesized conditions refer to the same actual coordinate \(b_x\). This is a per-vertex identity; its global sum is already redundant in the scalar shell cone (tested exactly on 43 independent A8/K rows). The rootwise and marked-\(C\) sums have not been shown redundant or contradictory.

## The exact odd rank-30 rooted coset

Independently describe the shortened section. In the ordinary graph pairing divided by seven, let \(B_H\) be the even lattice of neutral fields zero on the closed root star in the selected seven-extension. It has Gram determinant \(2^{21}\cdot49\). There is a canonical order-two coset \(\sigma+B_H\) in \(B_H^*/B_H\) consisting exactly of the zero-star fields which become odd at every outside site upon multiplying by two, with the doubled field eligible in \(H\).

To see the coset is nonempty, work at two. The saturation of the near marks has index four and is generated by the near marks and \(u_x=-\sum_{y\sim x}u_y/4\). The functional pairing with \(u_x/2\) is integral on this primitive lattice, since the near pairings of \(u_x\) are \(-8/9\) and its squared norm is \(28/9\). Extend the functional to the full dyadically self-dual lattice. If \(a\) is a vector representing it, then \(u_x-2a\) lies in the integral zero-star section and has odd evaluation on every outside site, because \((u_x,u_y)=1/9\) there. Hence the section \(B_H\), whose localization at two is this same section, has some such parity representative \(s\). For any \(t\in B_H\), \(s\cdot t\equiv\sum t_i\equiv0\pmod2\), and original seven compatibility gives \(7\mid s\cdot t\). Thus \(s/2\) is in the dual; two choices differ by an integral compatible field and give the same coset. With 84 odd coordinates, \(s^2\equiv4\pmod8\), and \(s^2\) is a multiple of 14; therefore \(\|s/2\|^2_{B_H}=s^2/28\) is odd. The extension \(\widehat B_H=B_H\cup(\sigma+B_H)\) is odd integral of determinant \(2^{19}\cdot49\).

Its odd vector of squared norm \(j\) corresponds uniquely to \(g=(s-d_x-\mathbf1)/2\), a charge-four field with a distinguished \(-2_x\), zero on all actual neighbors of \(x\), and cost \(25+7j\). This is an affine bijection with this marked portion of the graph shell; writing \(s=2g+d_x+\mathbf1\) gives the inverse and preserves eligibility because the site mark has zero seven-class. The odd minimum is at least three by the 84 odd sites; the norm-three vectors are precisely the flat bisections. On the rank42 unique-\(C\) face, at \(x\in C\) each antipodal flat pair has \(g\cdot c=9,16\). Indeed the other possible values 2 and 23 are complementary, and value 23 would make \(g-c\) a second compatible actual coclique (both cannot equal \(c\)). In particular the literal [B1 bisection subtype](hoffman-bisection.md) of cost \((2,36)\) angle \(-6\) is exactly half the total number of these rank-30 norm-three vectors over the 22 roots in \(C\), not a graph-independent formal census.
