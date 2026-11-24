# Signed seven-residue integrality improves the equitable 33-set floor to 412

Suppose the seven-rank is 42 and the selected signed-unit support is contained in \(\{(0,26),(2,28),(2,30)\}\). This is a necessary condition on that face only. All \(G_{at}\) below are literal positive-charge shell populations, not antipodal averages; \(N_t\) counts both signs. Set \(T=G_{333}\), \(A=G_{335}\), \(D=G_{444}\), \(h=A+D\), \(B=N_{14}\), \(S=G_{123}-99-7B\), \(M=G_{222}\), and \(p=M+S\). These are nonnegative integers. In particular \(T\) counts actual equitable 33-sets. Then
\[
 A\equiv D\bmod8,\qquad 2\mid A,D,\qquad
 h=0\Longrightarrow p\text{ odd},\qquad
 T\ge412.
\]
Equality in the last inequality requires \(B=0,\ h=0,\ p=1\); this is not an existence assertion.

**Physical residues.** We use the actual terminal anisotropic plane (it is the original discriminant plane at rank 42). Fix an anti-isometry to the auxiliary plane. Write \(g_k(c)\) for the literal count of charge/cost \(k\) in this signed seven-residue, not identified with \(-c\). For each species take the four lexicographically sorted representatives \(c=\min(c,-c)\). The comparison of all sixteen choices of the anti-isometry uses no symmetry of the graph. As in [the opposite-residue argument](two-type-residue-balance.md), the weight-26 auxiliary quadratic theta coefficient satisfies \([q^2]+48[q]=0\) at each of the four three-translates. In charge \(a>0\) the opposite charge is accounted for by a factor two, not by treating the two signed classes within positive charge as equal. In an auxiliary row paired with its negative gluing the even unknown is \((g_k(c)+g_k(-c))/2\); subtract the all-rotation mean to get its centered value \(v_k=(g_k(c)+g_k(-c))/2-G_k/8\). The odd unknown is \(w_k=g_k(c)-g_k(-c)\), obtained by subtracting the two gluings. The zero residue, the pure-root correction, and all fixed-charge constants cancel. In the odd chart so do all charge-zero shells by negation. The two projections do not assume that graph fields are uniformly distributed. The full-shell absences used by the checker are exactly the indicated neutral zeros, \(121,125,127,226,337\), and the universal \(224\) absence. Indeed nonunit \(125\) comes only from \(016\); nonunit \(127\) comes only from \(018,226\); these all vanish here.

The companion [exact checker](rank42_equitable_signed_gate.py) regenerates both row spaces (36 columns, rank 32; 28 columns, rank 24), and checks every listed output map on their exact nullspaces. With its integral matrices \(E_k,O_k\) and denominators \(e_k,o_k\) for \(k=444,230,228,129\), write \(u_i^\pm=g_{335}(\pm c_i)\), \(p_i=u_i^++u_i^-\), \(q_i=u_i^+-u_i^-\), \(P_i=4p_i-A\). Then
\[
  8g_k(\pm c_i)=G_k+(E_k P_{1:3})_i/e_k
                       \ \pm4(O_kq)_i/o_k.
\]
The four physical masses used, checked against the original 205-column native chart by the same program, are
\[
 2T=808+16p+96B+h,\quad G_{228}=784+8S+56B+h,\quad
 G_{230}=1732+12(S-M)+96B+A+2D,\quad
 G_{129}=7088+32S+40M+296B+5A-D .
\]
If \(h=0\), all inputs vanish and \(8\mid G_{230}\); since \(1732\equiv4\pmod8\), \(p\) is odd.

**The congruence at all sizes.** Multiply the 32 right-hand sides of the signed equations by 84 so that the coefficients are integers. Each must be a multiple of 672. Eliminate the eighth input using \(\sum u_i^\pm=A\). Write the resulting vector as \(b+Jx\) with seven *columns* of \(J\) corresponding to the remaining seven inputs. Solvability over the integers, even with no nonnegativity assumption, is equivalent to \(b\in J\mathbb Z^7+672\mathbb Z^{32}\) (the sign of \(b\) is immaterial). Inverting a square column-Hermite basis of the displayed lattice tests this by integrality of all coordinates. It suffices to take \(A,D\) modulo 8 and \(p\) modulo 2: on increasing \(A\) by 8 add one to all eight \(u_i^\pm\), which leaves \(P,q\) unchanged; the masses change by multiples of eight modulo the already fixed terms. Increasing D by eight, or p by two, likewise changes the relevant masses by multiples of eight. All coefficients after the indicated common multiplication are integral. For either parity of \(p\) the surviving \((A,D)\bmod8\) are exactly \((0,0),(2,2),(4,4),(6,6)\). These are accepted modular cases, not graph witnesses.

**The small endpoint.** For \(T\le412\), the physical mass identity implies \(B=0\) and either \(p=1,h=0\), or \(p=0\) and \(h=0,2,\dots,16\). In the second case set \(D=h-A\), run \(A=0,\dots,h\), then all four-part compositions of \(A\); discard any giving a negative or nonintegral output projective population. For each remaining composition run \(q_i=-p_i,-p_i+2,\dots,p_i\). Require the 32 signed outputs to be nonnegative integers. Here are the numbers (all compositions, those passing projective tests, signed candidates, signed survivors), including the endpoint \(h=16\):
```
0   1     1    1    0
2   15    0    0    0
4   70    2    17   0
6   210   0    0    0
8   495   3    98   0
10  1001  0    0    0
12  1820  4    354  0
14  3060  0    0    0
16  4845  5    979  0
```
This proves the bound and its necessary equality case, not that an equitable family achieving it exists.
