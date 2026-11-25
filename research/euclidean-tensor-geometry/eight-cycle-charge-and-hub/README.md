# Charge blocks and a uniform alternating max-flow bound for periodic tensor networks

**Yongxian Zhang.** AI-assisted research note with exact certificates.

We use the single-shared-tensor periodic model in [Gesmundo–Landsberg–Walter](https://arxiv.org/abs/1801.09106), over the complex numbers, with both the physical and bond dimensions equal to \(q\). Let \(F_{2d}(q)\) be the maximum rank of the odd/even flattening of the \(2d\)-cycle. This note proves exact additional eight-cycle values
\[
 F_8(10)=10000,\qquad F_8(11)=14640 ,
\]
and explicit bounds valid for all \(q\), not an exact formula in all dimensions. For fixed \(d\ge4\) the construction gives \(F_{2d}(q)\ge q^d-O_d(q^{d-2})\). For \(d=4\) the more precise bounds below are certified by small signed-multiset blocks. Compare Hastings's [general asymptotic relative max-flow result](https://arxiv.org/abs/1603.03717), Theorem 1.

## Exact charge blocks at 10 and 11

Take \(q\) shared matrices indexed by the additive group \(\mathbb Z/q\mathbb Z\). The slice \(A_i\) has a single possible entry in each row \(x\), in column \(x+i\bmod q\), with weight \((i+1)^x\) (indices \(i,x=0,\ldots,q-1\)). A trace word traverses a closed walk in this group, so the sum of all its labels is zero. The odd/even matrix therefore decomposes by total odd charge, with the matching even charge its negative. Each block is \(q^3\) square because the fourth label is determined by the first three and the charge. The checker `charge.cpp` verifies their ranks over the prime field of size 1009: all 10 blocks have rank 1000 for \(q=10\); for \(q=11\) the charge-zero block has rank 1330 and the other 10 have rank 1331. The nonzero integer minors modulo 1009 persist over \(\mathbb C\).

For the upper bound at 11, cyclicity gives \(M^\top=MP\) for the length-four rotation permutation \(P\), and \(M\) commutes with \(P\). The pairing on its \(-1\) eigenspace is skew-symmetric and this block is isolated from all other rotation eigenspaces. Its dimension is \((q^4+q^2-2q)/4=3685\) at 11. Odd-dimensional skew-symmetry forces at least one defect. The rank at 10 already reaches the size of the full matrix. Full rank at 10 also gives full rank at \(10a^2\) for all positive integers \(a\) by tensor product with the square-dimension GLW witnesses.

## Hub-and-spokes construction for general \(d\)

Use \(A_0=E_{00}\) and \(A_i=E_{0,i}+c_iE_{-i,0}\) for \(i\ne0\). Treat the \(c_i\) as algebraically independent complex parameters for generic-rank arguments. In the cyclic word of alternating row letters \(u\) and column letters \(v\), a nonzero trace corresponds to tiling the positions by length-one hub loops (label zero) and length-two excursions to a spoke and back (two opposite nonzero labels). This is because the only outgoing move from a nonzero state \(a\) uses label \(-a\) and returns to zero. For each such tiling the weight is the product of coefficients for the returning labels. Each tiling supplies one term, with the starting state at the first position already fixed by the tiling. Since each length-two tile contains one row position and one column position, after relabelling the column tuple \(w=-v\) the flattening is block-diagonal by the multiset of the row tuple \(u\).

If the multiset has no zeros, the only tilings use all forward or all backward pairs, so on each cyclic orbit of words the block is \(aI+bP_{\rm orbit}\) with \(a=\prod_j c_{-u_j}\), \(b=\prod_j c_{u_j}\). Distinct \(a,b\) are distinct monomials, so the block has full generic rank. If \(a=b\), each even-length orbit loses one rank and each odd orbit loses none. Balanced multisets, where every \(i\ne-i\) occurs with the same multiplicity as \(-i\), have only \(O_d(q^{\lfloor d/2\rfloor})\) words, as they are formed by choosing at most \(\lfloor d/2\rfloor\) non-self-inverse pair labels; the group has at most one nonzero self-inverse symbol.

If the multiset has a zero but neither an opposite pair of distinct nonzero labels nor a nonzero self-inverse symbol, specialize \(c_{-i}=t,\ c_i=t^{-1}\) for each nonzero label \(i\) in this one multiset; other weights can be any nonzero constants. These assignments are compatible. The maximum possible Laurent degree of any trace walk is the number of nonzero row letters, and it is attained only by pairing every nonzero row with the following column. This forces \(w=u\). Each such diagonal entry has a unique such walk, since at least one zero fixes the hub state on the cycle. Thus the leading coefficient matrix is the identity and this block has full generic rank. All other zero-containing words are \(O_d(q^{d-2})\) since they contain a fixed zero and either a fixed nonzero self-inverse label or a pair of nonzero opposite labels consuming two positions but only one free choice. We may choose parameters separately to establish each required nonzero minor; their product is a nonzero polynomial, so a single choice exists simultaneously. For \(d\ge4\) this proves the stated bound.

## Explicit eight-cycle defect bound

Set \(r=\lfloor(q-1)/2\rfloor\), the number of nontrivial inverse-label pairs. We claim
\[
 q^4-F_8(q)\ \le\
 \begin{cases}
 3r^2+2r,&q\text{ odd},\\
 3r^2+11r+4,&q\text{ even}.
 \end{cases}
\]
For the zero-free case, two distinct inverse-pair classes give six even rotation orbits per choice of pair classes, coming from 24 words with orbit size four. A repeated inverse pair has one orbit of length four and one of length two. If \(q\) is even, writing \(h=q/2\), the multiset \(\{h,h,a,-a\}\) contributes three length-four orbits per opposite pair. The multiset with four \(h\)'s has an orbit of length one. The zero-free upper bound on the defect is \(6\binom r2+2r\) for odd \(q\), plus \(3r\) for even \(q\).

For a zero-containing block, the coefficients depend only on which labels are zero, whether there is a nonzero self-inverse label, and which other symbols form inverse pairs. Indeed the label signs are used only in the test for returning from the current spoke to the hub. At most three distinct nonzero inverse-label classes are represented. Each such signed-label type embeds into the group of order 11 for odd \(q\), or order 12 for even \(q\), preserving opposites and the existence of the self-inverse symbol when used. The finite checker `verify_star.py` exhausts all zero-containing multisets in those two groups, with modular arithmetic. Every block is full except the following possibilities, for which the checker certifies deficits no larger than shown: \(\{0,0,a,-a\}\): 3; and in even dimension \(\{0,0,0,h\}\): 1, \(\{0,h,h,h\}\): 3, \(\{0,h,a,-a\}\): 6. In this list \(a\) ranges over nonzero non-self-inverse symbols and replacing \(a\) by \(-a\) does not change the multiset. This adds \(3r\) for odd \(q\), and \(9r+4\) for even \(q\), giving the two displayed bounds.

## Reproduction

Run `c++ -O3 charge.cpp -o charge && ./charge 10 11` and `python3 verify_star.py`. Both checks use ordinary exact Gaussian elimination modulo 1009; the second uses only standard-library Python. The finite check proves nonzero minors, not an upper bound on generic rank. Exactness at 10 and 11 uses the independent upper bounds above.
