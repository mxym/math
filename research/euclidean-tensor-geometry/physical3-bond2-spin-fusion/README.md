# Spin-one fusion for the alternating physical-3, bond-2 rank problem

**Yongxian Zhang.** AI-assisted proof development and internal verification; no external peer review claimed.

In the shared-site periodic model on \(2s\) sites over \(\mathbb C\), let \(F_s\) be the greatest alternating flattening rank with physical dimension 3 and bond dimension 2. In a dense normal form, **every charge and cyclic rotation block is generically full except possibly charge zero and rotation eigenvalue \(\mu=(-1)^{s+1}\)**. The proof is valid for both parities of \(s\). It gives the exact odd-half-length values
\[
F_3=27,\qquad F_5=241,\qquad F_7=2173,\qquad F_9=19585.
\]
In particular \(F_s<3^s\) for every odd \(s\ge5\). As \(s\) grows within each parity, the defect is at least \(\Omega(2^s/s^{7/2})\) for odd \(s\) and \(\Omega(2^s/s^{11/2})\) for even \(s\). The exceptional block is not classified in general.

We use the [Gesmundo–Landsberg–Walter model](https://arxiv.org/html/1801.09106#S2) and the dense slice normal form also used in [the exact twenty-cycle proof](../twenty-cycle-physical3-bond2/README.md). For related alternating spin-chain reductions and transfer fusion see [Santos](https://arxiv.org/abs/1408.1716) and [Frassek–Karpov–Tsymbaliuk](https://www.math.purdue.edu/~otsymbal/Papers/FKT.pdf). Below we verify the particular local identity directly.

## 1. Move the deformation to one seam

Choose the three slices to span the generic hyperplane \(W=\langle |01\rangle,|10\rangle,|00\rangle+t|11\rangle\rangle\), with \(t\ne0\). The alternating map can be realized by including \(W^{\otimes s}\) on the even bonds of the \(2s\) virtual bits and then taking the quotient by the annihilator of \(W^{\otimes s}\) on the odd bonds, using the ordinary bilinear pairing. This latter annihilator is the sum of spaces with a factor on the line \(|00\rangle+\rho|11\rangle\), \(\rho=-1/t\), on at least one odd bond.

Change the virtual coordinates at sites \(2j\) and \(2j+1\) by \(\operatorname{diag}(1,\rho^{-2j})\) and \(\operatorname{diag}(1,\rho^{2j+1})\), respectively, for \(0\le j<s\). On each even bond the covector annihilating the transformed row space becomes \((1,1)\) in the \(00,11\) coordinates. On an ordinary odd bond the transformed forbidden vector line likewise becomes \((1,1)\); on the final bond it becomes \((1,x)\), \(x=\rho^{2s}\). Applying \(|0\rangle\mapsto|1\rangle,\ |1\rangle\mapsto-|0\rangle\) at every odd site turns the ordinary lines into singlets and identifies the even row space with the symmetric square on every bond. At the seam, the odd forbidden line is the ordinary singlet acted on by \(\operatorname{diag}(1,x)\) on the even bit. Thus the odd quotient can be realized by applying its inverse, proportional to \(D=\operatorname{diag}(x,1)\), to that bit before taking the ordinary symmetric quotient. Invertible scaling or basis changes do not affect rank.

Let \(S\) be the spin-one operators on the symmetric square, and \(\sigma\) the Pauli matrices on an auxiliary bit. Define \(L_a(u)=uI+\sigma_a\cdot S\) and
\[
T_D(u)=\operatorname{tr}_a\!\left(D_a L_{a,0}(u)\cdots L_{a,s-1}(u)\right).
\]
Regrouping the matching moves the first constituent of a symmetric pair into the outgoing auxiliary bit and replaces it with the incoming bit. In the transfer contraction this is the swap between the auxiliary bit and the first constituent, compressed to the symmetric square on the site. The swap of two bits equals \((I+\sigma_a\cdot\sigma_1)/2\); the site compression of \(\sigma_1\) is \(S\). Close the auxiliary trace with \(D\) at the seam. Thus the alternating map has the rank of \(T_D(1)\) (the paired input-output convention can transpose the matrix, and the common scalar \(2^{-s}\) does not matter). The statement can also be obtained by expanding the swap contraction on bit pairs.

## 2. Fuse the two auxiliary bits

For two auxiliary bits \(a,b\), the local product \(L_a(1)L_b(0)\) preserves their antisymmetric line and acts there by \(-2I\). On their symmetric square its compressed action is twice the swap of the symmetric auxiliary and physical spin-one spaces. Here is a direct check. In the site basis \(|00\rangle,|01\rangle+|10\rangle,|11\rangle\) with charges \(m=1,0,-1\), the operator \(L_a(u)\) on auxiliary bit \(b\) has:
- unchanged bit and site charge, coefficient \(u+(-1)^b m\);
- flipped bit \(b'=1-b\), output charge \(m+b'-b\) when in range, coefficient 2 if \(m=0\) and 1 otherwise.

Apply these rules at \(u=0\) on the second bit then \(u=1\) on the first bit. On \((|01\rangle-|10\rangle)\otimes |m\rangle\) the result is \(-2\) times the input. On the nine symmetric-square basis pairs with auxiliary and site charges \((k,m)\), add the two \(01,10\) coordinates and divide by two to read their symmetric output; this gives \(2|m\rangle\otimes |k\rangle\). Equivalently the compressed operator is \(2B^2+2B-2\), with \(B\) the spin scalar product on the two spin-one spaces. Its values on total spin \(2,1,0\) are \(2,-2,2\). Both individual \(L\)'s are self-adjoint in the orthonormal spin basis, so reversing the local product has the same diagonal blocks and the opposite block triangularity.

In the product of the two twisted auxiliary traces, \(L\)'s of distinct auxiliary bits on distinct sites commute, so group them site by site. Use the above triangular blocks and trace with \(D\otimes D\), which preserves the two auxiliary summands. The singlet contributes \((-2)^s\det D\), and the symmetric swap trace is \(2^s\) times the shift with twist \(\operatorname{Sym}^2D\) on the moved site. With the convention moving the first site to the last, this gives both orders:
\[
T_D(1)T_D(0)=T_D(0)T_D(1)=2^s\bigl(\mathrm{Shift}_{\operatorname{Sym}^2D}+(-1)^s xI\bigr).
\]
The transfers preserve the total charge \(Q\) and commute with the twisted shift, the latter by the identity itself. On charge \(Q\), the shift to the \(s\)-th power is \(x^{s+Q}\). For generic \(x\) the only possible zero product sector therefore has \(Q=0\) and shift eigenvalue \(\mu x\) with \(\mu=(-1)^{s+1}\). On the other shift eigenspaces both factors are invertible. On the exceptional eigenspace the ranks of the two factors sum to at most its dimension.

To translate back to the original rotation blocks, on charge zero the even row gauge weights a word of charges \(q_j\) by \(\rho^{2\sum j q_j}\) times a factor depending only on letter multiplicities. In fact the charged basis vectors after the odd-site transformation have multipliers \(-\rho^{2j+1}\) and \(\rho^{-2j}\), and the charge-zero vector has multiplier 1. Moving its first letter to the last changes the scale by \(x^{q_0}\) at total charge zero, exactly the factor of \(\mathrm{Shift}_{\operatorname{Sym}^2D}/x\). Hence the exceptional eigenvalue is the original rotation eigenvalue \(\mu\). An opposite shift convention yields \(\mu^{-1}=\mu\) and the same sector.

## 3. Exact ranks via the two factors

At \(x=1\) use neutral word orbits of rotation eigenvalue \(\mu\), taking the signed orbit sum as a column and the coordinate of the representative as a row. The local rules in Section 2 compute the entries integrally. Elimination mod 2521 gives:

| Half-length \(s\) | Exceptional dimension | Rank \(T_I(0)\) | Rank \(T_I(1)\) | \(F_s\) |
| ---: | ---: | ---: | ---: | ---: |
| 3 | 3 | 0 | 3 | 27 |
| 4 | 5 | 3 | 2 | 78 |
| 5 | 11 | 2 | 9 | 241 |
| 6 | 23 | 9 | 14 | 720 |
| 7 | 57 | 14 | 43 | 2173 |
| 8 | 141 | 43 | 98 | 6518 |
| 9 | 351 | 98 | 253 | 19585 |

Each modular nonzero minor is a lower bound on the corresponding generic complex rank (use the exceptional projector of the normalized shift, regular at \(x=1\)). In every row the two bounds add to the dimension, so fusion proves equality. The total rank is \(3^s\) minus the dimension lost in the exceptional block. Independently, using the original three \(2\times2\) trace slices at \(t=7\) mod 251 gives the same exceptional \(T(1)\) rank in all the odd rows. The even rows agree with earlier exact calculations. The accompanying checker uses both representations.

## 4. A uniform strict gap and exponential defect

Let \(d=1\) for odd \(s\), \(d=2\) for even \(s\), and \(k=(s-d)/2\). Select words on plus and minus signs with \(k\) negative signs, such that any two rotations of different selected words, and distinct rotations of the same word, have Hamming distance \(>2d\). Require this also when comparing any two different shift indices of the same word, so each has full period. On each selected word choose \(2d\) positive sites in cyclic order and replace the positives in the odd positions of that list by zeros in the input, and in the even positions by zeros in the output. Both resulting words are neutral.

In a unit-twist \(T_I(0)\) entry between one chosen input and its own output, there is exactly one nonzero cycle of the auxiliary bit: the switches are fixed at the zero positions, alternate in direction, and all unchanged signs have nonzero diagonal coefficients. For a different representative or a nontrivial cyclic shift, the at most \(2d\) erasures cannot cover all disagreements of the underlying sign words. At a remaining disagreement a direct transition from plus to minus or vice versa is impossible. This exhibits a diagonal nonsingular minor from the signed input orbit sums and the output coordinates. The spin words retain full period since their minus positions do, so every chosen input orbit supports the desired \(\mu\). Its rank survives generically as above. Fusion makes this a lower bound on \(3^s-F_s\).

For a fixed nontrivial shift, a rejected sign word has at most \(2d\) changes along the permutation cycles of that shift. Choosing the change locations and the initial bit in each cycle gives at most \(2^{\lfloor s/2\rfloor}\sum_{j\le2d}\binom{s}{j}\) choices. Summing over shifts still leaves \((1-o(1))\binom{s}{k}\) eligible words. A greedy selection deletes at most \(s\sum_{j\le d}\binom{k}{j}\binom{s-k}{j}\) of these per word, giving the bound \(\Omega(2^s/s^{2d+3/2})\).

For every odd \(s=2k+1\ge7\), at least one eligible word is explicit: take the minus set \(\{0,\ldots,k-2\}\cup\{k\}\). A shift by 1 or 2 has intersection size \(k-2\); shifts from 3 through \(k\) have intersection at most \(k-2\), since the interval overlap is at most \(\max(0,k-1-j)\) for shift \(j\), plus at most the singleton \(k\). Reverse shifts have the same intersection counts. This yields a positive defect in all these odd lengths, and the exact \(s=5\) row fills the remaining case.

The observed relation between exceptional ranks at consecutive lengths is not used and is not proved in general.
