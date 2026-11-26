# Signed singlet counts in Hagendorf's mod-three spin-one chain

**Yongxian Zhang** ([ORCID 0009-0000-3864-3536](https://orcid.org/0009-0000-3864-3536)). AI-assisted proof development and internal mathematical checks; no external peer review claimed. 2026-11-26.

Consider the dynamical supercharge in [Hagendorf §4.3, Eq. (36)](https://arxiv.org/pdf/1207.0357), with real couplings \(\lambda,\zeta\):
\[
q(0)=\zeta\,22,\qquad q(1)=\lambda\zeta(02+20)-11,\qquad q(2)=\lambda\,00 .
\]
A letter \(j\) has charge \(j-1\). At twist \(\phi=0,\pm2\pi/3\), use the eigenvalue \(\mu_N=(-1)^{N+1}\) of the twisted translation on \(N\) sites. These are the signed sectors of the length-changing complex; at nontrivial twist they necessarily have total charge zero modulo three. A singlet here means a vector in the kernel of \(Q_N\) and of \(Q_{N-1}^\dagger\) in that sector, not necessarily a total-spin-zero vector. Use \(Q_0=0\).

| Couplings | \(\phi=0\) | Either \(\phi=\pm2\pi/3\) |
| --- | --- | --- |
| \(\lambda\zeta\ne0\) | 3 for odd \(N\), 0 for even \(N\) | 0 for every \(N\) |
| Exactly one coupling zero | 3 for odd \(N\), 0 for even \(N\) | 1 for every \(N\) |
| \((\lambda,\zeta)=(0,0)\) | binary necklace formula below | twisted binary necklace formula below |

On either axis at nontrivial twist, the odd-length singlet is the all-\(1\) state, and the even-length singlet has exact magnetization zero. At zero twist the two additional axis singlets at odd length have exact magnetizations \(\pm1\).

Hagendorf already gives the periodic nonzero-coupling classification and the odd periodic axis states. The pure binary XXZ sectors and their closely related hard-core fermion description are established in [Razumov–Stroganov](https://arxiv.org/abs/cond-mat/0102247) and [Fendley–Nienhuis–Schoutens](https://arxiv.org/abs/cond-mat/0307338). Here those sectors occur as an explicit equivariant summand of the spin-one complex; the argument counts all singlets, including the mixed sectors, all the listed twists and the origin.

## 1. Nonzero couplings

Put \(\alpha^3=(\lambda^2\zeta)^{-1}\), \(\beta=\lambda\alpha^2\), and \(M=\operatorname{diag}(\alpha,1,\beta)\); the real cube root is allowed for either sign. Directly \((M\otimes M)q(\lambda,\zeta)M^{-1}=q(1,1)\). Since \(M\) commutes with the twist, its tensor powers give a chain isomorphism at each twist. Hodge dimensions are therefore unchanged though nonzero Hamiltonian eigenvalues need not be.

The local density at \((1,1)\) is \(2I-X\otimes X^{-1}-X^{-1}\otimes X\), with \(X:j\mapsto j+1\bmod3\) ([Hagendorf §4.3](https://arxiv.org/pdf/1207.0357)). Write \(D|j\rangle=e^{i\phi(j-1)}|j\rangle\); \(DXD^{-1}=e^{i\phi}X\). The density is diagonal and positive semidefinite in the product Fourier basis, including the seam density obtained by conjugating one site by \(D\) or \(D^{-1}\). Every ordinary bond requires identical colors for zero energy, and the seam requires one color to differ by the twist. At nonzero twist these requirements contradict each other. At zero twist the three constant-color products have translation eigenvalue \(+1\) and so survive only at odd length.

This argument uses the periodic local density for \(N\ge3\). At \(N=1\), the untwisted outgoing projection of \(q\) onto antisymmetric length two vanishes, while at a nonzero twist the only eligible input \(1\) has nonzero outgoing projection of \(02+20\). At \(N=2\) with nonzero twist the signed sector is a single line supported on \(02,20\), and the incoming map just identified is onto it. For the untwisted \(N=2\) signed sector, at \((1,1)\) the outgoing cyclic split maps \(01-10\) to a nonzero multiple of \([221]-2[002]+[011]\), \(12-21\) to its charge-reversed counterpart up to sign, and \(02-20\) to a nonzero multiple of \([222]-[000]\). The three charges modulo three distinguish the images.

## 2. Word splitting and mixed runs

On an axis, reverse \(0,2\) and the sign of the twist if necessary to take \(\zeta=0\). In signed twisted rotation coinvariants, the differential is the split sum
\[
d(w)=\sum_{j=0}^{N-1}(-1)^j \operatorname{split}_j(q,w).
\]
Here an overall nonzero scalar in each degree has been removed: in Hagendorf's projected periodic formula, the \(N+1\) terms including the seam are equal after conjugating to a first-site split with alternating signs, and the \(N\) ordinary terms are equal for the same reason. This identifies the complexes and includes the boundary case \(N=1\). Hodge theory identifies the singlet dimension with the cohomology dimension of this word complex.

Pure \(1\) words contribute one at odd lengths and none at even lengths: the twist acts trivially on the word and its signed rotation relation kills it in even length. For mixed words, mark the beginning of a \(1\)-run, and write the resulting cyclic word as a sequence of blocks, each consisting of a nonempty \(1\)-run and a nonempty binary \(0/2\)-run. The number of such blocks is unchanged by both types of splits. Before forgetting the mark, this is the tensor product of the separate run complexes, with the sign from the lengths of the preceding runs. A run \(1^k\) splits with coefficient \(-\sum_{j=0}^{k-1}(-1)^j\), so its complex is the sum of the isomorphisms \(2r+1\to 2r+2\), for \(r\ge0\); each is acyclic. Thus the marked mixed complex is acyclic.

At a nontrivial twist restrict first to the subspace with the required charge modulo three. This does not affect the run contraction, which inserts or removes a charge-zero \(1\). Forgetting the mark is the quotient by the finite block rotation action. Moving a block of length \(a\) past the remaining \(b\) letters gives the Koszul sign \((-1)^{ab}\) (since \(a(N-1)\equiv ab\bmod2\)), and the twist phase of its block charge. This is a chain map: splits preserve each block charge modulo three and change its length by one, precisely as in the ordinary graded permutation of complexes. Rotating all blocks returns with identity sign and the twist of the full eligible charge, which is one. Every rotation that moves one marked start to another is a composition of these rotations. The quotient is therefore the unmarked complex, remains acyclic by averaging in characteristic zero, and contributes no mixed singlets. This includes the origin, when binary splits vanish.

## 3. Pure \(0/2\) words as a rotation character of a matching complex

On a nonzero axis, take \(\zeta=0\), \(\lambda\ne0\), and remove the nonzero factor \(\lambda\) from the purely binary differential. Replace \(0\) by a monomer and \(2\) by a domino. The conserved expanded length is \(w\). A word with \(N\) tiles has \(d=w-N\) dominoes and gives a matching on the \(w\)-cycle, with edge indexed by its initial position \(i\in\{0,\ldots,w-1\}\). The matching is oriented by the increasing list of these positions from the cut. Use the sign correction \((-1)^{\sum i}\). A split of the domino at \(i\) originally has sign \((-1)^{i-j}\), with \(j\) earlier dominoes. Removing this start changes the correction by \((-1)^i\), leaving the simplicial boundary sign \((-1)^j\). The empty matching is included in degree \(-1\).

Take \(R\) to be translation of the positions by \(-1\) and choose twisted tile rotation moving the first tile to last, with factor \(e^{i\phi(j-1)}\) for a tile of type \(j\). Moving a first monomer changes the correction by \((-1)^d\), without an orientation permutation. Moving a first domino changes it by \((-1)^w\), and it simultaneously moves one selected start past \(d-1\) others, with orientation sign \((-1)^{d-1}\). The signed tile relation uses the scalar \(\mu_N e^{-i\phi\ell}\) for the unweighted moved word, where \(\ell\) is the moved tile length (the charge is \(-\ell\bmod3\)). It follows that the required matching character is
\[
\chi=(-1)^{w-1}e^{-i\phi}
\]
for \(R\): the monomer relation gives \((-1)^d\mu_Ne^{-i\phi}=\chi\), and the domino relation gives \((-1)^{w+d-1}\mu_Ne^{-2i\phi}=\chi^2\). Reversing the convention conjugates the character. For each matching one may choose any tile boundary as the cut; moving between these cuts gives precisely the one- and two-step relations just checked. Conversely, each word yields a matching with a tile boundary at the origin, and every translate of a matching that starts at such a boundary is a cyclic tile rotation. This proves the identification with the full character coinvariant complex, including possible stabilizer signs. If \(e^{i\phi w}\ne1\) that character quotient is zero, in agreement with the charge condition.

For \(w\ge3\), the matching complex of the cycle is the independence complex of its line graph, itself a cycle. [Kozlov, Proposition 5.2](https://doi.org/10.1006/jcta.1999.2984) gives reduced homology concentrated in degree \(m-1\) of dimension two for \(w=3m\); in degree \(m-1\) of dimension one for \(w=3m+1\); and in degree \(m\) of dimension one for \(w=3m+2\). The reduced Lefschetz supertrace of \(R\) is \(-1\), since it fixes no nonempty matching and the degree \(-1\) term has trace 1. Accordingly in the dimension-two case its trace on homology is \((-1)^m\). The eigenvalues are a conjugate pair (a real pair from \(\{\pm1\}\) cannot give this trace), and therefore equal \((-1)^{w-1}\omega\) and \((-1)^{w-1}\omega^{-1}\), with \(\omega=e^{2\pi i/3}\). In the dimension-one cases the eigenvalue is \((-1)^{w-1}\). For \(w=1\) there is only the empty matching, and for \(w=2\) the two oriented positions of the singleton domino give a reduced degree-zero line negated by rotation. These agree with the same rule.

Taking the required character commutes with homology. In the nonzero-twist case only \(w=3m\) contributes, one class with \(d=m,\ N=2m\) and magnetization \(3d-w=0\). In the periodic case only the other two residue classes contribute, one class at each \(w=3m+1,3m+2\), with \(N=2m+1\) and magnetization \(-1,+1\), respectively. Adding pure \(1\) words proves the axis row.

## 4. Necklace count at the origin

The pure binary differential now vanishes and the pure \(1\) and mixed arguments above still apply. If \(p=1\) for zero twist and \(p=3\) otherwise, the full twisted shift on binary words has power \(pN\) equal to the identity. Trace its \(\mu_N\)-projector, including the possible higher powers, to obtain
\[
\dim\ker H_N=
{\bf1}_{N\ {\rm odd}}+
\frac1{pN}\sum_{j=0}^{pN-1}\mu_N^{-j}
\left(2\cos\!\left(\phi\,\frac{j}{\gcd(N,j)}\right)\right)^{\gcd(N,j)} .
\]
Use \(\gcd(N,0)=N\). A \(j\)-shift has \(g=\gcd(N,j)\) permutation cycles. Each cycle in a fixed word is monochromatic and crosses the seam \(j/g\) times, giving the displayed two-color sum. This proves the final row. See also [the separate norm identities](https://github.com/mxym/math/blob/a236b148148a706c0fa5e544bd544666830c84dc/research/euclidean-tensor-geometry/hagendorf-mod-three/SUM-RULES.md). The modular script checks representative cases but is not used in the proof.
