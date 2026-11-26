# Exact alternating rank of periodic physical-3, bond-2 tensors at every length

**Yongxian Zhang** ([ORCID 0009-0000-3864-3536](https://orcid.org/0009-0000-3864-3536)).  
2026-11-26. AI-assisted proof development and internal mathematical checks; no external peer review claimed.

## Theorem

Choose one complex local tensor with three physical slices \(A_-,A_0,A_+\in\operatorname{Mat}_{2}(\mathbb C)\), use it at every site of a \(2s\)-cycle, and flatten the state with coefficients \(\operatorname{tr}(A_{i_1}\cdots A_{i_{2s}})\) across odd versus even sites. Its maximum (equivalently generic) rank \(F_s\), for every \(s\ge2\), is
\[
F_s=3^s-r_s,\qquad r_1=0,\quad r_{s+1}=d_s-r_s,\qquad
d_s=\frac1s\sum_{j=0}^{s-1}(-1)^{(s+1)j}\,[z^0](1+z+z^{-1})^{\gcd(s,j)} .
\]
In particular \(3^s-F_s\sim\sqrt3\,3^s/(8\sqrt\pi\,s^{3/2})\). The first ranks for \(s=2,\ldots,12\) are
\[
8,\ 27,\ 78,\ 241,\ 720,\ 2173,\ 6518,\ 19585,\ 58796,\ 176509,\ 529746 .
\]

The quantum min-cut for this alternating partition is \(3^s\). The upper bound follows by cutting all physical edges on one side. For the lower bound, if a cut uses \(z<s\) physical edges, the two disjoint matchings of adjacent odd and even sites each have at least \(s-z\) pairs with neither external edge cut. Such pairs must be separated at their virtual edge, so the cut product is at least \(3^z 2^{2(s-z)}\ge 3^s\). If \(z\ge s\) the lower bound is immediate.

The [normal-form and fusion supplement](NORMAL-FORM.md) identifies all possible generic loss with one neutral signed-rotation block. The proof below computes its rank by linking the derivative of the fused transfer to a positive Hodge Laplacian of an exact cyclic complex. This determines this entire fixed-dimension, alternating, shared-site family; it does not determine other local dimensions or arbitrary bipartitions or networks. The standard-library-only checker is `node verify.js` (checks the local identity and both transfer ranks through \(s=10\); the all-length proof is not by enumeration).

Let \(T_s(u)=\operatorname{tr}_a\prod_{i=1}^s(uI+\sigma_a\cdot S_i)\) be the untwisted auxiliary-bit transfer on \(V^{\otimes s}\), \(V=\mathrm{Sym}^2\mathbb C^2\). Write \(R_s\) for cyclic shift, \(\mu_s=(-1)^{s+1}\), \(E_s=\ker(R_s-\mu_sI)\), and \(E_s^0\) for its charge-zero part. This proof builds on the normal form and special-point fusion already checked in the repository. It solves the exceptional generic rank in that normal form for every \(s\), not general quantum max-flow. Relevant prior art: [Gesmundo–Landsberg–Walter, model](https://arxiv.org/abs/1801.09106), [Hagendorf, periodic dynamical supercharge and local Hamiltonian, equations (6),(8),(9), and spin-one supercharge in §4](https://arxiv.org/pdf/1207.0357), [Loday, cyclic homology, §2.2.9](https://doi.org/10.1007/978-3-662-11389-9_2).

## 1. Acyclic dynamical complex

In a real orthonormal Cartesian spin basis \(e_1,e_2,e_3\), take \(qe_k=\sum_{a,b}\epsilon_{abk}e_a\otimes e_b\). Let \(\Pi_s\) be the orthogonal projector onto \(E_s\), and put
\[
Q_s=\sqrt{s(s+1)}\,\Pi_{s+1}(q\otimes I^{\otimes(s-1)})\Pi_s.
\]
This is Hagendorf's normalization: his alternating sum over \(s+1\) cyclic insertions has equal projected summands because \(\mu_s\mu_{s+1}=-1\), and his prefactor is \(\sqrt{s/(s+1)}\). This \(q\) is the isotropic point \(x=1,y=0\) of the spin-one supercharge in Hagendorf §4.1, allowing a phase convention for the magnetic basis. The cross-product contraction gives \(((q\otimes1)-(1\otimes q))q(v)=g\otimes v-v\otimes g\), up to the immaterial choice of sign on \(g=\sum_a e_a\otimes e_a\); thus the local condition in his equation (6) is satisfied.

Here is why the complex is not only nilpotent but exact. Let \(A=M_2(\mathbb C)=\mathbb CI\oplus V\), identifying \(e_a\) with \(i\sigma_a\) in \(V=\mathfrak{sl}_2\). Then \(P_aP_b=-\delta_{ab}I-\sum_c\epsilon_{abc}P_c\). Use cyclic Hochschild chains \(C^\lambda_n(A)=A^{\otimes n+1}/\langle 1-(-1)^n R_{n+1}\rangle\), with Hochschild boundary \(b\). Tensors with at least one scalar letter span a subcomplex \(K\): the only way to remove the last unit is to multiply it with either neighbor, and these give opposite terms in cyclic coinvariants. The quotient consists of signed cyclic tensors of \(V\), and \(b\) is the alternating adjacent multiplication projected to \(V\).

For completeness, the inclusion of all-scalar chains into \(K\) is a quasi-isomorphism. Filter by number \(r\) of non-scalar letters. In the associated graded for \(r>0\), first mark a non-scalar letter and write the cyclic word as the ordered sequence of \(r\) blocks \(v_i I^{k_i}\) with \(\sum k_i>0\). Then divide out changing the marked block by the finite signed cyclic group of order \(r\). The sign for moving a block of length \(a\) past the other blocks of combined length \(b\) is \((-1)^{ab}\), equivalent to the original cyclic sign. Only merges meeting a scalar survive on the associated graded. A run of \(k>0\) scalars contributes its \(k+1\) alternating merges, all yielding the same block sequence with that run shortened once; their sum is one when \(k\) is positive even and zero when \(k\) is odd, times the usual sign from the preceding block lengths. This is also valid for the last run (the wrap-around term multiplies the final scalar with the first \(v\), placing \(v\) first), including the single-block case \(r=1\). For \(k=0\) the corresponding operator is zero. Each elementary gap complex is therefore a singleton at \(k=0\) plus direct summands \(2j\to 2j-1\) for \(j\ge1\). The tensor product summand of positive total gap length is acyclic, and dividing by the finite signed block-rotation group preserves exactness by averaging. The positive-\(r\) associated graded pieces are acyclic, so \(K/C^\lambda_\bullet(\mathbb CI)\) is acyclic (the filtration is finite in each degree and bounded below).

The map \(HC_\bullet(\mathbb CI)\to HC_\bullet(M_2)\) is an isomorphism: the generalized matrix trace gives the Morita isomorphism and its composite with scalar inclusion acts by 2 on scalar cyclic chains. Hence the quotient \(C^\lambda_\bullet(A)/K\) is acyclic. In the orthogonal invariant realization of cyclic coinvariants, the adjoint of its boundary from length \(s+1\) to length \(s\) is a nonzero scalar multiple of \(Q_s\): the traceless multiplication has structure constants \(-\epsilon_{abc}\), and rotating each of the \(s+1\) successive merges onto the first yields the same signed projected term. Thus the \(Q_s\) complex is exact, also in the charge-zero summands since every map commutes with the charge. In particular this proves the zero-twist existence assertion (the no-singlet half) of Hagendorf Conjecture 4.2 at the specific isotropic point. His discussion of a possible Hochschild-homology link motivates care in distinguishing his established supercharge from the cyclic-complex identification used here.

## 2. Identify the two transfer images

For this step use the physical transpose \(T_s(u)^t\), which has the same ranks. Standard Cartesian generators are \((S^k)_{ij}=-i\epsilon_{kij}\), so transposing the physical indices changes this sign. The Cartesian entries of the transposed local tensor are then \(L_{ij}(u)=u\delta_{ij}+\sum_k\epsilon_{ijk}P_k\). For \(1\le i,j,k\le3\) the local identity is
\[
u\sum_{a,b} L_{ia}(u)L_{jb}(u)\epsilon_{abk}
 -(u^2-1)\sum_a\epsilon_{ija}L_{ak}(u)
= - L_{ik}(u)P_j-P_i L_{jk}(u).
\]
It follows by the quaternion multiplication just given. For a compact finite verification, for each \(u=0,1,2,3\) and each \(i,j,k\), expand both sides as four integer coordinates \(1,P_1,P_2,P_3\) using that product and compare. Each coordinate polynomial has degree at most 3. Thus this check proves the identity identically. Applied at the first split and traced against the other \(s-1\) local \(L\)'s, the two terms on the right differ by a one-step simultaneous output and input rotation, followed by cyclic trace. Their projections to \(E_{s+1}\leftarrow E_s\) cancel because the two rotation signs multiply to \(-1\). Transfers commute with rotation, so
\[
u T_{s+1}(u)^tQ_s=(u^2-1)Q_s T_s(u)^t.
\]
In particular \(Q_sT_s(0)^t=0\) and \(T_{s+1}(1)^tQ_s=0\). On \(E_s^0\), the symmetric Cartesian bilinear form is nondegenerate, since it pairs charge \(Q\) only with charge \(-Q\), and the real signed rotation projector is self-adjoint for it. Thus physical transpose preserves the rank of each exceptional restriction, and exactness yields
\[
\mathrm{rank}\,T_s(0)\le \mathrm{rank}\,Q_{s-1},\qquad
\mathrm{rank}\,T_s(1)\le \mathrm{rank}\,Q_s .
\]

## 3. Derivative of fusion excludes any common kernel

For all \(u\), auxiliary fusion gives
\[
T_s(u)T_s(u-1)=\operatorname{tr}_{\mathrm{Sym}^2(a,b)}\prod_i M_i(u)+c(u)^s I,
\quad
c(u)=(u+1)(u-2),
\]
where \(M_i(u)\) is the symmetric-auxiliary compression of \(L_{a,i}(u)L_{b,i}(u-1)\). To see preservation of the singlet and the scalar value, use special-point preservation at \(u=1\) and note that varying \(u\) changes the local product by a scalar and a multiple of \((\sigma_a+\sigma_b)\cdot S\), which vanishes on the singlet and preserves both summands. Its value there at 1 is \(-2\), giving \(c(u)=u^2-u-2\). On the symmetric auxiliary summand, \(M_i(1)=2P_{\mathrm{aux},i}\), with \(P\) the spin-one swap, and \(M_i'(1)=I+2B_{\mathrm{aux},i}\), with \(B=S_{\mathrm{aux}}\cdot S_i\). These formulas also follow directly by differentiating the pair of \(L\)'s.

The derivative of the regular transfer, after factoring \(2^s R_s\), is the nearest-neighbor sum of \(P(I+2B)/2\). Indeed a single differentiated local factor can be written as \(2P\) times that two-space operator; the surrounding swaps transport its auxiliary leg to the neighboring site and leave the usual cyclic shift. On \(E_s\), \(c(1)^s I=-2^sR_s\). The extra singlet derivative therefore adds the local scalar \(-c'(1)/c(1)=1/2\) after factoring \(2^sR_s\). The total density is
\[
P(I+2B)/2+I/2=(3I+P-2K_g)/2,\qquad K_g=|g\rangle\langle g|.
\]
For example, use the total-spin sectors \(2,1,0\), on which \(B\) has values \(1,-1,-2\), swap has values \(1,-1,1\), and \(K_g\) has values \(0,0,3\).

By [Hagendorf equations (8),(9)](https://arxiv.org/pdf/1207.0357), the sum of the doubled density on the signed momentum eigenspace is the Hodge Laplacian \(H_s=Q_s^\dagger Q_s+Q_{s-1}Q_{s-1}^\dagger\). Indeed \(q^\dagger q=2I\), \(qq^\dagger=I-P\), and both mixed contractions in (9) equal \(K_g-P\) by the epsilon formula. Thus the differentiated fused transfer restricted to \(E_s\) is \(2^{s-1}\mu_s H_s\), up to using the equally valid reverse cyclic direction. This is nonsingular since the complex is exact.

To handle the order of factors, the two \(T_s\) commute for all spectral values by the rational \(RLL\) identity. In detail, \(R_{ab}=(u-v)I+P_{ab}\) with the auxiliary-bit swap, and if \(X=\sigma_a\cdot S\) and \(Y=\sigma_b\cdot S\), Pauli and spin commutators give \((X-Y)P_{ab}=-[X,Y]\). Expanding \(R_{ab}(u+X)(v+Y)=(v+Y)(u+X)R_{ab}\) then proves the relation; apply it sitewise and take the double trace, using generic invertibility of \(R_{ab}\) and then polynomial continuation. In the common kernel of \(T_s(0)\) and \(T_s(1)\), both terms of the derivative vanish: write the derivative as \(T_s'(1)T_s(0)+T_s'(0)T_s(1)\). Thus their common kernel is zero. Fusion at \(u=1\) gives \(T_s(1)T_s(0)=T_s(0)T_s(1)=0\) on \(E_s\), implying the sum of the two ranks is at most its dimension. Trivial intersection of the kernels gives the reverse inequality, hence equality. The two inequalities in §2 must both be equalities, also on \(E_s^0\).

At \(s=2\) no periodic-density convention is needed: \(E_2\) is antisymmetric total spin one, \(T_2(0)=2B\) has eigenvalue \(-2\), and \(T_2(1)=2(I+B)\) vanishes there. At \(s=1\), \(T_1(0)=0\) and \(T_1(1)=2I\). These match the same recurrence.

## 4. Generic rank, exact enumeration, asymptotic

Let \(d_s=\dim E_s^0\), and \(r_s=\mathrm{rank}(T_s(0)|_{E_s^0})\). Exactness and the identified ranks give \(r_1=0,\ r_{s+1}=d_s-r_s\). A trace of the signed cyclic projector yields
\[
d_s=\frac1s\sum_{j=0}^{s-1}(-1)^{(s+1)j}C_{\gcd(s,j)},
\qquad C_m=[z^0](z+1+z^{-1})^m,
\]
because a rotation-fixed word is a repeat of a block of length \(\gcd(s,j)\) and the whole word has zero charge iff that block does. The projection onto the neutral exceptional eigenspace of the normalized twisted shift is regular near unit twist, with constant dimension there. Each nonzero untwisted minor therefore gives a generic lower rank bound. The twisted fusion upper bound on their sum is \(d_s\); saturation at unit twist shows both rank bounds are exact generically. In the original flattening, other sectors are generically nonsingular by the already established special-point fusion. Thus the generic (and maximum) alternating flattening rank is \(F_s=3^s-r_s\). This does not assert invertibility of the other sectors at unit twist. In particular \(F_2=8,\ F_3=27,\ F_4=78,\ F_5=241,\ F_6=720,\ F_7=2173,\ F_8=6518,\ F_9=19585\).

The \(j=0\) term gives \(d_s=C_s/s+O(3^{s/2})\). The central trinomial estimate, by the local central limit theorem (variance \(2/3\)) or its elementary Fourier integral, is \(C_s\sim \sqrt{3}\,3^s/(2\sqrt{\pi s})\). Unfold \(r_s=\sum_{j=1}^{s-1}(-1)^{j-1}d_{s-j}\). For fixed \(j\), \(d_{s-j}/d_s\to 3^{-j}\); for \(j\le s/2\) this ratio is uniformly \(O(3^{-j})\), and the aggregate tail \(j>s/2\) is exponentially small. The resulting geometric alternating sum is \(1/4\). Thus \(3^s-F_s=r_s\sim\sqrt3\,3^s/(8\sqrt{\pi}\,s^{3/2})\), with the same leading constant in both parities.

## Appendix: finite local identity certificate

The following exact-integer JavaScript verifies all quaternion coefficients, as noted in §2.

```js
const e=(i,j,k)=>i===j||j===k||i===k?0:((j-i+3)%3===1?1:-1);
const U=[1,0,0,0], P=Array.from({length:3},(_,i)=>Array.from({length:4},(_,j)=>+(j===i+1)));
function add(a,b,k=1){return a.map((x,i)=>x+k*b[i])}
function mul(a,b){let c=U.map((_,i)=>a[0]*b[i]+(i?a[i]*b[0]:0));for(let i=0;i<3;i++)for(let j=0;j<3;j++){c[0]-=(i===j)*a[i+1]*b[j+1];for(let k=0;k<3;k++)c[k+1]-=e(i,j,k)*a[i+1]*b[j+1]}return c;}
function L(i,j,u){return [i===j?u:0,...P.map((_,k)=>e(i,j,k))]}

for(const u of [0,1,2,3]) for(let i=0;i<3;i++) for(let j=0;j<3;j++) for(let k=0;k<3;k++){
  let A=U.map(()=>0);
  for(let a=0;a<3;a++)for(let b=0;b<3;b++)
    A=add(A,mul(L(i,a,u),L(j,b,u)),u*e(a,b,k));
  for(let a=0;a<3;a++)A=add(A,L(a,k,u),-(u*u-1)*e(i,j,a));
  A=add(A,mul(L(i,k,u),P[j]));
  A=add(A,mul(P[i],L(j,k,u)));
  if(A.some(x=>x!==0))throw new Error("local identity");
}
```
