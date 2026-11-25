# Symmetric border rank lower bound for Lovitz's 27-variable cubic

Over C, use Lovitz arXiv:2609.28292 §4. Let V have dimension 9, the union of G_i of dimension 5 with intersection the line Cc, and let Z have independent basis e_i for the 18 grid positions (two copies of a 3 by 3 grid). Write w_i for the grid vectors. The nonzero lambda factors may be absorbed in e_i. Scaling Z and the entire cubic degenerates Lovitz's tensor to
`F = sum_i w_i² e_i`.
We prove the symmetric border rank of F is at least 30, hence the same lower bound for Lovitz's tensor.

## Border apolarity and dimensions

Suppose the symmetric border rank of F is at most 29. By [Buczyńska–Buczyński's border apolarity theorem](https://arxiv.org/abs/1910.01944), there is an apolar ideal I in the closure of ideals of 29 points with generic Hilbert function, hence with Hilbert function (1,27,29,29,...). The fiber of apolar ideals with this Hilbert function in that closed component of the multigraded Hilbert scheme is projective and invariant under the one-dimensional torus scaling Z, since F is an eigenvector. Take a torus limit of I in this fiber. The resulting ideal is bigraded by (V-degree,Z-degree), and its graded annihilators W_ab ⊂ Sym^a V ⊗ Sym^b Z are closed under polar derivatives. The total dimensions in degrees 2 and 3 both equal 29.

Write A=W_20, B=W_11, C=W_02, p=dim C. By apolarity A ⊃ K=span{w_i²} of dimension 18 and B ⊃ D={sum_i w_i(x) w_i⊗e_i : x∈V*} of dimension 9, by concision of the grids. Each nonzero element of D has matrix rank at least 3: at least one block's evaluations form a nonzero additive 3 by 3 matrix, with at least three nonzero entries (if one row is zero all rows are constant; otherwise each row has a nonzero entry). Any three distinct vectors in a single grid are independent, because the linear dependency matroid of vectors u_r−2v_s is the cycle matroid of K_{3,3}; any cycle has size at least four. The matrix columns at these positions are therefore independent. Put t=dim A−18, so dim B−9=2−t−p with t+p≤2.

## Mixed prolongations

If B=D, any Q∈ W_21 has polar derivative in direction x of the form D(Lx) for an endomorphism L of V*. Columnwise quadratic symmetry implies L* w_i is proportional to w_i for every i. Each rectangle gives a dependence with all coefficients nonzero and unique up to scale, so the eigenvalues of its four vectors agree. The rectangles connect each grid, and the grids both span their respective five-dimensional G_i containing c. Therefore L* has the same eigenvalue on both G_i, hence it is scalar. Thus dim W_21≤1.

For one extra R, write derivative D(Lx)+b(x)R. In each column i the symmetry condition is w_i∧L*w_i plus R_i∧b equal to zero, up to simultaneous choice of sign. If any R_i is nonparallel to w_i, reduce modulo w_i to force b into span(w_i,R_i). The kernel at b=0 has dimension at most one as above, so dim W_21≤3. Otherwise write R_i=r_i w_i. Then Q is given by diagonal multipliers m=(m_i) and the condition mE ⊂ E+Cr, where E is the 9-dimensional evaluation subspace of C^18. For every linear dependence relation l among the w_i,
`sum_i l_i m_i w_i = l(r) b`.
If r breaks a rectangle relation, b lies in the corresponding 3-dimensional rectangle span, giving dimension at most 4 with the scalar kernel. If r respects all rectangles, m is constant in each grid and the dimension is at most 2.

For two extras R,S, write the polar derivative D(Lx)+b(x)R+d(x)S. In each column reduce its symmetry equation modulo w_i. If some R_i,S_i are independent there, their wedge equation puts both b,d into the 3-dimensional span of w_i,R_i,S_i, giving dimension ≤7 with the scalar kernel. Otherwise each nonzero projected column yields one constraint of the form λ_i b+μ_i d in a two-dimensional plane, by writing its two projected vectors as multiples of a common vector. Two independent coefficient pairs (λ_i,μ_i) yield dimension ≤5. If there is only one independent pair, change the complement basis so that S is all parallel to the w_i, bound b to a plane and use the one-extra bound ≤4 for its kernel, giving ≤6. Finally both extras may be completely diagonal. Then for each rectangle relation l, the vector l(r)b+l(s)d must lie in its 3-dimensional span, by the dependence equation above. If the residual vectors (l(r),l(s)) span dimension two this gives ≤7. In dimension one, change complement basis so s respects all rectangles: bound b to 3 dimensions and use the one-extra bound ≤2 for its kernel. Dimension zero is impossible: the space of tuples respecting all local rectangles is the direct sum of local grid evaluation spaces of dimension 5+5=10, only one larger than E. Hence in all cases dim W_21≤7 for two extras.

For p=0, W_12=W_03=0 by polar closure. For B=D and p≤2, any Z-polar derivative of Q∈W_12⊂V⊗C has matrix rank at most p, since it is a sum of p terms v_j⊗q_j(z). It lies in D and hence vanishes, implying W_12=0. For B=D+CR and p=1, if W_12 is nonzero, write its element v⊗q. Its Z-polars span v⊗im q disjoint from D by the lower bound on nonzero matrix rank in D; thus q has rank one. Since C=Cq and dim(B∩(V⊗im q))≤1, dim W_12≤1.

Always dim W_03≤p for p≤2. There exists a fixed polar direction ξ for which contraction C→Z is injective. If two independent symmetric matrices A,B were to have Aξ,Bξ dependent for every ξ, then if A has rank ≥2, comparing two ξ with independent A images and also their sum shows B is a scalar multiple of A (vectors in ker A are handled by translating those two ξ). If A and B have rank one their images must coincide; symmetry again makes them proportional. This proves existence for p=2, the p=1 case being immediate. Now contraction W_03→C by ξ is injective: if ∂ξP=0, then for every η the derivative ∂ηP∈C is killed by ∂ξ and must be zero, hence P=0.

## Pure V prolongations via syzygies

Let J be the 27-dimensional space of quadrics in Sym² V* vanishing at the 18 grid points. Write A^⊥⊂J and ℓ:J→U=J/A^⊥, dim U=t. Denote by S the image under id⊗ℓ of the linear syzygy space ker(V*⊗J→Sym³V*). A finite exact check (companion script) gives codim(V*J in Sym³V*)=18. Therefore by polar closure and by exactness of the induced quotient of the multiplication map,
`dim W_30 ≤ codim(V* A^⊥) = 18+9t−dim S.`
We prove dim S≥4 for t=1 and ≥9 for t=2.

Write V*=X_0⊕X_1⊕X_2, where X_0 is the dual line to c and the X_i (i=1,2) are the two four-dimensional dual complements. The cross-quadrics X_1X_2 lie in J. The local space L_i of quadrics in X_0+X_i vanishing on grid i and c has dimension 5, and is also in J; such quadrics have zero coefficient at X_0². After killing X_1X_2, a quadric is determined by its two local restrictions, sharing the c² coefficient. It follows that J/(X_1X_2+L_1+L_2) is a line detected by evaluation at c. Indeed this quotient has dimension 27−(16+5+5)=1. The companion script verifies both that evaluation at c detects this line and that products of quadrics vanishing on the grid and c have codimension 21; hence evaluation at c alone has a 6-dimensional syzygy image (18+9−21). It also verifies on one local block a single syzygy of L_i with invertible 5-by-5 coefficient matrix (determinant −16 in the chosen basis). The second block is identical. In particular any nonzero linear image of L_i yields a nonzero image of this internal syzygy.

For t=1, if the cross quadrics have a nonzero image on xy with x∈X_1 and y∈X_2, syzygies x′(xy)−x(x′y), with x′∈X_1, yield three independent directions in X_1. Similarly X_2 supplies three, giving ≥6. If cross images vanish but there is f∈L_i with nonzero image, then for every z in the opposite X_j there is a syzygy expressing zf as a sum of linear multiples of cross quadrics, since every monomial of f contains a variable from X_i. It yields four independent directions in X_j. Otherwise the map is proportional to evaluation at c, which gives six as above.

For t=2, first assume the cross image has dimension two. A fixed y gives a map X_1→U of rank d. The same cross syzygies give the image of x∧x′ ↦ x⊗ℓ(x′y)−x′⊗ℓ(xy), of dimension binom(4,2)−binom(4−d,2), namely 3 for d=1 and 5 for d=2. The formula follows by choosing a basis adapted to the map's kernel. If a fixed argument in each block realizes a rank-two map, the two syzygy blocks give 5+5. If just one block does so, the other has two rank-one maps with independent image lines, since the total cross image is U; its two contributions are disjoint and give 3+3. It is impossible that both blocks lack a rank-two map: two fixed x with independent rank-one image lines would give rank two in X_1→U for generic common y. Thus this case gives rank at least 10. If the cross image has dimension one, its own cross syzygies give six in that line, and quotienting U by the line projects onto a scalar instance of the t=1 argument, giving at least four more.

If the cross image is zero, set A_i=ℓ(L_i) ⊂U. The opposite variables as above show S includes (X_2⊗A_1)+(X_1⊗A_2), giving 4(dim A_1+dim A_2). If this sum of dimensions is at least 3 we are done. If A_1+A_2 is proper, it must be a line by surjectivity and the dimension-one remaining generator. Projection to U/(A_1+A_2) is detected by evaluation at c and gives six more than the at least four dimensions already in that line. Otherwise A_1+A_2=U and the dimension sum is 2. The existing directions have dimension 8. For any i with A_i≠0 the internal full-rank local syzygy has nonzero image in (X_0⊕X_i)⊗A_i, disjoint from the eight existing directions: either the two A_i are independent lines or one is zero. Thus dim S≥9.

## Contradiction

Consequently dim W_30 is at most 18, 23, 27 for t=0,1,2 respectively. The degree-three sums allowed by the preceding bounds are:
- (t,p)=(0,0): ≤18+7=25;
- (0,1): ≤18+4+1+1=24;
- (0,2): ≤18+1+0+2=21;
- (1,0): ≤23+4=27;
- (1,1): ≤23+1+0+1=25;
- (2,0): ≤27+1=28.

All are smaller than 29. This excludes the required border-apolar ideal, proving symmetric border rank at least 30 even for F. The argument does not settle the ordinary border rank.
