# Proof graph and internal audit

Status: written mathematical proofs. No external review or Lean verification.

## Dependency graph

    coefficient-map definition and original physical matrix
       |
       +-- tree determinant recursion (retained principal diagonals)
       |      +-- monic-polynomial interpolation determinant [Lemma 3]
       |      +-- squared branch-merging Jacobian [Lemma 4]
       |             -> independent (d,p) Jacobian [Lemma 5]
       |
       +-- physical (rates,leak) -> (d,p) leaf elimination [Lemma 6]
       |             -> arbitrary-tree physical Jacobian [Theorem 1]
       |
       +-- resultant multiplicativity and tree recursion
       |             -> full transfer resultant [Theorem 2]
       |
       +-- disjoint branch parameter sets and branch scaling [Lemma 7]
       |             -> exact coordinate multiplicities [Corollary 8]
       |                    -> GMS Conjectures 5.5 and 5.9
       |
       +-- positive tree diagonal similarity and spectral decomposition
                     -> spectral/minimality equivalence [Corollary 9]

All indefinite/zero-rate polynomial cases are included by direct polynomial identities, not by division at singular points. Signs are fixed orientation signs. No irreducibility claim is made for the resultants.

## Nontrivial audit points

1. Dimensions: n vertex diagonals plus n−1 products equal 2n−1 physical parameters. Child merging receives 2s−1 child coefficients plus one link rate; the root adds one diagonal. Each Jacobian is square.
2. The t^(m−1) factor is the derivative of (t,g) -> (t,tg); t=0 is retained, not cancelled.
3. The branch resultant appears twice because the derivative of product Q in its monic factors and the derivative of numerator W in its branch numerators have the SAME interpolation map on the two diagonal blocks.
4. Child polynomials use actual principal submatrices. Dropping boundary losses would make a leaf's polynomial z instead of z+b and create false universal branch collisions. A negative control detects that mutation.
5. The physical-coordinate determinant is proved for any leak root by leaf peeling. It uses a triangular Jacobian, not an assumed invertible parameter map at zero rates.
6. The exact multiplicity statement needs Lemma 7. We set the candidate variable to zero and construct a NONZERO resultant by scaling the disjoint sibling block. Positivity and retained boundary killing ensure the scaled block has no zero eigenvalue.
7. Spectral minimality does not automatically imply globally unique physical parameters. The manuscript claims differential regularity and local smooth invertibility, not a general fibre count.
8. At a positive single-leak point with root discharge output, the monic state pair and scaled discharge pair contain equivalent local information. This uses P(0)=kappa Q(0) and Q(0)>0; it is not silently generalized to distributed outflows.
9. The n=1 case has determinant one. The terminal outgoing edge on an endpoint path has exponent zero. The leak coordinate is not itself a factor, although it can occur inside branch resultants when the leak is not at the observation root.
10. The general proof requires neither numerical derivatives, real data nor experimental resources. Finite exact tests establish their own algebraic statements only; the text is not certified merely because CI is green.

## Still outside the theorem

Multiple free leaks; distinct input/output vertices; multiple input/output sets; unknown graph; nonlinear or time-varying transfers; quantitative inverse stability; full irreducible decomposition and singular-stratum ranks; global solution counts. These are not hypotheses hiding a desired conclusion: they define different, unproved extensions.
