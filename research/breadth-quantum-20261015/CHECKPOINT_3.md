# N0 checkpoint 3: complex high-copy code probes and a second failed tensor certificate

15 October 2026 (Asia/Shanghai). Yongxian Zhang (张永贤), South China
University of Technology. No external funding. OpenAI AI assistants
assisted. Original rights reserved; external inputs retain attribution.

**Complete N0 remains open in this packet; new major solutions = 0.**
The formulas below are an exact diagnostic reduction on explicitly
specified code families. They are not an assumption that an arbitrary
rank-two coefficient matrix lies in such a family.

## 1. Graph-state conventions and normal probes

All linear algebra in this section is over F_3, and omega=exp(2 pi i/3).
For a symmetric zero-diagonal k-by-k matrix G, define

    |G>=3^{-k/2} sum_x omega^{(x^T G x)/2}|x>.

Here1/2 means2 in F_3. Put X_a|x>=|x+a>, Z_b|x>=omega^{b.x}|x>, and

    D(a,b)=omega^{a.b/2} X_a Z_b.

Direct substitution shows D(a,Ga)|G>=|G>, so

    |G><G|=3^{-k} sum_a D(a,Ga).

The support weight wt(a,b) counts sites where (a_i,b_i)!=(0,0).
For each nonzero b, |G> and Z_b|G> are orthogonal because the graph
state has constant-magnitude computational amplitudes. For the two
normal rank-one coefficient rays P_G and Z_b P_G Z_b*, the two diagonal
values of Q_k are equal, and their crossed value is real. Multiplication
by6^k makes them integers:

    A_num=sum_a (-1)^{wt(a,Ga)}5^{k-wt(a,Ga)},
    B_num(b)=sum_a omega^{b.a}(-1)^{k-wt(a,Ga)}2^{wt(a,Ga)}.

The first identity follows by expanding a reduced stabilizer projector;
the second follows by expanding complementary reductions. The a and-a
terms make B_num real. Its Fourier computation takes place exactly in
Z[omega], represented by a pair of integers. The two normal rank-two
sign choices have values2(A_num +/- B_num)/6^k. Actual coefficient-matrix
contractions at k<=4 verify the formulas, including phases and the
integer identity B_num(0)=A_num.

All weighted graphs are enumerated only at k=2,3,4. Larger k use stated
finite graph samples, even though all nonzero Pauli shifts of each sampled
graph are included. At k=14 the finite array has3^14 entries; no state at
unbounded copy number is being checked. No negative normal probe appeared.

## 2. Distinct graphs retain the nonnormal crossed pairing

Let G,H be two such matrices and put Delta=G-H, K=ker Delta, r=dim K.
Choose b,c!=0 with Delta x0=c-b and an arbitrary phase offset g. The four
actual rays are

    u1=|G>, u2=Z_b|G>,
    v1=Z_g|H>, v2=Z_{g+c}|H>.

Both pairs are orthonormal; C=z1|u1><v1|+z2|u2><v2| has rank at most two.
Distinct graphs generically give different input/output planes. We do
not impose normality or replace the crossed term with ordinary
Cauchy–Schwarz diagonal factors.

Put t=-1/5 and let L={(h,Gh):h in K} in F_3^{2k}. Define

    A_g=sum_{h in K} omega^{-g.h} t^{wt(h,Gh)},
    C_g(v)=sum_{h in K} omega^{-g.h} t^{wt(v+(h,Gh))},
    v=(x0,Gx0+b).

Then the two diagonals of the actual crossed Gram matrix are both
(5/6)^k A_g. Its off-diagonal magnitude is (5/6)^k |C_g(v)|. These
identities follow from the Weyl projector expansions above. The matching
condition for two transition cosets is precisely Delta x0=c-b; the
Weyl phase involving b-c is constant on x0+K because Delta is symmetric.
The phase offset g survives as the character on K. Dropping it would
silently shrink the code family, so a separate shifted test retains it.

Thus the determinant sign in this specified family is exactly the sign of

    A_g^2-|C_g(v)|^2.                                      (G)

If Delta x0=c-b has no solution, the cross term is zero. If b or c were
zero, one ray pair would collapse; such a case is not a nontrivial
orthonormal-pair test. The finite coset enumerator may include these
harmless rank-one cases, including v=0. Therefore its recorded minimum
margin may be zero simply because of the identity coset. That zero is
not evidence of a new rank-two optimizer or a strict stability estimate.

### Exact Fourier evaluation of every coset for a chosen character

On F_3^{2k}, f(v)=t^{wt(v)} has ordinary Fourier transform

    fhat(w)=(-3/5)^k (-2)^{wt(w)}.

The one-site calculation is1+8t=-3/5 at w=0 and1-t=6/5 otherwise.
For a basis B of L's ordinary dot-product orthogonal complement and a
vector w0=(-g,0), character orthogonality gives

    C_g(v)=3^{r-2k}(-3/5)^k omega^{-w0.v}
             sum_z (-2)^{wt(w0+zB)} omega^{-zB.v}.

This is a length3^{2k-r} Fourier transform, rather than a direct tensor
array of coefficient matrices. Its two integer outputs a+b omega have
squared modulus a^2-a b+b^2. The comparison in (G) is therefore exact.
When this squared integer can exceed signed64-bit range, the program
explicitly switches to Python object integers before squaring.

The direct quantum contractions, direct coset sums and Fourier outputs
agree on the stated small controls. For the one-edge perturbation H-G,
r=k-2. The packet enumerates every G at k=3,4, all characters of K there,
and every affine coset for each character. At higher k, graph and/or
character samples are explicitly finite. It reaches k=12 using exact
Eisenstein arithmetic. No negative determinant appeared. No inference
to arbitrary G,H, arbitrary two-planes, or arbitrary k is made.

## 3. A second tensor route is too strong even for one qubit site

For the original all-complex crossed Gram problem put R_k=product_i
(I-F_i/2). On four copies of H define

    A_k=R_{13} R_{24},
    B_k=F_{34} A_k F_{12}.

For a four-ray product z=u1 tensor u2 tensor v1 tensor v2, its crossed
Gram determinant is <z,(A_k-B_k)z>. Moreover A_k and B_k factor over the
resource sites. A tempting sufficient proof would be the local Loewner
contraction -A_1<=B_1<=A_1, which would tensorize.

It fails. Already at one site with d=2, take

    w=|0101>+|1010>.

One has A_1 w=w/4 and direct permutation gives

    <w,A_1 w>=1/2,  <w,B_1 w>=5/2,
    <w,(A_1-B_1)w>=-2.

This w is not a four-ray product, so it does not violate the physical
crossed Gram inequality. The underlying qubit endpoint is positive and
all actual witness forms remain nonnegative. The failure excludes the
strong Loewner/tensor-contraction shortcut, not N0 or even the one-copy
rank-two condition. It illustrates again why ordinary positive-matrix
relaxations cannot replace the nonlinear ray and rank constraints.

## 4. Full-rank-two differential controls have not become a theorem

At qubit-wedge zeros embedded in qutrits, the complete real rank-two chart
has1936 parameters for k=5 and5824 for k=6. Fully assembled Hessians, with
EVD orthogonality and independently evaluated action residuals, have
142 and274 numerical zero directions respectively and no eigenvalue
below-1e-9. Their first positive eigenvalues at the sampled points are
approximately0.11577 and0.10062. These are diagnostics at particular
points; no certified neighborhood radius or uniform all-copy theorem
is claimed.

The unrestricted complex Stiefel search of the true crossed ratio ran
1600 computation seconds and completed190 homotopy trajectories at
k=3,4,5. Its best log ratios are within2e-14 of zero. Continuous
non-Clifford flat-phase probes are now being explored separately, using
phase parameters rather than roots-of-unity restrictions. These searches
remain finite heuristics with adversarial gradient controls.

## 5. Quantifier gates still open

Compactness would turn fixed-dimension finite-k counterexamples into one
all-copy NPT state only if their partial-transpose negativity stayed a
fixed positive distance from the PPT boundary. Existing shrinking
finite-copy intervals do not supply that gap. Changing d with k is not
a fixed physical state. A tensor-stable positive-map construction would
be a different sufficient route, but no nontrivial standard map with the
needed all-power property has been constructed here.

Symmetrizing a rank-two witness by swapping input/output planes can
increase its rank to four. Therefore normal-sector results, even if
extended to arbitrary k, would require a valid additional reduction
before they could settle the full complex rank-two target. No such
reduction is assumed in this packet. N0, N3 and N4 remain explicit open
gates; finite search counts and failed sufficient certificates are not
counted as solved major problems.
