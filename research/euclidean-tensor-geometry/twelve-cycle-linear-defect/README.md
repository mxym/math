# Linear, rather than quadratic, defect bound for alternating periodic twelve-cycles

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Let F12(q) be the maximum alternating flattening rank over C of a periodic twelve-cycle with the same local tensor at every site and common physical and bond dimension q. The model is that of [Gesmundo–Landsberg–Walter](https://arxiv.org/html/1801.09106#S1.SS4). This note proves

    F12(2r+1) >= (2r+1)^6 - 29r,
    F12(2r+2) >= (2r+2)^6 - 148r - 16.

These are uniform across q, not exact generic-rank claims. They extend the earlier quadratic-defect result for the same model. In particular, these bounds do not decide the maximal alternating rank in general. Characteristic-p computations in this note certify nonvanishing over C; no characteristic-p optimum is asserted.

## Prior ingredients and retained kernel types

Use the hub tensor and order-two perturbations of the earlier twelve-cycle proof and its exact necklace calculation: there are r ordinary signed classes {a,-a}; at even q there is one additional self-inverse leaf h. At the unperturbed point,

    A_0 = E_00;  A_a = E_(0,a) + c_a E_(-a,0).

At first order, for each ordinary leaf class add arbitrary diagonal loops in each of its two noncore slices, and arbitrary tilted leaf-to-hub returns in the core slice. The self-inverse leaf, if present, is left unperturbed. Relabel columns by sign negation. Decompose using simultaneous rotation of both length-six words, with orbit sums of eigenvalue lambda and evaluation at output representatives.

Recall the signed-multiset base decomposition. In the no-h blocks, the mixed nonzero defects are 5 per (1,1) one-class balanced pair and 20 per (2,2) repetition in a single class, plus 60 per distinct class pair (1,1)+(1,1). The latter has precisely two core letters and has sector defects 12,6,12,12,12,6. This distribution follows from the modular base calculations and the exact total defect 60 from the necklace proof: ranks cannot be smaller in characteristic zero, and the total fixes them. For zero-core words, every balanced orbit with even period loses one dimension, only in the -1 sector. There are 4 per single class (the (3,3) profile), and the prior quadratic proof lifts the zero-core 30-dimensional ordered pair block (2,2)+(1,1) and the 120-dimensional distinct triple block (1,1)+(1,1)+(1,1). Call their direct sum K. We retain all K and all the mixed distinct-pair kernels (call each such fiber E_ij), omitting the one-class kernels totaling 5+20+4=29 per class.

## Schur coefficient and locality

In each retained balanced block choose a base pivot minor of maximal rank. Let L and R be the explicit left and right coordinate projections/embeddings of the remaining zero-order Schur spaces, as obtained by these pivots. For a base matrix with pivot rows u, pivot columns v and complementary rows x and columns y, they are the maps

    L = (identity on x with correction -M0[x,v] M0[u,v]^-1 at columns u),
    R = (identity on y with correction -M0[u,v]^-1 M0[u,y] at rows v).

Base nearest lead coefficients are valid with rectangularly indexed row and column sets. At the base, L M0 = M0 R = 0 in that multiset block by rank equality.

Every marked excursion at first order either uses one noncore loop or one tilted zero return. For a loop, its two signed endpoints occur on one parity and its middle label on the other. After column sign relabeling, comparing the two signed multisets deletes one of the two signs. A tilt likewise changes one signed label count. Every other excursion preserves the signed multiset. Thus a first-order step between two words changes the ordinary signed multiplicity vector by one unit (possibly with either sign) in one coordinate. In particular, from a balanced profile the only possible first-order intermediate blocks have odd total ordinary token count, hence an unbalanced ordinary signed multiset. These entire blocks are full generically by the base-necklace formula (also with h, by its self-inverse ratio 1). Since there is no first-order balanced-to-balanced coupling, the order-two coefficient between any two retained balanced residual fibers is exactly

    L (M2 - sum_J M1[:,J] M0[J,J]^-1 M1[J,:]) R,

where J ranges over the common first-order neighbors. This also shows why accidental degeneracies of unrelated even-count base blocks under symmetric specialization have no effect: they never enter this coefficient. Pivot minor choices for the retained balanced residual fibers themselves are in their own block only. Any omitted residual coordinate can be excluded from the overall minor without removing one of these odd-neighbor inverses.

At order two every term has its two marks in the same ordinary class, since endpoint class counts are both even in every ordinary class. It can therefore change signed multiplicities of one class only. The n=4 mixed distinct-pair fibers have different distributions of counts if their pairs differ, so the direct quadratic entries between such fibers are zero. A self-coupling for one E_ij involves i,j and possibly one extra mark class a. Its terms with a given outsider are local to i,j,a and additive over outsiders. Indeed the direct trace cannot visit an outside leaf absent from its physical word (the outgoing spoke is labeled by that leaf), and a Schur chain can introduce at most one outsider by the single-label rule. If all marks on outsiders vanish, the diagonal is exactly the two-class calculation. This proves immediate generic invertibility of the retained fibers in all sectors other than -1: the local two-class calculation modulo 1009 has nonzero determinants 735,542,701,519,701,542 in the six sectors (the -1 entry alone does not address its coupling to K).

The P2 coefficient on K is block diagonal and local, as before. At order two, coupling E_ij to K can occur only when the K profile contains both signed pairs i,j: with one class changing and total size increasing by two, the zero-core profile must contain the two pairs already present. Conversely no omitted balanced base block is needed. Thus E_ij couples to two K ordered-pair blocks (which have the same underlying class pair), and each triple K whose underlying triple contains i,j. In the -1 sector eliminate K by its invertible P2 blocks. The resulting map W on E has the following shape when identical parameters are copied to all signed classes.

1. The diagonal on each pair is A+(r-2)B, where A is its local r=2 matrix and B the additional contribution of one outsider. Each Schur correction on the diagonal comes from either of the two ordered-pair K blocks or from a single triple containing that pair.
2. Off-diagonal entries can occur only between pairs sharing one vertex. Their only shared K is that one triple, so these entries are the same local triple blocks from r=3 in the natural identification of the three classes. Entries between disjoint pairs vanish.
3. This map is equivariant under S_r, using the natural action on the input kernel and output cokernel copies of each fiber. Its two fibers need not use the same pivot coordinates. This equivariance follows intrinsically from the permutation-invariant tensor and selections of *entire* balanced kernels and odd-neighbor blocks. The second Schur elimination is itself along the permutation-invariant direct sum K. Choosing local pivots merely chooses coordinates; when a permutation reverses a pair, it acts by that fixed two-label swap on its fiber.

## Uniform characteristic-p certificate for the -1 sector

Take p=13, c_a=2 for each designated positive a and c_-a=1, with the same per-sign perturbations in every class. The required odd target-intermediate blocks remain full at this copy: all have odd ordinary count, so their signed ratio product over any primitive token period is an odd power of 2. If the word transfer on a primitive length-ell necklace were singular, the characterization by the twisted exterior power implies that the sixth power of this ratio product equals 1. (For these no-h odd-count blocks, the twist sign is positive.) But 2 has order 12 in F_13, so this sixth power is -1. Thus the only needed inverse denominators are the computed balanced pivots and K blocks.

The files local-negative.cpp and verify-replica.py recover A, B and all off-diagonal blocks from r=2 and 3; they test the resulting modular determinants. For seed 1 the two K block types have determinant 4 and 4; for seed 4 they have determinant 4 and 1. The r=2 and 3 effective W determinants are respectively 1 and 12 for seed 1. Taking representative r=4,...,16 for every residue class modulo 13, seed 1 witnesses all except r=10,13; seed 4 witnesses those two, with determinants 12 and 1.

Here is the transport argument ensuring this finite table proves all r, rather than suggesting a pattern from a finite scan. Describe the pair-block array of W in ordered-pair coordinates. For an ordered listing of a pair, identify its fiber with one fixed two-class fiber by relabeling its first and second classes to 1 and 2. Reversing the order changes the input/output fiber coordinates by the fixed corresponding involutions. In these coordinates each block depends solely on the equality pattern of the four labels of its two pairs, by equivariance. This is true for W above, with coefficients polynomial in r. If it is invertible at a representative r0>=4, its inverse is automatically equivariant (between the input and output fibers in the reversed direction). Every equality pattern occurs when r0>=4, so the inverse's block values there define an array for arbitrary r>=4 using the same pair orientation conventions, equivalently the same equality patterns with their input/output swap actions. This is well-defined since the values at r0 satisfy exactly those swap compatibilities.

In a product of two such operators, sum over *ordered* intermediate pairs and divide by 2, since each unordered pair is then counted twice with matching swap involutions canceling. For given first and last ordered pairs, each possible equality pattern for the intermediate two labels with the distinguished labels is counted by 1, r-d, or (r-d)(r-d-1), where d<=4 counts distinct distinguished labels. Therefore product block coefficients are polynomial in r whenever the factors are constant or polynomial in r. In particular they are unchanged modulo p on replacing r0 by any r>=4 in the same residue class. The transport of the inverse thus remains an inverse, since the products give the corresponding identity for every pair-relation pattern. This works also when p divides r, because only the integer counts and the invertible scalar 2 are used; there is no semisimplicity or division by r in the argument.

For each actual r choose the indicated seed. The complete retained rational S2 matrix in the -1 sector is nonsingular at this modular specialization and hence gives a nonzero rational determinant in the generic complex parameters. W and its modular determinant are values of rational functions with only the pivot, odd-neighbor and K inverses already certified. Even if an unrelated even-count base pivot vanishes at the copy, the formula for S2 does not depend on it, and the rational nonvanishing thus continues to generic parameters. Intersecting the finitely many generic nonvanishing conditions across sectors, the retained original minor has nonzero lowest coefficient in t, with only the omitted 29r base dimensions lost. When r<2 no distinct-class fiber is needed.

## Self-inverse blocks and all even dimensions

Now add one unmarked self-inverse leaf h. Every occurrence of h belongs to the same-label dimer at base and at every order in the given perturbation, so its count is exactly conserved. The earlier even-necklace count adds

    16 + 119r + 180 binom(r,2)

to the no-h base defect. The terms quadratic in r come from precisely two mixed kinds, per distinct class pair i,j:

    h-count 1, n=5: {0, +i,-i,+j,-j,h}, defect 120;
    h-count 2, n=6: {+i,-i,+j,-j,h,h}, defect 60.

Retain those kernels and omit the others (16+119r). Within fixed h-count, the retained kernels all have the same ordinary token total and live in mutually distinct class pairs. Therefore their S2 submatrix is block diagonal by the one-class-change rule; it never touches the no-h submatrix. All first-order neighbors are full base blocks: the ordinary signed profile is unbalanced, irrespective of h, and h-count is fixed. For each retained pair choose a local specialization with only that pair perturbed (all other ordinary marks zero), so its block is exactly the two-class and one-self-inverse q=6 calculation. This certifies generic nonvanishing separately for each block. In the first profile, the five 24-square nonzero residual sectors have determinants 181, 815, 929, 815, 181 modulo 1009; the second profile has a 60-square residual in -1 with determinant 692. As before, exact total base defect from the necklace calculation fixes the relevant fiber dimensions. The all-sector minor conditions intersect generically. Consequently the total loss is at most 29r+16+119r=148r+16.

## Replay

Build each C++ file with a C++17 compiler (for example c++ -O3 -std=c++17 file.cpp -o file). Run the other-sectors executable with arguments 5 2, the selfinverse executable with 6 2, and python3 verify-replica.py ./local-negative (NumPy required). The expected logs are other-output.txt, selfinverse-output.txt, replica-output.txt. The computations only verify local ranks and one modular representative for each replica-count residue; all length-q propagation is mathematical.
