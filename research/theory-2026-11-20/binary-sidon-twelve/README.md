# A four-layer Fourier certificate for binary Sidon sets: s₂(12) ≤ 83

A Sidon subset of F₂^d has no zero sum of four distinct elements. We show that a Sidon subset of F₂^12 cannot have 84 elements. This gives an unconditional upper bound 83 by taking subsets. A 66-point example remains known; the two bounds do not determine the exact maximum. We use the [certified maximum 48 in binary dimension eleven](https://github.com/mxym/math/tree/05006795410cf1c8b8268ba3490238200fd3487b). The earlier proof, its full replay and the 84 upper bound it gives in dimension twelve are in that repository. The historical baseline is [Czerwinski–Pott, Table 2](https://arxiv.org/html/2411.12911v3#S6.T2). No code-classification tables or symmetry assumptions are used below.

## 1. All quarter shapes

For |S|=n in V=F₂^d write w(u)=∑_{x∈S}(−1)^(u·x). Summing over V gives ∑w²=2^d n and ∑w⁴=2^d(3n²−2n), by orthogonality and the absence of nontrivial zero-sum quadruples. Let m be the largest affine hyperplane size. For nonzero u, n mod 2 ≤ w(u)² ≤ (2m−n)². Thus summing (w²−(n mod 2))(w²−(2m−n)²) over u≠0 gives a nonpositive integer. This determines a lower bound on m.

Take n=84. Applying the inequality in dimension 12 and the dimension-eleven result gives m=48. Among **all** m-point hyperplanes choose one for which the largest sub-hyperplane section a is as large as possible. The same inequality inside this 48-point half, now in dimension 11, gives a≥29. The complementary 36-set splits into c≥d with c+d=36. The four parallel quarter layers have sizes n_i=(a,48−a,c,d); any two form part of an affine hyperplane of the original space, so every two sizes sum to at most 48. This implies exactly (29,19,18,18), (29,19,19,17), (30,18,18,18). The affine identification puts the four indexed layers A_i in a common F₂^10=W, with i=0,1,2,3 representing the two-bit additive index.

## 2. Allowed character profiles and exact moments

For u≠0 in W, let v_i be the signed Walsh coefficient of layer A_i. For each b in F₂² the global Walsh coefficient is ∑_i(−1)^(b·i)v_i and has modulus ≤2m−n. Also |v_i|+|v_j|≤2a−m whenever n_i+n_j=m: the pair makes another maximal-size hyperplane, whose internal sections are bounded by the globally chosen a, and both signs occur as Walsh extensions. Each v_i has parity n_i. Consequently we may enumerate all four absolute values and the sign of their product (zero product may use sign +1) satisfying these necessary conditions. Equivalently their largest absolute extension is the sum of the four magnitudes, minus twice their least magnitude when their product sign is negative. The independent checker directly builds the four signed extensions instead of using this shortcut.

Write Q=1024. Over all u including zero the 16 basic moment rows, in order, have totals
* constant: Q;
* v_i²: Q n_i; v_i⁴: Q(3n_i²−2n_i);
* v_i²v_j² for the six lexicographic pairs i<j: Q n_i n_j;
* v₀v₁v₂v₃: 0.

The mixed-square identity follows from disjointness of the four unordered distinct-pair-sum sets ΔA_i. A collision from two different layers would be a forbidden quadruple. The last identity holds because one point in each of the four quarters cannot sum to zero. Remove the explicitly known u=0 profile (n_i) from each right-hand side.

## 3. The information carried by even layers

Let g_i be the XOR of all points in A_i for each even n_i. Then u·g_i ≡ (n_i−|v_i|)/2 mod 2: flipping the sign changes this half by v_i, an even number. Classify the ordered tuple of g_i up to a change of basis in its span G: each successive vector either belongs to the current span or becomes the next basis vector. Starting at the zero space gives every possibility including zero/repeated vectors. For rank r all 2^r functionals on G occur exactly Q/2^r times. Retain only profiles whose implied parities give a functional on G, and add the corresponding exact count rows (including the known zero character when computing totals).

For each h≠0 in G, let χ_h(u)=(−1)^(u·h). Orthogonality gives
$$
 \sum_{u\in W}\chi_h(u)v_i(u)^2 = Q\#\{(x,y)\in A_i^2:x+y=h\}=2Q\,\mathbf1_{h\in\Delta A_i}.
$$
These four sums lie in [0,2Q], and their sum is at most 2Q, as the ΔA_i are disjoint. The upper-bound rows for each h are, in order, −χ_h v_i² ≤ 0 and χ_h v_i² ≤ 2Q *after summation* for i=0,1,2,3, followed by χ_h∑_i v_i² ≤ 2Q after summation. Always subtract u=0 explicitly. Knowledge of the ambient positions of h is unnecessary: the restriction of u to G determines its sign.

## 4. Integer certificates

Each surviving profile has an unknown nonnegative multiplicity. For an integer multiplier vector z, equality rows have unrestricted multipliers; upper-bound rows must have nonnegative multipliers. The verifier checks that every column dotted with z is nonnegative, yet every weighted right-hand side is strictly negative. This contradiction even excludes real nonnegative multiplicities. Signs and all arithmetic in validation are exact; the floating-point discovery algorithm is unnecessary for replay.

At the first two shapes the basic rows suffice. At (30,18,18,18) there are 67 ordered XOR-span types; all are excluded. The included immutable JSON stores 69 certificates. The independent verifier expands signed profiles rather than reproducing the discovery routine, independently derives restriction signs by binary dot products, recomputes all shapes and modes, rejects omitted or extra keys, and checks all 6,220 columns. The least strict negative margin across the certificates is 3,200. A positive 66-point Sidon control has even XOR span of rank 3; all signs occur and the checker compares every Fourier-signed second-moment sum with actual pair differences.

## Replay

Run `python3 -O check.py` and `python3 -O control.py` (standard library, Python ≥3.10). The first checks every certificate in `cert84.json`; the second verifies the known witness and its moment signs without using any certificates. Optional `cert.py` uses NumPy/SciPy to rediscover valid multipliers; neither numerical solver success nor the particular normalizations of the multipliers are a premise.
