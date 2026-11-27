# Perfect AREs over a fixed abelian group

All logarithms are base two. Let X_1,...,X_k be nonempty finite sets with k >= 1, f: product_i X_i -> {0,1}, and G a fixed finite abelian group written additively. Each party samples a G-valued message from a law depending only on its input. Conditional on the inputs, the parties' randomness is independent. The external evaluator receives only their sum. Perfect correctness means a decoder outputs f with probability one on every input; equivalently, the sum distributions for different outputs have disjoint supports. The exact statements permit arbitrary real probabilities. Privacy error delta means there is one simulator law Q_b for each output b such that every sum law for output b is within total variation (TV) delta of Q_b. Thus two sum laws for one output are within 2 delta, not necessarily delta. TV = (1/2) times the counting-measure l1 norm. There is no shared randomness or setup.

## 1. The fixed-group theorem

Call f XOR-separable if f(x) = c xor f_1(x_1) xor ... xor f_k(x_k), for local bits f_i and a fixed bit c. A party is essential if changing only its input can change f.

**Theorem 1.** Perfect correctness and perfect privacy over G are possible exactly as follows:

| Group order | Functions possible |
|---|---|
| Even | XOR-separable |
| Odd and greater than one | At most one essential party |
| One | Constant |

Here and below |G| means cardinality. The model makes no additional private-sampler rationality assumption.

### 1.1 Mixed rectangles and reductions

Fix two coordinates i,j and all other inputs. The parity of the four values on a two-by-two rectangle in those coordinates is zero for XOR-separable f. Conversely, if every such parity is zero, fix anchor a and define f_i(t)= f(a with coordinate i replaced by t) xor f(a). For any other-coordinate configuration, the difference between using a_i and t at coordinate i is unchanged when one other coordinate changes: this is precisely the corresponding rectangle identity (trivial if the two symbols coincide). By changing other coordinates one at a time this difference is always f_i(t). Changing the anchor into x one coordinate at a time now proves f(x)=f(a) xor f_1(x_1) xor ... xor f_k(x_k).

Thus a nonseparable f restricts to an odd-parity two-by-two table. It has one or three ones, so reindexing rows/columns and possibly flipping the output gives OR with its unique zero at (0,0). This restriction preserves the group, correctness, and privacy error: a fixed party's message distribution can be sampled with independent extra private randomness by one of the two active parties, who adds all such messages to its own. The full distribution of the sum is unchanged. If instead f is separable with at least two essential parties, restrict to two such parties, choosing two local symbols with distinct f_i values in each, and fix all other inputs. Local reindexing and a possible output flip give two-party XOR, again with unchanged sum laws after absorption.

### 1.2 The convolution identity

For any two-party encoding let L_0,L_1 and R_0,R_1 be the local message laws and let mu_ij=L_i*R_j. Here (a*b)(h)=sum_x a(x)b(h-x). Independence and commutativity imply

    mu_00 * mu_11 = mu_01 * mu_10.                          (1)

For a complex-valued function on G write its unnormalized Fourier transform as h^(chi)=sum_g h(g) chi(g) for all characters chi. Orthogonality gives (f*g)^=f^g^ and the Parseval identity sum_g f(g) overline(h(g)) = (1/|G|) sum_chi f^(chi) overline(h^(chi)). In particular the transform is injective.

For exact OR, perfect privacy means mu_01=mu_10=mu_11=C; set S=mu_00. By (1), (S-C)*C=0. For each chi with C^(chi) nonzero we have (S-C)^(chi)=0; frequencies with C^(chi)=0 do not contribute to the Parseval pairing against C. Thus <S-C,C>=0. But exact correctness gives <S,C>=0, while ||C||_2^2>0. This recovers the known exact OR impossibility of Ishai–Kushilevitz–Yerushalmi.

For exact XOR write P=mu_00=mu_11 and Q=mu_01=mu_10. Then (1) is P*P=Q*Q, with P,Q nonzero and with disjoint supports by correctness. The next lemma gives the odd-order obstruction without rationality.

### 1.3 Odd-order convolution-square lemma

**Lemma 2.** Let G have odd order. If A,B are complex-valued functions on G with disjoint supports and A*A=B*B, then A=B=0.

*Cyclotomic reduction proof.* Put M=exp(G), the least common multiple of the orders of elements of G. It is odd. The case G={0} is also included (M=1). Fix a primitive M-th root zeta and K=Q(zeta). Each character value belongs to K. In the Fourier coordinates the equation gives A^(chi)=s_chi B^(chi) for a sign s_chi in {+1,-1}; choose either sign when both vanish. Suppose one original coefficient is nonzero and rescale A and B by the same scalar so that coefficient is one. Keep the selected signs, impose that coefficient equals one, and impose that coefficients outside each original support vanish. The resulting system is linear over K, consistent over C by its construction. Gaussian elimination over K uses exactly the same pivots as over C, so it is also consistent over K. We obtain a K-valued pair with disjoint supports, not both zero, and equal convolution squares by Fourier injectivity. It need not be a probability pair.

Set R=Z[zeta], with the Z-basis 1,zeta,...,zeta^(phi(M)-1). Clear the finitely many rational denominators relative to this basis. Divide every entry of both functions by their largest common integer power of two in R: equivalently, take the smallest two-adic valuation of their nonzero integer basis coordinates. Then all entries remain in R and some entry has nonzero reduction in R/2R. The polynomial presentation R/2R = F_2[T]/(Phi_M(T) mod 2) shows this is a reduced ring: the monic polynomial Phi_M mod 2 divides the squarefree T^M-1, whose derivative in characteristic two is T^(M-1). Frobenius r -> r^2 on this quotient is consequently injective. In its commutative group algebra, squaring sum_g a_g [g] gives sum_g a_g^2 [2g]. Since G has odd order, multiplication by two is a bijection. Squaring on the group algebra is therefore injective as well. Reducing the equality of squares forces the two coefficient vectors to agree, and their disjoint supports force both to vanish. This contradicts the chosen nonzero reduction.

*Principal-minor proof.* There is an alternative which does not change the complex coefficients. Use the same signs with B^=s A^ and let T be the corresponding Fourier multiplier on coefficient vectors. Then B=TA. With n=|G|, the entries of T are n^(-1) sum_chi s_chi chi(h-g) at row g and column h. They belong to R'=Z[zeta,1/n] and T=I-2E, with E the multiplier projecting onto the negative-sign characters. The ideal 2R' is proper: otherwise n^j/2 would belong to Z[zeta] for some j >= 0, but this rational, nonintegral number is not an algebraic integer. Thus every principal submatrix T_{S,S} has determinant congruent to one modulo 2R' and is invertible over C. Taking S=supp(A), disjointness gives 0=B|_S=T_{S,S} A|_S, so A=0; hence also B=0. In even order the lemma is false: point masses at zero and a nonzero element of order two have identical convolution squares and disjoint supports.

### 1.4 Complete the proof of Theorem 1

Exact OR impossibility and Section 1.1 enforce XOR separability in all groups. If |G| is odd, Lemma 2 and the XOR restriction then exclude every f with two or more essential parties. The trivial group has a single possible observed sum and cannot compute a nonconstant function perfectly. Conversely, for even |G|, choose h in G of order two and let party i send f_i(x_i) h deterministically: the sum encodes the parity, and flipping by the constant c gives f. For a function depending only on party i, any two distinct elements of G encode its two possible output values with all other parties sending zero. Constants use only zero. Each sum here is determined by f, so privacy as well as correctness is perfect.

## 2. A separate group-size bound at perfect correctness

**Theorem 3.** For any two-party OR encoding over G with perfect correctness and simulator TV error delta, write C=mu_11 and x=||C||_2. Then

    delta >= x/(2+2 sqrt(3)) >= 1/((2+2 sqrt(3)) sqrt(|G|-1)). (2)

The premise forces |G|>=2, and the inequalities hold for all delta >= 0 (they rule out delta=0). The same last bound holds for every non-XOR-separable fixed finite-domain Boolean f. No stronger condition such as deterministic encoding of input zero or flat encoder laws is imposed.

Set S=mu_00, D=mu_01, E=mu_10, and r=max(TV(D,C),TV(E,C)) <= 2 delta. Write T_0=S-D-E+C, U=D-C, V=E-C. Equation (1) is T_0*C=U*V. In Fourier coordinates, at a frequency where C^ is nonzero, T_0^ overline(C^)=U^ V^ overline(C^)/C^, with the last ratio of modulus one; frequencies where C^ is zero contribute zero to the left pairing. By Parseval and Cauchy–Schwarz over characters,

    |<T_0,C>| <= ||U||_2 ||V||_2 <= 2r^2.                 (3)

The last inequality holds because a real signed law difference of TV at most r has positive mass and negative absolute mass both at most r, and hence squared l2 norm at most 2r^2. Moreover |<U,C>| and |<V,C>| are at most r ||C||_infty, since both signed differences sum to zero and C takes values in [0,||C||_infty]. Exact correctness makes <S,C>=0. Substituting <T_0,C>=x^2-<U,C>-<V,C> into (3) gives x^2 <= 2r ||C||_infty+2r^2 <= 2rx+2r^2. It follows that x <= (1+sqrt(3))r, including r=0. Also C is supported on at most |G|-1 elements, since S is a disjoint nonzero probability law. By Cauchy–Schwarz x >= 1/sqrt(|G|-1). This proves (2), including explicit simulator versus pairwise error normalization. Theorem 3 for general f follows by the OR restriction from Section 1.1. In particular, whenever delta > 0 it gives log2|G| >= 2 log2(1/delta) - 2 log2(2+2 sqrt(3)). This is a converse only: it neither asserts a sharp coefficient nor gives a statistical upper bound for any fixed G.
