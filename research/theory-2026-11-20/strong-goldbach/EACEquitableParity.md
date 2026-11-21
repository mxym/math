# An all-center 2-adic obstruction from equitable factor multiplicities

Let \(N>2\) be even. Suppose \(k\ge2\) distinct odd unit primes satisfy \(N-x_i=\prod_jx_j^{A_{ij}}\) with a nonnegative integral matrix \(A\). In the all-composite terminal application it is irreducible and loopless with row sums at least two, but the main obstruction does not require strong connectivity. Set \(B=I-A,\ r=\dim_{\mathbb Q}\ker B\), and
\[
                         h=[T^r]\det(TI-B)\in\mathbb Z .
\]
A partition of the vertices is *equitable for outgoing multiplicities* if for any two vertices in the same cell, the sums of their row entries over each target cell agree. This includes automorphism-orbit partitions, and the one-cell partition when all row sums are equal.

**Theorem.** If \(h\) is odd, every equitable partition is discrete. In particular a genuinely realized exponent matrix with a nontrivial automorphism, or merely a nontrivial equitable partition, necessarily has \(h\) even, including zero. Every genuinely homogeneous row-arity signature with \(k\ge2\) satisfies this parity condition. Equivalently, if \(h\) is odd, ordinary color refinement from a single vertex color, counting the full outgoing multiplicities in each color, must eventually separate all labels. This is an exact obstruction at **every even center**, with no bound on \(k\) or the multiplicities; it is not an elimination of all homogeneous signatures.

### 1. The matrix condition

Let \(C,V\in\mathbb Z^{k\times r}\) be column bases of the saturated integral left and right kernels. The following are equivalent:
\[
 \begin{gathered}
 h\ {\rm odd};\\
 \operatorname{rank}_{\mathbb F_2}B=k-r\quad\hbox{and}\quad
                     \det(C^\top V)\text{ odd};\\
                    \operatorname{rank}_{\mathbb F_2}
                    \begin{bmatrix}B\\ C^\top\end{bmatrix}=k.
 \end{gathered}
\]
With rank preserved the saturated bases reduce to full left/right kernels; the pairing is nonsingular exactly when the reduced kernel and image of \(B\) are complementary. This is semisimplicity at eigenvalue zero over \(\mathbb F_2\). Conversely the characteristic polynomial is divisible by \(T^r\) over \(\mathbb Z\), reduction cannot increase the rank, and an odd \(T^r\) coefficient makes both the geometric and algebraic multiplicities at zero equal to \(r\) after reduction. Empty determinants are 1. Also \(C^\top{\bf1}=0\bmod2\) is necessary for an actual solution: for each integral left-null \(c\),
\[
                   \prod_i(1-N/x_i)^{c_i}=(-1)^{\sum c_i}.
\]
Reduction at the *full* modulus \(N>2\) gives an even sum, including when \(v_2(N)=1\).

### 2. Uniqueness and existence in the odd 2-adic ball

We record the following stronger local fact. For an integral nonnegative matrix \(A\) with \(h\) odd and \(C^\top{\bf1}=0\bmod2\), the full equations \(X_i+X^{A_i}=N\) have exactly one tuple of odd 2-adic units, for every even positive integer \(N\). For uniqueness among known solutions alone one can use the same argument with the fixed values on the right even if sign parity is not assumed.

Choose \(k-r\) row indices \(I\) of \(B\) independent modulo 2; let \(J\) be their complement. Then \(C_J\) (the rows of \(C\) indexed by \(J\)) has odd determinant, since otherwise some nonzero left-null combination would be supported on \(I\). Use the \(I\)-indexed physical equations plus the \(r\) functions
\[
 H_c(N,X)=\frac{\prod_i (1-N/X_i)^{c_i}-1}{N},
                 \qquad c=\text{a column of } C .
\]
They are integral analytic with integral Taylor coefficients on odd units, by binomial expansion (also for negative \(c_i\)); modulo 2 they and their derivatives are those of \(-\sum_i c_i/X_i\). Equivalently, clearing odd denominators yields integral polynomial equations: the numerator after clearing is divisible identically by \(N\) as an indeterminate. The vector of ones is a solution of these augmented equations mod 2, and their Jacobian is \([B_I;C^\top]\bmod2\), nonsingular. Multivariable Hensel lifting gives exactly one odd solution to the selected equations \(X_i+X^{A_i}=N\), \(i\in I\), and \(H_c=0\). This is also obtained by choosing the unique correction mod 2 at each successive Taylor lift.

This solution satisfies every omitted equation. Write \(E_j=(N-X_j)/X^{A_j}\), a 2-adic unit. Each \(E_i=1\) for \(i\in I\), and the left-null identities together with \(H_c=0\) and \(C^\top{\bf1}=0\bmod2\) give \(\prod_j E_j^{c_j}=1\). Applying the adjugate of \(C_J^\top\) shows every remaining \(E_j\) is killed by an odd exponent, hence is 1, as \(\mathbb Z_2^\times\) has no odd torsion. Conversely every solution of the full equations satisfies the augmentation by the same identities. This proves the local fact.

For homogeneous even arity \(m\), there is a shorter independent application. Since \(A{\bf1}=m{\bf1}\), \(C^\top{\bf1}=0\) over \(\mathbb Q\). The polynomial \(z+z^m-N\) has a unique odd 2-adic root by its odd derivative. Its diagonal tuple must be the unique odd solution, which cannot have distinct coordinates. For homogeneous odd arity \(m>1\) the parity restriction on \(h\) is already forced by \(B{\bf1}=(1-m){\bf1}\) and \(C^\top{\bf1}=0\). A nontrivial matrix automorphism likewise sends any solution to another, so uniqueness forbids distinct labels directly.

### 3. Passage to every equitable quotient

For completeness, a nonsymmetric balanced partition need not come from automorphisms. Work over \(\mathbb Z_{(2)}\) (rationals with odd denominator). On the full coordinate module there are polynomial projectors onto the rational nullspace and its complementary image. In fact write \(\det(TI-B)=T^r f(T)\) with \(f(0)=h\) odd. Since its zero eigenvalue is also semisimple over \(\mathbb Q\), \(B f(B)=0\) (this includes \(r=0\)). The projector onto the kernel is \(P_0=f(B)/f(0)\), and \(b(B)\) for
\[
                  b(T)=\frac{f(0)-f(T)}{T f(0)}
\]
is an inverse for \(B\) on the complementary image, with \(B b(B)=I-P_0\). These claims follow directly on the two rational primary summands; all the displayed operators preserve the localized integral module.

The module of cell-constant vectors is a direct summand with its natural cell coordinates, and is invariant under \(B\) by equitability. Hence it is invariant under both polynomials, splits into their kernel/image summands, and the induced matrix \(B'=I-A'\) is zero on the first and an integral automorphism on the second. Here \(A'\) is precisely the nonnegative integral matrix of row counts into cells. In particular its corresponding characteristic coefficient is odd. Moreover the full all-ones vector belongs to the image of \(B\bmod2\) by the actual necessary left-null parity and rank preservation. Thus \(P_0{\bf1}=0\bmod2\). The vector \(b(B){\bf1}\) is cell-constant and \(B b(B){\bf1}={\bf1}\bmod2\), proving that the all-ones vector in the quotient cell coordinates belongs to \(\operatorname{im}(B'\bmod2)\). Therefore the quotient's saturated left kernel has even coordinate sums, as needed in section 2.

Apply the local existence result to the quotient. Repeating each of its odd unit coordinates throughout its cell gives a solution of the original full physical equations, by equitability. Uniqueness in section 2 forces the original integer labels to equal these values in \(\mathbb Z_2\), hence to be equal as integers within each cell. Distinct labels imply all cells singleton.

**Control and scope.** The [exact standard-library checker](check_eac_transverse_kernel.py) reconstructs the genuine 128 terminal, verifies \(r=1\), odd reduced kernel pairing, and that the color counts from the indiscrete partition grow as \(1,2,6,8\) to a discrete partition. This is a sanity check, not a claim of a new historical realization or that every discrete matrix is realizable. The criterion is purely arithmetic about integer prime-factor equations; it neither proves Goldbach nor requires its failure.
