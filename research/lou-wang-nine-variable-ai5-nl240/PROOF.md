# High nonlinearity at the exact nine-variable immunity-resiliency optimum

**Theorem.** Among 9-variable 3-resilient Boolean functions of algebraic immunity 5, the maximum nonlinearity is 240. An explicit maximizer is the previously published truth table of Andrey Khalyavin identified below, whose degree-four annihilator spaces are both zero.

This answers affirmatively the [open problem in Lou–Wang (2024), §3](https://doi.org/10.1587/transfun.2023EAL2111). Their rotation-symmetric maximum of 224 concerns the nine-coordinate rotation class and is not contradicted. The function used here is not new. The new check establishes its algebraic immunity and thus the joint optimum in the unrestricted class.

## 1. Universal upper bound in the 3-resilient class

Let \(f:\mathbb F_2^9\to\mathbb F_2\) be 3-resilient, meaning that every restriction obtained by fixing at most three coordinate variables is balanced. Write \(S=\{x:f(x)=1\}\). For each set \(I\) of coordinates, let \(N_I=|\{x\in S:x_i=1\text{ for all }i\in I\}|\). When \(|I|\le3\), balancedness of the restriction gives \(N_I=2^{8-|I|}\). For a nonzero \(u\) with support \(J\), take the full character sum minus twice the contribution of \(S\). Expanding the character on binary inputs gives
\[
 W_f(u)=\sum_x(-1)^{f(x)+u\cdot x}
        =-2\sum_{I\subseteq J}(-2)^{|I|}N_I .
\]
Terms with \(|I|\le3\) are multiples of \(2^9\); the others are multiples of \(32\). The zero coefficient \(W_f(0)\) is zero by balancedness. Thus all Walsh coefficients are multiples of \(32\), and at least one is nonzero by Fourier inversion. So every such \(f\) has nonlinearity
\[
       2^8-\tfrac12\max_u |W_f(u)| \le 240 .
\]
The divisibility and upper bound are known; this gives the needed special case without assuming an unrestricted nine-variable nonlinearity bound. See [SOURCES.md](SOURCES.md).

## 2. Witness and direct Fourier check

The hexadecimal word in [witness.txt](witness.txt) is the table labeled as the example with two seven-variable subfunctions of nonlinearity 56 in §7 of [Khalyavin, IACR ePrint 2007/212](https://eprint.iacr.org/2007/212.pdf), printed p. 6. The source is CC BY; the construction is Khalyavin's. The indices are in increasing order as integers with the first variable the least significant coordinate. Within each hex digit \(h_j\), define \(f(4j+i)\) as bit \(i=0,1,2,3\) of \(h_j\), least significant bit first. Reversing within every digit would merely translate the input by 3, preserving the claimed quantities.

The [verifier](verify.py) recomputes every Walsh coefficient by two exact methods: direct character summation and the fast radix-two transform. Both give 136 coefficients \(-32\), 256 zeros and 120 coefficients \(32\). The least Hamming weight of a frequency with nonzero coefficient is exactly 4. Walsh orthogonality then gives exact resiliency 3 (the lower-weight coefficients are precisely the character sums testing uniform conditional balance). The Walsh maximum is 32, so the nonlinearity is exactly 240. The Möbius transform independently gives degree 5.

## 3. The witness has algebraic immunity 5

Algebraic immunity is the least degree of a nonzero Boolean polynomial vanishing on \(S\) or its complement. The 256 multilinear monomials of degree at most 4 are indexed by masks \(u\) of weight at most 4; evaluating such a monomial at mask \(x\) gives \(1\) iff \(u\subseteq x\). For each \(b=0,1\), let \(M_b\) be the \(256\times256\) binary evaluation matrix with row set \(f^{-1}(b)\) and these monomial columns. A nonzero degree-at-most-4 annihilator on \(f^{-1}(b)\) exists exactly when the corresponding matrix has a nonzero kernel. The verifier checks rank 256 for both matrices by exact binary elimination.

An independent rank check uses the function's invariance under cyclic rotation of the first seven coordinates. Let \(R\) be this seven-cycle on row masks and monomial masks. Each row set and column set decomposes into four fixed points and 36 orbits of length seven; these counts are checked directly. Extend scalars to \(\mathbb F_8=\mathbb F_2[t]/(t^3+t+1)\), which does not change rank. The seven-cycle has the seven distinct nonzero elements of \(\mathbb F_8\) as eigenvalues. On a seven-orbit, the Fourier basis vectors have coefficients \((1,z,\ldots,z^6)\), one for each seventh root \(z\). On a fixed point, only \(z=1\) occurs. Since \(M_b(Rx,Ru)=M_b(x,u)\), the matrix preserves these blocks. For a row orbit representative \(x\) and a monomial orbit with representative \(u\), the entry in block \(z\) is the sum
\[
         \sum_{j=0}^{|O_u|-1} z^j \,1_{\{R^j u\subseteq x\}},
\]
omitting fixed orbits when \(z\ne1\). This follows by shifting \(j\) at a rotated row, which multiplies the value by \(z\). Exact finite-field elimination gives rank 40 in the \(z=1\) block and rank 36 in each of the six other blocks, for both supports. The sum is \(40+6\cdot36=256\). The two methods therefore independently rule out every nonzero annihilator of degree at most 4.

The degree-at-most-5 polynomial space has dimension \(256+\binom95=382\), so evaluation on either 256-point support has a nonzero kernel. Thus algebraic immunity is exactly 5. Together with the upper bound and spectral witness, this establishes the joint optimum. [RESULTS.txt](RESULTS.txt) records both rank computations and the negative controls.
