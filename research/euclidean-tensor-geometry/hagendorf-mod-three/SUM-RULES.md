# Norm and linear sum rules for the mod-three spin-one chain

Companion to the [all-twist singlet classification](README.md). We prove both displayed identities in [Hagendorf's Conjecture 4.9](https://arxiv.org/pdf/1207.0357#page=40) and integer polynomial factorization. Coefficientwise positivity of the factors is not proved here.

Use zero twist, \(N=2n+1\), \(\lambda\zeta\ne0\), and work within one charge modulo three. Let \(u\) be the uniform sum of all words in the charge class at \((1,1)\); by the Fourier diagonalization it is harmonic, with \(\|u\|^2=3^{N-1}\). In the real diagonal chain isomorphism \(M_N=M^{\otimes N}\) of the count proof, put \(a=M_N^{-1}u\), \(b=M_N^\dagger u\). Then \(a\in\ker Q_N\), \(b\in\ker Q_{N-1}^\dagger\), and \(\langle b,a\rangle=3^{N-1}\). Each charge has a one-dimensional harmonic space, since the three Fourier constant-color products split into the three distinct characters of the global charge.

For a real harmonic vector \(\psi\ne0\) in that charge, decompose \(a,b\) into their harmonic projections and the respective residual pieces in \(\operatorname{im}Q_{N-1},\operatorname{im}Q_N^\dagger\). The residual pieces are orthogonal to each other by \(Q_NQ_{N-1}=0\). Hence
\[
3^{N-1}\|\psi\|^2=\langle b,\psi\rangle\langle\psi,a\rangle .
\]
For \(\lambda=\zeta=t\), \(M_N\) acts on a word \(w\) by \(t^{\nu_1(w)-N}\), with \(\nu_1\) the number of middle letters. Substitution gives
\[
\|\psi\|^2=3^{1-N}
\left(\sum_w t^{\nu_1(w)}\psi_w\right)
\left(\sum_w t^{-\nu_1(w)}\psi_w\right).
\]

For the other rule use neutral charge and \(c=|11\cdots1\rangle\). It lies in \(\ker Q_{N-1}^\dagger\): only the \(-11\) term can contribute to its adjoint merge and the all-\(1\) word at positive even length is excluded by the signed shift. For \(N=1\) use \(Q_0=0\). Now \(\langle c,a\rangle=1\) and \(\langle b,a\rangle=3^{N-1}\); the same orthogonality argument says that the harmonic projections of \(c,b\) are in the ratio \(1:3^{N-1}\). In particular on the diagonal line,
\[
\sum_w t^{\nu_1(w)}\psi_w=3^{N-1}t^N\psi_{11\cdots1}.
\]

Finally take a primitive integer-polynomial vector \(\psi\) in the generic one-dimensional kernel. It exists by solving the harmonic equations over \(\mathbb Q(\lambda,\zeta)\), clearing denominators and removing the polynomial common divisor and integer content. If \(n_0,n_2\) are the counts of extreme letters, the diagonal entries of \(M_N\) are \(\lambda^{-(2n_0+n_2)/3}\zeta^{-(n_0+2n_2)/3}\) with real cube roots. Within one charge class, each numerator exponent has a constant residue modulo three. Therefore the two sums in the product, after deleting inverse common fractional monomials, are integer Laurent polynomials \(A,B\), and their product is \(3^{N-1}\|\psi\|^2\). For each variable, the smallest exponent in a product of two nonzero Laurent polynomials equals the sum of the two smallest exponents, by the integral domain property. Move an integer Laurent monomial from one factor to the other to make both ordinary polynomials. Gauss's content lemma then distributes the divisor \(3^{N-1}\) between their contents, giving an integer polynomial factorization of the norm. All polynomial identities extend by specialization; an arbitrary normalization at a degenerate parameter is not asserted to be the specialization of the primitive generic vector.

The modular checker supplies independent sample tests of both displayed identities, not a replacement for the harmonic projection proof. No claim of coefficient positivity, of full spectral formulas, or of Hagendorf's separate Fateev–Zamolodchikov alternating-sign-matrix conjectures is made.
