# Bit-polynomial identity tests for prime-power cyclic progression convolutions

**Scope.** This is an exact comparison of two fully specified forward probability laws, not an algorithm that learns parameters from samples or solves a cryptographic search problem. All interval lengths, lengths' encodings, strides and starts are supplied. No dense cyclotomic-field representation of dimension comparable with the numerical modulus is used.

Let \(p\) be a supplied prime and \(Q_0=p^e\ge2\) a binary-encoded modulus. A law on \(\mathbb Z/Q_0\mathbb Z\) is given by a list of integer starts \(a_i\), integer steps \(c_i\) (including zero and negative steps), and positive integer lengths \(L_i\), all in binary:
\[
            X=\sum_i(a_i+c_i U_i)\pmod {Q_0},
       \qquad U_i\text{ independent uniform on }\{0,\ldots,L_i-1\}.
\]
This specifies a uniform draw of the **index** in each progression, so multiplicities after wrapping are preserved.

**Theorem.** There is a deterministic algorithm, polynomial in the total bit length, to decide whether two such laws are equal. The lengths may differ between the laws and there is no small-doubling, small-step, common-step or no-wrap condition. In fact the procedure compares an explicit compact rational-coset signature at each conductor \(p^j\). By contrast, a single exact point-mass query is already \(\#\mathsf P\)-hard under counting Turing reductions for this class (even for every step equal to 1), by the unit-step interval counting reduction in the companion interval note. Identity does not require computing those point masses.

## 1. One representative at each conductor

For \(Q=p^j\mid Q_0\), put \(\zeta=\exp(2\pi i/Q)\) and take \(F_Q=\mathbb E\,\zeta^X\). All probability coefficients are rational. The Fourier coefficients at characters of exact order \(Q\) are the Galois conjugates of \(F_Q\), so equality of the laws is equivalent to equality of \(F_Q\) for all \(j=1,\dots,e\); the constant coefficients are both one.

A factor with \(Q\mid c_i\) is inactive, contributing only its start, and contributes no denominator. At active indices, the geometric identity gives
\[
 F_Q=\zeta^{A}\prod_{i\ {\rm active}}
       \frac{1-\zeta^{c_i L_i}}{L_i(1-\zeta^{c_i})},
       \qquad A=\sum_i a_i\pmod Q.                         \tag{1}
\]
If \(Q\mid c_iL_i\) for any active index, this conductor is exactly zero: check statuses before processing the expression. Different zero statuses certify inequality. Equal zero statuses require no further calculation at that conductor.

For \(Q=2\) a nonzero conductor contributes \(F_2=(-1)^A/\prod_{i\ {\rm active}}L_i\): active steps and lengths are both odd. This handles the unique case in which a unit residue is its own negative.

## 2. Distribution-relation normalization, without expansion

Assume \(Q=p^j>2\) and a nonzero conductor. Denote the unit residues by \(G=(\mathbb Z/Q\mathbb Z)^\times\) and use integer representatives in \([1,Q-1]\). For any integer \(u\) not divisible by \(Q\), set \(v=\nu_p(u)<j\), \(s=u/p^v\), and \(m=p^{j-v}\). We have the exact cyclotomic relation
\[
  1-\zeta^u=\prod_{\substack{g\in G\\g\equiv s\bmod m}}(1-\zeta^g).                \tag{2}
\]
Indeed the factors run over \(\zeta^s\) times all \(p^v\)-th roots of unity, and all their exponents are units. This class can have exponential cardinality when written out, but its modulus and representative are just binary integers.

Let \(D=\prod_{i\ {\rm active}}L_i=p^\lambda D_0\) with \(p\nmid D_0\). The identity \(\prod_{g\in G}(1-\zeta^g)=\Phi_Q(1)=p\) absorbs the rational power of \(p\). Thus (1) becomes
\[
 F_Q=\zeta^A D_0^{-1}\prod_{g\in G}(1-\zeta^g)^{b(g)},\qquad
 b=\sum_{i\ {\rm active}}\bigl(\mathbf1_{C(c_iL_i)}-\mathbf1_{C(c_i)}\bigr)
             -\lambda\mathbf1_G,                           \tag{3}
\]
where \(C(u)\) is the congruence class in (2). This specifies the integer function \(b\) by a list of at most twice the number of factors plus one weighted classes, with no field-element integer expansions.

Choose the lower-half representative \(g<Q/2\) for each pair \(\{g,-g\}\). Define an even function \(b^+(g)=b(g)+b(-g)\) on \(G\). With
\[
 \eta=\sum_{u>Q/2} b(u),\qquad
 T\equiv A-\sum_{u>Q/2}(Q-u)b(u)\pmod Q,\qquad
 \varphi\equiv 2T+Q\eta\pmod {2Q},                            \tag{4}
\]
the exact value is
\[
 F_Q=D_0^{-1}\,\exp(2\pi i\varphi/(2Q))
                     \prod_{g<Q/2,\ g\in G}(1-\zeta^g)^{b^+(g)}.
 \tag{5}
\]
This follows from \(1-\zeta^{-g}=-\zeta^{-g}(1-\zeta^g)\). Using modulus \(2Q\) accounts for both odd \(p\) and \(p=2\) in one expression; dropping the phase or reducing the sign incorrectly at \(p=2\) would not test equality.

## 3. Why the signature is complete

If \(F_Q=F'_Q\ne0\), take field norms of their ratio using (3). Each \(1-\zeta^g\) has absolute norm \(p\), and the root factor norm has absolute value one. Thus \((D_0'/D_0)^{\phi(Q)}\) is a power of \(p\), which, because \(D_0,D'_0\) are both coprime to \(p\), forces \(D'_0=D_0\). No factorization of these denominators is required.

The remaining issue is independence of the absolute conjugates. We include the classical logarithmic argument to isolate its prime-power hypothesis. On \(H=G/\{\pm1\}\) write \(f(g)=\log|1-\zeta^g|\). Its Fourier coefficient at every character of \(H\) is nonzero. For the trivial character the sum is \(\tfrac12\log p\). For a nontrivial character, lift it to an even character of \(G\); its conductor is \(p^a\) with \(1\le a\le j\). Summing \(f\) over a fiber of the reduction to \(p^a\) gives the log absolute value at conductor \(p^a\) by (2). At conductor \(p^a\) the character is primitive. The Abel expansion
\[
 \log|1-t\zeta_{p^a}^u|
   =-\frac12\sum_{k\ge1}\frac{t^k}{k}
                       \bigl(\zeta_{p^a}^{uk}+\zeta_{p^a}^{-uk}\bigr),
                     \qquad 0<t<1,
\]
the evenness of the character, and the primitive Gauss sum formula yield the Fourier coefficient
\(-\frac12\tau(\overline\chi)L(1,\chi)\) as \(t\uparrow1\). This is nonzero by the classical primitive Gauss sum identity and Dirichlet nonvanishing. The Abel limit is legitimate because the character is nonprincipal, so \(\sum_k\chi(k)/k\) converges.

Now set \(d_g=b^+(g)-b'^+(g)\) on \(H\). Equality implies \(\prod_g|1-\zeta^g|^{2d_g}=1\). This squared equation lies in the real cyclotomic field. Apply each Galois automorphism and take real logarithms; then \(\sum_g d_g f(kg)=0\) for every \(k\in H\). The matrix is a group convolution matrix up to inversion; nonvanishing of all its Fourier eigenvalues implies \(d=0\). Once these exponents are equal, (5) reduces equality to \(\varphi=\varphi'\) in \(\mathbb Z/(2Q)\mathbb Z\). Conversely, equality of the three signature parts \(D_0,b^+,\varphi\) implies equality by (5). The logarithms and their numerical values are **not** calculated in the algorithm.

## 4. Polynomial-bit comparisons of the compressed parts

\(D_0,\lambda\) are obtained by division by \(p\) and multiplication in the input bit size. Each class from (2) has the form \(C_{k,s}=\{u\in G:u=s\bmod p^k\}\), \(1\le k\le j\), with \(p\nmid s\); the full unit group has a separate marker. Taking the even part sends each class to itself plus the class with representative \(-s\bmod p^k\). To test equality of two such even functions, subtract the signed lists and do the following:

1. Combine identical class markers. At distinct depths two classes are nested or disjoint, decided by one modular comparison; include a full-group root even when its weight is zero.
2. Use the smallest listed strict superset as each class's parent. The cardinality of \(C_{k,s}\) is \(p^{j-k}\); the root cardinality is \(\phi(Q)\). The children of one class are disjoint.
3. Each node minus its children is a residual region. On a nonempty residual region the difference is the sum of weights along its ancestor chain, including the node. Its nonemptiness is a cardinality subtraction. These regions partition \(G\); check the sum is zero on each nonempty region.

This tests equality in polynomially many operations on binary integers even when all \(Q\) residues are not enumerable. The sums in (4) also use only the marker list: within a residue class, membership in \((Q/2,Q)\) is a finite arithmetic progression whose size and sum follow from floor endpoints. For the full unit group count all integers in the upper half and subtract multiples of \(p\). Linearity then gives both weighted sums in (4).

Finally \(e\le \log_2 Q_0\). All lists have length linear in the two input progression lists at each conductor, and all products and counts have polynomial bit length. This proves the stated algorithm. It includes, for example, equality under mixed-radix splitting of an interval into independent shorter progressions, under reflection with its compensating start, and under a nonunit step that becomes inactive in low conductors. It also handles zero and live conductors interleaved by different steps, rather than treating prime-power padding as a single primitive test.

The per-conductor argument also gives a reusable algebraic identity test without probability language. Given two expressions \(\rho\,\zeta_Q^A\prod_{i=1}^m(1-\zeta_Q^{u_i})^{e_i}\) with \(\rho\in\mathbb Q^\times\) explicitly encoded, \(Q\nmid u_i\), and \(e_i\in\mathbb Z\) binary-encoded, equality is decidable by the same compressed comparison. Replace \(\rho\) by its positive \(p\)-free rational part, a signed power of \(p\) in (3), and a sign contributing \(Q\) to (4) if negative. Weight each listed class by \(e_i\). The norm and logarithmic argument is unchanged, and arithmetic bounds are still polynomial in the input **bit** lengths of the exponents, not their magnitudes. At \(Q=2\) the only possible binomial value is 2, so the same signed-power separation is immediate. This test does not claim to compute the potentially enormous expanded value.

## Source and applicability limits

The distribution relations and the absolute-value independence are classical, rather than a new independence theorem for cyclotomic numbers. See [Conrad, *An Algorithm to Calculate a Basis Representation for Cyclotomic Units and Cyclotomic Numbers*](https://perisic.com/cyclotomic/cycalg.pdf), Algorithms 1.3 and 2.1 for distribution/norm relations and basis reduction modulo roots of unity, and [Dasgupta, *Factorization of p-Adic Rankin L-Series*](https://sites.math.duke.edu/~dasgupta/papers/Factorization.pdf), §4.2 for the primitive logarithm formula. The algorithmic claim here is specifically that, for a prime-power modulus, the relevant possibly enormous exponent lists **can remain unexpanded**, with a bit-polynomial equality check and all phases tracked, and that this decides the identity of the specified forward convolution laws. An explicit dense cyclotomic basis or residue vector can have length comparable with the numerical modulus.

This applies to a supplied cyclic additive quotient of a finite coefficient algebra with known inputs and known step coefficients. It does not imply joint identity across separate quotients merely from agreement of their marginal laws, and does not address arbitrary moduli with different prime factors, approximate equality in total variation, secret recovery, real parameters, or standard Ring-LWE. The associated exact checker uses only generated small forward laws and integer arithmetic, plus size sanity checks with compressed markers.
