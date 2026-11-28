# Joint smoothing of arbitrary dyadic ideal quotients, including fixed coefficient weight

Let \(n\) be a power of two, \(R_n=\mathbb Z[\zeta_{2n}]\), and \(J\subsetneq R_n\) a nonzero integral ideal. Put \(Q=N(J)=|R_n/J|\), \(s=\log Q\) (natural log), and assume \(s\le n\). In the power basis, the normalized Hermitian trace form \(\operatorname{Tr}(x\bar y)/n\) is the ordinary Euclidean coefficient metric. All laws below are standalone distributions of generated ring elements, not hidden-variable or deployed models.

**Theorem.**
1. Let \(X=\sum_{j=0}^{n-1} X_j\zeta_{2n}^j\), with independent integer \(X_j\), not necessarily identically distributed. Suppose for all \(j,t\),
   \[
   |\mathbb E e^{2\pi i tX_j}|\le
       \exp[-\kappa\operatorname{dist}(t,\mathbb Z)^2].
   \]
   Relative to the uniform law \(U_J\) on \(R_n/J\),
   \[
      Q\sup_y|\Pr[X\bmod J=y]-U_J(y)|
      \le (Q-1)\exp\!\left(-\frac{\kappa e^{-2}n}{4s}\right).
      \tag{1}
   \]
2. Let \(X\) instead be uniform among the signed coefficient vectors of exact weight \(k\), i.e. choose a uniform \(k\)-subset of positions and independent uniform signs on it. Let \(V=k(1-k/n)\). If \(Q\) is odd, let \(U_{J,k}=U_J\). If \(Q\) is even, let \(U_{J,k}\) be uniform on the coset with value \(k\bmod2\) under the reduction \(R_n/J\to R_n/(1-\zeta_{2n})\simeq\mathbb F_2\). There are absolute \(c,C>0\) such that
   \[
      Q\sup_y|\Pr[X\bmod J=y]-U_{J,k}(y)|
      \le C Q\sqrt{1+V}\exp\!\left(-\frac{c W}{s}\right),\qquad
      W=\begin{cases} k,&Q\text{ odd},\\ V,&Q\text{ even}.\end{cases}
      \tag{2}
   \]
   The parity constraint in the even case is exact. For \(k=0\) or \(n\) a bound with \(W=0\) may be vacuous.

In particular all factors of \(J\), including powers at different primes and the ramified prime at two, are handled **jointly**, not merely marginally. For fixed \(\kappa>0\), (1) gives exponentially small relative error when \(s\le c_0\sqrt n\) for a small absolute \(c_0>0\) depending on \(\kappa\). For (2) the analogous assertion holds at \(s\le c_0\sqrt W\) with \(W\to\infty\) and \(Q\) of the stipulated parity; in the odd case \(V\le k=W\). We do not claim these norm scales are optimal.

**Prior scope.** [Peikert–Regev–Stephens-Davidowitz, Lemma 6.9](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf) use the ideal norm/AM–GM inequality for a sufficient smoothing bound on an archimedean ideal lattice. The [fixed earlier dyadic subfield note, §§2–3](https://github.com/mxym/math/blob/32f6edfca9774bbedd298a0af4fe6e23993911ea/research/euclidean-tensor-geometry/theoretical-cryptography/dyadic-subfield-generation.md) supplies the single-residue-field subfield argument for independent discrete-Gaussian coefficients. The new algebraic step below treats **arbitrary composite ideals with arbitrary prime powers** without an extra factor for the number of contracted primes: take the top surviving conductor layers within a carefully chosen contracted factor. The [short-box coprimality note](cyclotomic-box-coprimality.md) gives a wider-conductor, all-unramified-moduli marginal atom bound; §5 below gives a sharper joint rare-event asymptotic in a smaller regime. The [fixed-weight threshold note](fixed-weight-odd-residue-threshold.md) treats a different fixed-size-weight asymptotic on particular full-order odd residue coordinates. Here \((2)\) concerns arbitrary ideals in the dyadic tower and growing effective weight. There is no new computational reduction, cryptanalysis, or practical target.

## 1. An additive character has an ideal conductor

For an additive character \(\chi\) on \(R_n/J\), lifted to \(R_n\), let its conductor be the ideal
\[
 I_\chi=\{a\in R_n:\chi(ax)=1\text{ for every }x\in R_n\}.
\]
This is the largest ideal contained in the kernel of \(\chi\), and contains \(J\). For a nontrivial \(\chi\), \(I=I_\chi\) is proper. The character is primitive on \(R_n/I\) in the sense that no nonzero ideal there lies in its kernel. By CRT write \(I=\prod_{\mathfrak p}\mathfrak p^{k_{\mathfrak p}}\), taking the primes with positive exponent. Each local component of this primitive character has the indicated conductor exponent \(k_{\mathfrak p}\).

Let \(m\mid n\) be dyadic, \(d=n/m\), \(z=\zeta_{2n}\) and \(\beta=z^d=\zeta_{2m}\). Write \(R_m=\mathbb Z[\beta]\), including \(R_1=\mathbb Z\). With \(I_m=I\cap R_m\), the quotient \(R_m/I_m\) is the image of \(R_m\) in \(R_n/I\). Its cardinality is nondecreasing up the dyadic tower. Choose the smallest dyadic \(m\) with \(m\ge\log N(I_m)\), which exists at \(m=n\) since \(\log N I\le s\le n\). Then
\[
  \log N(I_m)\le m\le2\log N(I_m).
  \tag{3}
\]
For \(m>1\), the upper inequality follows by failure at \(m/2\) and monotonicity; for \(m=1\), \(N(I_m)\ge2\) suffices.

## 2. Top surviving local layers keep the block span small

Fix a prime \(\mathfrak P\subset R_m\) under one of the factors of \(I\), and use \(e_{\mathfrak p},f_{\mathfrak p}\) for the relative ramification index and residue degree of \(\mathfrak p\) over \(\mathfrak P\). The exponent of \(\mathfrak P\) in \(I_m\) is
\[
 L_{\mathfrak P}=\max_{\mathfrak p\mid\mathfrak P,\ k_{\mathfrak p}>0}
                  \left\lceil k_{\mathfrak p}/e_{\mathfrak p}\right\rceil ,
\]
by restriction of normalized ideal valuations. For brevity put \(L=L_{\mathfrak P}\). Choose \(c_{\mathfrak P}\in R_m\) of valuation \(L-1\) at \(\mathfrak P\) and congruent to zero modulo every other complete prime-power factor of \(I_m\); this is possible by CRT. Define \(\chi_{\mathfrak P}'(x)=\chi(c_{\mathfrak P}x)\).

For \(\mathfrak p\mid\mathfrak P\), the new local conductor exponent is
\[
 k'_{\mathfrak p}=\max(0,k_{\mathfrak p}-e_{\mathfrak p}(L-1)).
 \tag{4}
\]
This follows directly from the definition of conductor: the new annihilator ideal is the colon ideal \((I:c_{\mathfrak P})\). Factors outside \(\mathfrak P\) vanish, and at least one exponent (4) is positive. Every surviving exponent is at most \(e_{\mathfrak p}\); hence the quotient by the new conductor is killed by \(\mathfrak P\), and is a vector algebra over \(F_{\mathfrak P}=R_m/\mathfrak P\). Its dimension is
\[
 B_{\mathfrak P}=\sum_{\mathfrak p\mid\mathfrak P} f_{\mathfrak p} k'_{\mathfrak p},
\]
by its cardinality. It is generated by \(z\) as an \(F_{\mathfrak P}\)-algebra since \(R_n=\mathbb Z[z]\). In an algebra generated by one element, the powers up to one less than the degree of its monic minimal relation form a basis; here that degree must be the vector dimension \(B_{\mathfrak P}\). Also \(z\) is a unit and \(z^d=\beta\in R_m\), so \(B_{\mathfrak P}\le d\) and any \(B_{\mathfrak P}\) consecutive powers form a basis. The original character \(\chi\) cannot vanish on \(\zeta_{2n}^i R_m\) for each \(i\) in a stretch of \(B_{\mathfrak P}\) consecutive indices: otherwise the same holds for \(\chi'_{\mathfrak P}\), since \(c_{\mathfrak P}\in R_m\), and spanning forces that nontrivial character to be trivial.

The point of passing to the top layers is the weighted dimension accounting. When \(k'_{\mathfrak p}>0\),
\(k_{\mathfrak p}=(L-1)e_{\mathfrak p}+k'_{\mathfrak p}\ge L k'_{\mathfrak p}\).
Thus
\[
 B_{\mathfrak P} L_{\mathfrak P}\log N(\mathfrak P)
 \ \leq\ \sum_{\mathfrak p\mid\mathfrak P}
        k_{\mathfrak p} f_{\mathfrak p}\log N(\mathfrak P).
\]
Sum over \(\mathfrak P\). The weights on the left sum to \(\log N(I_m)\), and the right sums to \(\log N(I)\). Choose a \(\mathfrak P\) of smallest \(B_{\mathfrak P}\), obtaining \(mB_{\mathfrak P}\le2\log N(I)\) by (3). There are therefore at least \(\lfloor d/B_{\mathfrak P}\rfloor\ge n/(4\log N(I))\) indices \(i\in[0,d-1]\) such that the additive restriction \(\chi(z^i\,\cdot)\) on \(R_m\) is nontrivial. This argument does not assume squarefreeness, a uniform local degree, or unramifiedness.

## 3. Phase energy and independent coefficients

Write \(\chi(z^j)=e^{2\pi i t_j}\) with each \(t_j\in[-1/2,1/2]\), either choice at the endpoint. Organize \(j=i+d\ell\) with \(0\le i<d,\ 0\le\ell<m\). The phase vector \((t_{i+d\ell})_{\ell=0}^{m-1}\) represents the restriction on \(R_m\) in the coefficient basis \(1,\beta,\ldots,\beta^{m-1}\); it pairs integrally with \(I_m\), because \(I_\chi\) is an ideal. The coefficient dual of \(I_m\) is \(\overline{I_m}^{\,-1}\) using the normalized trace form: \(R_m\) is self-dual for that form by the dyadic orthogonal power basis, and compatibility with multiplication by \(R_m\) then gives the fractional inverse ideal description. Explicitly if \(v\) pairs integrally with \(I_m\), then for every \(a\in I_m\) the element \(v\bar a\) pairs integrally with all \(R_m\), hence belongs to \(R_m\); the converse follows by pairing with \(1\). Any nonzero such \(v\) satisfies \(|N(v)|\ge N(I_m)^{-1}\) since \((v)\overline{I_m}\) is a nonzero integral ideal. AM–GM in the canonical coordinates yields
\[
 \|v\|_{\rm coef}^2\ge |N(v)|^{2/m}\ge N(I_m)^{-2/m}\ge e^{-2}.
\]
For the number of nontrivial blocks just established, \(v\ne0\). We have proved the reusable phase-energy estimate
\[
 \sum_{j=0}^{n-1}\operatorname{dist}(t_j,\mathbb Z)^2
   \ \geq\ \frac{e^{-2}n}{4\log N(I_\chi)}
   \ \geq\ \frac{e^{-2}n}{4s}.
 \tag{5}
\]
For independent coefficients, the assumed scalar Fourier bound, applied to each factor in \(\mathbb E\chi(X)\), gives the right-hand exponential in (1). Fourier inversion on \(R_n/J\) and summing over the \(Q-1\) nontrivial characters gives (1).

For instance a uniform binary coefficient on \(\{0,1\}\) obeys the hypothesis by \(|\cos\pi t|\le e^{-2\operatorname{dist}(t,\mathbb Z)^2}\). The same type of bound with an absolute \(\kappa>0\) holds for any uniform interval of at least three consecutive integers by pairing adjacent values and leaving at most one unpaired. Thus (1) does not require Gaussianity, symmetry, or the coefficient distributions to be the same.

## 4. Fixed weight, and the only mandatory parity character in this window

Take independent Bernoulli selectors of probability \(p=k/n\) with independent uniform signs, then condition on the total count \(K=k\). This gives the exact fixed-weight law. The binomial mass at \(k\) is at least a constant times \(1/\sqrt{1+V}\), where \(V=np(1-p)\). Indeed \(k\) is a mode (as seen from consecutive mass ratios) and Chebyshev's inequality puts at least \(3/4\) of the mass in \(O(\sqrt{1+V})\) consecutive sites. The cases \(p=0,1\) have mass one.

For a character with phases \(t_j\), project onto \(K=k\) by circle integration. Its unnormalized characteristic value is
\[
 \frac1{2\pi}\int_{-\pi}^{\pi}
   e^{-ik\theta}\prod_j\big(1-p+p e^{i\theta}\cos(2\pi t_j)\big)\,d\theta .
 \tag{6}
\]
If the doubled character \(\chi^2\) is nontrivial, each factor is bounded in modulus by
\(1-p+p|\cos(2\pi t_j)|\le e^{-2p\operatorname{dist}(2t_j,\mathbb Z)^2}\).
Apply (5) to \(\chi^2\). Dividing by the binomial mass shows that the conditional Fourier coefficient is \(O(\sqrt{1+V}\exp(-c k/s))\).

If a nontrivial character has order two, put \(a_j=\chi(z^j)\in\{1,-1\}\). The character \(x\mapsto\chi((z-1)x)\) is trivial exactly when \(\chi\) factors through \(R_n/(z-1)\simeq\mathbb F_2\); the only nontrivial one there is the claimed parity character. It assigns \(-1\) to every signed monomial and thus value \((-1)^k\) to \(X\) deterministically. For any other order-two character the derivative character is nontrivial. Its phases along the basis are those of \(a_{j+1}a_j\), with \(a_n=a_0\) because \(z^n=-1\) and the values have order two. By (5), the number of sign transitions in this cyclic list is \(\Omega(n/s)\), since each transition contributes phase square \(1/4\). The smaller of the plus and minus counts is at least half the number of transitions. The squared modulus of a positive-position factor in (6) is \(1-4p(1-p)\sin^2(\theta/2)\), and of a negative-position factor is \(1-4p(1-p)\cos^2(\theta/2)\). Their product in modulus is therefore \(O(\exp(-cV/s))\) uniformly in \(\theta\); divide by the same binomial mass. The uniform comparison law has the same coefficients at the trivial and parity characters, and zero at the others. Order-two nontrivial characters are absent for odd norm. Fourier inversion gives (2).

## 5. A sharp rare-event corollary for short-box differences

As a consequence, let \(q\) be odd prime, let \(f\) be its common residue degree in \(R_n\), and \(g=n/f\) the number of primes above it. Write \(Q_0=q^f\). Take \(r\) independent samples \(Y_i\) of either type (1) or (2), with fixed \(r\), and deterministic centers \(x_i\). In the independent case assume a common \(\kappa>0\) bounded below; in the fixed-weight case take the same count \(k\to\infty\). Suppose
\(\log Q_0=o(\sqrt n)\) or \(\log Q_0=o(\sqrt k)\), respectively. Then for \(r\ge2\), uniformly in the centers,
\[
 \Pr\big[(q,Y_1-x_1,\ldots,Y_r-x_r)\ne R_n\big]
            =(1+o(1))g Q_0^{-r}. \tag{7}
\]
Indeed the relative errors in (1) or (2) are \(o(1)\) uniformly on any product of a fixed number of distinct primes above \(q\), since its log norm is the fixed multiple of \(\log Q_0\). For (2) the factor \(\sqrt{1+V}\le\sqrt{1+k}\) is absorbed because \(k/\log Q_0\gg\sqrt k\). The single-prime probabilities are \((1+o(1))Q_0^{-r}\), and each distinct pair has probability \((1+o(1))Q_0^{-2r}\). Their total pair contribution divided by \(g Q_0^{-r}\) is \(O(g Q_0^{-r})=o(1)\), since the exact \(2n\) order of the primitive root in any such residue forces \(Q_0\ge2n+1\). The first two Bonferroni bounds give (7). This improves the earlier broad-scope marginal rate only in its stated low-log-norm regime; no weighted second-preimage or scheme accounting is inferred.

## Reproduction

Run `python3 verify-dyadic-ideal-joint-smoothing.py` (standard library only). It checks small exact character conductor/phase calculations, top-layer accounting with split and ramified examples, and the fixed-weight order-two sign identities. These checks illustrate the arithmetic ingredients, not a generator or an assessment of any real parameter.
