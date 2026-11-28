# A cyclotomic coefficient-box coprimality bound without a splitting assumption

Let \(M\geq3\) be a conductor, \(R=\mathbb Z[\zeta_M]\), \(n=\varphi(M)\), and let \(q\) be a rational prime with \(q\nmid M\). Write \(f=\operatorname{ord}_M(q)\); there are \(n/f\) primes above \(q\), each of residue degree \(f\). Let \(Y=\sum_{j=0}^{n-1} U_j\zeta_M^j\), where the \(U_j\) are independent and each is uniform on an interval of consecutive integers of length at least three. They need not have equal widths or centers.

**Theorem.** For every prime \(\mathfrak p\mid qR\), the largest atom of \(Y\bmod\mathfrak p\) is at most \(C/n\) for an absolute constant \(C\), uniformly in all the above choices. More precisely, for a possibly larger absolute constant \(C\) it is at most
\[
 A_{n,q,f}=
 \begin{cases}
 q^{-1}+C n^{-3/2},& f=1,\\[3pt]
 \min\!\left\{(2/3)^f,\ (q^{-1}+C\sqrt{f/n})^f\right\},& f\geq2 .
 \end{cases} \tag{1}
\]
Let \(B\subset R^m\) be a product of such coefficient boxes on \(m\) ring coordinates, and \(X\subseteq B\) with \(|X|=\delta|B|>0\). For any fixed \(x\in R^m\), a uniform \(y\in X\) satisfies
\[
 \Pr\big[(q,y_1-x_1,\ldots,y_m-x_m)\ne R\big]
 \ \leq\ \min\{1,\delta^{-1}(n/f) A_{n,q,f}^{\,m}\}
 \ \leq\ \min\{1,\delta^{-1}(n/f)(C'/n)^m\}. \tag{2}
\]
Here the parenthesized expression denotes a generated ideal, not a residue of a product. For \(x\in X\), the probability conditional on \(y\ne x\) when \(|X|>1\) is bounded by the same right-hand expression before the minimum, times \((1-|X|^{-1})^{-1}\), and is also at most one. In particular for the full box, and for every fixed \(m\geq2\), the fraction of nongenerating differences from **each** center in the box is \(O_m(n^{1-m})\), uniformly over all unramified moduli.

**Context.** [Boudgoust–Jeudy–Roux-Langlois–Wen, *On the Hardness of Module Learning With Errors with Short Distributions*, §2.1 and Remark 4.1 after Lemma 4.4](https://cjeudy.github.io/assets/pub/BJRW22_Hardness_MLWE_with_Short_Distributions.pdf) define the coefficient box \(S_\eta\) and explicitly ask for the proportion of differences from \(X\subseteq S_\eta^m\) that generate the unit ideal together with \(q\). They observe a favorable special case with no nonzero nonunits in the short box modulo \(q\), but that argument requires a restriction on splitting and width. Formula (2) answers their proportion question for the full box and quantified dense subsets (e.g. \(\delta n^{m-1}\to\infty\) for fixed \(m\)), not arbitrary sparse subsets. It does not on its own replace their second-preimage error term: a small fraction of differences with proper generated ideal may receive a substantially larger weight in that estimate. No cryptosystem, secret, attack, practical modulus selection, or new computational reduction is treated.

The local bound combines the classical Halász level-set argument in the completely split case (compare [Ferber–Jain–Zhao, §2](https://arxiv.org/abs/1808.07222)) with an elementary Fourier block Hölder bound for higher residue degrees. The [independent Gaussian subfield note](dyadic-subfield-generation.md) uses a different prime-ideal sieve with actual dyadic subfields and handles Gaussian module generation. The present result uses no dyadic assumption, no Gaussian input, no size upper bound on \(q\) or coefficient widths, and no counting over other rational primes.

## 1. Scalar Fourier decay for any interval width

Write \(\|u\|_{\mathbb R/\mathbb Z}\) for distance to an integer. If \(U\) is uniform on an interval of \(\ell\geq3\) integers, pair adjacent integers, leaving at most one unpaired. The absolute average of each pair at frequency \(u\) is \(|\cos(\pi u)|\). Thus
\[
 |\mathbb E e^{2\pi i u U}|
 \ \leq\ 1-\frac{2\lfloor\ell/2\rfloor}{\ell}\big(1-|\cos(\pi u)|\big)
 \ \leq\ e^{-c\|u\|_{\mathbb R/\mathbb Z}^{2}} \tag{3}
\]
for an absolute \(c>0\); the elementary cosine estimate holds uniformly for distance in \([0,1/2]\). Independently, modulo any prime \(q\geq2\), each residue of \(U\) has probability at most \(\lceil \ell/2\rceil/\ell\leq2/3\). This follows from the bound \(\lceil\ell/q\rceil\) occurrences in a consecutive interval.

Fix a factor \(\mathfrak p\), let \(Q=q^f\), and let \(\alpha\in\mathbb F_Q\) be the reduction of \(\zeta_M\). For \(q\nmid M\), the roots of \(\Phi_M\) in this characteristic are exactly the elements of order \(M\): the reductions of the divisor cyclotomic polynomials factor \(Z^M-1\) with no overlap and the orders can be classified by induction on divisors of \(M\). Frobenius acts by raising to \(q\), giving residue degree \(f\) and \(Q\geq M+1\geq n+1\). Characters of the additive group of the finite field are \(z\mapsto e^{2\pi i \operatorname{Tr}(uz)/q}\), \(u\in\mathbb F_Q\), with the usual trace to \(\mathbb F_q=\mathbb Z/q\mathbb Z\). Fourier inversion, absolute values, independence, and (3) show that every atom is bounded by
\[
 \frac1{Q}\sum_{u\in\mathbb F_Q}
   \prod_{j=0}^{n-1}
    e^{-c\|\operatorname{Tr}(u\alpha^j)/q\|_{\mathbb R/\mathbb Z}^{2}} .
 \tag{4}
\]

## 2. Split primes: distinct coefficients improve the scalar bound

In degree \(f=1\), the \(n\) weights \(a_j=\alpha^j\in\mathbb F_q\) are distinct, since \(j<M\). For \(u\in\mathbb F_q\), write \(S(u)=\sum_j\|a_j u/q\|_{\mathbb R/\mathbb Z}^2\) and \(T_s=\{u:S(u)\leq s\}\). Choose \(\vartheta=1/(4\pi^2)\). For \(u\in T_{\vartheta n}\), the real part of \(\sum_j e^{2\pi i a_j u/q}\) is at least \(n-2\pi^2S(u)\geq n/2\). By additive character orthogonality and distinctness of the \(a_j\),
\[
 \sum_{u\in\mathbb F_q}\left|\sum_j e^{2\pi i a_j u/q}\right|^2=qn,\qquad
 |T_{\vartheta n}|\leq 4q/n .
\]
For \(n>4\) this is strictly less than \(q\). The triangle inequality of the circle and then Euclidean Minkowski give \(kT_s\subset T_{k^2s}\) for the \(k\)-fold sumset. For \(0<s\leq\vartheta n\), take \(k=\lfloor\sqrt{\vartheta n/s}\rfloor\), which is at least half its unfloored value. By Cauchy–Davenport, \(kT_s\) has size at least \(\min(q,k(|T_s|-1)+1)\), and the first term cannot be active. Therefore
\[
 |T_s|\leq 1+C_0 q\sqrt{s}/n^{3/2}.
\]
Insert this into (4) using the layer cake \(e^{-cS(u)}=\int_{S(u)}^\infty c e^{-cs}\,ds\). The integral up to \(\vartheta n\) is at most \(q^{-1}+C_1n^{-3/2}\); the tail is at most \(e^{-c\vartheta n}\), which is absorbed in the same absolute constant. Enlarge the constant for the finitely many \(n\leq4\). This gives the \(f=1\) line of (1).

## 3. Higher residue degrees: block change of variables

Put \(L=\lfloor n/f\rfloor\). Every block of \(f\) consecutive powers of \(\alpha\) is a basis of \(\mathbb F_Q\) over \(\mathbb F_q\), by the minimal polynomial degree and multiplying a basis by a nonzero scalar. For the law of the first \(f\) coefficients reduced on this basis, the maximum atom is at most \((2/3)^f\). Adding any independent remaining coefficients cannot increase the maximum atom.

For the second bound, drop any residual short block from (4), then write its product as \(L\) block functions
\[
 g_b(u)=\prod_{j=0}^{f-1}
 e^{-c\|\operatorname{Tr}(u\alpha^{bf+j})/q\|_{\mathbb R/\mathbb Z}^{2}},
 \quad 0\leq b<L .
\]
The map \(u\mapsto(\operatorname{Tr}(u\alpha^{bf+j}))_{j=0}^{f-1}\) is bijective from \(\mathbb F_Q\) to \(\mathbb F_q^f\), by the nondegenerate trace pairing and the basis above. Hölder (also valid trivially at \(L=1\)) and the elementary one-dimensional Gaussian sum bound give
\[
 \begin{split}
 \mathbb E_{u\in\mathbb F_Q}\prod_{b=0}^{L-1}g_b(u)
 &\leq \prod_{b=0}^{L-1}(\mathbb E g_b(u)^L)^{1/L}\\
 &=\left(q^{-1}\sum_{z\in\mathbb F_q}
          e^{-cL\|z/q\|_{\mathbb R/\mathbb Z}^{2}}\right)^f
 \leq\left(q^{-1}+C_2/\sqrt L\right)^f .
 \end{split} \tag{5}
\]
The last inequality extends the sum over positive centered integer representatives to all positive integers and compares it to a decreasing Gaussian integral, with \(q^{-1}\) the zero frequency. Since \(L\geq n/(2f)\) this proves (1).

For completeness (1) is uniformly \(O(1/n)\). If \(f\geq D\log n\) with \(D\) a large absolute constant, the first bound \((2/3)^f\leq n^{-2}\) suffices. If \(f=1\), use \(q\geq n+1\); if \(f=2\), use \(q\geq\sqrt{n+1}\) in the second bound. For \(3\leq f<D\log n\), split at \(q=n^{5/12}\). If \(q\leq n^{5/12}\),
\[
 (q^{-1}+C_2'\sqrt{f/n})^f
 \leq q^{-f}\exp(C_2'f^{3/2}q/\sqrt n)
 \leq (1+o(1))/(n+1)
\]
uniformly, since \(f^{3/2} n^{-1/12}=o(1)\) and \(Q=q^f\geq n+1\). For \(q>n^{5/12}\), the bracket is at most \(2n^{-5/12}\) for large \(n\) uniformly in \(f<D\log n\), so its \(f\)-th power is at most \(8n^{-5/4}\). A universal constant also covers the finite \(n\) before these inequalities are valid.

## 4. From local atoms to the requested proportion

A proper ideal containing \(q\) lies in a maximal ideal above \(q\). For the full product box and any prescribed center \(x\), the event at a particular prime \(\mathfrak p\) of having every coordinate \(y_i-x_i\) in \(\mathfrak p\) has probability at most \(A_{n,q,f}^m\) by the uniform atom bound and independence across the \(m\) ring coordinates. Union over the \(n/f\) factors. Passing to a uniform \(y\) in a subset \(X\) of relative density \(\delta\) enlarges the probability by at most \(\delta^{-1}\) for every fixed center (not \(\delta^{-2}\)). This proves (2). Removing a prescribed diagonal point enlarges the upper estimate by at most its stated conditioning factor. For arbitrary \(X\) without a density or other assumption, a universal statement of high coprimality would be false: a subset contained entirely in one simultaneous residue class at a prime over \(q\) has no coprime pairs when it contains at least two points.

## Reproduction

Run `python3 verify-cyclotomic-box-coprimality.py` (standard library only). It checks finite coefficient convolutions in several residue degrees, the consecutive-power basis and exact \(L\)-block Hölder input in small ambient rings, and modular level-set relations in small split examples. These are arithmetic checks of the proof ingredients, not empirical randomness or security estimates.
