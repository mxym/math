# One-surplus Gaussian generation at vanishing coefficient width in dyadic rings

This note concerns only the probability that independent Gaussian columns generate a standard free module over a power-of-two cyclotomic integer ring. It does not bound the smoothing parameter of their kernel, prove a leftover hash lemma, or change the security claim of any cryptosystem.

## 1. Result and comparison

For a power of two \(n\), let \(R_n=\mathbb Z[\zeta_{2n}]\), with the canonical Euclidean norm counting both conjugate embeddings. Write \(D_{R_n,s}\) for the centered discrete Gaussian giving an element \(y\) weight \(\exp(-\pi\|y\|_{\rm can}^2/s^2)\). The powers \(1,\zeta_{2n},\ldots,\zeta_{2n}^{n-1}\) have canonical Gram matrix \(n I\), so the coefficient width is \(t=s/\sqrt n\).

Fix \(D>0\), let \(1\le r,u\) with \(r+u\le n^D\), and put
\[
 \lambda=\exp[-\pi/\min(t,1)^2],\qquad L_n=\log(4n^2),
 \qquad E_n=\lambda\sqrt{n/L_n}.
\]
If \(E_n/\log n\longrightarrow\infty\), then for a matrix \(X\) of shape \(r\times(r+u)\) with independent \(D_{R_n,s}\) entries,
\[
 \Pr(XR_n^{r+u}=R_n^r)
 =\prod_{j=u+1}^{u+r}(1-2^{-j})
   +O_D\!\left(n(2n)^{-u-1}
             +n^{3D+2}e^{-cE_n}\right)                       \tag{1}
\]
with a universal constant \(c>0\). The error statement is uniform for all sufficiently large \(n\) when \(E_n\) exceeds a sufficiently large \(D\)-dependent multiple of \(\log n\). In particular it applies uniformly for any fixed \(0<\delta<1/2\) and
\[
                         s\ge \sqrt{\frac{\pi n}{\delta\log n}} .
\]
The product in (1) is the probability of full row rank of a uniform binary matrix. In particular (1) allows **one** surplus column. The generation probability is then generally bounded away from both zero and one, not near one.

The [companion note](cyclotomic-gaussian-module-generation.md) proves the same asymptotic structural conclusion for prime-power conductors at canonical width \(s\ge C|\Delta_K|^{1/[K:\mathbb Q]}\), with \(C>1\); this is \(s\ge Cn\) in the dyadic case. The old all-prime estimate uses full-lattice smoothing to bound both the small-prime density and the large-prime atom. Here two complementary subfield inequalities replace that step. We reuse the one-fresh-coordinate large-prime sieve and restate it below.

For published context, [Albrecht–Felderhoff–Lai–Lapiha–Woo, Corollary 3.9](https://perso.jfelderhoff.fr/work/papers/AFLLW25.pdf) treats more general Gaussian/module models with many columns under GRH. [Düzlü–Gargava–Tairi, Theorem 5.9, fixed 2026-11-12 version](https://opencryptology.org/2026/2180/versions/20261112T135305Z.pdf) gives both surjectivity and kernel smoothing unconditionally at coefficient width at least one, with its stronger column-count hypothesis (41). Neither that smoother's conclusion nor the general-module statement is claimed here. [Stehlé–Steinfeld, Lemma 4.4](https://eprint.iacr.org/2013/004.pdf) gives a positive lower bound for two generating elements at larger widths. The Fourier product idea is classical, e.g. [Breuillard–Varjú, §2](https://ora.ox.ac.uk/objects/uuid%3Ad49495ed-7750-48f1-844e-76eb91a6910b/files/s2f75rb26g); the elementary bounds below use the dyadic tower rather than a scalar affine chain or an average over multipliers.

## 2. A coefficient Gaussian and the dyadic tower

Let \(\phi_t(v)=\mathbb E\exp(2\pi i v Z_t)\), where \(Z_t\) has weights proportional to \(\exp(-\pi z^2/t^2)\) on \(\mathbb Z\). Put \(a=\exp(-\pi/t^2)\). The Jacobi triple product gives
\[
 \phi_t(v)=\prod_{j\ge1}\left(1-
              \frac{4a^{2j-1}}{(1+a^{2j-1})^2}\sin^2(\pi v)\right).
\]
Every factor is positive and nonincreasing in \(t\); convergence gives a nonnegative, nonincreasing \(\phi_t(v)\). The first factor at width \(\min(t,1)\), together with \(\sin(\pi|v|)\ge2|v|\) for \(|v|\le1/2\), implies
\[
       0\le \phi_t(v)\le \exp(-4\lambda\,{\rm dist}(v,\mathbb Z)^2).
                                                                  \tag{2}
\]
Consequently for a sum of independent such coefficients times prescribed finite-group elements, the maximum atom is at zero and is nonincreasing in \(t\): its Fourier coefficients are nonnegative and nonincreasing, and the corresponding inversion at zero just adds them. This also holds when some prescribed elements are zero. The largest *exact* atom of an \(n\)-coefficient element is at most \(\exp(-\lambda n)\), since the coefficient's normalizer is at least \(1+2\lambda\) and \(\log(1+2\lambda)\ge\lambda\).

Fix an odd rational prime \(p\) and a prime ideal \(\mathfrak P\) above it. Write \(F=R_n/\mathfrak P\), \(Q=|F|=p^f\), and let \(\alpha\) be the image of \(\zeta_{2n}\). It has order \(2n\) because \(\alpha^n=-1\) and \(2n\) is a power of two. For a power of two \(m\le n\), write \(d=n/m\), \(\beta=\alpha^d\), \(F_m=\mathbb F_p(\beta)\subset F\), \(Q_m=|F_m|\), and \(\ell=[F:F_m]\). These are the residue field and norm for the contraction of \(\mathfrak P\) to \(R_m=\mathbb Z[\zeta_{2n}^{d}]\). We have \(\ell\le d\) by the relation \(\alpha^d=\beta\), and \(\ell\) divides \(d\): the two residue degrees are powers of two because they are the multiplicative orders of \(p\) modulo \(2n\) and \(2m\), so \(\ell\) and \(d\) are both powers of two. Every \(\ell\) consecutive powers of \(\alpha\) form a basis over \(F_m\), by the minimal polynomial degree and multiplication by a nonzero power. The polynomial with independent Gaussian coefficients splits as
\[
            Y=\sum_{i=0}^{d-1}\zeta_{2n}^i Y_i,\qquad
            Y_i=\sum_{j=0}^{m-1} Z_{i+dj}(\zeta_{2n}^d)^j ,
                                                                  \tag{3}
\]
where the \(Y_i\in R_m\) are independent \(m\)-coefficient blocks.

For an integral ideal \(I\) of \(R_m\), write \(\|\cdot\|_{\rm coef}\) for the ordinary norm of its power-basis coefficients. The normalized Hermitian trace form is
\(\langle x,y\rangle_{\rm coef}=\operatorname{Tr}(x\bar y)/m\).
The trace dual of \(R_m\) is \((1/m)R_m\), either by this orthogonal power basis or by the derivative of \(x^m+1\). Thus the coefficient dual of \(I\) is \(\overline I^{-1}\). For \(0\ne v\) in it, the integral ideal \((v)\overline I\) has norm at least one, so \(|\mathrm N(v)|\ge1/\mathrm N(I)\). Arithmetic-geometric mean over the embeddings gives
\[
       \|v\|_{\rm coef}^{\,2}
            =m^{-1}\sum_\sigma |\sigma(v)|^2
            \ \ge\ |\mathrm N(v)|^{2/m}
            \ \ge\ \mathrm N(I)^{-2/m}.                       \tag{4}
\]
The same identity without the last inequality gives \(|\mathrm N(x)|\le\|x\|_{\rm coef}^{m}\) for \(x\in R_m\). Degree \(m=1\) uses \(R_1=\mathbb Z\).

## 3. Small and medium prime norms: a subfield Fourier inequality

Assume \(Q\le e^n\). Choose the smallest dyadic \(m\le n\) satisfying \(m\ge\log Q_m\); at \(m=n\) the condition holds. Because \(p\ge3\) we cannot have \(m=1\). At the preceding dyadic \(m/2\) the condition fails, and \(F_{m/2}\subseteq F_m\). Thus
\[
            m<2\log Q_m,\qquad m\ell<2\log Q.                 \tag{5}
\]
Consider a nontrivial additive character \(\chi\) of \(F\). For each restricted character \(z\mapsto\chi(\alpha^i z)\) on \(F_m\), its values on \(1,\beta,\ldots,\beta^{m-1}\) determine its phases in \([-1/2,1/2)\). These phases are the coefficient vector of an element in the coefficient dual of the contracted ideal, since the phases pair integrally with its kernel. If the restricted character is nontrivial the vector is nonzero, hence has squared norm at least \(Q_m^{-2/m}\ge e^{-2}\) by (4). In (3), this block contributes a factor at most \(\exp(-4e^{-2}\lambda)\) to \(|\mathbb E\chi(Y)|\), by (2).

The restrictions cannot all be trivial on any \(\ell\) consecutive indices \(i\). Otherwise the character would be trivial on the sum of those \(\ell\) \(F_m\)-lines, which is all of \(F\). So at least \(d/\ell=n/(m\ell)\) blocks contribute the stated factor. We obtain the pointwise-in-character bound
\[
 |\mathbb E\chi(Y)| \le \exp\!\left(-a_0\lambda n/\log Q\right),
                  \qquad a_0=2e^{-2}.                         \tag{6}
\]
In particular if \(\mu_\mathfrak P\) is the law of \(Y\bmod\mathfrak P\), Fourier inversion gives both a relative bound
\(\sup_x|Q\mu_\mathfrak P(x)-1|\le Q\exp(-a_0\lambda n/\log Q)\)
and an additive bound
\(\sup_x\mu_\mathfrak P(x)\le Q^{-1}+\exp(-a_0\lambda n/\log Q)\).
The relative and additive uses have different ranges.

## 4. Large prime norms: independent subfields and atoms

For clarity assume \(\lambda\ge n^{-1}\), as holds eventually in the useful range of (1). By the monotonicity after (2), to upper-bound any maximum atom it suffices to work at \(\min(t,1)\). At this width the probability of an exact coefficient value is at most \(e^{-\lambda}\). Modulo an odd prime \(p\) the maximum atom is at zero; the probabilities of \(Z=1\) and \(Z=-1\) together are at least \(\lambda\), since its normalizer is at most \((1+\lambda)/(1-\lambda)<2\). They are outside the zero residue, so the modulo-\(p\) maximum is at most \(e^{-\lambda}\).

Suppose a dyadic \(m\le n\) satisfies \(\log Q_m\ge m L_n\). Distinct vectors in the coefficient box \([-n,n]^m\) map to distinct elements of \(F_m\). Otherwise their nonzero difference \(a\) would be in the contracted prime and \(Q_m\) would divide \(|\mathrm N(a)|\), whereas (4) gives
\[
                 |\mathrm N(a)|\le (2n\sqrt m)^m < e^{mL_n}\le Q_m .
\]
The mass of a point of \(F_m\) from one \(m\)-coefficient block inside the box is at most \(e^{-\lambda m}\). Its outside probability is at most \(4n\lambda^{(n+1)^2}\). Since \(n^{-1}\le\lambda\le e^{-\pi}\) and \(1\le m\le n\), for all sufficiently large \(n\) this is at most \(e^{-\lambda m/2}-e^{-\lambda m}\): the difference is at least \((\lambda m/2)e^{-\lambda m}\ge e^{-n}/(2n)\). Therefore the maximum atom of one block is at most \(e^{-\lambda m/2}\).

Take the **largest** dyadic \(m\) meeting \(\log Q_m\ge mL_n\), if one exists. Conditional on all the other blocks in (3), the \(\ell\) blocks at \(0,\ldots,\ell-1\) contribute independently in the direct sum of their \(\ell\) \(F_m\)-lines. Hence the atom bound is \(e^{-\lambda m\ell/2}\), not merely the bound for one block. If \(m<n\), failure at \(2m\) and \(F_m\subseteq F_{2m}\) imply \(\log Q_m\le\log Q_{2m}<2mL_n\), so \(m\ell>\log Q/(2L_n)\). If \(m=n\) we have \(m\ell=n\). If no such \(m\) exists, then \(\log p=\log Q_1<L_n\). Conditional on coefficients after the first \(f=[F:\mathbb F_p]\), those first \(f\) coefficients give independent scalar residue coordinates in the power basis of \(F\). Their total atom is at most \(e^{-\lambda f}\), with \(f>\log Q/L_n\). Combining the cases gives, at the original width as well,
\[
          \sup_x\mu_\mathfrak P(x)
            \le \exp[-(\lambda/2)\min(n,\log Q/(2L_n))].      \tag{7}
\]

Choose a universal \(b>0\) with \(b^2\le a_0/2\), and set \(H_0=\exp(b\sqrt{\lambda n})\). For \(Q\le H_0\), (6) gives relative error at most \(\exp(-b\sqrt{\lambda n})\). For
\(H_0<Q\le\exp(\sqrt{nL_n})\), use the **additive** form of (6) to get an atom bound \(H_0^{-1}+\exp(-a_0 E_n)\). For larger \(Q\), use (7) to get \(\exp(-E_n/4)\). The assumptions \(\sqrt{nL_n}\le n\) and \(\sqrt{\lambda n}\ge E_n\) hold for all sufficiently large \(n\), so all \(Q>H_0\) have atom at most \(2e^{-c_0 E_n}\) for an absolute \(c_0>0\).

## 5. Assembling the all-prime sieve

For arbitrary large width also allow the old smoothing cutoff \(H_s=(s/n)^n\), and use \(H=\max(H_0,H_s)\). At any prime ideal with \(Q\le H_s\), (4) at \(m=n\) gives canonical dual minimum at least \(n^{-1/2}Q^{-1/n}\), since the canonical metric scales primal coefficient lengths by \(\sqrt n\) and dual lengths by its inverse. Then \(s\ge nQ^{1/n}\) is enough for smoothing error \(e^{-n}\), by the usual [shortest-dual-vector bound, Lemma 2.6](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf). Poisson on the ideal and full ring gives \(\sup_x|Q\mu_\mathfrak P(x)-1|\le2e^{-n}\): all ideal cosets have the same main term up to relative \(e^{-n}\) and the full-ring normalizer is between its own main term and \(1+e^{-n}\) times it. Thus for every odd prime ideal of norm \(\le H\) use a relative atom upper \((1+\epsilon)/Q\) with \(\epsilon=e^{-b\sqrt{\lambda n}}+2e^{-n}\). Every prime with norm \(>H\) is odd for large \(n\) and has atom \(\beta_0\le2e^{-c_0 E_n}\).

*Small odd primes.* A nonzero left relation over a field of cardinality \(Q\) specifies one entry of its column, conditioned on the other entries. Use independent columns and union over projective nonzero left vectors of length \(r\). The failure bound at a prime with \(Q\le H\) is at most \(2(1+\epsilon)^{r+u} Q^{-u-1}\). Since \(Q\equiv1\bmod 2n\) and at most \(n\) primes have any given norm, their total is at most \(2(1+\epsilon)^{r+u}n(2n)^{-u-1}\zeta(u+1)\). Here \(\zeta(u+1)\le\zeta(2)\), and \((1+\epsilon)^{r+u}=O_D(1)\) in the stated range.

*Large odd primes.* Use the leading \(r+1\) columns. Induct over \(j\) on the event that the first \(j\) rows of the leading \(j+1\) columns have full row rank at every prime of norm \(>H\). The previous event implies that the first \(j-1\) rows of the leading \(j\) columns have full rank at each such prime, hence have rank \(j-1\) over \(K\); a rank loss over \(K\) would force all corresponding integral minors to be zero even after reduction. Conditional on those top rows, singularity of the leading \(j\)-square over \(K\) fixes one bottom entry given the others, costing at most \(e^{-\lambda n}\). Charge separately any entry of the square exceeding \(s\sqrt n\) in canonical norm, costing at most \(j^2 e^{-n}\). Indeed the Gaussian moment bound follows from \(\rho_{\sqrt2s}(R_n)/\rho_s(R_n)\le2^{n/2}\) by Poisson and yields \((\sqrt2 e^{-\pi/2})^n\le e^{-n}\) per entry.

For a nonsingular leading square with bounded entries, the only candidate primes divide its determinant. Hadamard at every place gives an absolute norm at most \((s\sqrt{jn})^{jn}\), so their number at norms \(>H\) is at most \(jn\log(s\sqrt{jn})/\log H\). This is \(O_D(jn\log n)\) uniformly: for \(s\le n^2\) use \(\log H\ge\log H_0\ge1\) in the stated range, and for \(s>n^2\) use \(\log H\ge n\log(s/n)\ge (n/2)\log s\). At a candidate prime the square's rank is exactly \(j-1\) and a left null row has nonzero last coordinate by the preceding event. Conditional on the actual square and the top \(j-1\) entries of the new column, the bottom entry is still fresh. Failure of rank repair fixes a single residue of this entry, of probability at most \(\beta_0\). That bound holds for each of the finitely many candidates and requires no independence between primes. Summing over \(j\) bounds the whole large-prime error by \(O_D(n^{3D+2}e^{-cE_n})\) for an absolute \(c>0\). Extra columns cannot decrease rank.

*The ramified prime.* The unique prime above two is \((1-\zeta_{2n})\) with residue \(\mathbb F_2\), where the entries are sums of \(n\) independent coefficients. Their parity differs from a fair bit with TV at most \(\frac12|\phi_t(1/2)|^n\le\frac12 e^{-\lambda n}\) by (2). Tensorization gives an \(r(r+u)e^{-\lambda n}/2\) matrix error. The uniform full-rank probability is the product in (1), by exposing its \(r\) rows in dimension \(r+u\). Surjectivity over \(R_n\) is equivalent to full row rank at every maximal ideal by finite generation of the cokernel and Nakayama's lemma. Intersecting with the ramified prime event and subtracting the union of odd-prime failures proves (1).

## 6. A necessary lower regime and limits

For \(r=u=1\), the corresponding uniform binary generation probability is \(3/4\). If along a subsequence \(n\lambda\to c_*<\infty\), necessarily \(t\to0\), and the original scalar characteristic function is \(\phi_t(1/2)=1-4\lambda+O(\lambda^2)\). The zero residue then has probability tending to \((1+e^{-4c_*})/2\). Therefore
\[
 \limsup \Pr(XR_n^2=R_n)
 \ \le\ 1-\left(\frac{1+e^{-4c_*}}2\right)^2 < \frac34.
\]
In particular \(n\lambda\to\infty\) is necessary for the uniform binary prediction even in rank one with one surplus. At widths \(s=C\sqrt{n/\log n}\) this rules out \(C\le\sqrt\pi\) and (1) proves every \(C>\sqrt{2\pi}\). The interval between them is not settled here. No statement is made for non-dyadic rings, nonfree modules, coefficient-dependent widths, nonzero centers, square matrices, or actual scheme parameters.

## Reproduction

Run `python3 verify-dyadic-subfield-generation.py` with Python 3 and SymPy. It checks exact generated finite-field tower/basis identities, phase-vector inequalities, independent subfield box injection, and fresh-coordinate repair. It is a finite arithmetic corroboration of the proof, not its source and not a test of a cryptosystem.
