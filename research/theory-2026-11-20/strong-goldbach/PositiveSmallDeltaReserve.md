# Positive reserve in the small part of an exact polynomial-scale δ cover

Use the ordered prime count, pole blocks \(M_q\), centered–centered blocks \(D_q\), and notation of [the exact δ identity](ExactDeltaLinearRemoval.md) and [its unconditional large-conductor reduction](LargeConductorDeltaSectors.md). Write \(I=\int w>0\). There are arbitrarily small fixed \(t>0\), and a choice between just two polynomial scales \(Y=X^t,X^{3t}\), \(Q=X/Y\), with the following property. Put \(Z=X^{100t}=X^\nu\); \(\nu\) is fixed sufficiently small. Let \(\tilde\beta\) be the one possible simple real exceptional zero of the primitive Dirichlet family of conductor and height at most \(Z\), in the usual zero-free strip specified below; set \(\Delta=(1-\tilde\beta)L\) if present, and \(\Delta=\infty\) otherwise. For any fixed \(C>0\), the chosen scale satisfies
\[
  \sum_{q\le Q} M_q+\sum_{q\le YL^C}D_q
   \ \ge\ c_w X\mathfrak S(N)\min(1,\Delta)-O_{w,g,\omega,\psi,C,t}(X^{1-c_t}). \tag{1}
\]
There is **no GRH hypothesis**. In particular if \(\Delta\ge L^{-1}\), the [three-large-conductor coefficient](LargeConductorDeltaSectors.md) is the only remaining contribution capable of canceling a fixed multiple of \(X\mathfrak S(N)/L\). No sign bound for that dense covariance is claimed. The treatment of possible real zeros uses established log-free density/repulsion and the arithmetic of the classical generalized singular series, not a new theorem on Dirichlet zeros.

For a literal counterexample to binary Goldbach, as distinct from just a zero weighted count on one particular interval, the repository's separately proved [polynomial-conductor exceptional criterion](PolynomialConductorExceptionalGoldbach.md) and its cited Matomäki–Merikoski other local strata rule out \(\Delta\le L^{-1}\) if \(\nu<\kappa(1)\) there. The implication is optional: (1) and the ordinary-regime consequence do not use that other criterion. One should **not** infer that a representation supplied there must fall in the support of the present \(w,g\).

## Uniform Gauss coefficients, without squarefreeness of the conductors

Fix primitive characters \(\chi,\psi\) of conductors \(r,s\), and \(l=[r,s]\). At \(q\) divisible by both conductors their complete coefficient is
\[
 B_q(\chi,\psi)=\varphi(q)^{-2}\sum_{a,b(q)}^*\bar\chi(a)\bar\psi(b)c_q(N-a-b).
\]
It is zero at moduli not divisible by \(l\). Factors at coprime prime powers separate exactly: the variables are reduced residues and \(c_q(k)\) is multiplicative in \(q\), so there is no untracked unit twist. At \(p^v\Vert l\) at least one local character is primitive of conductor \(p^v\). For modulus \(p^v\) use \(c_{p^v}(k)=p^v1_{p^v|k}-p^{v-1}1_{p^{v-1}|k}\). The second term vanishes by summing the primitive character on lifts of a fixed class modulo \(p^{v-1}\); when \(v=1\) this is just its zero total on units. Thus the local coefficient is \(p^v/\varphi(p^v)^2\) times the character sum on the **exact** reduced-pair congruence. The same factor without the characters equals \(1+s_p\), \(s_p=c_p(N)/\varphi(p)^2\): for each reduced first variable there are either no forbidden classes apart from zero when \(p|N\), or one additional forbidden class modulo \(p\) otherwise, each with \(p^{v-1}\) lifts. At a larger exponent \(v'>v\), both induced characters depend only on the first \(v\) digits, and summing \(c_{p^{v'}}(N-a-b)\) over the final lifts of either unit variable gives zero (by the two indicators above). At \(p\nmid l\), both characters are locally principal, giving exactly \(s_p\) at the first power and zero at higher powers, by averaging the two unit exponential sums. Consequently the supports and bounds are
\[
 B_q=B_l s_m\quad(q=lm,\ (m,l)=1),\qquad B_q=0\ \text{if }l|q,\ (q/l,l)>1;
 \quad |B_l|\le\prod_{p|l}(1+s_p).
\]
Here \(s_m\) itself vanishes for nonsquarefree \(m\). This proves both
\[
 \sum_q |B_q|\le K_0\mathfrak S(N),\qquad
 \left|\sum_q B_q\right|\le\mathfrak S(N),\tag{2}
\]
with an absolute \(K_0\), since \(\prod_{p>2}(1+(p-1)^{-2})/(1-(p-1)^{-2})<\infty\) and \(N\) is even. The second inequality uses the signed Euler factors and has **exact constant one**. The Rankin estimate \(\sum_m|s_m|m^{1/2}\ll X^{o(1)}\) and \(|B_l|\ll X^{o(1)}\) hold as in the pole model. The signed generalized singular series bound and its specialization to quadratic characters are classical; see [Bhowmik–Grimmelt, §§5–7, esp. (6.4)–(6.7)](https://arxiv.org/html/2607.27282v2#S6) and the cited Pintz Main Lemma. Here the absolute-moduli first bound is used **before** replacing the variable archimedean kernel.

## Exact low-sector zero truncation

After the primitive pole is removed at each input, the low \(D_q\) are sums over ordered pairs of nontrivial zeros. A pair \(\rho=\beta+i\gamma\), \(\rho'=\beta'+i\gamma'\) of inducing primitive characters has positive double-zero sign and coefficient \(c_QB_q\) times
\[
 J_q(\rho,\rho')= H^{-1}\int w(y/X)g(z/X)b_{q/Q}((y+z-X)/H)y^{\rho-1}z^{\rho'-1}\,dy\,dz,
 \qquad H=qQ.
\]
In the following formula the low sum \(q\le YL^C\) and its cuts are literal (not a conventional major arc approximation). Only \(|\gamma|,|\gamma'|\le Z\) need be retained, with overall \(O(X^{1-c_t})\) error. Details: the compact smooth explicit formula for each primitive \(L\) is a distributional sum of its unit pole density (when present), the negative densities \(y^{\rho-1}dy\) for nontrivial zeros, and the trivial-zero densities, which sum absolutely to \(O(y^{-1})dy\) on the supports. It follows as usual by shifting the Mellin contour in the log-derivative; any distribution supported at \(y=1\) plays no role. Primes here exceed \(q\), and on passing through primitive \(\Lambda\) measures, all proper powers, including those of divisors of \(q\), may be discarded. Per character the total variation of their measure in the fixed support is \(O(\sqrt X L^2)\). Bounding their pairing with a prime/pole/\(\Lambda\) measure trivially by \(O(X^{3/2} L^4/H)\), and summing even a crude \(O(q^3)\) in coefficients per modulus, costs \(O(X^{1/2+16t+o(1)})\) since \(q\le X^{3t+o(1)}\), \(H\ge X^{1-3t}\). A trivial-zero measure has even smaller variation \(O(1)\); it can be removed before expanding the opposite prime/pole measure (and then again by symmetry), so causes no large unweighted zero count.

The crude absolute integral satisfies \(|J_q|\le K_1 X^{\beta+\beta'-1}\), uniformly for \(H\) both below and above \(X\), by integrating the absolute kernel in \(z\) and using fixed positive supports. Alternatively, log-variable integrations by parts \(k\) times in each coordinate give
\[
 |J_q|\ll_k X^{\beta+\beta'-1}Y^{2k+1}(1+|\gamma|)^{-k}(1+|\gamma'|)^{-k}.
\]
This uses \(X/H\le Y\) and uniform kernel derivatives. The elementary unit-height zero count \(O(\log((f+2)(2+|\gamma|)))\) at conductor \(f\) gives \(\sum_\rho(1+|\gamma|)^{-2}\ll L\) here. If at least one height exceeds \(Z\), the extra \(Z^{-(k-2)}\) beats \(Y^{2k+1}\) and all powers from the polynomially many moduli/coordinates for sufficiently large fixed \(k(t)\), as \(Y\le X^{3t}, Z=X^{100t}\). This justifies the two-variable exchange and uniform truncation, including for imprimitive lifts and including the zeta zeros.

## Log-free weight of all genuinely nonexceptional modes

Use [Thorner–Zaman, arXiv:2208.11123v4, (1.1)–(1.2), Theorem 2.6, Proposition 6.2 and Corollary 6.1](https://arxiv.org/pdf/2208.11123v4). With conductor and height bounded by \(Z\), the region \((1-\beta)\log Z<c_1\) has at most the simple exceptional real zero of one primitive quadratic character. One can take a smaller fixed \(c_1>0\) to apply Theorem 2.6's height-dependent region uniformly up to \(Z\); if the narrow strip contains no zero, the ordinary bound suffices. If present, \(\tilde\beta=\beta_1(Z)\) in their notation. Excluding this zero, their bound for \(N^*\) is \(\ll \min(1,(1-\tilde\beta)\log Z)(C_1Z^{198})^{1-\sigma}\); without it use the ordinary \(N\) bound with smaller exponent 127. Both statements are log-free, count multiplicities, and concern **all** primitive characters/zeros, not one exceptional modulus at a time. For \(Z\) sufficiently large, \(C_1Z^{198}\le Z^{199}\). Thus the count of ordinary modes with \((1-\beta)L\le u\) in these ranges is zero below \(c_1/\nu\), and otherwise \(\ll m_*\exp(199\nu u)\), where \(m_*=\min(1,\nu\Delta)\) if the exceptional zero is present, and 1 otherwise. Above \(u=L\) extend the estimate with the total count at \(u=L\); a boundary equality can be handled by a limit. Integrating this count against \(e^{-u}du\) yields
\[
 E:=\sum_{\substack{f\le Z,\ \chi\pmod f\ {\rm prim.}\\ |\gamma|\le Z,\ \rho\ne\tilde\beta}}X^{\beta-1}
 \ \ll m_*\exp(-c_1(1-199\nu)/\nu),\tag{3}
\]
omitting the exclusion if there is no exceptional zero. Constants in (2), (3) and the crude archimedean bound are independent of \(\nu\). Choose \(\nu\) sufficiently small that their fixed multiples of this exponential factor are much less than \(I\), then fix \(t=\nu/100\). Using (2) and the crude bound on \(J_q\), the combined absolute cost of every double-zero term with at least one ordinary member is \(\le O(K_0K_1(E^2+2E))X\mathfrak S(N)\), hence as small a fixed multiple of \(I X\mathfrak S(N)\min(1,\Delta)\) as desired. This includes all low-height complex modes. Neither GRH nor an unquantified assumption that all near-1 modes are real has been used.

## Isolated real-pair archimedean and arithmetic factor

If there is no exceptional zero take \(Y=X^t\). If its conductor \(r\ge X^{2t}\), take \(Y=X^t\), so that no small modulus \(q\le YL^C\) is a multiple of \(r\). Otherwise choose \(Y=X^{3t}\). Then \(r<X^{2t}\), and only \(q=rm\), \((r,m)=1\), occur for the exceptional–exceptional pair. For \(m\le X^{t/2}\) all such \(q\) are within the small sector and \(H/X=q/Y\le X^{-t/2}\); normalized kernel mass and first absolute moment give
\[
 J_q(\tilde\beta,\tilde\beta)=X^{2\tilde\beta-1}\big(I_{\tilde\beta}+O(X^{-t/2}+ (q/Q)^2)\big),\quad
 I_b=\int w(u)g(1-u)[u(1-u)]^{b-1}du.
\]
The test derivatives needed here are bounded uniformly for \(b\in[0,1]\), as both prime weights are compactly supported away from zero. For \(m>X^{t/2}\), both the original finite tail and the signed completion of this expression cost \(O(X^{1-t/4+o(1)})\) by (2)'s Rankin estimate and the crude bound on \(J_q\). The entire exceptional term is therefore
\[
 X e^{-2\Delta} I_{\tilde\beta}\sum_q B_q(\tilde\chi,\tilde\chi)+O(X^{1-c_t}),
\]
with no cutoff dependent character phases. By (2) it is bounded below by \(-X\mathfrak S(N)e^{-2\Delta}I_{\tilde\beta}+O(X^{1-c_t})\). On the central support \(I_{\tilde\beta}\le I\exp(C_w\Delta/L)\), so for large \(X\), \(I-e^{-2\Delta}I_{\tilde\beta}\ge I(1-e^{-\Delta})\gg I\min(1,\Delta)\). When the exceptional pair is absent the full pole mass \(X I\mathfrak S(N)+O(X^{1-c_t})\) remains. Adding the small ordinary-mode error from (3) proves (1).

Take the independent large-sector theorem with \(A=3\) (larger if desired). Whenever \(\Delta\ge L^{-1}\), in particular throughout the ordinary no-exceptional-zero regime, \(R_w(N)=0\) forces the real part of its explicitly restricted three-large-conductor covariance at the selected polynomial scale to be \(\le -c_w X\mathfrak S(N)\min(1,\Delta)\). The real part allows even nonconjugation-symmetric adaptive sparse deletions. The literal common target atom and the remaining dense covariance prevent any positivity inference for the full prime-pair count. This is a statement about the specified exact cover at each target, not a density estimate over neighboring integers.
