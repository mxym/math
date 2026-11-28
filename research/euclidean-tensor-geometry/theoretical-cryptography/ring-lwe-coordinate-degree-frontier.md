# A sharp coordinate-degree threshold for broad dyadic observations

A random public multiplication design can contain enough information for reliable statistical recovery, while all bounded-variance scores of degree less than a positive multiple of the ring dimension still have vanishing expectation advantage. We compute the entire likelihood projection transition, including its logarithmic displacement. The relevant degree counts scalar response coordinates, and the score may be picked after arbitrary preprocessing of the complete public design. This is a restricted-class theorem, not an unrestricted time lower bound.

## 1. Experiments and theorem

Fix an odd modulus \(q\ge3\). Along powers of two \(d\) use
\[
R=(\mathbb Z/q)[X]/(X^d+1)
\]
with its coefficient coordinates. Let \(S,A_1,\dots,A_m\) be independent uniform in \(R\). Observe independent scalar responses given \(A,S\): the response at \((i,j)\) has signal symbol \((A_iS)_j\). We analyze either of two scalar channels, with \(b=\beta/d\), fixed \(\beta>0\), and \(m b^2\longrightarrow t>\log q\).

* **Wrapped Gaussian:** a signal \(a\) gives density \(f_b(y-a/q)\) on \(\mathbb R/\mathbb Z\), with \(f_b(x)=\sum_{k\in\mathbb Z}b^{k^2}e^{2\pi i kx}\). The product reference \(Q_*\) for all responses uses scalar density \(g_b=q^{-1}\sum_a f_b(\cdot-a/q)\).
* **Finite truth-or-uniform:** a signal \(a\) gives scalar law \((1-b)U_q+b\delta_a\) on \(\mathbb Z/q\), where \(U_q\) is uniform. The product reference \(Q_*\) uses \(U_q\).

For \(I\subseteq\{0,\ldots,d-1\}\) let \(\ell=|I|\), and condition on \(S_I=w\) as well as on the full public design \(A\). Denote the conditional likelihood ratio against \(Q_*\) by \(L^I_{A,w}\). Let \(\Pi_D\) be the \(L^2(Q_*)\) orthogonal projection onto the closed span of functions each depending on at most \(D\) distinct scalar **response** coordinates. (There is no degree charge on the public design.) Define
\[
Z_D^I(A)=\|\Pi_D(L^I_{A,w}-1)\|_2^2.
\]
The quantity is independent of \(w\), as shown below.

For wrapped noise, put
\[
\lambda_u=\int_0^1\frac{\left|\sum_{k\equiv u\bmod q} b^{k^2}e^{2\pi i kx}\right|^2}{g_b(x)}\,dx
 \quad (u\in\mathbb Z/q\setminus\{0\}),
 \qquad \Lambda=\sum_{u\ne0}\lambda_u=2b^2(1+o(1)).
\tag{1}
\]
For the finite channel all \(\lambda_u=b^2\). Let \(N=md\), and define
\[
G_D^{I} =
\begin{cases}
q^{\ell-d}\displaystyle\sum_{r=1}^D \binom{N}{r}\Lambda^r,&\text{wrapped},\\[3pt]
\displaystyle\sum_{\substack{u\mid q\\u>1}} u^{\ell-d}
          \sum_{r=1}^D\binom{N}{r}\bigl[(u-1)b^2\bigr]^r,&\text{finite}.
\end{cases}
\tag{2}
\]
For each fixed \(C<\infty\), there is a \(c>0\) (depending only on the fixed parameters) such that
\[
\max_{\substack{|I|\le cd\\0\le D\le Cd}}
\frac{|Z_D^I(A)-G_D^I|}{1+G_D^I}
 \ \xrightarrow{\ \Pr_A\ }\ 0 .
\tag{3}
\]

Here is the transition implied by (2). For the wrapped law let \(Q_0=q\) and \(\Lambda_*= \Lambda\). For the finite law let \(Q_0\) be the **smallest prime divisor of \(q\)** and \(\Lambda_*=(Q_0-1)b^2\). Put
\[
T_d=m\Lambda_*,\qquad B_d=(1-\ell/d)\log Q_0,
\quad \alpha_d\bigl(1+\log(T_d/\alpha_d)\bigr)=B_d,\quad
0<\alpha_d<T_d .
\tag{4}
\]
This is the smaller root of the logarithmic equation; it exists uniquely in the written interval for large enough \(d\). Then \(Z_D^I=o_{\Pr}(1)\) below this root by any fixed positive fraction of \(d\), while \(Z_D^I\) grows exponentially above it by any fixed positive fraction of \(d\) (for \(D=O(d)\)). More precisely set \(J_d=\log(T_d/\alpha_d)>0\). For degrees in the window
\[
s_d=D-\alpha_d d-\frac{\log d}{2J_d}=O(1),
\quad
Z_D^I(A)=\frac{\exp(J_d s_d)}{(1-e^{-J_d})\sqrt{2\pi\alpha_d}}+o_{\Pr}(1).
\tag{5}
\]
The expression keeps the integer-rounding displacement and the actual sequence \(m b^2\). In particular matching the leading sum of the \(\lambda_u\)'s does **not** make the two channels equivalent for a composite modulus. For example fix a finite-channel limit \(t_F>\log q\) and choose the wrapped limit \(t_W=(q-1)t_F/2\). The full-ring terms then have the same limiting exponent, but the finite channel reaches its transition strictly sooner, on its smallest scalar quotient. For the wrapped law the nonunit-frequency contribution fades.

## 2. The conditional orthogonal decomposition

Write \(\omega=e^{2\pi i/q}\). For wrapped noise, the one-coordinate likelihood at signal \(a\) is
\[
 \frac{f_b(y-a/q)}{g_b(y)}=1+\sum_{u\ne0}\omega^{-au}\psi_u(y), \qquad
 \psi_u(y)=g_b(y)^{-1}\sum_{k\equiv u} b^{k^2}e^{2\pi i ky}.
\]
The functions \(\psi_u\) have mean zero and are mutually orthogonal: translation by \(1/q\) preserves \(g_b\,dy\) and multiplies the \(u\)-th function by \(\omega^u\). Their squared norms are (1). Since \(g_b=1+O(b^{q^2})\) uniformly, ordinary Fourier Parseval gives \(\lambda_u=O_q(b^{2|u|_q^2})\), with \(|u|_q=\min_{k\equiv u}|k|\), and \(\lambda_{\pm1}=b^2(1+o(1))\). In particular nonunit frequencies have weight \(O_q(b^{18})\). In the finite case use \(\psi_u(y)=b\omega^{uy}\), with the same statements and \(\lambda_u=b^2\).

Let \(V_I\subset R\) consist of coefficient vectors supported on \(I\). A tuple \(U=(U_i)_{1\le i\le m}\) of response-frequency polynomials has combined coefficient weight \(r(U)\), and weight factor \(w(U)=\prod_{i,j:U_{i,j}\ne0}\lambda_{U_{i,j}}\). Conditional on \(S_I=w\), the mean of a character of the product phases has modulus one if its argument coefficient vector on \(S\) is in \(V_I\), and is zero otherwise. That argument is \(\sum_i\overline{A_i}U_i\), where bar is the involution \(X\mapsto X^{-1}\): multiplication by \(X\) is a signed permutation, so this is the adjoint relative to coefficient dot product. Products of \(\psi_u\) at distinct response coordinates are orthogonal over \(Q_*\), and a product supported on more than \(D\) is orthogonal to every function of at most \(D\) coordinates because at least one centered factor integrates out. Thus
\[
 Z_D^I(A)=
 \sum_{\substack{U\\1\le r(U)\le D}}w(U)\,
       {\bf1}\left\{\sum_i\overline{A_i}U_i\in V_I\right\}.
\tag{6}
\]
No positivity of individual complex coefficients is used; (6) is a squared norm.

For a fixed tuple \(U\), its image ideal \(J(U)=\sum_i R U_i\) contains the sum in (6). That sum is uniform on \(J(U)\), since it is the image of independent uniform elements under a homomorphism. The probability of the indicator is \(|J(U)\cap V_I|/|J(U)|\). We next control the possible ideals and then prove relative concentration within the main classes.

## 3. Fixed finite types of ideals

Choose a fixed dyadic \(d_0\) large enough that for every prime \(p\mid q\), the degree of every irreducible factor of \(X^d+1\) mod \(p\) is \((d/d_0)\) times its degree at \(d_0\). Indeed each root has order \(2d\), so the degree is \({\rm ord}_{2d}(p)\); this eventually doubles when \(d\) doubles by \(v_2(p^{2^k}-1)=v_2(p^2-1)+k-1\) for \(k\ge1\). For \(g=d/d_0\), write \(T=X^g\). Each factor \(F(T)\) at the base substitutes to \(F(X^g)\); the latter is irreducible mod \(p\) because its degree is exactly the degree of every irreducible factor at \(d\). The factorization is squarefree mod \(p\).

Over \(\mathbb Z/p^e\) the coprime Hensel lifts at \(d_0\) likewise substitute to the factorization at \(d\). The quotient by a monic lift of a mod-\(p\) irreducible factor is a finite free unramified local ring: elements not all divisible by \(p\) are units (invert in the residue field and lift over the nilpotent ideal), and all ideals are the powers of \(p\) (factor a nonzero element with minimum valuation). Thus every ideal at \(d\) is the extension of a unique base ideal \(J_0\) at \(d_0\), with finitely many types independent of \(d\), including at a composite \(q\) by CRT. More explicitly, \(R\) is free over \(R_0\) with basis \(1,X,\ldots,X^{g-1}\), by representing its polynomials in groups of powers with the same exponent mod \(g\). The idempotent factors and their powers of \(p\) correspond under extension. Hence for each ideal \(J=J_0R\),
\[
 J=\bigoplus_{h=0}^{g-1} X^h J_0,\qquad |J|=|J_0|^g.             \tag{7}
\]
The direct sum has disjoint groups of coefficient positions.

For any ideal \(J\), its scalar intersection with the embedded \(\mathbb Z/q\) has the form \(a\mathbb Z/q\) for a divisor \(a\) of \(q\). Its largest scalar ideal contained in \(J\) is \(J_a=aR\). By (7), when \(J\ne J_a\), the ratio \(|J|/|J_a|\ge 2^g\). A one-coordinate vector \(cX^r\) lies in \(J\) exactly when \(c\) lies in the scalar intersection, since \(X\) is a unit. Finally, for any nonzero ideal \(J\), \(|J|\ge2^g\). We will use all of these gap conclusions only with fixed \(q\) and \(d_0\).

## 4. Contributions outside the main classes

For the wrapped law, a non-full ideal \(J\) has scalar coefficients in a proper ideal of \(\mathbb Z/q\), so any allowed nonzero one-coordinate coefficient is a nonunit. In a fixed base coefficient block the sum of weights of all nonzero allowed words is \(O(b^{18})+O(b^4)=O(b^4)\): words of Hamming weight at least 2 have that bound by (1), and the block has constant length. Over \(mg=O(d^3)\) blocks, the sum of weights of all allowed nonzero tuples of any degree is
\[
 (1+O(b^4))^{mg}-1=O(d^{-1}).                                  \tag{8}
\]
Its expected contribution to (6), at any \(I,D\), is at most \(O(d^{-1})q^\ell 2^{-g}\) per possible exact ideal \(J\ne R\), since \(|J(U)\cap V_I|\le q^\ell\). Sum the fixed number of ideals. Markov's inequality and \(\exp(H(c)d+o(d))\) choices of \(I\) with \(|I|\le cd\) show that all proper ideals contribute \(o_{\Pr}(1)\) uniformly, by choosing \(c<1/2\) sufficiently small. Here \(H\) is natural-log binary entropy. The argument uses monotonicity in \(D\), so no extra union over degrees is needed.

For the finite law fix a nonscalar ideal \(J\ne J_a=aR\), where \(a\mathbb Z/q\) is its scalar intersection. When \(a=q\), the same estimate (8) and probability bound work, since it has no one-coordinate words. Otherwise set \(u=q/a\), \(\lambda=(u-1)b^2>0\). The base block enumerator \(P_J(z)=\sum_{v\in J_0} (b^2 z)^{\operatorname{wt}(v)}\) decomposes as \((1+\lambda z)^{d_0}+E(z)\), where \(E\) is nonnegative, begins at degree 2, and the coefficient of \(z^j\) is \(O_q(b^{2j})\). In coefficientwise order,
\[
 P_J(z)^{mg}\ \preceq\ (1+\lambda z)^N(1+E(z))^{mg}.
\]
For \(r\le Cd\) and \(0\le s\le r\), 
\[
\frac{[z^{r-s}](1+\lambda z)^N}{[z^r](1+\lambda z)^N}
=\lambda^{-s}\prod_{i=0}^{s-1}\frac{r-i}{N-r+i+1}
\le \left[\frac{r}{(N-r)\lambda}\right]^s .
\]
The square bracket stays bounded, since \(m b^2\) converges to \(t>0\) and \(u\ge3\). It follows that
\[
[z^r]P_J(z)^{mg}\le \bigl(1+O(d^{-1})\bigr)\binom{N}{r}\lambda^r .
\tag{9}
\]
In the sum over tuples of **exact** image \(J\), their common indicator probability divided by the scalar one \(u^{\ell-d}=|J_a\cap V_I|/|J_a|\) is bounded by \(a^\ell 2^{-g}\): compare \(|J\cap V_I|\le q^\ell\) and use (7). Therefore (9), followed by Markov and a union over small \(I\) and \(O(d)\) degrees, makes this whole nonscalar contribution negligible relative to \(1+G_D^I\) in (3). If \(a=q\) use the absolute bound (8), and if \(a=1\) there is no strictly larger ideal. This argument does not assume that a random image is a free module or that its proper factors have independent observations.

## 5. Relative concentration in the scalar classes

For the wrapped law the only main class is the full ideal \(R\). Use its full frequency domain and total scalar weight \(\Lambda\). For the finite law consider separately each \(J_a=aR\) with \(u=q/a>1\). Identify its additive coordinates with \(R^{(u)}=(\mathbb Z/u)[X]/(X^d+1)\) by dividing coefficients by \(a\). A uniform \(A_i\) in \(R\) reduces to independent uniform elements of \(R^{(u)}\); the target subgroup after dividing is the \(u^\ell\)-element subgroup supported on \(I\). The same notation applies to the full wrapped class with \(u=q\). Let \(\lambda_*\) denote total nonzero frequency weight on this scalar class, so the total weight of all its tuples at degree \(r\) is \(W_r=\binom Nr\lambda_*^r\).

Sample a tuple proportional to its weight in this shell. Its \(r\) positions are a uniform \(r\)-subset of \(N=md\) coordinates, and coefficients independently follow the normalized frequency weights. Uniformly over \(r\le Cd\), sequential exposure of positions has conditional probability \(O(1/d)\) of hitting a previously visited ring row. If \(r-\#\{\text{occupied rows}\}\le r/8\), at least \(3r/4\) positions are in singly occupied rows. The complementary probability is at most \(2^r(O(1/d))^{\lceil r/8\rceil}\), by selecting the collision steps and multiplying their conditional bounds. For the finite channel a fixed positive fraction of nonzero coefficients in each quotient are units; for the wrapped law the mass of unit coefficients tends to 1. A binomial tail bound on the singly occupied rows now implies: for some fixed \(\gamma,\gamma'>0\), except for weight fraction \(O(e^{-\gamma' r})\), the tuple has at least \(\gamma r\) ring rows each consisting of a single monomial with unit coefficient in the quotient. Call it good. There are only finitely many quotient choices, so the constants can be chosen uniformly. A good tuple has exact image \(J_a\).

Fix \(r\ge\varepsilon d\) for a constant \(\varepsilon>0\). Two independent weighted typical tuples \(U,U'\) admit a unit two-column minor for the maps in (6) if at least one singleton unit row of \(U\) is absent from the occupied rows of \(U'\): paired with any singleton unit row of \(U'\), the corresponding columns form a triangular matrix with unit diagonal. So their two outputs are jointly uniform and the two events in (6) independent. Given the good \(U\), the probability that all its \(\lceil\gamma r\rceil\) designated singleton rows are occupied in \(U'\) is at most
\[
          \frac{(r)_{\lceil\gamma r\rceil}d^{\lceil\gamma r\rceil}}
                     {(N)_{\lceil\gamma r\rceil}}
          \le (O(1/d))^{\lceil\gamma r\rceil}.                 \tag{10}
\]
To see the first inequality, order the \(r\) sampled positions of \(U'\) uniformly and choose an injection from the designated rows into that ordering; for a fixed injection, there are at most \(d\) eligible entries in each chosen row. Conditioning \(U'\) to be good changes the bound by a factor \(1+O(e^{-\gamma' r})\).

The good contribution to (6) from this shell has expectation \(p W_r(1+O(e^{-\gamma'r}))\), \(p=u^{\ell-d}\). Its variance divided by \((pW_r)^2\) is at most \(p^{-2}\exp[-\Omega(d\log d)]\): expand the variance over pairs, cancel all pairs for which (10)'s exceptional event fails, and upper bound the absolute covariance of the other indicators by 1. Chebyshev therefore gives the required relative concentration simultaneously over all \(I,r\le Cd\) (the number of \(I\)'s is at most \(2^d\)). Atypical tuples of **exact** image \(J_a\) have expected contribution at most \(p W_r O(e^{-\gamma' r})\), since the exact image is what fixes \(p\). Markov controls these relative to \(p W_r\) at an exponentially decaying error after a union over \(|I|\le cd\), by taking \(c\) small enough that \(H(c)<\gamma'\varepsilon/4\). Other atypical images belong to other classes already treated or treated this way separately. This is why the sum over scalar quotients in (2) is not a multiple count of the same tuples.

For \(1\le r<\varepsilon d\), the expected total scalar contribution at fixed \(I\) is at most \(\sum_{u} u^{\ell-d}\sum_{r<\varepsilon d}\binom Nr \lambda_*^r\), by classifying exact ideals first, so there is no concentration prerequisite. Since \(N\lambda_*=O(d)\), the sum is exponentially small in \(d\) for all \(\ell\le cd\) after first choosing \(\varepsilon\) small, then \(c\) small: use \(\binom Nr\lambda_*^r\le(eN\lambda_*/r)^r\) and \(\varepsilon(1+\log(C_1/\varepsilon))\to0\). A union and Markov control these same small degrees absolutely. Choose the same \(c\) to meet the proper-ideal and high-shell bounds; it is independent of \(d\). Summing all shells gives (3).

## 6. Growth, logarithmic window, and the restricted lower bound

For a term \(u^{\ell-d}\sum_{r\le D}\binom Nr\lambda_*^r\) in (2), set \(T_d=m\lambda_*\), \(B_d=(1-\ell/d)\log u\). Uniformly for \(r=O(d)\), \(\binom Nr \lambda_*^r=(dT_d)^r/r!\,(1+O(d^{-1}))\) since \(N=\Theta(d^3)\). On the scale \(D/d=x<T_d\), the exponential rate is \(x(1+\log(T_d/x))-B_d\), and above \(T_d\) the maximum is \(T_d-B_d\). All fixed limits are separated from zero around the smaller root except in its intended window. At \(D=\alpha_d d+(\log d)/(2J_d)+s_d\), Stirling and Taylor's theorem give the final-term value
\[
u^{\ell-d}\frac{(dT_d)^D}{D!}
=(1+o(1))\frac{e^{J_d s_d}}{\sqrt{2\pi\alpha_d}}.
\]
The ratio of each preceding term to its successor differs from \(\alpha_d/T_d\) by \(o(1)\) at each bounded backward offset, and all such ratios are dominated by a single constant less than 1. Summing the resulting geometric tail yields (5).

In the finite model, to identify the first quotient let \(p_0\) be the smallest prime factor of \(q\), \(a_0=1-\ell/d\), and put \(t_d=m b^2\). For a real variable \(u\ge p_0\) and fixed \(x>0\), the corresponding exponent is
\[
F_u(x)=x(1+\log((u-1)t_d/x))-a_0\log u .
\]
Let \(x_0\) be the smaller root at \(p_0\). It satisfies \(x_0<a_0(p_0-1)/p_0\), since at the latter point \(F_{p_0}>0\) for \(t_d>1\): after dividing by \(a_0\), use \(\log p_0\le p_0-1\) and \(\log(t_d/a_0)>0\). Also this point is smaller than \((p_0-1)t_d\), so it lies in the increasing branch. Now \(\partial_u F_u(x_0)=x_0/(u-1)-a_0/u<0\) on \(u\ge p_0\). Consequently the exponent at every larger divisor is strictly negative at the first quotient's root, uniformly when \(\ell/d\) lies in our fixed small compact interval and \(t_d\to t\). Those terms disappear in the first window, proving (4)-(5) for the finite model. For wrapped noise only the full ideal appears in (2).

For clarity, for a real score \(T_A(Y)\) of coordinate degree \(\le D\) with variance at most 1 under \(Q_*\), orthogonal projection and Cauchy-Schwarz yield
\[
 |{\mathbb E}[T_A(Y)\mid A,S_I=w]-{\mathbb E}_{Q_*}T_A|
       \le \sqrt{Z_D^I(A)}.
\]
This holds simultaneously for every \(w\) and every such score, even chosen with unlimited public-design preprocessing. In particular bounded-probability degree-limited decision functions cannot give a nonvanishing advantage below the threshold. For degree-limited acceptance functions \(T_{A,w}\in[0,1]\) of label guesses or lists with \(\sum_w T_{A,w}(y)\le L\) for each response, averaging over uniform \(w\) bounds the reported projection's success by \(L/q^\ell+\sqrt{Z_D^I(A)}\). Unrestricted statistical inference, by contrast, is possible in this wrapped setting: the [fixed odd-modulus broad-sample threshold](https://github.com/mxym/math/blob/18d24b1b111079badad2799860d77be0c27ec244/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-fixed-odd-modulus-threshold.md) has success tending to one at the same \(t>\log q\). The square-root bound does not say that an arbitrary threshold of a low-degree score, or a nonlinear combination of such scores, is itself low coordinate degree. Divergence above (4) is a statement about a likelihood projection, not an efficient test or even a bounded-score attainability guarantee.

The coordinate-degree projection framework is the one used by [Kunisky, Low Coordinate Degree Algorithms I](https://arxiv.org/abs/2403.07862) and [II](https://proceedings.mlr.press/v291/kunisky25a.html); those general frameworks do not supply this typical-public-design ring enumeration. The earlier [fixed-design bounded-independence note](https://github.com/mxym/math/blob/0407833e73454bc7b1b05e969fd5fa911f3d0e9e/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-classical-ac0-lower-bound.md) uses exact independence up to order \(d/\log d\) to fool a different model of Boolean circuits. Here the norm is not identically zero near degree proportional to \(d\); relative concentration of almost-orthogonal weighted tuples and scalar-ideal image sizes make its precise scale possible. No conclusion on general polynomial time, actual parameter choices, or a deployed scheme is made.
