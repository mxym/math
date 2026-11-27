# Bounded-eccentricity Arakelov theta extremality in the dyadic tower

Let \(d\) tend through powers of two, \(\zeta=\zeta_{2d}\), \(K_d=\mathbb Q(\zeta)\), and \(\mathcal O_d=\mathbb Z[\zeta]\). Index its \(d\) embeddings by the odd residues \(j\bmod 2d\). For weights \(w_j>0\), require \(w_j=w_{-j}\) and \(\prod_j w_j=1\). Put
\[
 E_w(x)=d^{-1}\sum_{j\ {\rm odd}} w_j|\sigma_j(x)|^2,\qquad
 \Theta_d(t,w)=\sum_{x\in\mathcal O_d}e^{-t E_w(x)}.
\]
The \(d^{-1}\) is just a normalization: \(E_{\bf1}(\sum_{\ell<d}x_\ell\zeta^\ell)=\sum_\ell x_\ell^2\), because the dyadic power basis is orthonormal for \(d^{-1}\operatorname{Tr}(x\bar y)\).

**Theorem.** Fix \(0<a\leq1\leq b<\infty\). There are constants \(C,d_0\), depending only on \(a,b\), such that for all dyadic \(d\geq d_0\), all \(t\geq C\log d\), and every admissible \(a\leq w_j\leq b\),
\[
 \Theta_d(t,w)\leq\Theta_d(t,{\bf1}). \tag{1}
\]
Equality holds exactly if there is a unit \(x\in\mathcal O_d^\times\) such that \(w_j=|\sigma_j(x)|^{-2}\) for all \(j\). We do not give effective \(C,d_0\).

In particular, at \(t=\pi d\), (1) proves the exact unique maximizing **class** on the part of the principal component of \(\operatorname{Pic}^0(K_d)\) admitting a representative in a fixed archimedean weight band. It is a restricted case of the van der Geer–Schoof size-function question, not a proof on the whole principal component or on nonprincipal ideal classes. Multiplying by a unit can preserve the theta while making a representative nonspherical; hence a uniqueness statement for the weight vector itself would be false.

The proof gives a separate rigidity statement for near-minimal elements. For each fixed band there are \(\delta>0\), a fixed field in the dyadic tower, and \(d_1\) so that if \(d\geq d_1\) and \(0\ne x\in\mathcal O_d\) has \(E_w(x)\leq1+\delta\), then \(x\) is a root of unity times a unit from that fixed subfield. In particular nonunits have a uniform positive energy gap above 1 in this band. No class-group hypothesis is used.

**Prior scope.** [Van der Geer–Schoof, §5](https://arxiv.org/pdf/math/9802121) pose the degree-zero maximization over the entire Arakelov class group of a Galois field. [Tran–Tian–Feaver, Theorem 1.1](https://www.numdam.org/item/10.5802/jtnb.1266.pdf) prove the full result for imaginary cyclic sextic fields, and review the earlier rank-zero, rank-one and cyclic cubic cases. [Peikert–Regev–Stephens-Davidowitz, Lemma 6.9](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf) use the norm/AM–GM lower bound to give a product-width smoothing estimate for fractional ideals. It does not identify these maximizing shapes or a uniform separation of nonunits. The additional ingredient here is finite-dimensional compactness of the odd conjugate orbit of a uniformly sparse integer polynomial and the multivariate Kronecker theorem. We make no exhaustive priority claim. This is a theta-function comparison for abstract ideal lattices, not a claim on the hardness reduction or any implementation.

## 1. Rigidity of nearly minimal sparse elements

For nonzero \(x\) the field norm is a nonzero integer, so weighted AM–GM gives
\[
 E_w(x)\geq\left(\prod_j w_j|\sigma_j(x)|^2\right)^{1/d}
           =|N_{K_d/\mathbb Q}(x)|^{2/d}\geq1. \tag{2}
\]
An individual nonunit of norm 2 is only separated from this floor by \(O(d^{-1})\) in that bound. We prove a band-dependent gap by excluding approximate equality.

Suppose a sequence \(d\to\infty\) satisfies \(E_w(x)\to1\). Its power-basis coefficient vector has uniformly bounded squared norm, since \(a\sum x_\ell^2\leq E_w(x)\). Pass to a subsequence with
\[
 x=\sum_{h=1}^r b_h \zeta^{e_{h,d}},\quad 0\leq e_{h,d}<d,
\]
where \(r\) and the nonzero integers \(b_h\) are fixed, and the exponents in any row are distinct. Set \(F(X)=\sum_h b_h X_h\) on the circle torus \(\mathbb T^r\). For \(T_j=w_j|\sigma_j(x)|^2\), one has \(0<T_j\leq b(\sum|b_h|)^2\) and
\[
 0\leq d^{-1}\sum_j\log T_j=(2/d)\log|N(x)|
      \leq\log E_w(x)\longrightarrow0.
\]
It follows that \(d^{-1}\sum_j(T_j-1-\log T_j)\to0\). On any fixed bounded positive interval \(T-1-\log T\geq c(T-1)^2\) for a positive constant (use the lower bound for the second derivative on the segment from 1 to \(T\)). Thus
\[
 d^{-1}\sum_j|T_j-1|\longrightarrow0. \tag{3}
\]

Write \(\tau_d=(\zeta^{e_{1,d}},\dots,\zeta^{e_{r,d}})\), and place probability \(1/d\) at each odd power \(\tau_d^j\), counting multiplicity. For \(k\in\mathbb Z^r\) the Fourier moment at the character \(X^k\) is
\[
 \begin{cases}
 0,&\sum_h k_h e_{h,d}\not\equiv0\bmod d,\\
 \zeta^{\sum_h k_h e_{h,d}}\in\{1,-1\},&\sum_h k_h e_{h,d}\equiv0\bmod d .
 \end{cases}
\]
Pass to a diagonal subsequence on which each moment is eventually constant. The indices with a nonzero eventual moment form a subgroup \(R\leq\mathbb Z^r\); their values define a character \(s:R\to\{1,-1\}\) by addition of the corresponding congruences. The support of every sufficiently late measure is in the fixed nonempty coset
\[
 \mathcal C=\{X\in\mathbb T^r:X^k=s(k)\text{ for all } k\in R\}.
\]
Indeed a finite set of generators of \(R\) satisfies its moment equations eventually, and a moment of modulus 1 forces that value at every atom. The limiting measure is uniform Haar on this coset: its moments are \(s(k)\) for \(k\in R\) and zero otherwise, as follows either by orthogonality or by Smith normal form of \(R\). Uniqueness and weak convergence then follow from density of trigonometric polynomials on the compact torus.

Every nonempty relative open subset of \(\mathcal C\) has positive Haar measure. By (3) and \(w_j\leq b\), \(|F|^2\geq1/b\) everywhere on \(\mathcal C\): otherwise some open set has \(|F|^2<(1-\varepsilon)/b\), giving \(T_j<1-\varepsilon\) on a positive limiting fraction. Consequently the function \(\log|F|\) on the coset is continuous, including across its disjoint finite components. The preceding norm limit and eventual support give
\[
 \int_{\mathcal C}\log|F|\,d{\rm Haar}
     =\lim_d d^{-1}\log |N(x)|=0. \tag{4}
\]
In particular, this argument does not replace the average of an unbounded logarithm by its weak limit at points of possible zeros; the weighted near-minimality is used to exclude such zeros on the whole fixed coset first.

## 2. Finite components and a Laurent norm polynomial

By Smith normal form, after a fixed unimodular monomial change of variables the coset has the form
\[
 \{z_1^{m_1}=\epsilon_1,\ldots,z_s^{m_s}=\epsilon_s\}
          \times\mathbb T^{r-s},\qquad \epsilon_i\in\{1,-1\}.
\]
Denote its finite coordinate set by \(\mathcal F\). The finite projection of the transformed \(\tau_d\) belongs to \(\mathcal F\); after a further subsequence it is a fixed tuple \(\omega\). Every coordinate of \(\omega\) is a root of unity of power-of-two order since it occurs in the original dyadic orbit. The finite projections of \(\tau_d^j\) are \(\omega^j\) for odd \(j\); for large \(d\) they cover all of \(\mathcal F\), since otherwise the weak limit would miss one of the components of positive Haar measure. Thus \(\mathcal F\) is exactly the orbit of the tuple \(\omega\) under the Galois group of \(B=\mathbb Q(\omega_1,\ldots,\omega_s)\); this is a fixed dyadic cyclotomic subfield, since any coordinate of maximal order generates it. Its tuples are counted once each among its embeddings. This also covers \(s=0\), with \(\mathcal F\) a singleton and \(B=\mathbb Q\).

After the monomial change the polynomial \(F\) has integer Laurent coefficients, still denoted by \(F\). Evaluate its finite coordinates at \(\omega\) and take the Laurent norm
\[
 P(Z)=\prod_{\omega'\in\mathcal F} F(\omega',Z)
             \ \in\ \mathbb Z[Z_1^{\pm1},\ldots,Z_{r-s}^{\pm1}]. \tag{5}
\]
Its coefficients are integral because the conjugate coefficients are algebraic integers and the product is Galois invariant. It has no torus zeros by (3) and the coset support argument, and its logarithmic Mahler measure is zero by (4) and the product Haar measure in these coordinates. The [Boyd–Smyth multivariate Kronecker theorem, e.g. Smyth Corollary 1](https://doi.org/10.4153/CMB-1981-068-8) says an integer Laurent polynomial of zero logarithmic measure is a signed monomial times cyclotomic polynomials evaluated on monomials. Every nonconstant such cyclotomic factor has a zero on the complex unit torus, since the monomial map with nonzero exponent is onto the circle. Hence \(P\) is a signed monomial, including the constant \(\pm1\) case.

Each factor in (5) must therefore be a unit in the complex Laurent polynomial ring, which means \(F(\omega',Z)=c_{\omega'}Z^{v_{\omega'}}\). One elementary verification of the latter fact chooses a real linear functional separating all exponent vectors of each candidate factor: the difference of the largest and smallest values on the support adds under multiplication by uniqueness of leading and trailing terms, and is zero for a monomial. The coefficients \(c_{\omega'}\) are Galois conjugates of an algebraic integer \(c_\omega\in B\), and \(|N_{B/\mathbb Q}(c_\omega)|=1\), by taking the coefficient in the product (5). Evaluation at the finite component \(\omega\) and free coordinates of the transformed \(\tau_d\) now gives
\[
 x=c_\omega\cdot\text{a power of }\zeta
\]
for all sufficiently late members of the subsequence. Thus \(x\) is a unit on this subsequence, and its embedding moduli are bounded above and away from zero by the finite positive list \(|c_{\omega'}|\).

This proves the uniform near-minimum statement by contradiction: if it failed, for each integer \(h\) take \(d\geq2^h\) with \(E_w(x)\leq1+1/h\) but \(x\) not a root of unity times a unit from \(\mathbb Q(\zeta_{2^{h+1}})\). The analysis just given yields such a representation in a fixed dyadic subfield on a subsequence, which is contained in \(\mathbb Q(\zeta_{2^{h+1}})\) eventually. Its units remain units in the larger field, a contradiction. For our use below, the preceding sequence argument also supplies a positive lower bound on the conjugate moduli of the selected near-minimal elements along its subsequence.

The fixed band cannot simply be omitted from this energy gap. The nonunit \(x=1-\zeta\) has norm 2, and the conjugation-invariant weights \(w_j=2^{2/d}/|1-\zeta^j|^2\) have product one and energy \(E_w(x)=2^{2/d}\to1\), while their largest value grows on the order of \(d^2\). This is a barrier for the proof, not a counterexample to the original size-function conjecture.

## 3. From a competing theta value to one near-minimal unit

By a diagonal contradiction, it suffices to rule out sequences with \(d\to\infty\), \(t/\log d\to\infty\), and \(\Theta_d(t,w)\geq\Theta_d(t,{\bf1})\) for weights that are *not* equivalent to the spherical ones by any unit. Indeed failure of the existence of \(C,d_0\) allows \(d\geq2^h\), \(t\geq h\log d\) at each \(h\).

Let \(Q\) be the real symmetric form in the coefficient basis, with normalization \(E_w(x)=x^{\mathsf T}Qx\). The unitary Fourier basis at the odd roots diagonalizes \(Q\) with eigenvalues \(w_j\in[a,b]\). All its diagonal entries are \(d^{-1}\sum_j w_j\). For any fixed integer \(R\), the number of coefficient vectors of squared Euclidean norm at most \(R\) is \(O_R(d^R)\): there are at most \(R\) nonzero coordinates and each magnitude is at most \(\sqrt R\). For the remainder,
\[
 \sum_{\|x\|^2>R} e^{-ta\|x\|^2}
   \leq e^{-taR/2}\,\vartheta(ta/2)^d,\qquad
 \vartheta(u)=\sum_{k\in\mathbb Z}e^{-uk^2}. \tag{6}
\]
Here \(\vartheta(c t)^d=1+o(1)\) for any fixed \(c>0\), since \(\vartheta(u)=1+O(e^{-u})\) as \(u\to\infty\) and \(t/\log d\to\infty\).

If the minimum nonzero \(E_w(x)\) were \(\geq1+\varepsilon\) on a subsequence for fixed \(\varepsilon>0\), the finite-norm bound and (6), with \(aR/2>1+\varepsilon\), would give \(\Theta_d(t,w)-1=o(d e^{-t})\). But the spherical comparison has \(2d\) vectors of energy 1, so this contradicts the competing theta. Together with (2), the minimum must tend to 1. Choose a shortest nonzero element, and pass to the subsequence in §§1–2 so that it is a unit \(x\) with conjugate moduli uniformly bounded above and below.

Multiplication by \(x\) is an integral lattice automorphism and leaves the theta unchanged after replacing \(w_j\) by \(T_j=w_j|\sigma_j(x)|^2\). Write \(Q'\) for the new form. Its eigenvalues are \(T_j\), their product is 1, their average is \(\mu=E_w(x)\to1\), and they lie in a fixed positive band. Every diagonal entry of \(Q'\) is \(\mu\) and each matrix entry of \(Q'-I\) has modulus at most \(d^{-1}\sum_j|T_j-1|=o(1)\), by the normalized Fourier matrix and (3). Consequently, for each fixed \(R\) and all \(2\leq\|y\|^2\leq R\),
\[
 E_{w'}(y)=y^{\mathsf T}Q'y\geq \|y\|^2-o(1).
\]
For this use \(\|y\|_1^2\leq R^2\) (the support size and squared norm are each at most \(R\)). For the remaining \(y\), apply (6) with the new fixed eigenvalue lower bound and choose \(R\) large enough. Therefore for a constant \(\gamma>0\) along the subsequence,
\[
 \Theta_d(t,w')=1+2d e^{-t\mu}+O(e^{-(1+\gamma)t}).
 \tag{7}
\]
For example the bounded vector part has energy \(\geq 7/4\) eventually and count \(O_R(d^R)\), so any \(\gamma<3/4\) works after choosing \(R\) for the tail. The assumption of a competing theta and \(\mu\geq1\) yield \(1-e^{-t(\mu-1)}=O(d^{-1}e^{-\gamma t})\). Hence \(t(\mu-1)\to0\) exponentially in \(t\). The eigenvalues are uniformly bounded, and the same strong convexity bound as in (3) gives
\[
 \sum_j(T_j-1)^2\leq C_1\sum_j(T_j-1-\log T_j)=C_1d(\mu-1).
\]
So \(\|Q'-I\|_{\rm op}\to0\). This is much stronger than the entrywise control prior to (7).

## 4. Strict local comparison completes the proof

Write \(H=\log Q'\), a real symmetric matrix with \(\operatorname{tr}H=0\). On the subsequence \(\|H\|_{\rm op}\leq1/10\) eventually. The path \(Q_\lambda=e^{\lambda H}\), \(0\leq\lambda\leq1\), is diagonalized by the same unitary Fourier matrix, so its diagonal entries are constant, \(d^{-1}\operatorname{tr}Q_\lambda\). For \(x\) in the ordinary squared-norm-one shell the exact loss between \(\lambda=0,1\) is \(2d e^{-t}(1-e^{-t(\mu-1)})\). From \(e^h\geq1+h+c h^2\) on \(|h|\leq1/10\), \(\mu-1\geq c\|H\|_F^2/d\). Since \(t(\mu-1)\to0\), the loss is at least \(c' t e^{-t}\|H\|_F^2\) eventually.

For the tail \(T(\lambda)=\sum_{\|y\|^2\geq2}e^{-t y^{\mathsf T}Q_\lambda y}\), its first derivative at zero vanishes. Indeed \(\sum_{\|y\|^2\geq2}yy^{\mathsf T}e^{-t\|y\|^2}\) is a scalar matrix by signed coordinate permutations, and pairs against the trace-zero \(H\). The differentiations are justified by convergent Gaussian majorants uniformly along the compact path. There is a constant \(B_1\) such that
\[
 |T''(\lambda)|\leq
 B_1 t^2\|H\|_F^2
 \sum_{\|y\|^2\geq2}\|y\|^4
 e^{-t e^{-1/10}\|y\|^2}
 \ \leq\ B_2 t^2\|H\|_F^2 e^{-1.4t}.
\]
For the last bound absorb the polynomial into \(e^{t\|y\|^2/10}\) with a fixed constant for \(t\geq1\), factor out \(e^{-2t(e^{-1/10}-1/5)}\), and sum the remaining Gaussian with precision \(t/10\) using (6). Here \(2(e^{-1/10}-1/5)>1.4\). Thus the possible tail change is \(o(t e^{-t})\|H\|_F^2\). If \(H\ne0\) the first-shell loss strictly dominates it, contradicting a competing theta value. If \(H=0\), the weights after multiplication by the unit are all one, also excluded by the choice of sequence. This proves (1) in its uniform quantifiers. The converse equality when a unit removes the weights follows by the same integral change of variables.

## Reproduction

Run `python3 verify-dyadic-arakelov-bounded.py` with Python and its standard library. It checks exact finite examples of the odd-power Fourier and coset calculations, the algebraic norm of fixed-subfield units and nonunits through increasing dyadic degrees, and the Fourier Gram and quadratic expansions on small forms. The checker illustrates identities and is not evidence for a particular numerical value of \(C\) or \(d_0\).
