# Necessary rate for retaining the entire centered likelihood field

In a broad-noise ring experiment, a usual posterior query may be much cheaper than retaining every likelihood ratio. We prove a sharp distinction for the latter, stronger task. For a typical public design its centered log-likelihood vector is a near-isometric product of circles. This yields both exact minimal sufficiency and the sharp finite-distortion coding rate, with a strong converse under every fixed label. No claim is made about the data required for finding one label, a particular posterior feature, or a test.

## 1. Setup and main conclusions

Fix \(q\ge3\), not necessarily odd or prime, a dyadic \(d\), \(R=(\mathbb Z/q)[X]/(X^d+1)\), and arbitrary rank \(r\ge1\). Let \(k\) independently uniform public rows \(A_i\in R^r\) give \(N=kd\) scalar coordinates. The following limits take \(d\to\infty\), \(k\ge1\), \(\log k=o(d)\), and \(b\to0\). There is no restriction to a particular relationship between \(b\) and \(d\) in the coding theorem. The ring parameter ranges and model are abstract.

For each \(s\in G=R^r\), conditional on \(A\), the response is \(Y_i=\langle A_i,s\rangle_R/q+E_i\) in the coordinate torus. The noises are independent with wrapped density
\[
 f_b(y)=\sum_{h\in\mathbb Z} b^{h^2} e^{2\pi i h y}.
\]
For \(A\) fixed, let \(\ell_A(y)\) be the real vector \(s\mapsto\log p_s(y\mid A)\) with its mean over the uniform label group \(G\) subtracted; any common reference factor cancels. Give these fields squared norm \(\|H\|_G^2=|G|^{-1}\sum_s |H(s)|^2\). A summary has at most \(M\) distinct messages and a reconstruction \(\widehat\ell(A,m)\) for each message; the reconstruction need not itself be a likelihood vector. We measure distortion by
\[
 \Delta_A(y,m)=\frac{\|\ell_A(y)-\widehat\ell(A,m)\|_G^2}{2b^2N}.   \tag{1}
\]
Both the encoder and decoder may use the public design. No computational budget is imposed on this compression problem.

With probability \(1-e^{-\Omega(d)}\) over the design, the following hold, uniformly for all sufficiently small \(b\):

1. The whole centered field is an injective, continuous function of \(y\) with continuous inverse on its image. Thus an exactly sufficient statistic for the full finite family determines the **entire** observation almost surely; in particular no finite-alphabet statistic and no \(C^1\) statistic with fewer than \(N\) real output coordinates is exactly sufficient. In the discrete version on any uniform grid of \(m\) points divisible by \(q\), exact sufficiency requires at least \(m^N\) different messages, and this count is attained by retaining the response.
2. For every fixed \(D\in(0,1)\), the critical rate for retaining the field to distortion \(D\) is
\[
 \mathcal R(D)=u\sqrt{1-D}-\log I_0(u),
 \qquad \frac{I_1(u)}{I_0(u)}=\sqrt{1-D}.                        \tag{2}
\]
Here \(I_0(u)=\frac1{2\pi}\int e^{u\cos x}dx\) over a period and \(I_1=I_0'\). Rates are in nats per scalar observation. Every fixed rate greater than \(\mathcal R(D)\) suffices with worst-case distortion at most \(D\) for all \(y\). Every fixed strictly smaller rate gives exponentially small success probability \(\Pr_s[\Delta_A(Y,m)\le D\mid A]\), uniformly in the true label and in the choice of code. The same converse holds for any mixture of labels, or the product of uniform circle laws.
3. If \(D_d\to0\), achieving success bounded below by a positive constant requires rate at least \(\frac12\log(1/D_d)-O_q(1)\). Conversely worst-case distortion \(D_d\) is possible with rate \(\frac12\log(1/D_d)+O_q(1)\). Thus in the narrower broad-noise scaling \(b=\beta/d,\ k=\Theta(d^2)\), any prescribed fixed positive error tolerance in the whole field norm, with constant success, requires \(\frac12 N\log_2 d-O(N)\) bits; the same leading bound suffices. These are field-error requirements, not the sample or memory requirements of any individual decision problem.

## 2. Independent frequency lines in a typical ring design

Write \(\langle a,s\rangle_{\rm dot}\) for the ordinary coefficient pairing modulo \(q\). If \(j\in\{0,\ldots,d-1\}\), the \(j\)-th scalar response phase in row \(i\) is \(\langle u_{ij},s\rangle_{\rm dot}/q\), where
\[
 u_{ij}=X^j\overline A_i,\qquad
 \overline A_i=A_i(X^{-1}).
\]
Indeed multiplication by a ring element has coefficient-dot adjoint multiplication by its involution, since multiplying by \(X\) is a signed permutation with transpose multiplication by \(X^{-1}\). For \(u\in G\) identify \(u\) with the character \(\chi_u(s)=e^{2\pi i\langle u,s\rangle_{\rm dot}/q}\).

Except on an event of probability \(O_q(N^2e^{-c_qrd})\), every \(u_{ij}\) has additive order exactly \(q\), and the cyclic frequency sets \(\{a u_{ij}:a\in\mathbb Z/q\}\) for distinct coordinates meet only at zero. Here is a prime-power check that does not assume the ring is a field. For any candidate nontrivial relation
\[
 a u_{ij}=c u_{i'j'},\qquad (a,c)\ne(0,0)\ \text{in }(\mathbb Z/q)^2,
\]
pick \(p^e\Vert q\) at which \(a,c\) are not both zero. Divide out the smaller common \(p\)-power and reduce modulo \(p\), so at least one coefficient is nonzero mod \(p\). If \(i\ne i'\), independence of the rows and invertibility of the nonzero coefficient times a power of \(X\) now gives probability at most \(p^{-rd}\). If \(i=i'\) but \(j\ne j'\), the relation forces each entry of \(\overline A_i\) to lie in the kernel of a polynomial \(\alpha-\delta X^h\) with \(0<|h|<d\), up to an invertible power of \(X\). A sole nonzero coefficient gives zero kernel. Otherwise, for odd \(p\), \(X^d+1\) is squarefree and among its roots at most \(\gcd(h,2d)\le d/2\) satisfy \(X^h=\alpha/\delta\), because its roots lie in the group of \(2d\)-th roots of unity. For \(p=2\), \(X^d+1=(X+1)^d\), while the multiplicity at \(X=1\) in \(X^{|h|}-1\) is \(2^{v_2(h)}\le d/2\). In both cases the gcd with the modulus has degree at most \(d/2\). This degree equals the multiplication-kernel dimension: dividing by the gcd, the remaining factor of the modulus must divide the multiplicand. Thus the probability is at most \(p^{-rd/2}\). Failure of order \(q\) in a single coordinate is an equation \(a u_{ij}=0\) with \(a\ne0\), bounded by the same division argument with one nonzero coefficient. A union bound over coordinates and the finitely many scalars gives the stated event. In what follows fix any design on this event, called separated.

## 3. Geometry and exact data retention

Writing coordinates as \(l=1,\dots,N\), let \(W(y)=(e^{2\pi i y_l})_l\). For a separated design define
\[
 J_A(w)(s)=\sqrt2\sum_{l=1}^N\operatorname{Re}
             \big(w_l\,\overline{\chi_{u_l}(s)}\big).
\]
This is a real-linear isometry from \(\mathbb C^N\) with its Euclidean norm into the real field norm. Distinct first-harmonic lines are orthogonal by §2, and \(\chi_{2u_l}\ne1\) since the character has order \(q\ge3\). Let \(R_A(y)\) denote the centered higher-order remainder. The scalar \(C^1\) expansion \(\log f_b(y)=2b\cos(2\pi y)+O(b^2)\) gives
\[
 \begin{split}
 \ell_A(y)&=\sqrt2\,b\,J_A(W(y))+R_A(y),\\
 \sup_y\|R_A(y)\|_G&\le C b^2\sqrt N,\qquad
 \|R_A(y)-R_A(y')\|_G\le C b^2\|W(y)-W(y')\|_2.                 \tag{3}
 \end{split}
\]
For the last bound, each scalar centered remainder belongs to the nonzero frequencies in its own cyclic set. Its scalar derivative in \(y_l\) is bounded by \(Cb^2\), so the difference bound is \(Cb^2\) times circular distance, and that distance is bounded by a constant times chord distance. Square and sum using orthogonality across coordinates. This is also why the estimate grows as \(\sqrt N\), not \(N\).

Consequently the whole field has a lower Lipschitz bound \((\sqrt2\,b-Cb^2)\|W(y)-W(y')\|_2\), and a matching upper bound with the plus sign. This proves injectivity and continuous inverse for small \(b\). For any sufficient statistic of a finite dominated positive family, the likelihood ratios to a single reference label are measurable functions of the statistic almost surely. To see this directly, a common conditional law of \(Y\) given the statistic shows that the likelihood ratio of two response laws is the ratio of the induced laws of the statistic, composed with that statistic. There are only finitely many labels at each \(d\), so all the ratios, hence their centered logs and \(\ell_A(Y)\), are measurable simultaneously almost surely. The inverse in (3) then recovers \(Y\). Equivalently, preserving the full posterior for a prior of full support forces the same property by Bayes' ratio. This remains an almost-sure conclusion for arbitrary measurable statistics; it does not assert an output-dimension lower bound for arbitrary measurable real-valued encodings.

For a \(C^1\) statistic to fewer than \(N\) real coordinates, consider an open coordinate chart on which its differential has its maximal rank \(<N\). The constant-rank theorem supplies local coordinates with positive-dimensional fibers. Fubini's theorem prevents injectivity on a full-measure set there; the positive response densities are equivalent to volume. This contradicts sufficiency. In the discrete grid version the row translation by \(q^{-1}\) permutes the grid, so response normalization is label-independent and the same centered field restriction is injective on every one of the \(m^N\) outcomes. All atoms have positive mass. This proves the finite counting assertion.

**Binary boundary.** The algebraic separation event of §2 also holds when \(q=2\). The centered scalar likelihood then has just one real character, with coefficient \((\log f_b(y)-\log f_b(y-1/2))/2\). It is an injective function of \(x=\cos(2\pi y)\), not of the full circle coordinate. In fact \(f_b(y)=1+2\sum_{j\ge1}b^{j^2}T_j(x)\), with \(T_j\) the Chebyshev polynomial and \(\sup|T_j'|\le j^2\) on \([-1,1]\). The coefficient is therefore \(2b x+O_{C^1}(b^2)\) and is strictly increasing for small \(b\). Consequently the complete vector of cosines is minimal sufficient, with reflection signs not determined by the likelihood. A grid of \(m\) points with \(m\) even has exactly \((m/2+1)^N\) minimal classes. The product-circle coding theorem here is not claimed for the resulting arcsine coordinate source.

## 4. Sharp product-circle bound

Let \(\mathcal U\) be an independent vector of \(N\) uniform unit-circle points. For any reproduction \(w\in\mathbb C^N\) and every \(0<D<1\),
\[
 \Pr\big[\|\mathcal U-w\|_2^2\le ND\big]\le e^{-N\mathcal R(D)}.   \tag{4}
\]
For completeness, set \(r_0=\sqrt{1-D}\), \(u>0\) by (2), and \(\lambda=u/(2r_0)\). Exponential Markov gives a product of moments with scalar factor \(e^{-\lambda(1+r^2)}I_0(2\lambda r)\) for a reproduction coordinate of radius \(r\). Its maximum over \(r\ge0\) occurs at \(r_0\). Here is an elementary uniqueness check. The Bessel quotient \(m(x)=I_1(x)/I_0(x)\) increases from 0 to 1 because it is the mean cosine under tilt, with derivative its positive variance, and concentration near cosine 1 as \(x\to\infty\). Moreover \(m(x)/x\) strictly decreases: the Bessel equation gives \(m'=1-m/x-m^2\), and the sign of its quotient derivative is the sign of \(H(x)=x(1-m^2)-2m\). The series at zero gives \(H=-x^3/8+O(x^5)\); at any positive zero of \(H\), substituting \(m'=m/x\) gives \(H'=-2m^2<0\), so no first crossing from negative is possible. Thus the derivative of the scalar log-moment is \(2\lambda(m(2\lambda r)-r)\), positive below \(r_0\) and negative above. Evaluating at the maximizing radius including the exponential Markov factor yields exactly (4).

The exponent is sharp as a covering rate even for worst-case input. At any \(0<D'<1\), choose radius \(\sqrt{1-D'}\) for every coordinate of a random codeword with independent uniform angles. For every fixed input on the product circle, the probability the codeword lies within normalized squared distance \(D'\) is
\(\Pr[N^{-1}\sum_i\cos U_i\ge\sqrt{1-D'}]=\exp[-N\mathcal R(D')+o(N)]\).
The lower large-deviation bound follows by tilting the independent angles to any cosine mean just above \(\sqrt{1-D'}\) and then taking the mean down to that value. The upper bound is (4). If \(M=e^{NR+o(N)}\) with \(R>\mathcal R(D')\), the chance to miss one fixed input is doubly exponentially small in \(N\). A product of fixed-resolution circle nets has only \(e^{O(N)}\) points. For every \(D''>D'\), use a net whose normalized root distance to any input is less than \(\sqrt{D''}-\sqrt{D'}\); the union bound gives a deterministic codebook meeting distortion \(D''\) at every input. This proves the covering rate. The function in (2) is the known squared-error rate-distortion function for the uniform planar circle with arbitrary Euclidean reproduction, not for reproduction constrained to have unit radius.

## 5. Transfer to the response field and high precision

For a reconstructed score vector \(v\), project \(v/(\sqrt2 b)\) orthogonally onto the image of \(J_A\), and write \(w\) for its isometric coordinates. By (3), any input with \(\|\ell_A(y)-v\|_G\le\sqrt{2b^2ND}\) satisfies
\[
 N^{-1/2}\|W(y)-w\|_2\le\sqrt D+C b.
\]
The actual response law at any fixed label has density with respect to product Haar at most \(e^{C N b}\), since each shifted scalar \(f_b\le1+C b\). This bound also holds under every mixture of labels. Thus (4) and the union bound for the \(M\) codewords give the one-shot success bound
\[
 \Pr_s[\Delta_A(Y,m)\le D\mid A]\le
 \min\left(1,\exp\{\log M+C N b-N\mathcal R((\sqrt D+Cb)^2)\}\right)             \tag{5}
\]
whenever the argument of \(\mathcal R\) is below 1. The argument is valid for any encoder; independent randomization can be conditioned on. In particular it does not assume the messages are obtained by nearest-neighbor encoding. At a fixed \(D\in(0,1)\) and rate strictly below \(\mathcal R(D)\), continuity and \(b\to0\) give the uniform exponential converse.

Conversely any product-circle codebook at squared distortion \(D''<D\) supplies field centers \(\sqrt2\,b\,J_A(w)\). These meet the target \(D\) for every \(y\) when \(b\) is small by (3). For a rate strictly above \(\mathcal R(D)\), choose \(D'<D''<D\) sufficiently close to \(D\) to use the proof of §4. This establishes the sharp fixed-distortion threshold, not only expected distortion.

For \(D_d\to0\) the additive perturbation in (5) need not be small compared with \(\sqrt{D_d}\). Instead, if the successful input set for one reconstruction is nonempty, choose any representative input \(y_0\) in it. By the lower bi-Lipschitz bound of (3), all other inputs in that set obey
\[
 N^{-1/2}\|W(y)-W(y_0)\|_2
   \le \frac{2\sqrt{D_d}}{1-Cb}.
\]
Apply (4) with \(4D_d/(1-Cb)^2\) to each such set. As \(D\downarrow0\), \(\mathcal R(D)=\frac12\log(1/D)+O(1)\): for example the standard large-\(u\) asymptotics \(I_0\asymp e^u/\sqrt u\), \(m(u)=1-1/(2u)+O(u^{-2})\) in (2) yield it. Thus constant success requires rate \(\frac12\log(1/D_d)-O(1)\) even for arbitrarily small distortion. Product angular quantization with \(O(D_d^{-1/2})\) levels per coordinate, and representing each quantized observation by its own field, gives the matching worst-case upper bound by the upper metric inequality in (3). This is an existence result about field representations, not an efficient routine for evaluating all labeled likelihoods.

An equivalent requirement is to retain pairwise posterior log odds for arbitrary binary priors. For a fair prior on \(s,s'\), those log odds are \(\ell_A(y)(s)-\ell_A(y)(s')\). A single summary usable for all such pairs, with average squared error over a uniformly chosen ordered pair, has the same optimal distortion after the factor 2: the map \(H\mapsto(H(s)-H(s'))_{s,s'}\) on centered fields has squared norm \(2\|H\|_G^2\). Even if the reported log odds are inconsistent, orthogonally projecting the entire table onto the image of this map can only lower its error against the true table. This observation does not concern one pair fixed in advance or an average error in the posterior probabilities rather than their log odds.

## 6. Prior and boundary

[Dytso–Cardone, Uniform Distribution on the Sphere: Rate-Distortion under Squared Error Distortion](https://arxiv.org/abs/2401.04248), Theorem 1 with ambient dimension 2 and radius 1, gives exactly the scalar rate in (2). The direct bound (4) explains the strong and worst-case versions used here without treating the phases as a Gaussian source. The old finite-family sufficiency criterion is standard. The new transfer is the generic separation of all cyclic coordinate frequency sets over every fixed prime or composite modulus \(q\ge3\), the resulting bi-Lipschitz product geometry of the entire centered likelihood field, and the coding/sufficiency consequences conditional on a typical public design. [The earlier posterior-surprisal result](https://github.com/mxym/math/blob/15a25c0d1d01551372cfb03794958adc753ca3b6/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-posterior-surprisal-coarsenings.md) instead concerns statistical performance of particular label features and does not imply these all-field requirements.

Small summaries can still retain an individual decision or suitably defined approximate posterior property. No implication for efficient search, standard parameter families, or any particular cryptographic system is drawn.
