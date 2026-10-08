# Sharp logarithmic growth of permanental cofactor spectra

Text rendering of sharp_cofactor_extrema.tex. The TeX and PDF are the typeset reference.

# Definitions, statements, and attribution

All Hermitian inner products are linear in their first argument. The minor $A(i\mid j)$ is not transposed. For a PSD matrix with $\mathop{\mathrm{per}}A>0$, put $$C(A)_{ij}=a_{ij}\mathop{\mathrm{per}}A(i\mid j).$$ The real part of a matrix is entrywise. Thus $\lambda_{\max}(\mathop{\mathrm{Re}}C(A))$ is the maximum of $w^*C(A)w$ over real unit vectors, even when $A$ has non-real entries. It is not a supremum restricted to real matrices.

Let $R_N,R_N^{\mathbb R}$ be the suprema of the two normalized eigenvalues over all complex Hermitian PSD matrices of order $N$ with positive permanent. Let $R_N^{(2)},R_N^{(2,\mathbb R)}$ restrict these suprema to rank-exactly-two correlation matrices, for $N\ge2$.


**Theorem 1**. *As $N\to\infty$, $$\frac{R_N}{\log N}\longrightarrow1,\qquad
 \frac{R_N^{\mathbb R}}{\log N}\longrightarrow\frac12,\qquad
 \frac{R_N^{(2)}}{\log N}\longrightarrow1,\qquad
 \frac{R_N^{(2,\mathbb R)}}{\log N}\longrightarrow\frac12.$$ The first two limits are unchanged if the suprema are restricted to positive-definite correlation matrices.*



Drury’s order-eight example already disproved the cofactor eigenvalue conjecture with constant one ; that disproof is not new here. The first-compound indicator inequality used for our upper bound is a classical refinement of Lieb’s inequality, appearing in Pate’s work . We supply its full contraction proof. The connection of cofactor directions with local Hadamard perturbations is also established in the literature . Our assertions concern dimension-dependent extrema and the sharp ramp constant. A separate source audit records the finite search and access limitations; no exhaustive priority claim is made. In particular no unchecked all-$k$ reading of the abstract of is used.

# The first-compound indicator inequality and the upper bounds

For homogeneous polynomials use the Bargmann–Fock inner product $$\left\langle\sum_\alpha p_\alpha x^\alpha,
 \sum_\alpha q_\alpha x^\alpha\right\rangle_B
 =\sum_\alpha\alpha!p_\alpha\overline{q_\alpha}.$$ If $A$ is the Gram matrix of rows $v_i$ and $\ell_i$ their linear forms, the pairing expansion gives $$\label{eq:fock}
 \mathop{\mathrm{per}}A=\left\|\prod_i\ell_i\right\|_B^2,
 \qquad C(A)=\operatorname{Gram}
 \left(v_i\otimes\prod_{j\ne i}\ell_j\right)_{i=1}^N.$$ Thus $C(A)\succeq0$. The Laplace expansion gives $C(A)\mathbf 1=(\mathop{\mathrm{per}}A)\mathbf 1$. These statements also follow for singular matrices directly from their Gram factorizations.


**Lemma 2**. *For every subset $S\subseteq\{1,\ldots,N\}$, $$\mathbf 1_S^*C(A)\mathbf 1_S\le |S|\mathop{\mathrm{per}}A.$$*




*Proof.* Write $a=|S|$, $b=N-a$. The empty and full subsets are immediate. Relabel so $S=\{1,\ldots,a\}$. Let $u$ and $v$ be the symmetrizations of the two row tensors, of degrees $a$ and $b$, respectively, with symmetrization defined by averaging over permutations. Classify a permutation by the number $j$ of indices mapped from $S$ to $S^c$. The permutations in this class form a double coset of $S_a\times S_b$ with cardinality $$a!b!\binom aj\binom bj.$$ Indeed choose the $j$ cross rows and columns in each block, match the cross sets, and match the two remaining sets; the count simplifies to the displayed number. Averaging the original tensor on both sides over $S_a\times S_b$ replaces it by $u\otimes v$. For the representative swapping the first $j$ coordinates of the two blocks, summing those coordinates shows that its matrix coefficient at $u\otimes v$ is $\|u\mathbin{\operatorname{contr}_j}\overline v\|^2\ge0$. Here the contraction pairs $j$ coordinates and leaves the other coordinates in the tensor product of the underlying space and its conjugate. In coordinates it is the squared norm of the array obtained by summing the products of $j$ matching entries of $u$ and $\overline v$; this is the usual two-block symmetric-tensor contraction. Consequently the sum of Gram products in this class is $$t_j=a!b!\binom aj\binom bj
       \|u\mathbin{\operatorname{contr}_j}\overline v\|^2\ge0,
 \qquad \mathop{\mathrm{per}}A=\sum_jt_j.$$ Expanding $\sum_{i,l\in S}a_{il}\mathop{\mathrm{per}}A(i\mid l)$ counts a permutation once for each $i\in S$ with its image also in $S$. There are exactly $a-j$ such indices in the $j$th class. Hence the sum equals $\sum_j(a-j)t_j\le a\sum_jt_j$. ◻




**Lemma 3**. *If a $d$ by $d$ PSD Hermitian matrix $M$ satisfies $b^*Mb\le\|b\|^2$ for all binary $b$, then, with $S_d=\sum_{j=1}^d(\sqrt j-\sqrt{j-1})^2$, $$\lambda_{\max}(M)\le4S_d\le4+H_{d-1},\qquad
 \lambda_{\max}(\mathop{\mathrm{Re}}M)\le2S_d\le2+\tfrac12H_{d-1}.$$ Here $H_0=0$.*




*Proof.* Sort a nonnegative vector $x$ so $x_1\ge\cdots\ge x_d\ge0$, and set $x_{d+1}=0$. In the seminorm $\|M^{1/2}\cdot\|$, the nested-indicator expansion and summation by parts give $$\|M^{1/2}x\|
 \le\sum_j(x_j-x_{j+1})\sqrt j
 =\sum_jx_j(\sqrt j-\sqrt{j-1})
 \le\sqrt{S_d}\|x\|.$$ Splitting a real vector into its positive and negative parts bounds its seminorm by $\sqrt{2S_d}$ times its norm. Splitting a complex vector into the four positive and negative real and imaginary parts gives $2\sqrt{S_d}$. These are the two spectral bounds. For $j\ge2$, $(\sqrt j-\sqrt{j-1})^2\le1/(4(j-1))$, giving the harmonic estimates. ◻



Applying the lemmas to $C(A)/\mathop{\mathrm{per}}A$ proves $$\label{eq:upper}
 R_N\le4+H_{N-1},\qquad R_N^{\mathbb R}\le2+\tfrac12H_{N-1}.$$

# A finite ring construction attaining the leading constants


**Lemma 4**. *For $b>1$ put $E(b)=b^{b/(b-1)}/(b-1)$. If positive numbers $d_1>\cdots>d_s$ satisfy $d_i/d_{i+1}\ge b$ and have sum $j$, then $$\frac{j^j}{\prod_i d_i^{d_i}}\le E(b)^j.$$*




*Proof.* Index $p_i=d_i/j$ starting at zero. The first $k$ terms sum to at least $p_{k-1}(b^k-1)/(b-1)$, whereas the remaining tail is at most $p_{k-1}/(b-1)$. Thus $\sum_{i\ge k}p_i\le b^{-k}$, and $\sum_i i p_i\le1/(b-1)$. Nonnegativity of relative entropy with respect to $g_i=(1-1/b)b^{-i}$ gives $$-\sum_i p_i\log p_i
 \le-\log(1-1/b)+(\log b)/(b-1)=\log E(b).$$ Multiplication by $j$ and exponentiation finish the proof. Zero probabilities past the finite support cause no problem in the relative entropy inequality. ◻



Fix $b>1$, $0<\delta<1$, and $\eta>0$. Choose a positive real number $$C>\frac{E(b)}{e(1-\delta)},\qquad
 \theta=\frac{E(b)}{Ce(1-\delta)}<1,\qquad q=\theta^2.$$ Choose an integer $d_0\ge2$ so large that $$\label{eq:d0}
 2e\exp\!\left(\frac{q^{d_0}}{1-q}\right)q^{d_0}
 \left(\frac{d_0}{1-q}+\frac{q}{(1-q)^2}\right)\le\eta.$$ Set $d_{k+1}=\lceil bd_k\rceil$. For each sufficiently large integer $N$, let $K$ be maximal with $D'=\sum_{k=0}^{K-1}d_k\le\delta N/2$. For each $k$ take the full ring of $2d_k$ numbers $z$ determined by $$\label{eq:ring}
 \prod_{z\text{ in ring }k}(x+zy)
 =x^{2d_k}+\epsilon_k\left(\frac{N}{2Cd_k}\right)^{d_k}y^{2d_k},
 \qquad \epsilon_k\in\{-1,1\}.$$ Their squared moduli are $N/(2Cd_k)$. Add $N-2D'$ zero slopes. Normalize every row $(1,z_i)$ to unit length. The matrix $A$ is a rank-two correlation matrix: a reserve row exists and every ring has a nonzero slope. As each ring has at least four points, $$\label{eq:slopes}
 \sum_i z_i=\sum_i z_i^2=0,
 \qquad \sum_i|z_i|^2=\frac{NK}{C},
 \qquad \sum_i(\mathop{\mathrm{Im}}z_i)^2=\frac{NK}{2C}.$$

Let $\gamma>0$ be the product of the first row coordinates. Write their product polynomial as $$P/\gamma=\sum_{j=0}^{D'}c_jx^{N-2j}y^{2j},\qquad
 R=\frac{\mathop{\mathrm{per}}A}{N!\gamma^2}
   =\sum_{j=0}^{D'}\frac{|c_j|^2}{\binom N{2j}}\ge1.$$ Choose the signs in <a href="#eq:ring" data-reference-type="eqref" data-reference="eq:ring">[eq:ring]</a> independently and uniformly. For a subset $S$ of ring indices, put $j(S)=\sum_{k\in S}d_k$. Its coefficient contribution has magnitude $$a_S=\left(\frac{N}{2C}\right)^{j(S)}
           \prod_{k\in S}d_k^{-d_k}.$$ Distinct subsets have orthogonal sign products, including when their degree sums coincide. Hence $$\label{eq:randomnorm}
 \mathbb ER=1+\sum_{S\ne\varnothing}
          \frac{a_S^2}{\binom N{2j(S)}}.$$ By Lemma <a href="#lem:entropy" data-reference-type="ref" data-reference="lem:entropy">4</a>, $a_S\le[NE(b)/(2Cj)]^j$ for $j=j(S)$. The elementary integral comparison $\sum_{r=1}^h\log r\le\int_1^h\log t\,dt+\log h$ gives $h!\le eh(h/e)^h$. For $2j\le\delta N$ it follows that $$\binom N{2j}\ge\frac{[e(N-2j)/(2j)]^{2j}}{2ej}
 \ge\frac{[e(1-\delta)N/(2j)]^{2j}}{2ej}.$$ Every summand in <a href="#eq:randomnorm" data-reference-type="eqref" data-reference="eq:randomnorm">[eq:randomnorm]</a> is therefore at most $2ejq^j$. The subset generating function $Z(q)=\prod_k(1+q^{d_k})$ yields $$\sum_Sj(S)q^{j(S)}
 =Z(q)\sum_k\frac{d_kq^{d_k}}{1+q^{d_k}}
 \le\exp\!\left(\sum_kq^{d_k}\right)\sum_kd_kq^{d_k}.$$ The $d_k$ are distinct integers at least $d_0$, so bounding these sums by the complete integer tails and using <a href="#eq:d0" data-reference-type="eqref" data-reference="eq:d0">[eq:d0]</a> proves $\mathbb ER\le1+\eta$. At least one of the finitely many sign choices consequently satisfies $$\label{eq:Rsmall}
 R\le1+\eta.$$ This is finite averaging, not an assertion about almost-sure limits.

For any complex vector $w$, define $$G_w=\sum_i\overline{w_i}v_i\otimes\prod_{j\ne i}\ell_j.$$ By <a href="#eq:fock" data-reference-type="eqref" data-reference="eq:fock">[eq:fock]</a>, $\|G_w\|^2=w^*C(A)w$. The coefficient of $x^{N-1}$ in its second vector component is $\gamma\sum_i\overline{w_i}z_i$. Keeping only this squared coefficient proves $$\label{eq:marked}
 w^*C(A)w\ge(N-1)!\gamma^2
                  \left|\sum_i\overline{w_i}z_i\right|^2.$$ Use $w=z$ for the complex test. For the real test use $w_i=\mathop{\mathrm{Im}}z_i$; <a href="#eq:slopes" data-reference-type="eqref" data-reference="eq:slopes">[eq:slopes]</a> gives $\sum_iw_iz_i=i\|w\|^2$. Equations <a href="#eq:Rsmall" data-reference-type="eqref" data-reference="eq:Rsmall">[eq:Rsmall]</a>–<a href="#eq:marked" data-reference-type="eqref" data-reference="eq:marked">[eq:marked]</a> give $$\frac{\lambda_{\max}(C(A))}{\mathop{\mathrm{per}}A}\ge\frac{K}{C(1+\eta)},\qquad
 \frac{\lambda_{\max}(\mathop{\mathrm{Re}}C(A))}{\mathop{\mathrm{per}}A}\ge\frac{K}{2C(1+\eta)}.$$ The recurrence implies $d_0b^k\le d_k\le(d_0+1/(b-1))b^k$, and maximality of $K$ therefore gives $K=\log N/\log b+O(1)$, with all parameters fixed. The lower limits are at least $1/[C(1+\eta)\log b]$ and half this. Let $C$ approach its allowed lower endpoint, then let $\delta,\eta\downarrow0$ and $b\downarrow1$. Since $E(b)\log b\to e$, they approach $1$ and $1/2$, matching <a href="#eq:upper" data-reference-type="eqref" data-reference="eq:upper">[eq:upper]</a>. This proves the four limits in Theorem <a href="#thm:main" data-reference-type="ref" data-reference="thm:main">1</a>. For each desired accuracy, parameters are fixed first and only then is $N$ taken to infinity; the lower construction works for every sufficiently large $N$.

Positive diagonal congruence multiplies $C(A)$ and $\mathop{\mathrm{per}}A$ by the same positive scalar. Thus correlation normalization loses no generality when $\mathop{\mathrm{per}}A>0$. Finally $(A+\varepsilon I)/(1+\varepsilon)$ is positive-definite and correlation whenever $A$ is correlation and $\varepsilon>0$. Continuity at each finite $N$ retains any strictly smaller Rayleigh bound. The positive-definite assertion does not retain rank two for $N>2$.

# An explicit dyadic family and exact certificates

Fix $K\ge1$, let $M=2^K$, $n=2M$, and $c>4$. For $k=0,\ldots,K-1$, put $d_k=2^k$, $r_k^2=(M-1)/(cd_k)$, and take the slopes $$z_{k,j}=r_k\exp\left(\frac{(2j+1)\pi i}{2d_k}\right),
 \quad0\le j<2d_k,$$ together with two zero slopes. Normalize the corresponding rows $(1,z)$. Their product is $$P=\gamma x^2\prod_k(x^{2d_k}+r_k^{2d_k}y^{2d_k})
  =\gamma\sum_{j=0}^{M-1}c_jx^{n-2j}y^{2j}.$$ Binary expansion is unique. Lemma <a href="#lem:entropy" data-reference-type="ref" data-reference="lem:entropy">4</a> with $b=2$, for which $E(2)=4$, gives $$c_j\le(4/c)^j\binom{M-1}{j},\qquad
 1\le R=\sum_j\frac{c_j^2}{\binom{2M}{2j}}
     <\frac{c^2}{c^2-16}.$$ The last bound uses Vandermonde’s inequality $\binom{2M}{2j}\ge\binom Mj^2$ and a geometric series. Root sums give $$\sum|z_i|^2=\frac{2K(M-1)}c,\quad
 \sum z_i^2=-\frac{2(M-1)}c,\quad
 \sum(\mathop{\mathrm{Im}}z_i)^2=\frac{(K+1)(M-1)}c.$$ Applying <a href="#eq:marked" data-reference-type="eqref" data-reference="eq:marked">[eq:marked]</a> to $z$ and $\mathop{\mathrm{Im}}z$ proves $$\label{eq:dyadic}
 \frac{\lambda_{\max}(C(A_n))}{\mathop{\mathrm{per}}A_n}
 >\frac{(c^2-16)K(M-1)}{c^3M},\quad
 \frac{\lambda_{\max}(\mathop{\mathrm{Re}}C(A_n))}{\mathop{\mathrm{per}}A_n}
 >\frac{(c^2-16)(K+1)(M-1)}{2c^3M}.$$ Taking $c=7$ gives the constants $33/343$ and $33/686$.

For reproducible finite values we give the full Rayleigh formulas. Put $B=2(M-1)/c$, $c_M=0$, and let $s_2(j)$ be the number of ones in the binary expansion of $j$. Define degree-$n-2$ polynomials $$S_0=\gamma\sum_{j=0}^{M-1}B(K-s_2(j))c_jx^{n-2-2j}y^{2j},\quad
 S_1=\gamma\sum_{j=0}^{M-1}2(j+1)c_{j+1}x^{n-2-2j}y^{2j}.$$ Terms with zero coefficients at the endpoint are omitted. Summing reciprocals within each root ring gives $$G_z=(-y,x)S_0,\qquad G_{\bar z}=(y,-x)S_1,
 \qquad G_{\mathop{\mathrm{Im}}z}=\frac1{2i}(y,-x)(S_0+S_1).$$ For example, on a ring of size $m$ and squared radius $a$, $\sum\bar z/(x+zy)=-am,yx^{m-2}/(x^m+a^{m/2}y^m)$ and $\sum|z|^2/(x+zy)=am,x^{m-1}/(x^m+a^{m/2}y^m)$. The formula for $S_1$ follows by differentiating $P$ in $y$ and dividing by $y$. Finally $\|xS\|^2+\|yS\|^2=n\|S\|^2$ for degree $n-2$. These identities reduce both full Rayleigh quotients to rational arithmetic. The two independent supplied programs use, respectively, binary coefficients and a marked-product recurrence. Exact integer calculations certify $$\begin{array}{c|c|c}
 (K,c,n)&\text{complex direction }z&\text{real direction }\mathop{\mathrm{Im}}z\\\hline
 (8,7,512)&1137/1000<Q<1138/1000&639/1000<Q<640/1000\\
 (10,5,2048)&1991/1000<Q<1992/1000&1094/1000<Q<1095/1000.
 \end{array}$$ These finite examples illustrate the formulas, not the proof of the asymptotic limits. The actual normalized matrix entries are algebraic; the Rayleigh quotients are rational because the common row-normalization factor cancels.

# The sharp ramp constant

Let $w_i=2i-n-1$ and define $M=C(A)/\mathop{\mathrm{per}}A$. For $1\le j<n$, let $b_j(i)=\mathbf 1_{\{i>j\}}$ and $u_j=b_j-(n-j)\mathbf 1/n$. Lemma <a href="#lem:indicator" data-reference-type="ref" data-reference="lem:indicator">2</a> and $M\mathbf 1=\mathbf 1$ give $$u_j^*Mu_j\le\frac{j(n-j)}n,
 \qquad w=2\sum_{j=1}^{n-1}u_j,
 \qquad\|w\|^2=\frac{n(n^2-1)}3.$$ The triangle inequality in the $M^{1/2}$ seminorm proves the all-rank bound $$\label{eq:ramp}
 \frac{w^*C(A)w}{\mathop{\mathrm{per}}A\,\|w\|^2}
 \le B_n:=\frac{12\bigl(\sum_{j=1}^{n-1}\sqrt{j(n-j)}\bigr)^2}
                 {n^2(n^2-1)}
 \longrightarrow\frac{3\pi^2}{16}.$$ The limit follows from the Riemann sum for $\int_0^1\sqrt{t(1-t)}\,dt=\pi/8$.

We include the lower construction, rather than infer sharpness from numerics. Choose unit row configurations whose empirical projective measures approach Haar measure on $\mathbb {CP}^1$, for example uniform grids in squared first-coordinate modulus and relative phase. Let $p_m$ be any global projective maximizer of the product of the $m$ forms. No form vanishes there. Apply a unitary variable change sending $p_m$ to $(1,0)$ and write the resulting ratios as $z_i=b_i/a_i$. The rotated empirical measures still approach Haar measure: every sequence of unitaries has a convergent subsequence, and Haar measure is invariant under its limit. The ratio map is continuous outside one Haar-null point. Thus the empirical real parts approach the law $$f_X(x)=\frac1{2(1+x^2)^{3/2}},\qquad
 F_X(x)=\frac12\left(1+\frac{x}{\sqrt{1+x^2}}\right).$$ For independent $X,Y$ with this law, $$\mathbb E|X-Y|=2\int F_X(x)(1-F_X(x))\,dx=\frac\pi2.$$ Weak convergence of product empirical measures applied first to the bounded continuous function $\min(|x-y|,T)$, and then monotone convergence as $T\to\infty$, give $$\label{eq:pairs}
 \liminf_m\frac1{m^2}\sum_{i<j}|\mathop{\mathrm{Re}}z_i-\mathop{\mathrm{Re}}z_j|\ge\frac\pi4.$$ This does not assume convergence of unbounded first moments.

Append the unit row form $p_m^*u$. It has modulus at most one on the sphere, with equality only at the projective point $p_m$. The new product consequently has a unique maximum there. In the rotated coordinates this adds one zero ratio, and <a href="#eq:pairs" data-reference-type="eqref" data-reference="eq:pairs">[eq:pairs]</a> persists with $n=m+1$. Order these $n$ rows by increasing $\mathop{\mathrm{Re}}z_i$. Stationarity of the maximum gives $\sum_i z_i=0$.

For each fixed augmented base repeat every row $L$ times consecutively, let $N=nL$, and let $U_L$ be the isometry taking a base coordinate to the normalized indicator of its cluster. Write $P$ for the base product. The sphere identity $$\langle f,g\rangle_B=(d+1)!\int_{\mathbb {CP}^1}f\bar g\,d\mu
 \quad(\deg f=\deg g=d)$$ follows by phase integration and the beta integral for monomials. It gives the exact compressed normalized cofactor matrix $$K_L:=\frac{U_L^*C(A_L)U_L}{\mathop{\mathrm{per}}A_L},\qquad
 (K_L)_{ij}=\frac{L}{nL+1}\mathbb E_{\mu_L}
       \frac{\langle v_i,v_j\rangle}{\ell_i\overline{\ell_j}},
 \quad d\mu_L\ \propto\ |P|^{2L}d\mu.$$ The unique maximum implies concentration at $(1,0)$. The kernels’ poles are harmless: outside a fixed neighborhood of the maximum, $$|P|^{2L}\frac1{|\ell_i\ell_j|}
 =|P|^{2L-2}|P/\ell_i||P/\ell_j|.$$ The quotients are bounded polynomials on the sphere, and the maximum of $|P|$ on that complement is strictly smaller than its value on a sufficiently small neighborhood of the peak. Comparing with that neighborhood in the normalizing integral proves exponential decay of the displayed tail. Locally the kernels are continuous. Hence $$K_L\longrightarrow\frac{J+zz^*}{n}.$$ All cofactor blocks between row clusters are constant, so $C(A_L)$ annihilates $\operatorname{ran}(U_L)^\perp$. The order-$N$ ramp compresses exactly to $L^{3/2}$ times the order-$n$ ramp. Its Rayleigh quotient therefore tends to $$\frac{3|\sum_i(2i-n-1)z_i|^2}{n^4}.$$ The real part of the numerator’s unsquared sum equals $\sum_{i<j}|\mathop{\mathrm{Re}}z_i-\mathop{\mathrm{Re}}z_j|$. By <a href="#eq:pairs" data-reference-type="eqref" data-reference="eq:pairs">[eq:pairs]</a>, a diagonal sequence of finite base sizes and sufficiently large finite $L$ attains the lower limit $3\pi^2/16$. Together with <a href="#eq:ramp" data-reference-type="eqref" data-reference="eq:ramp">[eq:ramp]</a>, this proves $$\limsup_{N\to\infty}\sup_{\mathop{\mathrm{rank}}A=2}
 \frac{w_N^*C(A)w_N}{\mathop{\mathrm{per}}A\,\|w_N\|^2}=\frac{3\pi^2}{16}.$$ The same limsup holds without the rank restriction and within positive-definite correlation matrices by continuity. No dimension-by-dimension limit of these ramp suprema is asserted.

# Rank-two endpoint interpretation

For binary row forms $\ell_i=a_ix+b_iy$ put $$S=\sum_{i<j}(a_ib_j-b_ia_j)\prod_{r\notin\{i,j\}}\ell_r.$$ For the real ramp weights, $$G_w=\sum_{i<j}(v_j\ell_i-v_i\ell_j)
                \prod_{r\notin\{i,j\}}\ell_r=(-y,x)S.$$ Thus the Fock identity gives $n\|S\|^2=w^*C(A)w$. Substitution in <a href="#eq:ramp" data-reference-type="eqref" data-reference="eq:ramp">[eq:ramp]</a> yields $$\frac{\|S\|^2}{\binom n2\mathop{\mathrm{per}}A}
 \le D_n:=\frac{8\bigl(\sum_{j=1}^{n-1}\sqrt{j(n-j)}\bigr)^2}
                 {n^3(n-1)}\longrightarrow\frac{\pi^2}{8},$$ and the preceding rank-two construction supplies the matching lower limsup.

For clarity, if $P_q(A)=\sum_{\sigma\in S_n}q^{\operatorname{inv}(\sigma)}
\prod_i a_{i,\sigma(i)}$, direct expansion also gives $$2P'_1(A)=\binom n2\mathop{\mathrm{per}}A-\|S\|^2.$$ Indeed the product of two $2$ by $2$ row determinants is the corresponding $2$ by $2$ Gram determinant. Expanding $\|S\|^2$, a permutation receives a positive contribution from each non-inversion and a negative contribution from each inversion, for total coefficient $\binom n2-2\operatorname{inv}(\sigma)$. Consequently $\pi^2/8$ is the optimal asymptotic constant for this normalized rank-two endpoint ratio. The identity linking $S$ to the ramp cofactor form has only been used in rank two; no all-rank endpoint bound with this constant is claimed. The endpoint counterexample mechanism itself was already established in the preceding research; the matching sharp upper constant is the issue treated here.

# What remains unresolved

Neither a large noncentral cofactor eigenvalue nor its real Rayleigh excess is automatically a normalized character or subgroup projector. Ordinary rank-two immanants lie in two-row sectors where classical dominance results already apply. Marcus’s rank-two large-order regime is independently excluded by a factorial/Jensen comparison; the precise inequality and finite thresholds are recorded in the stage summary. Higher-rank and genuine subgroup couplings have not been resolved. Numerical searches are reported only as searches.

An unrestricted higher-compound binary-vector formula was separately tested under an explicit definition and has an exact internal counterexample. The full text and qualifications of the potentially related statement in were not obtained. We make no assertion that its theorem is false, and do not use that unverified statement anywhere in this paper.


9 S. W. Drury, A counterexample to a question of Bapat & Sunder, *Math. Inequal. Appl.* 21 (2018), 517–520. [doi:10.7153/mia-2018-21-37](https://doi.org/10.7153/mia-2018-21-37). T. H. Pate, Group algebras, monotonicity, and the Lieb permanent inequality, *Linear Multilinear Algebra* 40 (1996), 207–220. [doi:10.1080/03081089608818438](https://doi.org/10.1080/03081089608818438). T. H. Pate, On permanental compounds, *Linear Algebra Appl.* 429 (2008), 1093–1101. [doi:10.1016/j.laa.2007.05.019](https://doi.org/10.1016/j.laa.2007.05.019). J. W. Neuberger, Norm of symmetric product compared with norm of tensor product, *Linear Multilinear Algebra* 2 (1974), 115–121. [doi:10.1080/03081087408817047](https://doi.org/10.1080/03081087408817047). L. Pioge, K. K. Pietrasz, B. Seron, L. Novo, N. J. Cerf, A logical implication between two conjectures on matrix permanents, *Linear Algebra Appl.* 725 (2025), 309–318. [doi:10.1016/j.laa.2025.07.011](https://doi.org/10.1016/j.laa.2025.07.011); [arXiv:2508.00111v1](https://arxiv.org/abs/2508.00111v1). I. M. Wanless, Lieb’s permanental dominance conjecture, in *The Physics and Mathematics of Elliott Lieb*, Vol. II, EMS Press (2022), 501–516. [doi:10.4171/90-2/48](https://doi.org/10.4171/90-2/48); [arXiv:2202.01867v1](https://arxiv.org/abs/2202.01867v1).


