# A small-bias EXIT argument for weak random-erasure recovery

## 1. The theorem

Let \(C\subseteq\mathbb F_2^M\) be a binary linear code. The erasure set \(E\subseteq[M]\) consists of independent Bernoulli\((\eta)\) selections of coordinates. Recovery means that the unerased coordinates uniquely determine the transmitted codeword. Let \(R=\dim C/M\).

**Theorem.** There are absolute constants \(\gamma>0,\zeta>4\) such that, for every sufficiently large \(M\), every doubly transitive binary linear code of length \(M\), and every \(M^{-\gamma}<\varepsilon<1/2\) with \(R\le1-\varepsilon\), the block failure probability at any \(\eta\le\varepsilon^\zeta\) is at most \(M(M-1)^{-4}\). Both the size condition and the failure bound are uniform in \(C,R,\varepsilon,\eta\).

A code is called doubly transitive here if its coordinate permutation group contains a subgroup transitive on ordered pairs of distinct coordinates. Binary Reed–Muller codes \(\mathrm{RM}(m,r)\) satisfy this because evaluation of polynomials of degree \(\le r\) on \(\mathbb F_2^m\) is invariant under invertible affine coordinate substitutions. Such substitutions do not increase degree, including after binary multilinear reduction; their inverses are of the same type. The affine group is doubly transitive: translate the first point and then use an invertible linear map taking one nonzero difference to any other. Thus \(M=2^m\) specializes the theorem to the full quantifiers of [Conjecture 16](https://arxiv.org/html/2604.04188v2) of Błasiok, Lou, Rosen and Sudan. When recovery is possible, the codeword can be recovered by a polynomial-time linear solve over the known coordinates.

## 2. The area identity and block failure

For a set \(S\subseteq[M]\), put \(C_S=\{w\in C:\operatorname{supp}w\subseteq S\}\). For each coordinate \(i\), define the extrinsic failure indicator on subsets \(S\subseteq[M]\setminus\{i\}\) by
\[
 f_i(S)=\mathbf 1_{\{\exists w\in C_{S\cup\{i\}}\text{ with }w_i=1\}},
 \qquad h_i(p)=\mathbb E_p f_i(S).
\]
Here \(p\) is the independent erasure probability of each coordinate *other than* \(i\). The event is monotone in \(S\). Transitivity makes \(h_i(p)\) the same polynomial \(h(p)\) for every \(i\); double transitivity also makes the stabilizer of \(i\) transitive on its \(M-1\) other coordinates and hence on the variables of \(f_i\).

For completeness, put \(g(p)=\mathbb E_p\dim C_E\) over erasures in all \(M\) coordinates. For any function of a product of independent Bernoulli variables, the expectation is multiaffine in their biases, and its partial derivative in one bias is the expectation of the corresponding set difference. Along the common bias \(p\), this gives
\[
 g'(p)=\sum_{i=1}^M \mathbb E_p\left[\dim C_{S\cup\{i\}}-\dim C_S\right]
      =\sum_{i=1}^M h_i(p)=M h(p).
\]
Indeed, \(C_S\) is the kernel of the \(i\)-th coordinate functional on \(C_{S\cup\{i\}}\); the dimension jump is exactly \(f_i(S)\). Since \(g(0)=0\) and \(g(1)=\dim C\),
\[
 \int_0^1 h(p)\,dp=R,\qquad \int_0^1 (1-h(p))\,dp=1-R\ge\varepsilon.           \tag{1}
\]
This is the linear-code erasure EXIT area identity.

Block failure is exactly the event that \(C_E\ne0\). It is the union over \(i\) of the events \(\{i\in E,\ f_i(E\setminus\{i\})=1\}\): choose a nonzero coordinate of any witness word for one direction, and use the witness in \(C_E\) for the other. The two conditions of each event use disjoint independent parts of \(E\). Hence
\[
 \Pr_p(\text{block failure})\le M p\,h(p).                                \tag{2}
\]
This step does not assume independence between the extrinsic failures of different bits.

## 3. The small-bias threshold estimate

For a monotone Boolean \(f\) on \(d\ge2\) variables with a transitive group of variable permutations, write \(u(p)=\mathbb E_p f\). The needed Friedgut–Kalai bound is, for an absolute \(c>0\) and \(0<p\le1/2\),
\[
 u'(p)\ge \frac{c\ln d}{p\ln(1/p)}\,u(p)(1-u(p)).                          \tag{3}
\]
Use pivotal influences \(I_i^p(f)=\Pr_p[f(x_{-i},0)\ne f(x_{-i},1)]\) on the other coordinates. By the product derivative identity and monotonicity, \(u'=\sum_i I_i^p\). Theorem 3.1 of Friedgut–Kalai gives a maximum pivotal influence at least \(c\min(u,1-u)\ln d/[d p\ln(1/p)]\), using \(1-f\) for \(u>1/2\); the influences are equal by transitivity and \(\min(u,1-u)\ge u(1-u)\).

Here is also the dyadic reduction underlying the bias factor and its extension to all \(p\). Represent a dyadic \(p=j/2^b\) by a Boolean gadget \(G\) on \(b\) independent fair bits, accepting the \(j\) lexicographically first bit strings. If bit \(\ell\), numbered from the most significant, is pivotal, its more-significant prefix must be the unique length-\((\ell-1)\) prefix whose contiguous interval is split by the threshold (if none is split, its influence is zero). Also, exactly one bit value of each pivotal pair is accepted. Thus its influence is at most \(\min(2p,2^{-(\ell-1)})\), and the sum of the gadget influences is at most \(C_0 p\ln(1/p)\) for an absolute \(C_0\), by splitting the sum at \(\lceil\log_2(1/p)\rceil\) and summing the geometric tail.

Compose \(f\) with \(d\) independent copies of the gadget. Its mean is \(u(p)\). A fair-bit influence in block \(i\) and position \(\ell\) is exactly \(I_i^p(f) I_\ell^{1/2}(G)\): pivotality of the outer bit depends only on the other blocks, and pivotality in the gadget depends only on its own remaining bits. In particular each influence is repeated in all \(d\) blocks, and the total \(J\) of the fair influences is \(u'(p)\sum_\ell I_\ell^{1/2}(G)\). The uniform max-to-total KKL inequality (e.g. Friedgut–Kalai Theorem 3.4 specialized to the uniform cube) gives \(J\ge c_0 u(1-u)\ln(1/\max I)\). If \(J\le\sqrt d\), then \(\max I\le J/d\le d^{-1/2}\), giving \(J\ge(c_0/2)u(1-u)\ln d\). If \(J>\sqrt d\), the same form with a smaller absolute constant follows from \(u(1-u)\le1/4\) and \(\ln d\le\sqrt d\). Comparing with the gadget influence sum proves (3) at dyadic biases. All terms in (3) are continuous for \(0<p\le1/2\); take dyadic limits. Constant indicators are trivial in (3).

## 4. Placing the transition and bounding the lower tail

The zero code has no block failures and can be set aside. A nonzero transitive code has \(h(1)=1\). The rate assumption excludes the full code, so it cannot contain a weight-one word by transitivity, and \(h(0)=0\). Since all subsets of the other coordinates have positive probability for \(0<p<1\), \(0<h(p)<1\) there.

Apply (3) to \(f_i\) with \(d=M-1\), and integrate the derivative of the log-odds \(\mathcal L(p)=\ln[h(p)/(1-h(p))]\). For \(0<u<v\le1/2\),
\[
 \mathcal L(v)-\mathcal L(u)\ge
 c\ln(M-1)\ln\!\left(\frac{\ln(1/u)}{\ln(1/v)}\right).                     \tag{4}
\]
Use the absolute \(c\) from (3), and set
\[
 \gamma=\min\{c\ln(2)/4,\ 1/4\},\qquad \zeta=4\exp(4/c).
\]

First put \(p_0=\varepsilon^4\), \(p_1=\varepsilon/2\). These satisfy \(0<p_0<p_1<1/2\). The ratio of the inner logarithms in (4) is \(4\ln(1/\varepsilon)/\ln(2/\varepsilon)\ge2\) since \(\varepsilon<1/2\). If \(h(p_0)\ge1/2\), then \(\mathcal L(p_0)\ge0\) and (4) gives \(1-h(p_1)\le (M-1)^{-c\ln2}\). Since \(h\) is nondecreasing, this would imply
\[
 \int_0^1 (1-h(p))\,dp
 \ \le p_1+1-h(p_1)\ \le \frac{\varepsilon}{2}+(M-1)^{-c\ln2}
 \ <\varepsilon
\]
for all sufficiently large \(M\) uniformly in \(M^{-\gamma}<\varepsilon\): \(M-1\ge \sqrt M\) for \(M\ge3\), so the error term is at most \(M^{-2\gamma}\), which is \(<\varepsilon/2\) for sufficiently large \(M\). This contradicts (1). Therefore \(h(p_0)<1/2\).

Next take \(p_*=\varepsilon^\zeta\). The log ratio in (4), between \(p_*\) and \(p_0\), is exactly \(\ln(\zeta/4)=4/c\). As \(\mathcal L(p_0)<0\), it follows that \(\mathcal L(p_*)\le-4\ln(M-1)\), so \(h(p_*)\le(M-1)^{-4}\). By monotonicity all \(\eta\le p_*\) have \(h(\eta)\le h(p_*)\), and (2) gives the claimed uniform bound. The proof uses the small-bias logarithmic scale to reach a power of \(\varepsilon\); it does not give recovery at erasure rate \(\varepsilon-M^{-\gamma}\).
