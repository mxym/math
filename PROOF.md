# Projective functional batch at the \(N+1\) threshold

A projective line means a one-dimensional linear subspace. Set \(V=\mathbb F_q^s\), \(\mathcal P=\{L\le V:\dim L=1\}\), and \(N=N_s=1+q+\cdots+q^{s-1}\), with \(N_0=0\). A length-\(m\) functional batch generator is a list of \(m\) indexed columns in \(V\) such that every list of the prescribed number of nonzero request vectors has pairwise disjoint column subsets spanning the corresponding requests. No locality restriction is needed for the lower bound. For the upper bound fix arbitrary distinct nonzero \(\rho_L,\kappa_L\in L\) for each \(L\), possible because \(q\ge4\). These are the two sides.

## 1. The quotient determinant

We include the determinant method of Essayag–Zabokritskiy [EZ, Lemmas 3.1 and 3.3] to make clear that neither the recovery implication nor the factorization requires odd characteristic.

Use the index set \(\mathcal O=\{0\}\cup\mathcal P\). Its corresponding scalar orbits are \(O_0=\{0\}\), \(O_J=J\setminus\{0\}\) for \(J\in\mathcal P\). Put \(u_0=0,\ u_I=\rho_I\) for \(I\in\mathcal P\), and use integer indeterminates \(x_L\). Define
\[
 B_{IJ}=\sum_{L\in\mathcal P}x_L
   \bigl|\{w\in L\setminus\{0\}:u_I+w\in O_J\}\bigr|.
\]
If the coefficient of \(x^c=\prod_L x_L^{c_L}\) in \(\det B\) is nonzero, some signed Leibniz term has chosen a column permutation \(\sigma\) and for each row \(I\) a request line \(L_I\) and \(w_I\in L_I\setminus\{0\}\) witnessing the corresponding entry. Exactly \(c_L\) lines \(L_I\) equal \(L\). The \(0,0\) entry is zero, so \(\sigma(0)\ne0\) and \(\sigma^{-1}(0)\ne0\). At row \(0\) use the singleton \(\kappa_{\sigma(0)}\), at row \(\sigma^{-1}(0)\) use the singleton \(\rho_{\sigma^{-1}(0)}\). For every other row use \(\rho_I\) and \(\kappa_{\sigma(I)}\): indeed \(w_I=\beta\kappa_{\sigma(I)}-\rho_I\) for some \(\beta\ne0\). Each indicated coefficient is nonzero, including in characteristic two. The two columns in any such pair are distinct even when their lines coincide, by the choice of representatives. Every left and every right column is used once. Assign the requests on each line bijectively to its rows and scale by the appropriate nonzero factor. This gives exactly two singletons and \(N-1\) cross-side pairs.

Write
\[
 X=\sum_{L\in\mathcal P}x_L,\qquad
 X_H=\sum_{L\subseteq H}x_L\quad(H\text{ a hyperplane}).
\]
Over \(\mathbb C\), the convolution \(Af(u)=\sum_L x_L\sum_{w\in L\setminus\{0\}}f(u+w)\) acts on functions invariant under nonzero scalar multiplication, with matrix \(B\) in the orbit-indicator basis. To diagonalize, choose a nontrivial additive character \(\psi\) of \(\mathbb F_q\) and use \(\chi_\xi=\psi\circ\xi\) for the \(\mathbb F_q\)-linear forms \(\xi\in V^*\). These characters are distinct (a nonzero linear form is onto) and form a basis of all complex functions on \(V\) by finite character orthogonality. Convolution has eigenvalue \((q-1)X\) on \(\chi_0\) and \(qX_{\ker \xi}-X\) on \(\chi_\xi,\ \xi\ne0\): the sum of \(\psi\) over nonzero field scalars is \(-1\), and over a line in the kernel all \(q-1\) summands are \(1\). Summing the characters in each nonzero scalar orbit gives \(N\) additional linearly independent invariant eigenvectors (the supports in the character basis are disjoint). Together with \(\chi_0\) these give the full \(N+1\) dimensions of the invariant space. Thus, as a polynomial over \(\mathbb Z\),
\[
 \det B=(-1)^N(q-1)XD,\qquad D=\prod_H(X-qX_H).
 \tag{1}
\]
The calculations hold after arbitrary complex substitution, which implies the polynomial identity. There are \(N\) hyperplanes, including the sole hyperplane \(\{0\}\) for \(s=1\).

## 2. The extra valuation

Fix \(q=2^a\) with \(a\ge2\). Write \((n)_j=n(n-1)\cdots(n-j+1)\), with \((n)_0=1\). Let \(v_2\) be the exponent of two in a nonzero rational, and \(\mathbb Z_{(2)}\) the ring of rationals of odd denominator. The strengthened form of [EZ, Lemma 3.5] is
\[
 a j-v_2((N_s)_j)\ \ge a\qquad(1\le j\le N_s).
 \tag{2}
\]
For \(s=1\), only \(j=1\) occurs and \(N_s=1\). In general put \(N_s=1+qN_{s-1}\) and consider indices \(0\le i<j\) in the factors \(N_s-i\). A factor has valuation at least \(a\) precisely when \(i\equiv1\bmod q\). If there are no such factors then \(j=1\), so the difference in (2) is exactly \(a\). Otherwise let their number be \(b\). They occur at \(i=1+qk,\ 0\le k<b\); since \(j\le N_s\), these indices satisfy \(k\le N_{s-1}-1\). Their product is \(q^b(N_{s-1})_b\), so by induction its valuation is at most \(2ab-a\). The \(b\) distinct preceding factors at \(i=qk\) are odd. Every other factor has valuation at most \(a-1\). These are disjoint sets of indices, so the total valuation is at most
\[
 2ab-a+(j-2b)(a-1)\le aj-a.
\]
This proves (2), with no difficulty at \(j=N_s\).

It remains to extend [EZ, Proposition 3.4]. For \(|c|=N+1\), take the direct expansion of \(XD\), selecting \(-qX_H\) in \(j\) hyperplane factors and \(X\) in all others. After choosing one variable from each selected \(X_H\), let \(b\) record their multiplicities. Divide the contribution to \([x^c]XD\) by the multinomial \(\binom{N+1}{c}=(N+1)!/\prod c_L!\). It is zero if \(b\not\le c\); otherwise the contribution is
\[
 (-q)^j\,\frac{\prod_L(c_L)_{b_L}}{(N+1)_j}.
\]
Indeed the unnormalized contribution is \((-q)^j\) times the coefficient of \(x^{c-b}\) in \(X^{N+1-j}\). In particular the \(j=0\) ratio is 1. Our claim is
\[
 \frac{[x^c]XD}{\binom{N+1}{c}}
  \in 1-qN_{s-1}+2^{2a-1}\mathbb Z_{(2)}.
 \tag{3}
\]
When \(j\ge2\) the denominator is \((N+1)(N)_{j-1}\), and \(v_2(N+1)=1\) because \(N+1=2+qN_{s-1}\). The numerator is integral, so (2) gives valuation of \(q^j/(N+1)_j\) at least \(2a-1\). For \(j=1\) sum the contribution \(-q c_L/(N+1)\) over incidences \(L\subseteq H\); each line lies in \(N_{s-1}\) hyperplanes since the forms vanishing on that line form an \((s-1)\)-dimensional subspace of \(V^*\). The sum is exactly \(-qN_{s-1}\). This also covers \(s=1\) where there are no incidences. Both (2) and (3) concern integer/rational coefficients; no determinant is reduced to characteristic two before proving that its coefficients are nonzero.

## 3. Exact length and scope

By (1) and the nonzero coefficients, every multiplicity vector of weight \(N+1\) gives a recovery. In fact
\[
 v_2([x^c]\det B)=v_2\!\left(\binom{N+1}{c}\right)
\]
because the prefactor in (1) and the ratio in (3) are odd.

For the length lower bound, in any solution with \(m\) columns, request the same nonzero vector on \(L\) exactly \(N+1\) times. If the recovery uses \(u\) singletons, its disjoint nonempty subsets consume at least \(u+2(N+1-u)\) columns. Hence \(u\ge 2(N+1)-m\), all from nonzero columns on \(L\). If \(m<2N\), this would require at least three nonzero columns on each of \(N\) different lines, impossible. Together with the construction this gives equality. It also shows any equality generator has exactly two nonzero indexed columns per line (not necessarily distinct as vectors).

For \(q=2\) there is only one nonzero vector per line, and \(v_2(N+1)=s\), not the normalization in this proof. The binary equality already follows from the known result recorded in [KRS, Eq. (6)]. The determinant method here need not retain support if formally used at \(q=2\): for \(s=2\), \(XD=(x+y+z)(-x+y+z)(x-y+z)(x+y-z)\) has zero \(x^3y\) coefficient. This is not a counterexample to binary batch equality. For odd \(q\) use [EZ, Theorem 2.3 and Corollary 1.2(b)]. Together the results answer Open Problem 3.13 for all finite fields, with the present proof supplying the missing even-field range.
