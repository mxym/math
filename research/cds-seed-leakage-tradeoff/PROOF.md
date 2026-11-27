# Transcript distance, one-sided likelihood tails, and Hadamard witnesses

## 1. Model and statement

Let \(f:X\times Y\to\{0,1\}\) on finite input sets. Alice has a
secret bit \(s\) and \(x\); Bob has \(y\), but not \(s\). The
privately shared seed \(R\) is independent of the inputs and of
the secret. Its positive masses are \(\pi_r\). Conditional on
\(r,x,y,s\), the private coins of the two parties are independent,
and their message laws are \(P^x_{s,r}\) and \(Q^y_r\),
respectively. The receiver, knowing \(x,y\), observes the messages
but not the seed. Message alphabets may be finite or countably
infinite. For each input, put
\[
 T_s^{x,y}(a,b)=\sum_r \pi_r P^x_{s,r}(a)Q^y_r(b),
 \qquad D(x,y)=\tfrac12\|T_0^{x,y}-T_1^{x,y}\|_1 .
\]
Here \(\|v\|_1\) is the sum of absolute coordinates, not half that sum.
In the terminology of Hasegawa–Mataraarachchi v2 Definition 2.4,
\(\varepsilon\)-correctness means that on every positive input a
decoder succeeds with probability at least \(1-\varepsilon\) for each
secret. \(\delta\)-privacy means on every negative input a common
secret-independent distribution is within \(\delta\) in \(\ell_1\)
of each \(T_s^{x,y}\). These imply
\[
 f=1\implies D\ge1-2\varepsilon,\qquad
 f=0\implies D\le\delta.
 \tag{1}
\]
For the first bound, measure the difference on the event that the
decoder outputs zero; for the second use the triangle inequality.
Write \(\gamma=1-2\varepsilon-\delta>0\) and
\(\theta=(1-2\varepsilon+\delta)/2\).

For a fixed Alice input \(x\), let
\(P^x_{\mathrm{av},r}=(P^x_{0,r}+P^x_{1,r})/2\) and
\(\nu_x(a)=\sum_r\pi_rP^x_{\mathrm{av},r}(a)\).
For fixed Bob input \(y\), let \(\nu_y(b)=\sum_r\pi_rQ_r^y(b)\).
For a real cutoff \(K\ge1\) define
\[
 h^A_K(x)=\sum_{a,r}\pi_r[P^x_{\mathrm{av},r}(a)-K\nu_x(a)]_+,
 \quad
 h^B_K(y)=\sum_{b,r}\pi_r[Q^y_r(b)-K\nu_y(b)]_+ .
 \tag{2}
\]
These are hockey-stick divergences between the joint law of seed
and local message and the product of their marginals. The Alice
joint law uses a uniform bit independent of the seed, not the
worst conditional law for each secret. They are unrelated to the
privacy error \(\delta\) of the secret itself.

**Theorem 1.** Fix \(K\ge1\); let
\(M=\lceil8K/\gamma\rceil\), \(d=2M\) and \(\mu=\gamma/8\).
Select any finite subset \(U\) of positive-mass seeds with
\(q'=|U|\) and omitted mass at most \(\gamma/8\).
On the rows \(I=\{x:h^A_K(x)\le\gamma/8\}\) and all columns,
or all rows and the columns \(J=\{y:h^B_K(y)\le\gamma/8\}\),
the sign matrix \(2f-1\) has a real sign representation with
entrywise margin at least \(\mu\) and rank at most
\(\binom{q'+d}{d}\). If \(f(x,y)=x\cdot y\bmod2\) on
\(\mathbb F_2^n\times \mathbb F_2^n\), then, with
\(C=1+2K\,3^d\),
\[
 \max(|I|,|J|)
 \le (C/\mu)^2\binom{q'+d}{d}
 \le (C/\mu)^2(q'+1)^d .
 \tag{3}
\]
Only one leakage requirement is needed in each restriction.

## 2. Clipping one local likelihood ratio

Ignore zero-mass messages in all subsequent sums. Fix \(x,y\)
and sample independently \(a\sim\nu_x,b\sim\nu_y\), not from
the actual correlated transcript law. Set
\[
 w_{y,b}(r)=\frac{\pi_r Q^y_r(b)}{\nu_y(b)},\qquad
 u_{x,a}(r)=\frac{P^x_{0,r}(a)-P^x_{1,r}(a)}{2\nu_x(a)}.
\]
Then \(\|w_{y,b}\|_1=1\) and
\(D(x,y)=\mathbb E_{a,b}|\sum_r u_{x,a}(r)w_{y,b}(r)|\).
Removing coordinates outside \(U\) costs at most the omitted
mass in this expectation: use \(|P_0-P_1|/2\le P_{\rm av}\)
and sum all \(a,b\) after cancellation of the marginal denominators.
No reconditioning on \(R\in U\) is done, and the local reference
distributions remain the original marginals.

For a good row \(x\), put \(L_{x,a}(r)=P^x_{\mathrm{av},r}(a)/\nu_x(a)\).
The value \(\widetilde u_{x,a}(r)=u_{x,a}(r)\min(1,K/L_{x,a}(r))\)
(where the multiplier is one at \(L=0\)) is bounded by \(K\) in
absolute value. Also
\[
 |u_{x,a}(r)-\widetilde u_{x,a}(r)|\le [L_{x,a}(r)-K]_+ .
\]
Since \(\mathbb E_b w_{y,b}(r)=\pi_r\), the extra cost of clipping
is at most \(h^A_K(x)\), regardless of \(y\).
Thus
\[
 \left|D(x,y)-\mathbb E_{a,b}
             \left|\sum_{r\in U}\widetilde u_{x,a}(r) w_{y,b}(r)\right|
 \right|\le \gamma/4. \tag{4}
\]
For columns use instead
\[
 w_{x,a}(r)=\frac{\pi_r(P^x_{0,r}(a)-P^x_{1,r}(a))}{2\nu_x(a)},
 \qquad u_{y,b}(r)=\frac{Q^y_r(b)}{\nu_y(b)} .
\]
Now \(\|w_{x,a}\|_1\le1\) and
\(\mathbb E_a |w_{x,a}(r)|\le\pi_r\).
Omitted mass and clipping cost the same bounds using \(h^B_K(y)\).
This handles the fact that only Alice's encoder knows the secret.

## 3. Polynomial separation and the Hadamard bound

For \(-1\le z\le1\) the Chebyshev expansion is
\[
 |z|=\frac{2}{\pi}+\frac{4}{\pi}\sum_{j=1}^{\infty}
             \frac{(-1)^{j-1}}{4j^2-1}\,T_{2j}(z),
 \tag{5}
\]
where \(T_j(\cos t)=\cos(jt)\). This follows by integrating
the Fourier cosine series for \(|\cos t|\) separately over
its two sign intervals on \([0,\pi]\). The coefficients of odd
orders vanish by symmetry about \(\pi/2\); the integral of
\(\cos t\cos(2jt)\) on \([0,\pi/2]\) is
\((-1)^{j-1}/(4j^2-1)\). The series is absolutely uniformly
convergent, so equality follows from uniqueness of Fourier
coefficients. The tail after \(M\) terms is at most
\(2/[\pi(2M+1)]\), using the telescoping identity
\[
 \frac1{4j^2-1}=\tfrac12\left(\frac1{2j-1}-\frac1{2j+1}\right).
\]
Consequently \(\mathcal P(z)=K\) times that \(M\)-term partial
sum approximates \(K|z|\) by at most \(\gamma/8\).
The ordinary coefficients \(c_k\) of \(\mathcal P\) satisfy
\(\sum |c_k|\le 2K3^d\): from the recurrence
\(T_{j+1}=2zT_j-T_{j-1}\) its coefficient \(\ell_1\) norm is
at most \(3^j\), while the total absolute Chebyshev coefficient
mass in (5) is \(4/\pi<2\).

On good rows, write \(\bar u=\widetilde u/K\), so each coordinate
is in \([-1,1]\), and \(w=w_{y,b}|_U\) has \(\|w\|_1\le1\).
On good columns the same roles are reversed. By (4),
\[
 E(x,y)=\mathbb E_{a,b}\mathcal P(\langle\bar u,w\rangle)
 \quad\text{satisfies}\quad |E(x,y)-D(x,y)|\le3\gamma/8.
\]
By (1), \(E-\theta\) has sign \(2f-1\) with margin \(\mu\).
For a multi-index \(\alpha\) with \(|\alpha|=k\), expand the \(k\)-th
power as \(\sum_\alpha\bar u^\alpha\binom{k}{\alpha}w^\alpha\).
The expectation of each factor depends only on its own
sender by the independent sampling rule. The total count
over degrees at most \(d\) is \(\binom{q'+d}{d}\), including
the constant. This is the claimed rank bound.

For the quantitative input count, write the degree-\(k\) factorization
as \(A_k B_k^\top\), with the \(h_k=\binom{q'+k-1}{k}\) monomial
indices (and \(h_0=1\)). On rows with bounded \(\bar u\), each
row of \(A_k\) has squared \(\ell_2\) norm at most \(h_k\); on
columns with \(\ell_1\)-bounded \(w\), each row of \(B_k\) has
\(\ell_1\) norm at most one since
\(\sum_\alpha\binom{k}{\alpha}|w^\alpha|=(\sum_r|w_r|)^k\).
These row norm bounds hold also after expectation.
Let \(N=2^n\) and \(H(x,y)=(-1)^{x\cdot y}\). Summing the
characters gives \(HH^\top=NI\), so the restriction
to \(I\) has operator norm at most \(\sqrt N\).
For the Frobenius inner product, Cauchy--Schwarz yields
\[
 |\langle H|_I,A_kB_k^\top\rangle|
 \le\sqrt N \|A_k\|_{\mathrm F}\|B_k\|_{\mathrm F}
 \le N\sqrt{|I|h_k}.
\]
All entries of \(-H|_I\) times the corresponding entries
of \(E-\theta\) are at least \(\mu\), giving, if \(I\ne\varnothing\),
\[
 \mu |I|N \le CN\sqrt{|I|\binom{q'+d}{d}} .
\]
The factor \(C\) bounds \(\sum_k|c_k|\) plus \(\theta\le1\).
Transposing gives the same estimate for columns. This proves (3);
the last upper bound follows by encoding each multiset of
at most \(d\) elements from \(q'\) labels as a sorted word
of length \(d\) padded by a distinguished zero label. Empty
restrictions trivially satisfy the theorem.

## 4. Entropic consequences and optimal order in the restricted model

For any fixed input on one side, denote the joint distribution of
seed and local message by \(\mathsf J\) and product marginal by
\(\mathsf P\), with likelihood \(L=\mathsf J/\mathsf P\).
All logs below are base two. If the corresponding local mutual
information is \(I=D_{\rm KL}(\mathsf J\|\mathsf P)\), then for \(K>1\)
\[
 h_K\le\Pr_{\mathsf J}[L>K]
 \le\frac{I+1/(e\ln2)}{\log_2 K}. \tag{6}
\]
Indeed the negative part of \(L\log_2 L\), integrated over
\(\mathsf P\), is at most \(1/(e\ln2)\) pointwise, and the
positive part controls the indicated likelihood tail.
Thus for \(I\le I_0\) take
\(K=2^{8(I_0+1/(e\ln2))/\gamma}\). For an entropy bound
\(H(R)\le s<\infty\), take
\(U=\{r:-\log_2\pi_r\le8s/\gamma\}\).
It has \(q'\le2^{8s/\gamma}\) and omitted mass at most
\(\gamma/8\) by Markov applied to the information content.
For \(s=0\) the seed is deterministic; take its entire support.

At a fixed error gap and fixed \(I_0\), (3) for every input
on one side yields \(2^n\le\text{const}\cdot (2^{8s/\gamma}+1)^d\)
with \(d\) constant. This gives \(H(R)=\Omega(n)\). In particular
a constant-length message on one side has \(I_0\) constant
by the entropy bound on that message. The same lower order
applies to support cost \(\log_2|\mathrm{supp}(R)|\), which
is at least \(H(R)\).

For \(s=O(n^\alpha)\), choose \(K=n^\beta\) for fixed
\(0<\beta<1-\alpha\). Every input with
\(I\le(\gamma\beta/8)\log_2 n-1/(e\ln2)\) lies in the
good row or column set, by (6). The logarithm of the right
side of (3) is \(O(n^{\alpha+\beta})\), by
\(d=O(n^\beta)\), \(\log(q'+1)=O(n^\alpha)\) and
\(\log(C/\mu)=O(d+\log K)\). This gives the separate
exception counts on each side.

For a matching order on the one-side low-leakage class, take
\(R=(v,t)\) uniform in \(\mathbb F_2^n\times\mathbb F_2\).
Alice sends \(s+x\cdot v+t\); Bob sends the unordered pair
\(\{(v,t),(v+y,t+1)\}\).
For inner product one, the value \(x\cdot v+t\) is identical
on the two elements of the pair, so the receiver recovers the
bit without error. For inner product zero, the value toggles
between the two elements, both equally likely conditioned on
the pair. Thus the transcript distribution is identical for
both secrets. The uniformly averaged Alice message is independent
of \(R\), and its length is one bit. The shared seed uses
\(n+1\) bits. This construction witnesses the restricted large-\(n\)
order; it is not claimed to be a new protocol or to use
constant leakage on both sides.
