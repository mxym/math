---
title: "Quadratic-logarithmic Gaussian dimension for all integer cell counts"
author: "Yongxian Zhang"
date: "October 2026"
geometry: margin=1in
fontsize: 10pt
header-includes:
  - |
    \usepackage{microtype}
---

**Yongxian Zhang**, School of Computer Science and Engineering, South China University of Technology. ORCID [0009-0000-3864-3536](https://orcid.org/0009-0000-3864-3536). Correspondence: mxymmxym1@gmail.com.

**Mathematical research note — 7 October 2026 (PDT)**

The spherical-cap converse proves that bounded \(O(1/k)\)
additive error to the unrestricted equal-mass Gaussian centroid
optimum requires dimension \(\Omega((\log k)^2)\) for every \(k\).
We prove the **matching sufficient dimensional order for every
sufficiently large integer number of cells**.
The first stage uses binary linear codes at dyadic cardinalities;
a one-dimensional Gaussian selector and a bounded-entropy binary
expansion then extend it to **all** integers \(k\).
Every partition block has exact Gaussian mass \(1/k\).

The only substantial classical external probabilistic input is the
Berry–Esseen inequality for independent, not necessarily identically
distributed, centered summands. We state the exact form and
constants used and trace every application below. All other
probabilistic estimates are derived directly.

## Main theorem

**All-integer conclusion (Theorem 11).** For every sufficiently
large integer \(k\), without arithmetic restrictions on \(k\),
the least Gaussian dimension needed for additive \(92/k\)
accuracy satisfies
\[
 \boxed{\displaystyle
 \frac{(\log k)^2}{108}
      \le D_{92}(k)
      \le\lceil(\log k)^2\rceil+1.}
\]
Thus the central dimension-order problem has the
**complete answer \(\Theta((\log k)^2)\) for all \(k\)**.
The proof first resolves dyadic \(k=2^r\)
by linear codes and then glues the binary expansion
with a one-dimensional Gaussian selector.

Let \(F_d(k)\) denote the global optimum of
\[
 P(\mathcal A)=\sum_{u=1}^k
       \left\|\int_{A_u}x\,d\gamma_d(x)\right\|^2
\]
over arbitrary measurable partitions of standard Gaussian
\(\mathbb R^d\) into exactly \(k\) regions of mass \(1/k\).
Let \(F_\infty(k)=F_{k-1}(k)\).

**Theorem 1 (dyadic component of the all-integer theorem).**
There is an absolute integer \(r_0\) such that for every
integer \(r\ge r_0\), writing \(k=2^r\) and \(L=\log k\),
there exists an exact equiprobable \(k\)-cell Gaussian
partition in
\[
              d=\lceil L^2\rceil
\]
dimensions with
\[
 \boxed{\displaystyle
        F_d(k)\ge F_\infty(k)-\frac{100}{k}.}
 \tag{1}
\]
The partition is obtained by taking the largest of \(k\) explicitly
specified unit Gaussian linear scores indexed by
\(\mathbb F_2^r\).

Together with the universal spherical-cap lower bound, the
minimum dimension \(D_{100}(2^r)\) required to achieve error
at most \(100/2^r\) satisfies
\[
 \boxed{\displaystyle
           D_{100}(2^r)=\Theta(r^2)
              =\Theta((\log k)^2).}
 \tag{2}
\]
Theorem 11 below removes the dyadic restriction with
a one-coordinate exact Gaussian selector. Neither result
identifies the finite-\(k\) global optimizer.

The construction is probabilistic in the proof of existence.
After choosing a successful binary matrix, all its entries
are ordinary finite integers and the induced Gaussian cells
are completely deterministic. Exact equal masses follow
from an orthogonal group action; there is no probabilistic
mass correction.

## 1. Linear-code orbit and pairwise independence

Let \(k=2^r\), \(m=\lceil(\log k)^2\rceil\).
Choose column vectors
\(g_1,\ldots,g_m\in\mathbb F_2^r\)
independently and uniformly.
For each \(u\in\mathbb F_2^r\), set
\[
 v_u=m^{-1/2}
       \big((-1)^{u\cdot g_1},\ldots,
            (-1)^{u\cdot g_m}\big)\in S^{m-1}.
 \tag{3}
\]
Here the inner products inside the exponents are
taken in \(\mathbb F_2\).

**Lemma 2 (exact transitivity when the matrix has full rank).**
If \(g_1,\ldots,g_m\) span \(\mathbb F_2^r\),
the \(v_u\) are pairwise distinct. The Gaussian
score-maximizing sets
\[
 A_u=\{x:\langle v_u,x\rangle>
                  \langle v_w,x\rangle\text{ for all }w\ne u\}
 \tag{4}
\]
partition \(\mathbb R^m\) modulo null hyperplanes,
and satisfy \(\gamma_m(A_u)=1/k\) exactly.
Moreover,
\[
 \boxed{\displaystyle
        P(\mathcal A)\ge
       \frac{1}{k}\left(
        \mathbb E\max_u\langle v_u,G\rangle
                    \right)^2.} \tag{5}
\]

*Proof.* Distinctness follows since
\(v_u=v_w\) would imply
\((u-w)\cdot g_j=0\) for every \(j\),
contradicting the span condition.
For each \(a\in\mathbb F_2^r\),
the diagonal orthogonal transformation
\[
 D_a=\operatorname{diag}
     ((-1)^{a\cdot g_1},\ldots,
      (-1)^{a\cdot g_m})
\]
satisfies \(D_a v_u=v_{u+a}\).
It carries each score-max cell to the corresponding
translated cell. Gaussian rotational invariance
makes all cell masses equal; they sum to one.

Writing \(b_u=\int_{A_u}x\,d\gamma_m(x)\),
we have
\[
 \mathbb E\max_u\langle v_u,G\rangle
       =\sum_u\langle v_u,b_u\rangle
       \le\sqrt{k}\left(\sum_u\|b_u\|^2\right)^{1/2}.
\]
Squaring gives (5). \(\square\)

Let the score for message \(u\) be
\(X_u=\langle v_u,G\rangle\),
where \(G_1,\ldots,G_m\) are independent \(N(0,1)\).
Condition on the entire Gaussian vector \(G\), and
put \(a_j=G_j/\sqrt m\). The score for \(u=0\)
is the deterministic (given \(G\)) value
\[
             X_0=\sum_j a_j. \tag{6}
\]

**Lemma 3 (pairwise-independent conditional exceedances).**
Over the random binary columns, for every nonzero
\(u\), the conditional distribution of \(X_u\)
is that of the Rademacher-weighted sum
\(S_a=\sum_j a_j\epsilon_j\), with independent
symmetric signs \(\epsilon_j\).
For every two distinct nonzero \(u,w\),
the conditional random variables \(X_u,X_w\)
are independent. Consequently, for any real
threshold \(t\), if
\(q_a(t)=\Pr_{\epsilon}(S_a\ge t)>0\),
then
\[
 \boxed{\displaystyle
 \Pr_g\{\max_u X_u<t\mid G\}
     \le\frac{1}{(k-1)q_a(t)}.}               \tag{7}
\]

*Proof.* The \(\mathbb F_2\)-linear functional
\(g\mapsto u\cdot g\) is unbiased for nonzero \(u\).
Distinct nonzero \(u,w\) are linearly independent
over \(\mathbb F_2\), so
\(g\mapsto(u\cdot g,w\cdot g)\) is uniform
on \(\mathbb F_2^2\). Independent columns yield
independent sign vectors for the two messages,
conditional on fixed \(G\).

Let \(N_t=\#\{u\ne0:X_u\ge t\}\).
Conditional pairwise independence gives
\(\mathbb E_gN_t=(k-1)q_a(t)\) and
\(\operatorname{Var}_gN_t\le(k-1)q_a(t)\).
Chebyshev's inequality for the event
\(N_t=0\) proves (7). \(\square\)

Thus the code structure supplies exact mass symmetry
and, independently, a second-moment method.
No bound on the worst correlation of two codewords
is required.

## 2. Tilted Rademacher anti-concentration

Write
\[
 Q_2=\sum_j a_j^2,\qquad
 Q_4=\sum_j a_j^4,\qquad
 {\cal G}=\{1/2\le Q_2\le2,\quad Q_4\le10/m\}.
 \tag{8}
\]

**Lemma 4 (typical Gaussian weights).**
For \(G_j\stackrel{\rm iid}{\sim}N(0,1)\),
\[
 \boxed{\Pr_G({\cal G}^c)\le10/m.}             \tag{9}
\]

*Proof.* Direct normal moment calculation gives
\[
 \mathbb EQ_2=1,\quad
 \operatorname{Var}Q_2=2/m,\quad
 \mathbb EQ_4=3/m,\quad
 \operatorname{Var}Q_4=96/m^3,
\]
since \(\mathbb EG^4=3\) and
\(\mathbb EG^8=105\).
Chebyshev bounds the first failure by \(8/m\)
and the second by \(96/(49m)<2/m\).
Union bounding proves (9). \(\square\)

For nonzero weights \(a\) and \(\lambda>0\),
introduce the exponentially tilted sign law
\[
 \Pr_\lambda(\epsilon_j=e)
     =\frac{\exp(\lambda a_j e)}
            {2\cosh(\lambda a_j)},\qquad e=\pm1.
\]
Set
\[
 \Lambda(\lambda)=\sum_j\log\cosh(\lambda a_j),
 \quad \mu=\Lambda'(\lambda)
     =\sum_j a_j\tanh(\lambda a_j),
 \quad V=\Lambda''(\lambda)
     =\sum_j a_j^2\operatorname{sech}^2(\lambda a_j).
 \tag{10}
\]

**Classical Berry–Esseen input.**
For independent centered real random variables \(W_j\)
with total variance \(V>0\), the inequality
\[
 \sup_x\left|\Pr\!\left(
    \frac{\sum W_j}{\sqrt V}\le x\right)-\Phi(x)\right|
 \le\frac{\sum_j\mathbb E|W_j|^3}{V^{3/2}}
 \tag{11}
\]
holds (the deliberately nonoptimal constant \(1\)
is sufficient). For a published strictly stronger
**non-identically distributed** version with constant
\(0.5591<1\), see I. S. Tyurin,
*A Refinement of the Remainder in the Lyapunov Theorem*,
*Theory of Probability & Its Applications* **56** (2012),
693–696, DOI
[10.1137/S0040585X9798572X](https://doi.org/10.1137/S0040585X9798572X).
We apply (11) only to bounded
independent centered tilted signs and explicitly
bound the numerator and denominator below.
This standard result is the sole non-elementary
probability theorem imported into the proof.

**Lemma 5 (uniform moderate-deviation lower tail).**
There exists an absolute \(L_0\) (one may take
\(L_0=10^{10}\)) such that whenever
\(L=\log k\ge L_0\), \(m=\lceil L^2\rceil\),
and \(G\in{\cal G}\), put
\[
 \lambda=\sqrt{\frac{2L}{Q_2}},\qquad
 B_0=\frac12\log L+12,\qquad
 s_y=\mu-\frac{B_0+y}{\lambda}
       \quad(0\le y\le\lambda/4).
 \tag{12}
\]
Then
\[
 \boxed{\displaystyle
 \Pr_\epsilon\{S_a\ge s_y\}
    \ge\frac{e^{-L+B_0+y-1}}{20\lambda}.}
 \tag{13}
\]
Consequently the randomly generated code satisfies
\[
 \boxed{\displaystyle
 \Pr_g\{\max_uX_u<s_y\mid G\}
      \le\eta e^{-y},\qquad
             \eta=80e^{-11}<1/10.}           \tag{14}
\]

*Proof.* On \({\cal G}\),
\(\sqrt L\le\lambda\le2\sqrt L\).
Since \(\operatorname{sech}^2x\ge1-x^2\),
\[
 V\ge Q_2-\lambda^2 Q_4
     \ge1/2-40L/m\ge1/4
\]
for \(L\ge160\), while \(V\le Q_2\le2\).
The centered tilted variables are bounded
in absolute value by \(2|a_j|\). Hence
\[
 \sum_j\mathbb E_\lambda|W_j|^3
   \le8\sum_j|a_j|^3
   \le8\sqrt{Q_2Q_4}
   \le8\sqrt{20/m}.
\]
By (11), the error for a tilted CDF
is at most \(64\sqrt{20/m}<288/\sqrt m\).

For \(L\ge10^{10}\) we have
\(B_0\le\lambda/4\). Therefore for
\(0\le y\le\lambda/4\), the interval
\[
            I_y=[s_y,s_y+1/\lambda]
\]
lies, after centering at \(\mu\) and
dividing by \(\sqrt V\), inside \([-1,0]\).
Its standardized length is at least
\(1/(2\lambda)\). A standard normal
has density at least \(\varphi(1)>1/5\)
on this range. Thus its probability in
\(I_y\) is at least \(1/(10\lambda)\).
Two applications of (11) cost less
than \(576/\sqrt m\le1/(20\lambda)\)
for \(L\ge10^{10}\).
Consequently
\[
                       \Pr_\lambda(S_a\in I_y)
                             \ge1/(20\lambda).             \tag{15}
\]

The exact change-of-measure identity gives
\[
 \Pr_\epsilon(S_a\ge s_y)
 \ge\frac1{20\lambda}
      \exp\{\Lambda(\lambda)
                -\lambda(s_y+1/\lambda)\}.
 \tag{16}
\]
For every real \(x\),
\[
 \log\cosh x-x\tanh x+x^2/2\ge0,
\]
because the left side is even, vanishes
at zero, and its derivative for \(x>0\)
is \(x\tanh^2x\ge0\).
Summing over \(x=\lambda a_j\), we obtain
\[
 \Lambda(\lambda)-\lambda\mu
 \ge-\lambda^2Q_2/2=-L.
\]
Inserting \(s_y\) in (16) proves (13).

Finally, using \(\lambda\le2\sqrt L\),
\(k-1\ge k/2\), and \(k=e^L\),
\[
 (k-1)q_a(s_y)
 \ge\frac{e^{B_0+y-1}}{40\lambda}
 \ge\frac{e^{11+y}}{80}.
\]
Apply Lemma 3 to obtain (14).
The inequality \(\eta<1/10\) follows
from \(e>2\), hence \(e^{11}>2^{11}>800\).
\(\square\)


## 3. From exceedance tails to a sharp expected maximum

The next lemma converts the preceding
exponentially improving threshold estimate into
an **expectation bound at the \(1/\sqrt L\) scale**.
This is the crucial step that a single
constant-probability exceedance estimate would
*not* provide.

**Lemma 6 (conditional expected-score estimate).**
For \(L\ge10^{10}\), \(m=\lceil L^2\rceil\),
and every Gaussian vector \(G\in{\cal G}\),
the random generator satisfies
\[
 \boxed{\displaystyle
 \mathbb E_g[M\mid G]\ge
   \mu-\frac{B_0}{\lambda}
      -\frac{\eta}{\lambda}
      -\eta(4\sqrt L+|X_0|)e^{-\lambda/4},
 \qquad M=\max_{u\in\mathbb F_2^r}X_u.}       \tag{17}
\]

*Proof.* As \(y\) runs from \(0\) to
\(y_*=\lambda/4\), the threshold \(s_y\)
decreases linearly with slope \(-1/\lambda\).
The pointwise identity
\[
 (s_0-M)_+
 =\frac1\lambda\int_0^{y_*}
                \mathbf1_{\{M<s_y\}}\,dy
       +(s_{y_*}-M)_+
\]
holds, regardless of any ties.
Using (14), the expected integral is
at most \(\eta/\lambda\).
Since \(M\ge X_0\), and
\(s_{y_*}\le\mu\le\lambda Q_2\le4\sqrt L\),
\[
 (s_{y_*}-M)_+
 \le(4\sqrt L+|X_0|)
            \mathbf1_{\{M<s_{y_*}\}}.
\]
Its expectation is at most
\(\eta(4\sqrt L+|X_0|)e^{-\lambda/4}\).
Finally \(M\ge s_0-(s_0-M)_+\).
Taking expectations proves (17).
\(\square\)

**Lemma 7 (mean over generators and Gaussian data).**
For \(L\ge10^{10}\),
\[
 \boxed{\displaystyle
 \mathbb E_{g,G}M
 \ge \sqrt{2L}
       -\frac{\log L}{2\sqrt{2L}}
       -\frac{27}{\sqrt L}.}                 \tag{18}
\]

*Proof.* Let \(\sigma=\sqrt{Q_2}\), so
\(\lambda=\sqrt{2L}/\sigma\).
The elementary inequality
\[
         \tanh x\ge x-x^3/3\quad(x\ge0)
\]
follows on differentiation from
\(x^2-\tanh^2x\ge0\).
It implies
\[
 \mu\ge \lambda Q_2-\lambda^3Q_4/3.
\]
On \({\cal G}\), \(\sigma\ge1/\sqrt2\),
so
\[
 \mu\ge\sqrt{2L}\,\sigma
                   -\frac83 L^{3/2}Q_4.
\]
Since \(\mathbb EQ_4=3/m\),
\[
 \mathbb E[\mu\mathbf1_{\cal G}]
 \ge\sqrt{2L}\,\mathbb E[
                   \sigma\mathbf1_{\cal G}]
                   -8L^{3/2}/m.             \tag{19}
\]

Because
\(|\sqrt{x}-1|\le|x-1|\) for \(x\ge0\),
\(\mathbb E|\sigma-1|
 \le\sqrt{\operatorname{Var}Q_2}
 =\sqrt{2/m}\).
Cauchy–Schwarz, \(\mathbb E\sigma^2=1\),
and Lemma 4 give
\[
 \mathbb E[\sigma\mathbf1_{\cal G}]
       \ge1-\sqrt{2/m}-\sqrt{10/m}.
\]
Using \(m\ge L^2\),
\[
 \mathbb E[\mu\mathbf1_{\cal G}]
 \ge\sqrt{2L}-7/\sqrt L-8/\sqrt L.
                                                        \tag{20}
\]

Also, \(\mathbb E\sigma\le1\) by
Jensen's inequality, so
\[
 \mathbb E[
   (B_0/\lambda)\mathbf1_{\cal G}]
 \le\frac{B_0}{\sqrt{2L}}
 =\frac{\log L}{2\sqrt{2L}}
                  +\frac{12}{\sqrt{2L}}.
\]
The last constant term is less than
\(9/\sqrt L\).
Furthermore \(\eta/\lambda\le1/\sqrt L\)
on \({\cal G}\).

For \(L\ge10^{10}\), the elementary
inequality \(e^x\ge x^4/4!\) and
\(\lambda\ge\sqrt L\) give
\[
 \eta e^{-\lambda/4}
       (4\sqrt L+\mathbb E|X_0|)
              \le1/\sqrt L.
\]
Indeed \(X_0\sim N(0,1)\),
\(\mathbb E|X_0|\le1\), and
\(e^{-\sqrt L/4}\le6144/L^2\).

Finally, on \({\cal G}^c\)
we still have \(M\ge X_0\).
Since \(\mathbb E X_0^2=1\),
Lemma 4 yields
\[
 \mathbb E[
 M\mathbf1_{{\cal G}^c}]
 \ge-\sqrt{\Pr({\cal G}^c)}
 \ge-\sqrt{10/m}\ge-1/\sqrt L
\]
for \(L\ge10^{10}\).
Combining all the displayed bounds
with Lemma 6 gives (18):
the six separate \(1/\sqrt L\)
losses have coefficients at most
\(7,8,9,1,1,1\), totaling \(27\).
\(\square\)

## 4. Enforcing full rank without losing the estimate

The previous expectation averages over all binary
generators, including the rare matrices whose columns
fail to span the message space. We now remove them
without appealing to numerical rank search.

**Lemma 8 (full-rank extraction).**
For \(L\ge10^{10}\), there is a binary
\(r\times m\) matrix of rank exactly \(r\)
whose codeword Gaussian maximum satisfies
\[
 \boxed{\displaystyle
 \mathbb E_G\max_u\langle v_u,G\rangle
 \ge\sqrt{2L}
      -\frac{\log L}{2\sqrt{2L}}
      -\frac{30}{\sqrt L}.}                  \tag{21}
\]

*Proof.* For any nonzero \(u\in\mathbb F_2^r\),
the probability that \(u\cdot g_j=0\)
for every \(j\) is \(2^{-m}\).
The rank-failure event is the union of
these events, hence
\[
 p_{\rm bad}\le(k-1)2^{-m}
       \le\exp(L-m\log2)\le L^{-2}
\]
for \(L\ge10^{10}\), since
\(\log2>2/3\) and \(m\ge L^2\).

For every fixed generator, each score
\(X_u\) is a standard normal. A Gaussian
union bound yields
\[
 \Pr_G(M\ge t)\le k e^{-t^2/2}
                    \quad(t\ge0).
\]
Moreover \(M\ge X_0\), so the negative
part satisfies \(M_-\le(X_0)_-\).
Integrating the positive tail at the
split \(\sqrt{2L}\), we get
\[
 \mathbb E_{g,G}M_+^2
   \le2L+2,\qquad
 \mathbb E_{g,G}M_-^2\le1.
\]
Therefore
\[
  \mathbb E_{g,G}M^2\le2L+3.
\]
By Cauchy–Schwarz,
\[
 \left|\mathbb E[M\mathbf1_{\{\operatorname{rank}<r\}}]\right|
 \le\sqrt{(2L+3)p_{\rm bad}}
 \le\frac2{\sqrt L}.
\]
Lemma 7 now shows that the
unconditional average of \(M\) over
**full-rank** matrices, normalized by
their probability, is at least the
right side of (21); the normalization
can only increase a positive lower
bound for all sufficiently large \(L\).
At least one full-rank matrix attains
this average or better. \(\square\)

## 5. Proof of the main theorem and optimal order

*Proof of Theorem 1.* Choose the full-rank
matrix of Lemma 8. Its score-max partition
has exactly equal masses by Lemma 2, and
\[
 kP(\mathcal A)\ge
   \left(\sqrt{2L}
       -\frac{\log L}{2\sqrt{2L}}
       -\frac{30}{\sqrt L}\right)^2.
\]
For \(L\ge10^{10}\) the bracket is positive.
Expanding the square and discarding
nonnegative terms gives
\[
 kP(\mathcal A)\ge
       2L-\log L-60\sqrt2
       \ge2L-\log L-85,
\]
since \(60\sqrt2<85\).

The scalar quantile ceiling
\[
        h(1/k)^2\le2L-\log L+3
\]
follows directly from Mills' inequalities.
Indeed, let \(t=\Phi^{-1}(1-1/k)>1\).
Then \(h(1/k)\le t+1/t\), so
\(h(1/k)^2\le t^2+3\); and
\(L\ge t^2/2+\log t+\tfrac12\log(2\pi)\).
If \(t^2\ge L\), this forces
\(t^2\le2L-\log L\). Otherwise
\(t^2<L\le2L-\log L\).
Thus the ceiling holds in both cases.
The individually optimal halfspace
upper envelope is \(U_k=h(1/k)^2/k\);
thus \(U_k-P(\mathcal A)\le88/k\).
Because \(F_\infty(k)\le U_k\),
\[
        P(\mathcal A)
           \ge F_\infty(k)-88/k
           \ge F_\infty(k)-100/k,
\]
proving (1).

For the optimal dimension order,
the independently established spherical-cap
converse says that any partition with
score at least \(F_\infty(k)-100/k\)
must, for all sufficiently large \(k\),
have
\[
                  d\ge\frac{(\log k)^2}{116}.
\]
Our construction has \(d=\lceil(\log k)^2\rceil\).
Restricting to the dyadic subsequence
\(k=2^r\) proves (2). \(\square\)


## 6. Binary-block completion for **all** cell counts

The dyadic theorem already determines the optimal dimensional
**order for all sufficiently large integers k**, using a
nonuniform one-dimensional *selector* and a bounded-entropy
binary expansion. This section removes the dyadic restriction.

Let \(r_0\) be the fixed exponent threshold in Theorem 1,
and set \(Q_0=2^{r_0}\).

**Lemma 9 (sharp binary-expansion entropy).**
Write any positive integer as a sum of distinct powers of two,
ordered strictly decreasing:
\[
       k=q_1+\cdots+q_s,\qquad
       q_j=2^{r_j},\quad r_1>\cdots>r_s\ge0,
\]
and put \(w_j=q_j/k\). Then
\[
 \boxed{\displaystyle
     H(w):=\sum_{j=1}^s w_j\log(1/w_j)
                     <2\log2\quad(s<\infty),} \tag{22}
\]
with equality approached as \(k=2^s-1\to\infty\),
so **the coefficient \(2\log2\) is best possible**.
Furthermore,
\[
        \sum_{j:q_j<Q_0}q_j<Q_0.              \tag{23}
\]

*Proof.* Since \(q_j\) is a power of two and
every subsequent \(q_\ell\) is a distinct smaller power,
\[
 \sum_{\ell>j}q_\ell\le q_j-1<q_j.
\]
Put \(S_j=\sum_{\ell\ge j}w_\ell\), \(S_{s+1}=0\).
Then \(S_{j+1}<w_j\), hence
\[
       \frac{S_{j+1}}{S_j}<\frac12,\qquad
       S_j\le2^{1-j}.
\]
Define \(\alpha_j=w_j/S_j\) and the
binary entropy function
\[
 h_2(t)=-t\log t-(1-t)\log(1-t),
          \quad 0\log0:=0.
\]
The exact entropy chain identity is
\[
 \boxed{\displaystyle
 H(w)=\sum_{j=1}^s S_j h_2(\alpha_j).}
\]
Indeed expansion of \(S_j h_2(\alpha_j)\) gives
\(-w_j\log w_j-S_{j+1}\log S_{j+1}
  +S_j\log S_j\), and the last two
terms telescope. Because \(h_2(t)\le\log2\)
for every \(t\in[0,1]\),
\[
 H(w)\le(\log2)\sum_{j=1}^s S_j
       \le(\log2)\sum_{j=1}^s2^{1-j}
       <2\log2.
\]
To see optimality, put \(k=2^s-1\),
so \(w_j=2^{s-j}/(2^s-1)\). For each
fixed \(j\), \(w_j\to2^{-j}\), and
the geometric bound above permits dominated
convergence in the entropy series. The
limiting geometric distribution has entropy
\(\sum_{j\ge1}2^{-j}j\log2=2\log2\).
Thus the coefficient cannot be improved.

Finally, the powers of two smaller than
\(Q_0=2^{r_0}\) have total sum at most
\(1+2+\cdots+2^{r_0-1}=Q_0-1\),
proving (23). \(\square\)

**Lemma 10 (one Gaussian coordinate glues exact mass blocks).**
Suppose \(k=\sum_jq_j\) with positive
integers \(q_j\), and for each \(j\)
there is a Gaussian partition
\(\mathcal B^{(j)}\) of a common
\(\mathbb R^m\) into exactly \(q_j\)
cells of measure \(1/q_j\), with
squared-first-moment objective \(P_j\).
There is then an exactly equiprobable
\(k\)-cell partition of
\(\mathbb R^{m+1}\) with objective
\[
 \boxed{\displaystyle
       P_{\rm glue}\ge
             \frac1{k^2}\sum_j q_j^2P_j.}    \tag{24}
\]

*Proof.* Take an independent standard
Gaussian selector \(T\in\mathbb R\)
and partition its real line into
Borel intervals \(E_j\) of probabilities
\(\Pr(T\in E_j)=q_j/k\).
Such intervals exist uniquely using
the continuous Gaussian CDF.

For every local cell \(B^{(j)}_u\),
define the final cell
\(A_{j,u}=E_j\times B^{(j)}_u\).
Independence gives
\[
 \gamma_{m+1}(A_{j,u})
        =(q_j/k)(1/q_j)=1/k.
\]
The first moment in the \(m\)
*data coordinates* equals
\[
 \int_{A_{j,u}}x_{\rm data}\,
      d\gamma_{m+1}
 =\frac{q_j}{k}\int_{B^{(j)}_u}
       x\,d\gamma_m.
\]
Summing squared norms over all
final cells yields exactly
\(\frac1{k^2}\sum_jq_j^2P_j\)
from the data coordinates.
Each cell's selector-coordinate
moment contributes a further
nonnegative square. This proves
(24). \(\square\)

**Theorem 11 (universal quadratic-logarithmic
dimension, all integers).**
With \(Q_0=2^{r_0}\) as above, take the explicit
threshold \(K_0=Q_0^2\). Then **for every**
integer \(k\ge K_0\),
writing \(L=\log k\), there is a
Gaussian partition of \(\mathbb R^d\)
into exactly \(k\) cells, each of
measure \(1/k\), with
\[
 \boxed{\displaystyle
       d\le\lceil L^2\rceil+1\le L^2+2,
       \qquad
       P(\mathcal A)\ge
                  F_\infty(k)-\frac{95}{k}.}
 \tag{25}
\]
More precisely, its objective meets
the universal one-cell halfspace envelope:
\[
 \boxed{\displaystyle
     U_k-P(\mathcal A)\le92/k.}              \tag{26}
\]

Let \(D_{92}(k)\) be the smallest
Gaussian ambient dimension allowing
an exactly equiprobable \(k\)-cell
partition with objective at least
\(F_\infty(k)-92/k\).
Combining (25) with the spherical-cap
dimension converse gives, for all
sufficiently large integers \(k\),
\[
 \boxed{\displaystyle
    \frac{(\log k)^2}{108}
    \ \le D_{92}(k)
    \ \le\lceil(\log k)^2\rceil+1.}          \tag{27}
\]
Consequently,
\[
 \boxed{\displaystyle
       D_{92}(k)=\Theta((\log k)^2)
       \quad(k\to\infty)
       \ \text{for all integers }k.}        \tag{28}
\]
This settles the **optimal order**
of dimensional growth for bounded
additive \(O(1/k)\) approximation of
the global equal-mass Gaussian
first-moment optimum.

*Proof.* Fix \(k\) and write its binary
expansion as in Lemma 9.
Take a common data Gaussian space
of dimension
\(m=\lceil L^2\rceil\).

For every binary block \(q_j\ge Q_0\),
Theorem 1's **proved construction**
has local dimension
\(\lceil(\log q_j)^2\rceil\le m\).
After padding with unused independent
Gaussian coordinates, it defines a
\(q_j\)-cell equiprobable partition in
the common space satisfying the
stronger *halfspace* estimate
\[
            P_j\ge\frac{h(1/q_j)^2-88}{q_j}.
                                                        \tag{29}
\]
Indeed the proof of Theorem 1
already obtained the stronger estimate
with \(88\) as displayed.

For a smaller block \(q_j<Q_0\),
choose any equiprobable Gaussian
\(q_j\)-partition of the same data
space, e.g. the consecutive quantile
intervals of its first coordinate.
Only the trivial bound \(P_j\ge0\)
is used for these blocks.

Apply Lemma 10. Let \(W_{\rm sm}\)
be the sum of \(w_j=q_j/k\) over
small blocks. Then
\[
 \begin{aligned}
 kP_{\rm glue}
 &\ge\sum_{j:q_j\ge Q_0}
           w_j\left(h(1/q_j)^2-88\right),\\
 h(1/k)^2-kP_{\rm glue}
 &\le 88+
     \sum_{j:q_j\ge Q_0}w_j
         \left[h(1/k)^2-h(1/q_j)^2\right]
        +W_{\rm sm}\,h(1/k)^2.
 \end{aligned}
\]
Define \(h(1)=0\), the continuous
extension of the upper-tail conditional
mean to the sure event. The squared Gaussian upper-tail
conditional mean is globally
2-Lipschitz in log tail mass:
for \(q_j\le k\),
\[
 0\le h(1/k)^2-h(1/q_j)^2
             \le2\log(k/q_j)
             =2\log(1/w_j).
\]
By Lemma 9, the total difference
term is at most
\(2H(w)<4\log2\).
Also \(W_{\rm sm}<Q_0/k\)
and the elementary Gaussian
exponential-moment bound gives
\(h(1/k)^2\le2L\).
Hence
\[
 h(1/k)^2-kP_{\rm glue}
       \le88+4\log2+\frac{2Q_0 L}{k}.
                                                        \tag{30}
\]
For \(k\ge K_0=Q_0^2\),
the function \(x\mapsto\log x/x\)
is decreasing on \(x\ge e\), so
\[
  \frac{2Q_0\log k}{k}
  \le\frac{4\log Q_0}{Q_0}<1.
\]
The last inequality holds for
\(Q_0\ge2^{10}\) by monotonicity,
since \(4\log(2^{10})/2^{10}
<40/1024<1\). Our \(r_0\) is
much larger than ten.
Since \(4\log2<3\) (as \(e^{3/4}>1+3/4+(3/4)^2/2>2\)), the right
side of (30) is strictly below
\(88+3+1=92\).
This proves (26). Because
\(F_\infty(k)\le U_k\),
(25) follows.

For the matching lower dimension,
the independently proved spherical-cap
converse says that for each fixed
additive tolerance \(C\), every
sufficiently accurate partition
must have dimension at least
\(L^2/(C+16)\).
Put \(C=92\) to obtain (27).
The sandwich proves (28). \(\square\)

### What is now resolved, and what remains

The order \(\Theta((\log k)^2)\) in (28)
is a **complete all-integer dimension-rate
classification at the level of orders**
for a fixed bounded \(1/k\) additive error.
The proof explicitly handles arbitrarily
many binary digits and includes extreme
binary-expansion boundary cases.

The theorem does not determine the
smallest possible dimensional *constant*,
the best additive-error constant,
the exact finite-\(k\) optimizer,
or efficient algorithms for the
binary generator matrices.
Those remain valid further research targets.

## 7. Source status and remaining global problems

Theorems 1 and 11 establish a **matching-order
quadratic-logarithmic dimensional law** for all
sufficiently large cell counts, not only dyadic
subsequences. The lower and upper constants
\(1/108\) and \(1\), and the additive error
\(92/k\), are not claimed sharp.

The only substantial external probabilistic
input is the classical Berry–Esseen inequality
for independent, non-identically distributed
summands. The Gaussian and finite-field
calculations are derived in detail here.
No numerical solver, simulation or optimizer
assertion is used as a theorem.

The matrix construction is by the probabilistic
method: an admissible finite full-rank binary
matrix is proved to exist for every sufficiently
large dyadic block, but efficiently computing it
is not established. The Gaussian selector and
binary expansion are explicit deterministic
operations once these matrices are fixed.

The **core dimension-order problem for fixed
bounded additive error is resolved at order level**.
Remaining open questions include the sharp
leading dimension coefficient, best additive
constant, effective polynomial-time construction,
stability and equality cases, and the exact
fixed-\(k\) Standard Simplex optimality question.
No historical world-first claim is made pending
full specialist literature comparison and
external peer review.

Proof-interface checks, attribution and
dependency limitations are recorded in
AUDIT.md and LITERATURE.md.
