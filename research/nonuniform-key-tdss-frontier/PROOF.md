# Exact nonuniform-key TDSS for a uniform target

## 1. Model

Fix \(N\ge1\), a uniform message \(M\in[N]\), and an independent key \(K\)
with a finite probability vector \(\pi\). Remove zero-probability keys
and label the remaining \(k\) in nonincreasing order. A randomized encoder
uses private randomness, with no extra shared secret. Perfect correctness
requires that for each message and positive-probability key the decoder
returns that message on every emitted ciphertext (almost surely in a general
alphabet). A decoder given only \((C,K)\) may be taken deterministic:
if two distinct positive conditional messages were possible at \((c,i)\),
a randomized decoder there could not be almost surely correct. For discrete
ciphertexts one may fill unobserved pairs arbitrarily. The lower bound also
applies to general ciphertext alphabets where the finite conditional
posteriors are defined by conditional expectations.

For a predicate specified by \(A\subseteq[N]\), let \(q_C\) be the posterior
of \(M\). Prior Bayes success is \(1/2+\big|\,|A|/N-1/2\,\big|\) and posterior conditional
success is \(1/2+|q_C(A)-1/2|\). The gain for this one fixed predicate is
\[
g_A=\mathbb E |q_C(A)-1/2|-\big|\,|A|/N-1/2\,\big|.
\tag{1}
\]
This is precisely the single-ciphertext TDSS objective of Su–Cheng–Wang
(SCW), with the variation that \(\pi\) need not be uniform. The predicate
is chosen before observing \(C\); the guessing rule may depend on \(C\).
For \(|A|\le N/2\), Bayes plausibility \(\mathbb E q_C(A)=|A|/N\)
rewrites (1) as \(g_A=2\mathbb E(q_C(A)-1/2)_+\). Complementation
preserves \(g_A\).

## 2. The attainable least-majorant profile

For a probability vector \(x\), let \(S_j(x)\) be the sum of its largest
\(j\) entries, with zeros appended beyond its length. Write \(x\preceq y\)
if \(S_j(x)\le S_j(y)\) for all \(j\). Among length-\(N\) probability vectors
majorizing \(\pi\), the least in this order is the following \(w\).
If \(k\le N\), use \(\pi\) padded with zeros. Otherwise choose \(r<N\) by
starting at \(r=0\) and increasing \(r\) as long as
\(\pi_{r+1}>(1-\sum_{i\le r}\pi_i)/(N-r)\). Stop and write
\[
b=\frac{1-\sum_{i\le r}\pi_i}{N-r},
\qquad w=(\pi_1,\ldots,\pi_r,\underbrace{b,\ldots,b}_{N-r}).
\tag{2}
\]
The procedure must stop by \(r=N-1\), where the threshold is the total
remaining mass. Every accepted entry exceeds the threshold at its selection,
which decreases upon selection; thus the retained entries exceed \(b>0\),
and all remaining keys have mass at most \(b\). Ties are in the equalized
group and do not change \(w\). This is the previously known majorant
\(R_N(\pi)\) of Cicalese–Gargano–Vaccaro when \(k>N\). For completeness:
\(S_j(w)=S_j(\pi)\) for \(j\le r\), and for \(r<j\le N\), the added mass
\((j-r)b\) is at least the corresponding sum in \(\pi\). If \(z\) is any
sorted \(N\)-vector that majorizes \(\pi\), then for \(r\le j\le N\),
\[
S_j(z)\ge S_r(z)+\frac{j-r}{N-r}(1-S_r(z))
       \ge S_r(\pi)+\frac{j-r}{N-r}(1-S_r(\pi))=S_j(w).
\tag{3}
\]
The first inequality is the decreasing-coordinate property, including
\(r=0\) with \(S_0=0\). Together with \(j\le r\) this proves minimality.
When \(k\le N\), minimality of the padded vector follows directly by
definition.

**Posterior converse.** Let \(\theta_C\) be the posterior of \(K\).
At a fixed ciphertext the distribution \(q_C\) groups the masses
of \(\theta_C\) by their decoded message. Consequently the total posterior
mass of any \(j\) designated keys is at most \(S_j(q_C)\): those keys
occupy at most \(j\) message bins. Apply this at every ciphertext to the
\(j\) keys with largest *prior* masses and take expectations:
\[
S_j(\pi)\le \mathbb E S_j(q_C)=S_j(v),\qquad v=\mathbb E q_C^\downarrow.
\tag{4}
\]
For \(j\ge N\) the inequality is automatic; for \(k<j<N\) take all
keys, which occupy at most \(k\le j\) message bins.
The mean of the sorted vectors is sorted. By (3) and its \(k\le N\) case,
\(w\preceq v\). Hence for every symmetric convex real function \(\Phi\)
on the \(N\)-simplex for which the expectations exist,
\[
\mathbb E\Phi(q_C)\ge\Phi(v)\ge\Phi(w).
\tag{5}
\]
The first inequality is Jensen after sorting and the second is the
standard majorization characterization: a vector majorized by another is
a convex combination of permutations of the latter (the
Hardy–Littlewood–Pólya theorem).

**Exact attainment.** When \(k\le N\), use one auxiliary key-posterior
vector \(\theta=\pi\). When \(k>N\), set \(m=N-r\). The light-key
inclusion marginals \((\pi_i/b)_{i>r}\) are in \([0,1]\) and sum to \(m\).
The polytope
\[
\{x\in[0,1]^{k-r}:\ \sum x_i=m\}
\]
is the convex hull of the incidence vectors of the \(m\)-subsets.
Indeed, any nonintegral point has at least two fractional entries, and a
small transfer in either direction between the entries precludes extremality.
Thus choose a finite law \(p_S\) on \(m\)-subsets of light keys with these
marginals; its support may also be reduced by Carathéodory to at most
\(k-r\) subsets since the polytope is in one affine hyperplane. For subset
\(S\) let \(\theta^S\) have mass \(\pi_i\) on each retained heavy key,
mass \(b\) on \(S\), and zero on the other keys. Every \(\theta^S\)
has the same multiset of positive masses and pads to \(w\).
The mean \(\sum_S p_S\theta^S=\pi\) holds coordinate by coordinate.
In the \(k\le N\) case regard the single vector as also indexed by \(S\).

For each \(S\), let \(D_S\) be the support of \(\theta^S\); use a uniformly
random injection \(\varphi:D_S\to [N]\) and give the public ciphertext
the label \(c=(S,\varphi)\). To specify the joint law, put
\[
\Pr(M=j,K=i,C=(S,\varphi))=
\frac{p_S}{(N)_{|D_S|}}\theta_i^S\,1\{i\in D_S,\ \varphi(i)=j\},
\tag{6}
\]
where \((N)_\ell=N(N-1)\cdots(N-\ell+1)\) counts injections.
Each component table has at most one nonzero entry in each key column,
so the decoder uses \(\varphi(i)\) on every possible encoded pair. For any
\(i\in D_S\), exactly a \(1/N\) fraction of injections send it to \(j\).
Summing (6) over ciphertexts therefore gives \(\pi_i/N\). Consequently
conditioning (6) on \((j,i)\) realizes a legal randomized encoder with the
prescribed independent inputs. In sampling terms, choose \(S\) given the
actual key \(i\) with probability \(p_S\theta^S_i/\pi_i\) and choose the
injection uniformly subject to \(\varphi(i)=j\). This uses finite
ciphertext support and can have arbitrary real channel probabilities; it
does not require a fixed finite number of fair coins. For rational \(\pi\),
the subset law and channel may be chosen rational.

At \(c=(S,\varphi)\) the message posterior places key masses
\(\theta^S_i\) on their distinct images; it is \(w\) up to permutation.
Its conditional law given \(S\) is invariant under message permutations
because \(C\) in (6) is uniform in \(\varphi\) given \(S\).
It follows that (5) is attained simultaneously for every \(\Phi\)
in its stated class. The construction does not claim to preserve
key secrecy; for instance, the auxiliary label may give information
about the actual key.

## 3. Exact all-predicate frontier

For \(a=\lfloor N/2\rfloor\) let
\(\Phi_a(x)=\binom Na^{-1}\sum_{|A|=a}(x(A)-1/2)_+\).
It is symmetric and convex. The largest \(g_A\) is at least its mean
over the predicates of size \(a\). Equations (1) and (5) bound that mean
below by \(2\Phi_a(w)\). Under (6) the gain of every fixed predicate
depends only on its size. For sizes \(s\le a\), take an increasing chain
of fixed subsets. Its posterior masses increase pointwise, and the hinge
is increasing at each fixed posterior. Hence the gain is nondecreasing
in \(s\) on this range. Complementation handles the rest. Thus the
worst gain equals the mean at size \(a\), proving the formula in README.

For \(k>N\), grouping the terms by the selected heavy-key subset \(B\)
gives the alternative exact sum
\[
\frac{2}{\binom Na}\sum_{B\subseteq[r]}
\binom{N-r}{a-|B|}\left(\sum_{i\in B}\pi_i+(a-|B|)b-\tfrac12\right)_+ ,
\tag{7}
\]
with an out-of-range binomial coefficient zero. The half-subset average
is zero exactly when \(S_a(w)\le1/2\), because all subsets carry positive
probability. For \(N=1\) every gain is zero. For even \(N\ge2\), the
largest \(N/2\) entries have sum at least \(1/2\), with equality only for
the uniform vector: the individual differences between top and bottom
halves in sorted order are nonnegative, and if all vanish, ordering
forces all entries equal. The least majorant \(w\) is uniform exactly
when \(\pi_1\le1/N\) (equivalently, the uniform vector majorizes \(\pi\)).
For odd \(N\), zero gain need not mean uniform posteriors: e.g.
\(N=3,\pi=(2/5,3/10,3/10)\). Distinguish this from Shannon secrecy.

If \(\pi\) is uniform on \(k<N\) keys then \(w\) is uniform on \(k\) of its
\(N\) slots. The half-subset sum is \(H/k\) with \(H\) hypergeometric with
parameters \((N,a,k)\), giving the already-known perfect-correct uniform-key
result. If \(k\ge N\) and \(\pi\) is uniform then \(w\) is uniform on all
\(N\) messages. In contrast, for \(N=4\) the six masses
\((40,12,12,12,12,12)/100\) give \(w=(.4,.2,.2,.2)\) and gain \(1/10\);
\((40,35,20,2,2,1)/100\) give \(w=(.4,.35,.2,.05)\) and gain \(2/15\).
Both laws have the same support size and min-entropy; those two statistics
do not determine the exact optimum. We do not claim the closed formula
for a nonuniform message prior, an arbitrary restricted predicate class,
or encoders with decoding errors.

## 4. General finite priors: an application of the known decoder-vector LP

For arbitrary finite \(P\) and fixed independent \(\pi\), a finite exact
optimization is immediate from Su–Cheng–Wang ePrint 2026/2192 Appendix B.4
and a change of objective. We include it solely to specify where the
closed result does and does not depend on uniform \(P\). Use the
decryption-vector labels \(d=(d_1,\ldots,d_k)\) over the message alphabet,
and variables \(x_{d,i}\ge0\) with
\(\sum_{d:d_i=j}x_{d,i}=P_j\pi_i\). If a key/cipher pair has no mass,
its entry of the decryption vector can be filled arbitrarily.
Merge ciphertexts with identical vectors; Jensen applied to (1)
shows that no fixed predicate gain can increase. Conversely any set of
these variables describes a uniquely decodable channel by conditioning
its column-unique tables on the message-key pair. Inputs of zero prior
probability, if still required to be decoded, can be given disjoint
tags that never occur in the source experiment.

Write \(x_d=\sum_i x_{d,i}\), \(y_{d,A}=\sum_{i:d_i\in A}x_{d,i}\).
Introduce \(z_{d,A}\ge0\) satisfying
\(z_{d,A}\ge y_{d,A}-x_d/2\) and \(z_{d,A}\ge x_d/2-y_{d,A}\).
For a prescribed nonempty finite predicate class \(\mathcal F\),
minimize \(\tau\) with
\[
\sum_d z_{d,A}-|P(A)-1/2|\le\tau\qquad(A\in\mathcal F).
\]
The two linear inequalities give the smallest \(z_{d,A}=|y_{d,A}-x_d/2|\);
substituting recovers (1), including \(x_d=0\). The objective is therefore
exact; it is not a new representation of correct channels or an efficient
algorithm in bit lengths. The empty class may be assigned zero gain.
