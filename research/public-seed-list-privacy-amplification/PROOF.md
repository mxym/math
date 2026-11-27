# Joint and selected ideal states for a list of keys

## 1. Model

Let \(X\) be a finite classical variable shared by the honest
parties, with finite quantum side information \(E\) in a normalized
cq state. A classical public seed \(F\) is sampled independently of
\(XE\). The honest list is \(K=(K_1,\ldots,K_L)\), where
\(K_j=g_j(F,X)\) is deterministic conditional on \(F,X\) and has
alphabet size \(M_j=2^{\ell_j}\), \(\ell_j\ge1\).
Set \(b=\sum_j\ell_j\). The index \(I\), when used, is sampled
independently of \(K,F,X,E\); it may be public or remain private
as explicitly specified. All entropy units are bits.
Write \(T(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1\).

The ideal for the complete list is
\(U_K\otimes\rho_{FE}\), with \(U_K=\bigotimes_j U_{M_j}\).
Its error \(d_{\rm joint}\) compares this with \(\rho_{KFE}\).
For public selection the key can be compared with a uniform
value of its own length, conditioned on the disclosed index.
Without other keys disclosed, define
\[
 d_j^0=T(\rho_{K_jFE},\,U_{M_j}\otimes\rho_{FE}).
\]
With the entire complementary list disclosed, define
\[
 d_j=T(\rho_{K_jFEK_{-j}},\,U_{M_j}\otimes\rho_{FEK_{-j}}).
\]
Here \(K_{-j}\) is the remaining list in a specified order.
For an independent index law \(\Pr(I=j)=q_j\), the respective
errors with the index included in the side register are exactly
\(\sum_jq_j d_j^0\) and \(\sum_jq_j d_j\), by equality of the
trace norm with the sum over orthogonal classical sectors.
This is an equality, not a hybrid approximation. For differently
sized keys the first factors of the ideal output are controlled
by the disclosed index.

The model makes no statement about a data-dependent index that
selects a key for its value or about interactive preprocessing
that generates additional shared secret randomness. Authentication
of a public transcript does not remove it from the side information.

## 2. Joint list: necessary entropy scale and a positive guarantee

For a source uniform on a \(2^k\)-point set, with integer \(k\)
and trivial \(E\), fixing any public seed leaves at most \(2^k\)
joint list values. Testing membership in the actual support
against a uniform \(b\)-bit list gives
\[
 d_{\rm joint}\ \ge\ (1-2^{k-b})_+ .                         \tag{1}
\]
The same argument applies if a classical readable side register
makes the conditional source uniform on at most \(2^k\) points
for every side value. For any error \(\varepsilon<1\), the
necessary worst-case bound is \(b\le k-\log_2(1-\varepsilon)\).
The particular test here compares mathematical distributions,
not the operation of an implementation. Adding an independent
index after hashing does not change the \(K,F,E\) marginal.

Conversely, assume the \(L\) public hash choices are independent,
and for each \(j\) satisfy
\[
 \Pr_F[g_j(F,x)=g_j(F,x')]\le 1/M_j
       \quad (x\ne x').
\]
Then the complete map \(G_F(x)=(g_j(F,x))_{j=1}^L\) is
two-universal to \(2^b\) values, by multiplying the collision
probabilities. In particular, if \(H_{\min}(X|E)_\rho\ge k\),
\[
 d_{\rm joint}\ \le\ \frac12\sqrt{(2^b-1)2^{-k}}.            \tag{2}
\]
This is a direct application of ordinary quantum leftover
hashing to the **entire** concatenated output. The common
source does not provide independent key outputs conditional
on the disclosed seeds. For completeness, the following
fixed-marginal proof derives the quoted bound.

Write \(R_x\) for the subnormalized states of \(E\), \(\sigma=\sum_xR_x\),
and \(A_x=\sigma^{-1/4}R_x\sigma^{-1/4}\), inverse powers understood
on the support and as zero off it. Let \(Q=\sum_x\operatorname{tr}A_x^2\).
The operators \(V_x=\sigma^{-1/2}R_x\sigma^{-1/2}\) are a POVM on
the support of \(\sigma\), and \(\sum_x\operatorname{tr}R_xV_x=Q\).
Since conditional min-entropy is minus the logarithm of the optimal
guessing probability, \(Q\le2^{-k}\). Alternatively, from
\(R_x\preceq2^{-k}\eta\) for one state \(\eta\), the same inequality
follows by multiplying each such inequality by \(V_x\) under the
trace and summing.

Let \(M=2^b\) and \(A_z(f)=\sum_{x:G_f(x)=z}A_x\).
The sum of the output blocks is \(\sigma\); after weighting by
\(\sigma^{-1/4}\) the true ideal block is \(\sigma^{1/2}/M\).
If \(C_f=\sum_z\operatorname{tr}A_z(f)^2\), the weighted
squared distance is \(C_f-1/M\). Schatten Hölder, with exponents
\(4,2,4\) and outer factors \(I_M\otimes\sigma^{1/4}\),
gives the fixed-seed error at most \(\tfrac12\sqrt{M C_f-1}\).
Moreover \(\operatorname{tr}(A_xA_y)\ge0\) and
\(\sum_{x,y}\operatorname{tr}(A_xA_y)=1\), so two-universality gives
\(\mathbb E C_f\le Q+(1-Q)/M\). Jensen's inequality and the
classical seed direct-sum identity prove (2).
If one normalized cq approximation within trace distance \(\delta\)
satisfies the min-entropy bound, (2) holds for the original state
with an additional \(2\delta\): both the hashed real state and its
ideal side marginal change by at most \(\delta\). This optional
statement specifies the smoothing convention used here.

A jointly uniform list suffices for any of the stated selection
models by appending an independent \(I\) and then applying a
common channel to real and ideal states: select \(K_I\), disclose
\(I\) if desired, and copy any specified off-list records.
For a private index with equal lengths, use a compact ordered
list of off-list values with no missing-slot label. With unequal
lengths the lengths in the output may themselves reveal the
index, so we make no index-confidentiality claim in that case.
For a public index no encoding restriction is needed. In the ideal,
conditioned on the chosen index, the selected key is independent of all other keys
and of the seed and quantum side information. Without any other
keys disclosed, its ideal side marginal is the actual \(F,E\)
marginal, so \(d_j^0\le d_{\rm joint}\) by contractivity.
With the complementary list disclosed, the ideal produced by
the common channel has **uniform** complementary keys, rather
than the actual complementary-key marginal used to define \(d_j\).
A second comparison costs at most the distance between these
side marginals. In detail, with
\(d_{-j}=T(\rho_{FEK_{-j}},\rho_{FE}\otimes U_{K_{-j}})\),
\[
 d_j\le d_{\rm joint}+d_{-j}\le 2d_{\rm joint}.
\]
The first inequality is the triangle inequality after applying the
common channel, and the second follows by tracing out \(K_j\)
from the joint comparison. Averaging gives the analogous bound
for a public index. For a private index, use the same triangle
argument on the corresponding encoded side register, with the
uniform key controlled by the index retained in the mathematical
test. Exact joint uniformity gives zero in these comparisons.
None of this implies that authentication hides the index.

## 3. Selected-only: no other keys are disclosed

The exact direct-sum identity in §1 means a list with a public
independent selection has \(d_{\rm selected}^0=\sum_j q_jd_j^0\).
If each marginal hash is two-universal, each \(d_j^0\) is
bounded by (2) with \(b\) replaced by \(\ell_j\).
There is no addition of \(\log_2 L\) to the input entropy:
the same law of \(I\) appears on both sides of the ideal-state
comparison. This conclusion also applies if \(I\) is included
as an honest output register in the mathematical test, even
if it is not separately sent to the adversary.

For equal lengths, fixing \(F,I\) and applying the same support
argument to the selected key alone gives the flat-source bound
\(d_{\rm selected}^0\ge(1-2^{k-\ell})_+\). If some other state
comparison deletes \(I\) entirely, it is a different guarantee:
the parties must already share the hidden \(I\), and any secrecy
contributed by it must be charged as additional private input.
The statement here concerns a public \(I\), or the joint test
that retains it.

## 4. Selected key with all other keys disclosed

**Theorem (sharp conditional entropy sharing).** For any
deterministic list functions in §1, with arbitrary quantum side
information,
\[
 \sum_{j=1}^L\ell_j\left(1-\frac{d_j}{1-2^{-\ell_j}}\right)
       \le H(X|E)_\rho .                                    \tag{3}
\]
Thus at equal lengths \(\ell\) with a uniform public index and
all off-list keys disclosed, the error \(d=L^{-1}\sum_jd_j\)
satisfies
\[
 d\ \ge\ (1-2^{-\ell})
      \left(1-\frac{H(X|E)_\rho}{L\ell}\right)_+.             \tag{4}
\]
The coefficient and whole equal-length line are jointly
sharp as a statement depending only on the conditional
von Neumann entropy and output lengths.

### One-key entropy deficit from trace distance

Given any normalized cq state \(\tau_{ZD}\) with alphabet size
\(M\ge2\), put \(\sigma=U_M\otimes\tau_D\) and \(a=1/M\).
Every positive \(Z\)-block is bounded above by their sum
\(\tau_D\), so \(\tau_{ZD}\preceq M\sigma\).
Consequently \(\sigma=a\tau_{ZD}+(1-a)\omega\) for a density
operator \(\omega\). We use Audenaert's telescopic relative
entropy inequality
\[
 D(\eta\|a\eta+(1-a)\omega)\le-\log_2(a)\,T(\eta,\omega).
\]
For clarity, it follows by writing \(M_t=t\eta+(1-t)\omega\)
and differentiating the operator logarithm on the support of
\(\eta+\omega\). In nats the Fréchet derivative
\[
 \mathcal T_M(B)=\int_0^\infty(M+uI)^{-1}B(M+uI)^{-1}\,du
\]
is positive, self-adjoint under the trace, and maps \(M\) to
the identity on its support. Thus
\[
 \begin{split}
 -\tfrac d{dt}D_{\ln}(\eta\|M_t)
 &=\operatorname{tr}\eta\,\mathcal T_{M_t}(\eta-\omega)\\
 &\le t^{-1}\operatorname{tr}M_t\,\mathcal T_{M_t}((\eta-\omega)_+)
   =t^{-1}T(\eta,\omega).
 \end{split}
\]
For \(t<1\), restrict to the combined support; the endpoint has
\(0\le D_{\ln}(\eta\|M_t)\le-\ln t\) by monotonicity of the
logarithm under \(M_t\succeq t\eta\), with regularization if
needed. Integrate to 1 and convert to bits. No commuting
assumption is used.

Now \(T(\tau_{ZD},\omega)=T(\tau_{ZD},\sigma)/(1-1/M)\),
and \(D(\tau_{ZD}\|\sigma)=\log_2 M-H(Z|D)_\tau\).
We obtain, for \(d_Z=T(\tau_{ZD},\sigma)\),
\[
 H(Z|D)_\tau\ge\log_2 M\,(1-d_Z/(1-1/M)).
                                                               \tag{5}
\]
In particular \(d_Z\le1-1/M\) also follows directly from the
mixture representation.

### Entropy sharing and attainability

Apply (5) to each \(Z=K_j\) with \(D=(F,E,K_{-j})\).
Strong subadditivity says that conditioning on more registers
cannot increase the conditional entropy, so
\[
 \sum_j H(K_j|F E K_{-j})
     \le\sum_j H(K_j|F E K_{<j})
     =H(K|F E).
\]
Since \(K\) is determined by \(X,F\),
\(H(X|FE)=H(K|FE)+H(X|KFE)\); the last entropy is
nonnegative because \(X\) is classical. The independence of
\(F\) gives \(H(X|FE)=H(X|E)\). These inequalities give (3).
Averaging for equal lengths and also using \(d\ge0\) gives (4).
The entropy in (3) is the actual conditional von Neumann
entropy, not a lower bound on the conditional min-entropy.

For sharpness, take no seed, and let the side system carry a
classical flag \(Y\). With probability \(q\), the list is
a deterministic splitting of a uniformly random \(b\)-bit raw
string; otherwise \(X\) is a known constant string mapped to
a constant list. Thus \(H(X|Y)=qb\), and
\(d_j=(1-q)(1-1/M_j)\) for every \(j\), even including the
other keys. This gives equality in (3) for any \(h=qb\in[0,b]\),
including (4) for equal lengths. More generally, choose independent
classical flags \(Y_j\) with active probabilities \(q_j'\);
given all flags, choose each active input block independently
uniform and the inactive blocks constant. Include all flags in
\(E\), and use deterministic block projections for the list.
Then \(d_j=(1-q_j')(1-1/M_j)\) and
\(H(X|E)=\sum_j q_j'\ell_j\), so equality holds for every
prescribed vector of errors in the allowed box. This uses
flags in the side information, not any extra secret seed. When \(H(X|E)\ge b\), extra
raw randomness can be ignored and all errors can be zero.
There is also equality for a flat source with \(k=p\ell\) bits,
\(p\in\{0,\ldots,L\}\): allocate \(p\) independent uniform
keys and let the remaining keys be constants. If desired,
a publicly sampled random permutation of the positions gives
the same error averaged over the public seed for each \(j\).
These are mathematical attainability examples, not a claim
optimal over every source with the same entropy.

## 5. Public and private seeds in the cited preprint

The latest publicly located version of arXiv:2603.18097 is v1.
Its Definition 6 requires the honest list to consist of
independent uniform strings, and Definition 8's displayed
state does not name the seed. In Theorem 10, Hybrid 0 explicitly
averages out the seeds. In contrast, Theorem 12's proof
explicitly uses a public hash seed, and Remark 9 and §6.3
describe sending the selected index on an authenticated
channel. The cases cannot be treated as the same state or
used together for one entropy-length equivalence.

**If the seeds are omitted and genuinely private:** assume the
input domain has at least two points (or that the single input
has a uniform output over the seed as a separate hypothesis).
For each fixed \(x\), each \(F_j(x)\) is then uniform by the
one-point marginal of strong universality, and the draws
\(F_j\) are independent. Hence the entire list is
exactly uniform **even conditioned on \(X=x\)** after averaging
away these private seeds. Thus \(K,X,E,I\) has the full ideal
list marginal for every source, and the same holds with any
consistent ideal copies of off-list values. It is not a nontrivial
threshold or an “if and only if” rule in \(H_{\min}(X|E)\):
the honest parties must already share the unrevealed seed
randomness. On a domain with two distinct inputs, a strongly
two-universal family makes the pair of hash outputs at those
inputs uniform on \(M_j^2\) pairs. This pair is determined
by the seed, so the seed has support at least \(M_j^2\);
the independent seed tuple thus has at least \(2^{2b}\)
possible values. This lower bound is specific to the stated
strong-universality construction, not to the minimum cost of
sampling a private uniform list directly. For a public \(F\),
privacy is measured before
discarding its register, and this argument does not apply.

**If the seeds are public:** (1) refutes reading Theorem 10's
condition as a sufficient joint list guarantee. For example,
take a flat \(32\)-bit source, \(L=2\), \(\ell=17\), and
\(\varepsilon=1/16\). Its smooth min-entropy is at least \(32\).
The paper's sufficient condition is met since
\(17\le32+1-8-3=22\), but a list of \(34\) jointly uniform bits
has distance at least \(1-2^{32-34}=3/4>4\varepsilon\).
This holds for every actual public hash family used in this
deterministic model, without reference to its implementations.
Even if only the publicly selected key is tested with no
other disclosures, the flat-source obstruction in §3 excludes
a uniform additive \(\log_2 L\) gain. For instance, take any
raw register containing a flat \(8\)-bit source, \(L=2^{16}\),
\(\ell=10\) and the same \(\varepsilon\); the claimed condition
allows \(10\le13\), but the selected-only distance is at least \(3/4\).

The public-seed reading cannot use the hybrid at rendered lines
244–248: distinct hashes on the same raw string need not
produce a product state conditional on their public seeds, and
averaging an index does not divide a per-index error bound by
the number of indices. The lower estimate at 255–257 does not
follow from min-entropy of the source for a deterministic hash
output (whose alphabet alone bounds its min-entropy). Lines
258–261 do not introduce a new hash for the already formed pair,
and the common \(\log_2 L\) in the input-pair and output-pair
lengths cancels. In fact the proof of Theorem 12 at 297–304
already arrives at a length bound with no additive \(\log_2 L\).
These are statements about the proof's state comparisons.

If a protocol genuinely has independent shared secret randomness
\(S\) of \(s\) uniform bits, it can incorporate \(S\) as part of
its input to a proper two-universal hash. The guessing min-entropy
of \(XS\) is \(H_{\min}(X|E)+s\) before any disclosure of \(S\).
Conversely, for the flat-source family, if \(S\) has support
at most \(D\) then the list has support at most \(2^kD\) for
fixed seed and readable side value, so \(\log_2D\) is exactly
the maximum support allowance attributable to that extra resource.
The entropy-sharing converse also applies with \(XS\) as input,
or with any extra public data in the conditioning register after
its disclosure. In this last use no independence simplification
of the conditional entropy is made unless warranted.
The original independent \(I\) is selected after all \(K_j\) are
computed and is therefore not an out-of-model source of entropy
for the complete list.

The model distinctions, the positive guarantees, and the sharp
entropy-sharing bound are separate from any physical or network
security claim. We make no assertion about implementing an
attack, or about all other proposed list-key functionalities
or device-independent/CV key-distribution models.
