# Exact one-ciphertext TDSS for a uniform target

## 1. Model and statement

Let M be a message drawn from a finite target distribution P; K is independent
and uniform on [k]={1,...,k}. An encoder is a finite randomized channel from
(M,K) to C, and the decoder sees (C,K). Private randomness local to the
algorithms is allowed, without a second shared secret. In the model of
Su–Cheng–Wang [SCW], correctness is perfect. In the separately defined error
extension here, require Pr[Dec(C,K)=M] >= 1-delta for delta in [0,1], averaging
over M,K and coins. All logarithms used to discuss key size are base 2, but k
itself is the number of possible keys, not a bit length.

For a predicate A (a subset of the message alphabet), write q_C(A) for its
posterior probability. The optimal Bayes guess for a Bernoulli probability x
has success 1/2+|x-1/2|. Thus the prediction gain is

    g_A = E_C |q_C(A)-1/2| - |P(A)-1/2|.                         (1)

The all-predicate TDSS is max_A g_A. The predicate is fixed before observing C;
only the prediction can depend on C. By E q_C(A)=P(A) and convexity every
g_A>=0. When P(A)<=1/2, identity (1) also equals
2 E_C [(q_C(A)-1/2)_+]. Complementing A never changes g_A.

**Theorem 1 (uniform target).** Let P be uniform on [N], with N,k>=1. If k>=N
the minimum TDSS is zero, with perfect correctness. Otherwise define

    m = floor(N/2),  s = max(k/N,1-delta),
    H ~ Hypergeom(N, m, k),
    hypergeom meaning Pr[H=h]=binom(m,h)binom(N-m,k-h)/binom(N,k).

The minimum TDSS is

    D(N,k,delta)
      = E |(s/k)H + [(1-s)/(N-k)](m-H) - 1/2| - |m/N-1/2|.      (2)

It is attained with success exactly s on every fixed message-key pair. In
particular the infimum is unchanged if the error bound is instead required on
every pair. For perfect correctness use s=1. For any epsilon>=0, the uniform
perfect-correct key-space requirement in [SCW] is exactly the least k in
[1,N] for which (2), with the stated endpoint at k=N, is at most epsilon.

### Converse

For a posterior vector q on [N], let S_k(q) be the sum of its k largest
entries. A deterministic decoder at a fixed c names at most k different
messages as the key varies. Its conditional success is at most the posterior
mass of that list, hence at most S_k(q_c). A randomized decoder cannot improve
on the deterministic Bayes decoder at each (c,key) because its conditional
success is a convex combination of point guesses. Therefore
E_C S_k(q_C) >= 1-delta. Also S_k(q)>=k/N by averaging the largest k entries.
These two bounds give E S_k(q_C)>=s.

For r=0,...,N define F_r(q) to be the average of |q(A)-1/2| over all r-element
subsets A. This is symmetric and convex. Put
Q(u)=(u/k repeated k times, (1-u)/(N-k) repeated N-k times).
For any fixed q, sort it and average its permutations that act separately on
the first k and last N-k coordinates. The average is Q(S_k(q)); symmetry and
Jensen give F_r(q)>=F_r(Q(S_k(q))). Since Q is affine, averaging over C gives

    E_C F_r(q_C) >= F_r(Q(E_C S_k(q_C))) >= F_r(Q(s)).            (3)

For the last step, u->F_r(Q(u)) is convex on [k/N,1], and its minimum is at
k/N: averaging all permutations of any q gives the uniform vector, so F_r
at uniform is no bigger than at q. A convex function with a minimum at the
left endpoint is nondecreasing (write any intermediate point as a convex
combination of the left endpoint and the later point). Ties in ordering are
irrelevant.

The maximum in (1) is at least the mean over all fixed predicates of size m.
Subtracting their common prior baseline in (3) gives (2): the number of
members of an m-set among the k top coordinates of Q(s) has the displayed
hypergeometric law (equivalently, count intersection with a uniformly random
k-set). No predicate is chosen in response to a particular ciphertext.

### Attainment

For k<N the ciphertext is an ordered k-tuple of distinct elements of [N].
On input (x,j), in a branch of probability s choose the tuple uniformly
subject to c_j=x. In the remaining branch choose it uniformly with x absent.
The decoder returns c_j. The branches are feasible even at k=N-1 and k=1,
and conditional success on each pair is exactly s.

Write (a)_b=a(a-1)...(a-b+1), with (a)_0=1. For a fixed tuple c, uniformity
of the key gives Pr[c|x, first branch]=1/[k (N-1)_(k-1)] if x is in c, zero
otherwise. In the second branch it gives 1/(N-1)_k if x is absent, zero
otherwise. Averaging over uniform x gives 1/(N)_k in both branches: use
(N)_k=N (N-1)_(k-1) and (N-1)_k=(N-k)(N)_k/N. Bayes' rule now says

    q_c(x) = s/k if x occurs in c, (1-s)/(N-k) otherwise.         (4)

In particular a ciphertext samples a uniform k-subset when order is ignored.
By relabeling symmetry g_A depends only on |A|. For r<=N/2, (1) is twice
E[(q_C(A)-1/2)_+], which is nondecreasing with r by taking nested sets; use
complements for r>N/2. Consequently the worst g_A occurs at r=m, and (4)
gives exactly (2). The success extension treats real channel probabilities;
for rational delta, all the constructive probabilities are rational. No
fixed number of fair random bits is imposed.

For k>=N, on input (x,j) let the ciphertext be a uniformly random injection
phi:[N]->[k] subject to phi(x)=j. The decoder returns its inverse at j, or
a fixed message when j is outside the image. For each x, the fraction of all
injections with phi(x)=j is 1/k for every j. Hence averaging over the uniform
key makes phi independent of x, and correctness is perfect. This is also the
constant-posterior case of [SCW, Lemma 5]. N=1 is included.

## 2. Zero predicate gain and the perfect-correct recurrence

For 1<=k<N, put s as above. Then (2) vanishes precisely in the following cases:

* N even: s=k/N.
* N odd, N=2m+1, k<=m: s<=(k+1)/(N+1).
* N odd, N=2m+1, k>=m: s<=min(1,k/(N-1)).

The two odd formulas agree at k=m, where the threshold is 1/2. For proof,
(1) says zero gain is equivalent to q_C(A)<=1/2 almost surely for a fixed
m-set A. The uniform k-set of (4) can attain the largest possible intersection
min(k,m) with A, with positive probability. Because the in-set mass is at
least the out-of-set mass for s>=k/N, the largest m-set posterior mass is

    T = s + (m-k)(1-s)/(N-k)  if k<=m;
    T = m s/k                if k>=m.

For N even and s>k/N, (4) has two unequal levels, and the average of the
largest m entries is strictly greater than the overall average 1/N: the two
groups of the first m and last N-m have different averages, since the list is
sorted, is nonconstant, and both groups are nonempty. Thus T>1/2, while at
s=k/N equality holds. For odd N, solving T<=1/2 gives the displayed formulas.
At perfect correctness the least key size giving zero is N for even N, N-1
for odd N>=3, and 1 for N=1. This is a statement about prediction gain, not
Shannon secrecy: for odd N>=3, the N-1-subset posterior actually excludes a
message even though no Boolean predicate gains. E.g. N=5 gives perfect-correct
values 2/5,1/10,1/10,0,0 for increasing keys 1 through 5.

Write D_N(j)=D(N,j,0). For N>=2 and 1<=j<N,

    D_N(j)-D_N(j+1)
       = 0                                             if j is even;
       = Pr[H_(j+1)=(j+1)/2]/(2j)                      if j is odd,   (5)

where H_(j+1) counts the m-set elements in a uniform (j+1)-subset of [N].
This includes j+1=N because D_N(N)=0 and the N-subset empirical mass equals
m/N. To prove (5), remove a uniform entry from the (j+1)-subset. The remaining
subset is uniform among j-subsets. Given original count h, its empirical
mass is (h-1)/j with probability h/(j+1) and h/j otherwise; conditional
mean h/(j+1). For h=0 or h=j+1 only one value is possible. The Jensen gap
for |x-1/2| is zero unless the two values strictly straddle 1/2, which
occurs exactly when j is odd and h=(j+1)/2. There both occur with probability
1/2 and have absolute deviation 1/(2j), while the mean is exactly 1/2.
The prior baseline cancels in (5).

## 3. Sharp universal constant for perfect correctness

For a finite P, let D_P(k) mean the infimum TDSS over perfectly correct
target-dependent ciphers with a uniform k-element key, not over source-oblivious
ciphers shared by different P. Then for k>=1 and r=floor(k/2),

    sup over finite P of D_P(k) = b_k = binom(2r,r)/(2*4^r).       (6)

The supremum here is over domain sizes as well; no maximum or fixed domain
size is asserted. As k tends to infinity, b_k is asymptotic to 1/sqrt(2*pi*k).

For the upper bound, use [SCW, SampleEnc, Lemma 1]: put x in the key coordinate
and independently fill all other coordinates from P. Under M~P its ciphertext
has distribution P^k independently of the key. Each posterior is its
empirical distribution. For a fixed predicate of prior p, its gain is
E|B/k-1/2|-|p-1/2| for B~Bin(k,p). By (1) for p<=1/2 this equals
2 E[(B/k-1/2)_+], nondecreasing in p by coupling k Bernoulli variables through
the same uniform draws. Complements handle p>=1/2, so the maximum over any
p is the fair-binomial value. For the lower bound, in (2) let N tend to
infinity through even integers with fixed k. A uniform ordered sample without
replacement is an iid uniform sample conditioned on all entries being
distinct; the conditioning event has probability at least 1-binom(k,2)/N
by the collision union bound. Thus the hypergeometric expectation converges
to the same binomial value, and the prior baseline is zero for every even N.

For the closed form, write W_k for a sum of k independent fair signs. The
fair-binomial value is E|W_k|/(2k). For even k=2r>=2, reflect the negative
values and telescope using
(2h-2r) binom(2r,h)=2r[binom(2r-1,h-1)-binom(2r-1,h)].
This yields E|W_(2r)|=(2r) binom(2r,r)/4^r. On adding one independent sign,
conditional absolute value changes in expectation only at W_(2r)=0, where
it increases by 1. Dividing by 2(2r+1) proves the same expression (6) for
odd k; for k=1 use W_0=0. The asymptotic follows from Stirling's formula.

## 4. Exact finite variational form for other priors and predicate classes

This subsection concerns average correctness only. Fix any finite P and any
nonempty class F of predicates. Restrict the label domain to supp(P), of
size N, as only positive-probability inputs affect the quantities; the
construction can use separate ciphertexts for any excluded inputs if required.
Let h=min(k,N) and S_h(q) be the top-h posterior mass.

**Posterior-law lemma.** A finite law assigning probabilities w_a to
posterior probability vectors q_a can be realized by a finite randomized
cipher with uniform independent k-element key and average success at least
1-delta iff

    sum_a w_a q_a = P,   sum_a w_a S_h(q_a) >= 1-delta.           (7)

Necessity is Bayes plausibility and the fixed-ciphertext list bound already
proved. For sufficiency use the following joint sampling description. Draw
a with law w; draw M from q_a; choose a fixed set T_a of h largest entries
(with deterministic tie handling). Independently of M given a, choose a
uniform injection phi:T_a->[k] and let C=(a,phi). When M is in T_a set
K=phi(M); otherwise choose K uniformly on [k]. Since every injected
message's image is also uniform across phi, K is uniform independently of
(a,M), and the marginal M is P. Conditioning the joint law on (M,K) gives
a legal encoder. At ciphertext (a,phi) the posterior is q_a and the decoder
returns the inverse when defined, or an arbitrary fixed element of T_a
otherwise. If k<=N then h=k and phi is onto, so exactly the inputs in T_a are
decoded correctly; if k>N then h=N and all are decoded correctly. This realizes
average success exactly sum_a w_a S_h(q_a). At delta=0 this recovers the
posterior-law criterion of [SCW, Lemma 5], since S_h(q_a)=1 for all w_a>0.

To give a finite LP, intersect the probability simplex with each set of
inequalities q_i>=q_j for i in a designated h-set T and j outside T, and
with one of q(A)>=1/2 or q(A)<=1/2 for each A in F. These finitely many
closed polytope cells cover the simplex; discard empty cells, and call V the
union of their vertices. On each cell the top-h mass and all the functions
|q(A)-1/2| are affine, including ties. Replace each posterior in that cell
by a mixture of its vertices with the same barycenter; this preserves every
relevant average. Thus the optimum is exactly the minimum of t subject to

    w_v>=0,  sum_v w_v=1,  sum_v w_v v=P,
    sum_v w_v S_h(v) >= 1-delta,
    sum_v w_v |v(A)-1/2| - |P(A)-1/2| <= t   for every A in F.     (8)

Conversely every feasible law in (8) is realized by (7). There are finitely
many variables and compact feasible weights; the optimum is attained. If
one starts from a general posterior distribution instead of a finite one,
assign shared boundary points to the first covering cell, average within
each positive-weight cell, and then apply the same vertex decomposition.
This proves that allowing arbitrary output alphabets cannot improve the
optimum where posterior laws are defined. It does not claim a practical LP
or sharper explicit nonuniform bounds. At perfect correctness for any F,
(8) can equivalently use only the k-sparse simplex faces as its starting
cells; this part is a direct piecewise-linear consequence of [SCW, Lemmas
2 and 5]. In particular it is an exact finite form of the approximate
posterior optimization discussed in their conclusion, not a resolution of
all bounds requested there.
