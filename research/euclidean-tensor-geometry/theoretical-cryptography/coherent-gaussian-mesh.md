# Coherent Gaussian aliases and parity in ideal Fourier sampling

**Scope.** In the positive quantum sampling step of [Regev, Lemma 3.14](https://cims.nyu.edu/~regev/papers/qcrypto.pdf), reused in [Peikert–Regev–Stephens-Davidowitz, Lemma 6.7](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf), an ideal finite Fourier transform produces amplitudes proportional to a periodized Gaussian. Measurement squares a *sum* of amplitudes; folding an ideal discrete Gaussian instead *sums their squares*. Regev's proof controls the error for a sufficiently fine grid and then unwraps. We compare the two exact quotient laws, identify their leading difference and the parity-sensitive product threshold. This does not design a state-preparation, decoding or unwrapping algorithm, or analyze any implementation or scheme.

## 1. Exact positive interference

Fix a full-rank Euclidean lattice L, and let R grow through positive integers. Write a(x)=exp(-pi ||x||^2), Z=sum_(x in L) a(x)^2, and use the quotient L/RL. For y in that quotient let

    Q_R(y) = (1/Z) sum_(x in y+RL) a(x)^2,
    P_R(y) proportional to (sum_(x in y+RL) a(x))^2.

Q_R is the ideal folded mass. For P_R, the Fourier-series coefficients of a periodized continuous Gaussian on the dual lattice are a(x) up to a common factor. Sampling at the R-division points and applying the finite Fourier transform aliases indices in the same class modulo RL, which yields the specified amplitudes before measurement. This is exactly the ideal intermediate expression after equation (16) in Regev; no approximate state construction is assumed.

Completing the square in two alias terms gives

    P_R=(Q_R+C_R)/(1+delta_R),   delta_R=sum_y C_R(y),
    C_R(y)=sum_(0 != v in L) c_(R,v)(y),
    c_(R,v)(y)=exp(-pi R^2||v||^2/2)/Z
                 * sum_(x in y+RL) exp(-2pi ||x+Rv/2||^2).  (1)

Indeed each ordered pair of distinct lifts differs by Rv. Where R is even, (1) is exactly convolution of Q_R with the law of Rv/2 modulo RL, for v on L with weight proportional to exp(-pi R^2||v||^2/2), including v=0. This additive perturbation is supported on the quotient's elements of order at most two. No analogous convolution is asserted in odd parity.

Let lambda be the shortest length of L, M a set with one representative of each +/- pair of shortest vectors, and

    b_R=exp(-pi R^2 lambda^2/2),    eta=R mod 2.

Along a fixed parity,

    TV(P_R,Q_R)/b_R ->
        (2/Z) sum_(v in M) sum_(a in L-eta v/2) exp(-2pi ||a||^2).
                                                                    (2)

## 2. Product threshold on an arbitrary fixed lattice

Let D be the number of independent copies of this fixed lattice block, and define the boundary intensity

    kappa_eta = (2/Z) sum_(v in M)
                  sum_(a in L-eta v/2 : <v,a>=0) exp(-2pi ||a||^2).
                                                                    (3)

If D b_R tends to tau in [0,infinity), then

    TV(P_R^(tensor D),Q_R^(tensor D))
       -> TV(Poisson(2 kappa_eta tau), Poisson(kappa_eta tau)).        (4)

When kappa_eta>0 and D b_R tends to infinity, the product TV tends to one. Even parity always has kappa_0>0 (take a=0). Odd parity can have none or can still have a positive intensity: for example an A2 root lattice has a nearest vector v and a lattice vector w with <v,w>=||v||^2/2, so w-v/2 is a permitted boundary offset. The scale in (4) is at fixed lattice shape, not a guarantee uniform over changing geometries.

**Proof.** The dominant terms in (1) are those with ||v||=lambda. The theta sums over L+Rv/2 depend only on the parity of Rv modulo 2L, so are bounded uniformly. If lambda_2 is the next distinct nonzero lattice length, the total of all longer-shift masses is O(exp(-pi R^2 lambda_2^2/2)); this follows from absolute summability at R=1. The total mass of each shortest pair is exactly b_R times its factor in (2). The normalized cross-term law C_R/delta_R concentrates near the residues Rv/2+a where v belongs to M and a is in a bounded set. Under Q_R each such region has probability tending to zero: the nearest lift has length at least R lambda/2-O(1), by the triangle inequality and the shortest-vector property. Making the bounded set larger captures arbitrarily close to the entire limiting cross-term mass. Hence TV(C_R/delta_R,Q_R) tends to one, and (2) follows from (1).

Fix v in M. For the combined contribution of v and -v, put m=Rv/2, f(a)=exp(-2pi||a||^2), and let a range over (y-m)+RL using any representative of the residue y. Then exactly

    C_(R,v pair)(y) = (2 b_R/Z) sum_a f(a),
    Q_R(y) = (b_R/Z) sum_a f(a) cosh(2pi R <v,a>).           (5)

The two exponential terms in the cosine average give the same wrapped sum: they correspond to the lifts m+a and -m+a, differing by Rv. Cauchy–Schwarz therefore gives

    sum_y C_(R,v pair)(y)^2/Q_R(y)
       <= (4 b_R/Z) sum_(a in L-eta v/2) f(a)/cosh(2pi R <v,a>).

The bound also works if the numerator is restricted to any subset of the offsets, with the sum on the right restricted to that subset. In particular, the contribution of offsets with norm greater than K can be made arbitrarily small relative to b_R, uniformly in R, by taking K large. Of the bounded offsets only those satisfying <v,a>=0 can contribute at the b_R scale.

For bounded a, the two distinct lifts +/-Rv/2+a are the only possible leading terms in Q_R. In fact the two shortest lifts of v/2 modulo L are exactly +/-v/2: equality at any other lattice point in the triangle inequality against v/2, with minimum lattice length lambda, is impossible. The other lift lengths have a fixed positive gap after rescaling by R. Also bounded-offset residues for distinct v in M are disjoint for sufficiently large R, since two nonopposite shortest vectors cannot be equal modulo 2L (their half-sum and half-difference would both be nonzero lattice vectors and their squared lengths sum to lambda^2). At a bounded perpendicular offset, (5) gives

    Q_R([Rv/2+a])/b_R -> (2/Z) f(a),    P_R/Q_R -> 2.       (6)

Here contributions from all other shortest midpoints are exponentially smaller, since their centers differ by a distance comparable to R on the quotient. The same is true of all longer shifts in total L2 scale: for each ordered shift Cauchy–Schwarz gives c_(R,v)(y)<=Q_R(y), so ||c_(R,v)/sqrt(Q_R)||_2^2<=sum_y c_(R,v)(y). Summing square roots of the longer-shift masses bounds their combined L2 norm by O(exp(-pi R^2 lambda_2^2/4))=o(sqrt(b_R)). This also justifies ignoring those terms when proving (6).

For K fixed, let B_K consist of the perpendicular-offset residues in (6) with ||a||<=K. Compare P_R to a law P_(R,K) that doubles Q_R on B_K and rescales its restriction to the complement proportionally so that the total is one. On B_K the weighted squared difference with denominator Q_R is o(b_R) by (6). Off B_K it is bounded by o(b_R) plus C b_R times the summed Gaussian tail for ||a||>K, by (5), the longer-shift estimate, and the normalization term O(delta_R^2). Here P_(R,K) is at least Q_R/2 for all large R. Accordingly these weighted squared differences also bound the squared Hellinger distance to P_(R,K) up to an absolute factor. For D b_R bounded, the product TV cost tends uniformly to zero as K tends to infinity, by tensorizing Hellinger.

For the simplified product, the count of coordinates in B_K is sufficient for the likelihood. The count is binomial with probabilities Q_R(B_K) and 2Q_R(B_K), respectively, and Q_R(B_K)/b_R tends to the finite K sum in (3). Standard binomial-to-Poisson convergence in TV, then K tending to infinity, proves (4), including kappa_eta=0. If kappa_eta>0 and D b_R tends to infinity, the count in a single active residue has means under the two laws in ratio tending to two and variances at most of order D b_R. Comparison at a point between the means gives TV tending to one.

## 3. Odd mesh on a line: the next, Gaussian, window

Take L of rank one with squared step length lambda^2, and put theta=pi lambda^2 and Z=sum_(j in Z) exp(-2 theta j^2). If R is even, (4) has kappa_0=2/Z. If R is odd, kappa_1=0, and the exact next nontrivial window is

    D b_R exp(-theta R) -> tau in [0,infinity].

In this window the product TV tends to the following, with the endpoint at tau=infinity interpreted as one:

    2 Phi(sqrt((8 exp(-theta/2)/Z) tau)/2)-1,               (7)

where Phi is the usual normal CDF.

**Proof.** In coefficient coordinates choose a centered representative u of y-R/2 modulo R, a half integer with |u|<=R/2. The nearest two midpoint offsets have u=+1/2 or -1/2. Here b_R=exp(-theta R^2/2), and from (5) at either of those residues

    Q_R(y) ~ (b_R/Z) exp(theta R-theta/2),
    C_R(y) ~ (2 b_R/Z) exp(-theta/2).

The first expression is dominated by the shorter of the two adjacent lifts; any other lifts are exponentially smaller. Uniformly over residues the shortest-pair cross term is at most C b_R exp(-2theta u^2), by a one-dimensional periodized Gaussian tail, and Q_R(y) is at least (b_R/Z) exp(2theta R |u|-2theta u^2). The remaining shifts contribute negligible weighted L2 error even on the scale b_R exp(-theta R), by the longer-shift bound above since their lengths are at least 2lambda. Thus outside the two nearest offsets the sum of squared cross terms divided by Q_R is O(b_R exp(-3theta R))+o(b_R exp(-theta R)). Normalization has smaller squared error because delta_R=O(b_R). It follows that

    chi^2(P_R||Q_R) ~ (8 exp(-theta/2)/Z) b_R exp(-theta R).

In addition, max |P_R/Q_R-1|=O(exp(-theta R)): the shortest-pair terms satisfy this by the same pointwise bounds, and the remaining cross mass is uniformly negligible using min Q_R>=b_R/Z. Write U=P_R/Q_R-1 under Q_R. For positive finite tau the sum of independent log(1+U) over the D blocks has the Gaussian limit N(-v/2,v) with v=(8 exp(-theta/2)/Z)tau. Indeed E U=0, the sum of squared terms concentrates by the uniform bound, the third-order remainder is o(1) in mean, and the first-order sum obeys the bounded-increment central limit theorem. Evaluating TV as E_Q (1-exp(log likelihood))_+ gives (7). At tau=0 product chi-squared tends to zero. At tau=infinity the one-copy affinity is 1-(1+o(1)) E U^2/8, and the product overlap tends to zero.

In particular, the one-copy exponential asymptotic (2) alone does not describe the correct high-dimensional comparison, even for product lattices: the even mesh produces a Poisson critical window, whereas the odd mesh on a line produces a smaller error scale and a Gaussian critical window.

## Reproduction

    node verify-coherent-gaussian-mesh.js

The verifier checks the Gaussian energy identities and a lattice's half-coset boundary witnesses exactly, and replays synthetic Fourier transforms, overlap formulas, and one-copy/fixed-radius asymptotics numerically. No cryptographic instances, private data or actual quantum devices are involved.
