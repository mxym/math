# Exact classical minimax error for strong extraction

All alphabets are finite and `TV(p,q) = (1/2) sum_x |p(x)-q(x)|`. A seed is independent of the source and always part of the output tested. For a seed S and maps f_s, the error is TV((f_S(X),E,S), U_D times the actual law of (E,S)), where U_D is uniform on D symbols. This is the average over (E,S) of the conditional total variation, not the error after averaging out S.

## 1. One fixed flat-source benchmark (classical)

For uniform X on K points and a D-symbol output, a map with preimage counts c_y on those K points has distance (1/(2K)) sum_y |c_y-K/D| from uniform. The best over maps that may know the flat support is

    b(K,D) = r(D-r)/(KD), where r = K mod D.                  (1)

Indeed, if two counts differ by at least two, move one unit from the larger to the smaller. Convexity of |t-K/D| implies the sum cannot increase. Iteration terminates as the sum of squared counts strictly decreases. The resulting D-r counts floor(K/D) and r counts ceil(K/D) give (1). These counts are feasible, including K<D, r=0 or D=1. Revealing an independent seed cannot improve on (1), because its conditional errors are averaged. For classical E with X|E=e uniform on K_e points, any hash's error is at least sum_e Pr[E=e] b(K_e,D); this is attainable when the supports are pairwise disjoint and the map can be tailored to their partition. We do not assume it is simultaneously attainable on general overlapping supports.

## 2. Source-oblivious exact classical minimax

Here X=[N], E is any finite classical variable, D>=1 is any output alphabet size, and the error is the total variation to U_D times the actual joint marginal of E and S. Minimize worst-case error over all independent finite public seeds and deterministic maps per seed. There is no bound on seed alphabet size. A seed uniformly distributed over a finite non-power-of-two alphabet is permitted; in the model of arbitrarily many but fixed fair bits, the displayed value remains the infimum by dyadic approximation and exact attainment is not asserted. The approximation is uniform in the source: the strong error is an average of costs in [0,1] over the seed, so perturbing the seed distribution changes it by at most the total variation between the two seed distributions.

Let C be any nonempty class of joint laws closed under permuting the labels of X by a common permutation for every E value. Take an arbitrary balanced map h:[N]->[D] (bin sizes differ by at most one), and choose a uniformly random permutation pi of [N]; use h composed with pi. **This same family is minimax for every C.** In particular, it is source-oblivious. Here and below minimax is over all public-seed families, not just over two-universal families.

Proof. For a fixed input law and conditional distribution p_e on X, define

    G_e(a) = average over uniform a-subsets A of |p_e(A)-1/D|.

Its discrete second difference G_e(a+2)-2G_e(a+1)+G_e(a) is nonnegative for 0<=a<=N-2. Draw an a-subset A and ordered distinct i,j outside uniformly. The marginals of A union {i} and A union {j} are uniform (a+1)-subsets, and their union with both added is a uniform (a+2)-subset. Put t=p_e(A)-1/D, u=p_e(i)>=0, v=p_e(j)>=0. The difference is the average of |t+u+v|-|t+u|-|t+v|+|t|, which is nonnegative because the increment |t+v|-|t| is nondecreasing in t for v>=0. This works for any nonnegative p_e and, by the same increment argument, any convex scalar function in place of the absolute value.

For any deterministic h with bin sizes a_1,...,a_D, the distance averaged over a uniform relabeling of X is (1/2) sum_y sum_e Pr[E=e] G_e(a_y): each preimage is individually sent to a uniform subset of its size. Discrete convexity and the unit transfer argument in Section 1 show that balanced sizes minimize this average for every fixed joint law. Now take any seed family and a fixed law in C; average its error over all permutations of the law. This average is at least the balanced-family error at that law. Some permuted law in C has error at least the average, proving the converse by taking the supremum over original laws. The balanced family achieves the value because its error is invariant under permuting the input. This proves the claim also at N=1 or D=1.

The balanced family is already collision-two-universal for N>=2: for fixed distinct x,x' its collision probability is sum_y a_y(a_y-1)/(N(N-1)), at most (ceil(N/D)-1)/(N-1) <= 1/D. The last inequality follows from D(ceil(N/D)-1) <= N-1. The same minimax value therefore obtains if one further restricts competitors to collision-two-universal families. Exact pairwise uniformity is not required or asserted.

**K-flat value.** For 1<=K<=N write a=floor(N/D), v=N mod D. Let H_{N,b,K} be the size of the intersection between a fixed b-subset and a uniform K-subset. Its mass at c is binom(b,c) binom(N-b,K-c)/binom(N,K), with out-of-range binomials zero. The formula for the law follows by choosing c elements inside and K-c outside. The minimax strong error on the class of all K-flat laws (no E) is exactly

    V_K = [(D-v) E |H_{N,a,K}-K/D| +
                v E |H_{N,a+1,K}-K/D|] / (2K).               (2)

Omit the second term when v=0, especially if a=N. This follows by conditioning the balanced map on a fixed flat support and permuting the labels. It is also the exact value for the no-E class with p_max<=1/K: the vertices of the capped simplex are K-flat. To see this, a vertex cannot have two coordinates strictly between 0 and 1/K (transfer a sufficiently small signed mass between them); it cannot have exactly one because the other coordinates are integral multiples of 1/K and their sum with it is 1. Convexity of the error and the converse on K-flat laws give equality.

**Single-atom expression when D divides N.** For 1<D dividing N and 1<=K<N the value (2) also equals

    (1-1/D) (N-K)/(N-1) Pr[H_{N-2,N/D-1,K-1}=floor(K/D)].    (3)

To see this, let b=N/D, w_c=Pr[H_{N,b,K}=c], and t=floor(K/D)+1. The balance of consecutive binomial coefficients gives

    w_c (b-c)(K-c) = w_(c+1) (c+1)(N-b-K+c+1)

for all c in the support, with zero flux at the outer endpoints. The difference between the two factors at state c, (b-c)(K-c)-c(N-b-K+c), is Kb-Nc. Sum the identity over c>=t to telescope, obtaining E[(H_{N,b,K}-K/D)_+] = w_t t(N-b-K+t)/N. The same identity holds if the upper sum is empty: both sides are zero. Expanding w_t, the numerator is b(N-b) binom(b-1,t-1) binom(N-b-1,K-t)/binom(N,K). In (2), replace the absolute deviation by twice the positive deviation because the mean is K/D, and use binom(N-2,K-1)/binom(N,K)=K(N-K)/(N(N-1)). This gives (3). If K=N and D divides N, the error is zero directly.

**Arbitrary cap without side information.** For g in [1/N,1], let K=floor(1/g) and r=1-Kg. If r=0, the minimax error is (2). If r>0, necessarily K<N. The vertices of the capped simplex have K atoms of mass g and one more atom of mass r: the same small-transfer argument gives at most one unsaturated nonzero atom, and normalization fixes these masses. The balanced-family error is convex and invariant under permutations, so its worst error is the common value on these vertices. For a uniform b-subset of [N], let J be the indicator that it contains the residual atom and H count its heavy atoms. Then J is Bernoulli with mean b/N and conditional on J=j, H is the intersection of a uniform (b-j)-subset of [N-1] with the fixed K-point heavy set. Only compute conditional laws at positive-probability values of J. Defining

    W(b) = E |g H + r J - 1/D|,

the exact minimax error is ((D-v) W(a)+v W(a+1))/2, with the same a,v and zero-term convention as (2). This is an explicit finite formula for every real cap, not just reciprocal integers.

## 3. Classical side-information value

For g in [1/N,1], allow all finite joint laws with guessing probability sum_e Pr[E=e] max_x Pr[X=x|E=e] <= g. Equivalently their average conditional min-entropy (negative log base two of the guessing probability) is at least -log2(g). Then the exact minimax value is the finite linear program

    max sum_{j=1}^N lambda_j V_j
    subject to lambda_j>=0, sum lambda_j=1,
                sum lambda_j/j<=g.                          (4)

One or two j suffice because an extreme solution to these two aggregate constraints cannot have three positive variables (a nonzero signed perturbation preserving both sums would be feasible in both directions). Equivalently this is the upper hull of the points (1/j,V_j), maximized up to horizontal coordinate g.

For the upper bound, fix a positive-probability E=e, sort p_e in decreasing order and put p_e(N+1)=0. The distribution decomposes as a mixture of uniform laws on its first j points with weights j(p_e(j)-p_e(j+1)). This identity follows by telescoping each coordinate. Its weights sum to one and their weighted 1/j averages to p_e(1). Refining E with this mixture label leaves guessing probability unchanged and can only increase the error, since forgetting a classical label is contraction and forgets the same ideal marginal label. The balanced family has error V_j per refined flat conditional law, giving (4). For the matching lower bound for any seed family, choose the maximizing lambda, draw j according to lambda and a uniform j-subset A; set E=(j,A) and choose X uniform on A. This law has the required guessing probability. By the balancing proof the average error of **each** seeded map over A is at least V_j, so every family has error at least (4). This also specifies a single law for the lower bound independently of which seed family is chosen. No side information of any specific system is being modeled.

Example: N=4,D=2 gives (V_1,V_2,V_3,V_4)=(1/2,1/6,1/6,0). At g=1/2 a mixture with weights 1/4 on j=1 and 3/4 on j=3 yields 1/4, and each point satisfies V_j <= (1/j)/2, so 1/4 is optimal. The corresponding no-E capped class only has value 1/6. Thus one cannot generally replace the average-guessing optimum by the single flat K=1/g value. These finite minimax evaluations are for classical side information; we do not claim that noncommuting quantum side information has the same frontier.
