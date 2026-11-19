# Weighted mean versus minimum for independent unequal laws

**Yongxian Zhang.** Research draft, November 19, 2026. AI-assisted and internally checked, not externally peer reviewed. The argument is analytic; no sampling, smoothness, densities, moment or lattice assumptions are used.

**Theorem (Feldheim–Feldheim, Conjecture 1).** Let X,Y be independent, finite, nonnegative random variables, each with unbounded support. For every fixed p in (0,1), set q=1−p and W=pX+qY. Then
$$
 \limsup_{t\to\infty}
    \frac{\Pr(W>t)}{\Pr(X>t)\Pr(Y>t)}=\infty .
$$
Equivalently, the conditional probability that both X and Y exceed t given that their weighted mean exceeds t has limit inferior zero. All thresholds t here are real and all survival tails use a strict inequality. No full-limit assertion is made.

Naomi D. Feldheim and Ohad N. Feldheim, [*Mean and minimum of independent random variables*](https://doi.org/10.1007/s11856-021-2195-0), [author text](https://u.cs.biu.ac.il/~feldhen/Papers/MinMean.pdf), proved the equal-weight two-variable case without identical laws (Thm. 1, a question of Alon); their Thm. 2 allows multiple positive weights and assumes identical laws. Their §1.1, Conj. 1 asks for the joint removal of these restrictions above. We use a finite concave envelope of inverse tail levels, a **truncated** exponential estimate, and random affine interpolation of the two tilted tails.

### 1. Assuming a bounded quotient

Suppose there is a finite C≥2 with
$$
 S_W(t)\le C S_X(t)S_Y(t)\qquad(t\ge0),                 \tag{1}
$$
where each S denotes the strict survival tail. Failure of the conclusion implies this eventual bound, and the constant can cover the remaining compact interval because both survival functions are nonincreasing and positive. Define f=−log(S_X S_Y), right-continuous, nondecreasing, finite everywhere and tending to infinity. At any t>0, the event X≥t,Y>t implies W>t, since q>0. By independence and (1), S_X(t−)≤C S_X(t). Symmetrically S_Y(t−)≤C S_Y(t), so all positive-time jumps of f are at most B=2 log C. For any x,y≥0 and z=px+qy, the strict rectangle X>x,Y>y lies in W>z, whence
$$
 S_X(x) S_Y(y)\le C S_X(z)S_Y(z).                       \tag{2}
$$

### 2. Long intervals nearly maximizing the tilted product at both ends

For each integer N≥2 we claim that there are 0<a<b and s>0 with s(b−a)≥N such that, writing M(t)=exp(st−f(t)) and $P=\sup_{[a,b]} M$,
$$
 \min\{M(a),M(b)\}\ge e^{-B-3}P.                          \tag{3}
$$
The intervals can start beyond any prescribed finite cutoff. Fix J greater than f at the cutoff and at zero and let Q_j=inf{t≥0:f(t)≥J+j}, j≥0. These finite points need not be strictly increasing, but tend to infinity since f is finite locally. Right continuity gives f(Q_j)≥J+j, and the left limit and jump bound give f(Q_j)≤J+j+B. All Q_j are positive and beyond the cutoff (by right continuity).

We first show there exist i<j with d=j−i≥N and h=(Q_j−Q_i)/d>0 such that
$$
 Q_r\le Q_i+h(r-i+2)\qquad(i\le r\le j).                 \tag{4}
$$
For the finite list (r,Q_r), 0≤r≤T, take its upper concave polygonal hull, the least concave majorant of its linear interpolation. It joins contact vertices at integer indices, including both endpoints, with slopes nonincreasing and nonnegative (the data are nondecreasing). A positive face of horizontal length ≥N gives (4) with no additive 2. Otherwise all positive faces have length <N. Starting at zero, group consecutive positive faces until their total length first reaches N; close each such group and repeat, leaving at most one incomplete group. The complete lengths lie in [N,2N), and the incomplete length is <N. Ignore the possible horizontal terminal face, which contributes no rise. If the first and last slopes of a complete group satisfy max/min≤1+1/N, its average h is positive and max−h≤h/N. The excess of its polygon over the secant is at most (max−h)d≤2h throughout; its contact endpoints yield (4).

If neither construction succeeds for any T, each complete group reduces the slope by a factor >1+1/N, and the initial positive slope is bounded by L=max_{1≤r≤N}(Q_r−Q_0)/r, independently of T (the first face, when positive, has length <N). Thus the entire rise, allowing the incomplete group and discarding any horizontal end, is at most
$$
  2N L \sum_{k\ge0}(1+1/N)^{-k} ,
$$
also independently of T. This contradicts Q_T→∞ and proves (4).

Set a=Q_i, b=Q_j, s=1/h. Then s(b−a)=d. For t∈[a,b] with f(t)<J+j, take r=floor(f(t)−J)+1. We have i+1≤r≤j and t<Q_r. From (4),
$$
  s(t-a)\le r-i+2\le f(t)-(J+i)+3 .
$$
If f(t)≥J+j the same bound follows from s(t−a)≤d. Consequently st−f(t)≤sa−(J+i)+3, while at both endpoints it is ≥sa−(J+i)−B. This proves (3) including flat intervals or repeated inverse levels.

### 3. Truncation gives bounded area for each factor

On an interval furnished by (3), set U(t)=exp(pst)S_X(t), V(t)=exp(qst)S_Y(t); UV=M. Divide these functions by their separate suprema over [a,b], giving u,v∈(0,1]. By (2) and the cancellation psx+qsy=sz,
$$
 U(x)V(y)\le C M(px+qy),\qquad
 u(x)v(y)\le C u(px+qy)v(px+qy)  .                        \tag{5}
$$
Taking separate suprema in the first inequality yields (sup U)(sup V)≤CP even if suprema are not attained. Therefore at either endpoint t=a,b,
$$
 u(t)v(t)\ge \eta:=e^{-B-3}/C.                             \tag{6}
$$
In particular each individual endpoint value is at least η.

For any finite nonnegative variable Z and c>0, integration of the increasing exponential gives the exact identity
$$
 \mathbb E[e^{c\min(Z,b)}{\bf1}_{Z>a}]
   =e^{ca} S_Z(a)+c\int_a^b e^{ct}S_Z(t)\,dt .             \tag{7}
$$
Indeed on Z>a integrate from a to min(Z,b) and use Tonelli. This also handles atoms at either endpoint. Apply (7) individually to X with c=ps and Y with c=qs, multiply, and retain the product of the integrals. On X>a, Y>a we have W>a and p min(X,b)+q min(Y,b)≤min(W,b). By independence, (7) for W, and (1),
$$
 pq s^2(\int_a^b U)(\int_a^b V)
 \le \mathbb E[e^{s\min(W,b)}{\bf1}_{W>a}]
 \le C\,[ M(a)+s\int_a^b M(t)\,dt ] .
$$
Divide by (sup U)(sup V), writing I_u=s∫u and I_v=s∫v; u,v≤1 imply
$$
 pq I_u I_v\le C(1+\min(I_u,I_v)).                          \tag{8}
$$
For every x≤y on the interval,
$$
 u(x)\ge u(y)e^{-ps(y-x)},\qquad
 v(x)\ge v(y)e^{-qs(y-x)},                                \tag{9}
$$
because the survival factors are nonincreasing. On the interval of length 1/s immediately to the left of b, each function is therefore ≥η/e. Thus min(I_u,I_v)≥η/e, and (8) implies a bound independent of the particular interval or N:
$$
 \max(I_u,I_v)\le A:=C(1+e/\eta)/(pq).                     \tag{10}
$$

### 4. Interpolation forces arbitrarily large area

Write α=−log u, β=−log v, w=α+β. Each is nonnegative, the two endpoint values of w are ≤D=−log η, and (5) gives
$$
 w(px+qy)\le \alpha(x)+\beta(y)+\log C .                    \tag{11}
$$
Start Z_0=a. At each step independently draw E uniformly from {a,b} and a fair role coin; set the next point equal to pZ_i+qE or pE+qZ_i according to the role. Average (11) over that role to obtain
$$
 \mathbb Ew(Z_{i+1})\le \tfrac12\mathbb Ew(Z_i)
                 +\tfrac12\mathbb Ew(E)+\log C .
$$
Induction bounds all these means by K=D+2log C. Hence every depth l has probability ≥1/2 of w(Z_l)≤H:=2K+1, on every interval under consideration.

After affinely normalizing the endpoints to 0,1, the support of Z_l is a finite set depending only on p,l. Every point in it has probability at most
$$
 c_l={l\choose\lfloor l/2\rfloor}/2^l .
$$
To see this, condition on all role coins. The normalized point is a subset sum of l strictly positive weights: at each step a fresh Bernoulli bit enters with a positive coefficient, and previous coefficients are multiplied by p or q, also positive. All subsets of a prescribed sum form an antichain for set containment, including when weights coincide or p is algebraic. This is the classical [Sperner–Littlewood–Offord argument](https://www.renyi.hu/~p_erdos/1945-04.pdf). Counting maximal chains in the Boolean lattice gives the bound: summing 1/binom(l,|A|) over an antichain counts the expected number of its elements on a uniformly ordered maximal chain, at most one. The conditional bound survives mixing over roles. Since c_l→0, the number of distinct good points w≤H is at least 1/(2c_l), uniformly in the interval.

For fixed l≥1 the normalized finite support contains 0 and at least one positive point; its minimum spacing δ_l is strictly positive, regardless of coincidences among histories. Now choose N≥2/δ_l and use Section 2. Any two distinct support points on [a,b] differ by ≥2/s. Except for a itself, the intervals of length 1/s immediately to the left of the good points lie inside [a,b] and are disjoint. At a good point z, u(z)≥exp(−H) because β≥0. By (9), u≥exp(−H−1) throughout its left interval. Thus
$$
 I_u\ge \big(1/(2c_l)-1\big)e^{-H-1}.
$$
As l→∞ this contradicts (10): first choose l to exceed the fixed bound there, then choose the interval, not vice versa. This proves the theorem.

### 5. Multiple positive weights

As already observed by Feldheim and Feldheim, Conjecture 1 suffices for a general positive weighted mean. Explicitly, take finite n≥2, positive weights summing to one, and independent nonnegative X_i with individual unbounded supports. Set U=X_1 and V=Σ_{i≥2}λ_i X_i/(1−λ_1). Then U,V are independent and unbounded, and P(V>t)≥∏_{i≥2}P(X_i>t). The weighted-mean quotient with the full product denominator is at least the two-variable quotient at every t, so it too has infinite limsup. No alignment of subsequences is needed. The grouping itself is not claimed as new. The claim is asymptotic along a sequence of real thresholds; it does not assert an unrestricted limit or any specified rate.
