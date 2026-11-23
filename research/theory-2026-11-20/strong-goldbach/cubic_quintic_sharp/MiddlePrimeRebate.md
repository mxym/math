# A true middle-factor prime rebate for the cubic–quintic score

Use the literal \(H=V-\Pi\), target units, fixed even \(N\), actual intervals \(NJ\) and \(N(1-J)\), \(L=\log N\) and \(M=|J|N\mathfrak S(N)\) of the [sharp cubic–quintic detector](CubicQuinticSharp.md). Put
\[
 A(n)=[-H(n)]_+1_{\{N^{.040}<P^-(n)\le N^{.105}\}}.
\]
The **actual prime crosses** satisfy, in each orientation,
\[
       \langle A,\Pi\rangle>.0333M+o(M),\qquad
       \langle\Pi,A\rangle>.0333M+o(M).                       \tag{1}
\]
There is no binary hypothesis. The genuine signed union where at least one arm is in this negative support is therefore bounded below by
\[
 (-4m(A)+.0666)M-\langle A,A\rangle+o(M),                  \tag{2}
\]
by the exact one-arm transfer of the [negative-arm union](NegativeArmUnion.md). Thus (1) improves the prime rebate in that exact identity; it is not a claim that the subtracted positive overlap or the rest of the original exterior is paid. These are prime-cross credits arising in the transfer, not an extra positive product of the original \(H\) on rows with a prime argument, where \(H\) is zero. The magnitude in (1) is measured on actual ranks 3 through 6 with two named true least factors. In particular it does not use the support of a negative-arm prime rebate with least factor \(>.105\) or at most \(.040\).

## 1. Actual over-root lower sieve with a named factor slot

Fix an ordered angular cell \(t_0<t_1\le v_0<v_1\), with the smaller prime \(p\) in \((N^{t_0},N^{t_1}]\), the larger prime \(q\) in \((N^{v_0},N^{v_1}]\). All cells below have width \(.001\), \(t_0\ge.040,\ t_1\le.105,\ v_1\le.170\). Put
\[
 B=.499+v_0/2,\qquad E=B-t_1-v_1,\qquad
 z=\max((1-t_0-v_0)/5,v_1)+.0001 .
\]
We use only \(E>2z\). Then the count on the literal prime arm \(y=N-x\), weighted by \(\log y\), with \(x=pqm\), \(P^-(m)>N^z\), and \(x\) squarefree, is at least
\[
 \frac{M}{L}\left(\frac{2\log(E/z-1)}{E}
      \int_{t_0}^{t_1}\frac{dt}{t}\int_{v_0}^{v_1}\frac{dv}{v}+o(1)\right).
                                                               \tag{3}
\]
In particular the counted \(p,q\) are the unique two actual least primes, not two arbitrarily chosen divisors.

Here the lower linear sieve on \(m\) uses Iwaniec's modified well-factorable lower weights of level \(N^E\) up to \(N^z\), in the form recalled in [Lichtman, §6.1](https://arxiv.org/html/2309.08522v1#S6.SS1). Their usual lower constant is \(F_{\rm low}(s)=2e^\gamma\log(s-1)/s\) for \(2<s\le4\). For their use at genuine moduli \(pq d\) we give the actual splitting rather than assuming that multiplying by two prime tags preserves triply well-factorable support.

Use [Lichtman, Proposition 5.2](https://arxiv.org/html/2309.08522v1#S5) with the literal residue \(a=N\) and length \(\asymp_J N\); the proposition permits \(|a|<X^{1+\epsilon}\). Apply the proof-level Heath–Brown reduction in his §3 with \(k=3\). Explicitly, write \(\Lambda\) on the actual central prime interval (with true \(N^{1/(\log\log N)^3}\)-rough support, which does not remove central primes), then split its at most six variables dyadically. If a factor has length between \(X^{10^{-5}}\) and \(X^{1/3+10^{-5}}\), it is the genuine small factor with length \(Y\) and the Siegel–Walfisz condition in Proposition 5.2. The Möbius/constant/log factors with the subpower rough filter obey that condition as in the cited proof; all other factor weights can be collected in the other block. There are the same two long-factor alternatives as in §3: with only one long free variable use his Lemma 3.4 since \(B\le.584<1-6\cdot10^{-5}\); with two long free variables use Proposition 3.2 since \(B<2/3-6\cdot10^{-5}\). In both alternatives the weight is bounded by a fixed divisor power on the grouped moduli. Proper prime powers in the original \(\Lambda\) terms, if introduced, occur at \(O(N^{1/2+o(1)})\) genuine \(y\)'s, each with divisor-power multiplicity, and likewise cost power-small in the models.

For the moderate-\(Y\) case set \(A_0=Y N^{-10^{-6}}\), \(P_+=N^{t_1}\), \(D=N^E\). A plain two-way well-factorable decomposition of \(\widetilde\lambda^-\) at **one of the following splits** gives the requisite three coefficients:
* If \(A_0\ge P_+\), split \(d=d_1d_3\) at \(A_0/P_+\) and \(DP_+/A_0\). Put \(q_1=p d_1,\ q_2=q,\ q_3=d_3\).
* If \(A_0<P_+\), split at \(A_0\) and \(D/A_0\). Put \(q_1=d_1,\ q_2=q,\ q_3=p d_3\).

Each division scale is at least one: \(A_0>1\), \(D>P_+\), and \(D P_+=N^{B-v_1}>N^{.4}>Y\) for these cells. These are exact signed convolutions, with a genuine prime indicator in the second coefficient and a single genuine prime convolution in one of the other two. The support for any coprimality to \(N\) is a product of conditions on the three slots, so it does not couple them. Intersecting with dyadic cells afterwards preserves independence. Fixed divisor-power coefficient bounds can be truncated at \((\log N)^C\) and normalized as in §5 of Lichtman: a discarded modulus coefficient is then supported on a large \(\tau(pqd)\), and the trivial progression count \(O(N/(pqd))\), together with divisor moments, pays any fixed logarithmic reserve. For the genuine HB variable weights, use the real clipping argument at the beginning of the proof of his Proposition 3.1, preserving the SW condition. Product cutoffs on the actual prime interval are separated by his Lemma 4.2 (or its Hilbert-kernel proof), with fixed log losses and no power loss.

Now \(Q_1\le A_0\), \(N^{v_0}/2\le Q_2\le N^{v_1}\), and \(Q_3\ll N^{B-v_1}/A_0\). With \(\theta=7/32\) and \(\varepsilon=10^{-7}\) in Proposition 5.2 the first constraint follows from \(Y/A_0=N^{10^{-6}}\). For the next three constraints the logarithmic exponents are at most, up to \(o(1)\),
\[
 \begin{split}
  & 2\cdot10^{-6}+2B-v_1 < .999,\\
  & 2B+3v_1+\theta+10^{-6}<1.9,\\
  & 2B+3v_1+2\theta(B-v_0-v_1)+(1+2\theta)10^{-6}<1.935.
 \end{split}
\]
These give the required strict margins, using \(B=.499+v_0/2\), \(B\le.584\), \(v_1\le.170\). Thus the true signed remainder on these three factors is \(O_C(N/\log^C N)\) for any fixed \(C\). In this proof \(q_2\) is the actual larger named prime; it has not been replaced by a well-factorable surrogate.

The sieve identity uses the physical condition \(d\mid m\), or equivalently \(pq d\mid x\), including repeated factors. Terms with \(d\) sharing \(p\) or \(q\) occur only on physical \(x\)'s divisible by a square of a prime \(\ge N^{.040}\). Their total is \(O(N^{.960+o(1)}+N^{.170+o(1)})\) with all genuine divisor and log multiplicities. Their principal reciprocal cost is power-small as well, by \(\sum_{p>N^{.040}}1/\varphi(p^2)\ll N^{-.040+o(1)}\) times fixed log powers. Thus the subsequent local model really factors \(1/\varphi(pqd)=1/(\varphi(pq)\varphi(d))\) on the retained terms. Removing all such overlaps is equivalent in the positive lower count to requiring genuine squarefree \(x\); additional squares of quotient primes \(>N^z\) cost \(O(N^{1-z+o(1)}+N^{1/2+o(1)})\). A genuine prime \(y\mid N\), or a named \(p,q\mid N\), is either absent by units or contributes only the usual negligible omitted harmonic/spatial cost. The lower sieve's dimension-one density on the remaining literal residue is \(1/(\ell-1)\) for \(\ell\nmid Npq\), with the local correction at \(p,q\) of size \(1+o(1)\). Its product is \((1+o(1))e^{-\gamma}\mathfrak S(N)/(zL)\), with the usual even-target root at 2 accounted for by the target mask. Multiplying by \(F_{\rm low}(E/z)\) and the genuine reciprocals of \(p,q\) proves (3). There is no per-fixed-\((p,q)\) equidistribution claim.

## 2. Guaranteed negative score on the actual counted sources

Write \(t,v\) for the own-log angles of the two actual least factors, \(s=t+v\), \(X_0=1-t_1-v_1\) and \(X_1=1-t_0-v_0\). The fixed true restrictions \(z>v_1\) and \(5z>X_1\) ensure the remaining quotient has from one to four prime factors. Thus the entire lower source consists of actual squarefree ranks 3 through 6. As usual central own-log versus target-log angles differ by \(O_J(1/L)\); all needed physical rank/least margins are strict, and replacing lower amplitudes by the calculated cell bounds costs only \(o(1)\) on the normalized scores.

Rank 3 has negative magnitude bounded below by
\[
 K_3=16t_0v_0X_0\{5(t_0^2+v_0^2+X_0^2)-3\}
\]
on cells where this is positive, by the exact odd formula. Rank 5 has negative magnitude at least \(K_5=1920t_0v_0z^2(X_0-2z)\). For rank 6 use the exact centered box-density expression in the negative-arm proof:
\[
 H_6/\log x=\left(\prod u_i\right)\{96 b_6''(0)-3840 b_6(0)\}.
\]
The density is symmetric and unimodal, with \(b_6''(0)\le0\) and \(b_6(0)\ge1\) because it is supported on an interval of length 1. Thus its negative magnitude is at least \(K_6=3840t_0v_0z^3(X_0-3z)\). These product lower bounds follow by concentrating all slack in one quotient angle, the minimum of the product with a fixed sum and a common lower bound \(z\).

For rank 4 let \(W\) be the centered sum of independent uniforms of the four actual widths; this is a deterministic finite-difference representation of the detector, not a model of paired prime factors. Four distributional derivatives of \(F\) give
\[
  \frac{H_4}{\log x\,\prod u_i}=96b_4(0)-1920\,\mathbb E|W|.
\]
At fixed actual \(t,v\), this expression is maximized when the two free remaining widths are equal. Indeed for two uniforms with fixed sum of widths, the density of the equal-width pair minus that of the unequal pair has at most one sign change on the positive half-line, from plus to minus: the unequal density is flat in the center and then has a larger linear shoulder. The equal pair therefore gives larger probability on every centered interval. Convolution with the remaining symmetric unimodal density preserves that order, since the probability of a centered interval under a translate of that density is symmetric decreasing in the translation and admits a centered-interval layer representation. Thus equalizing increases the central value and decreases \(\mathbb E|W|\).

Set \(G(t)=2|1-2t|^3-|1-2t|^5\). For equal remaining widths \(w=(1-s)/2\), the folded actual score is \(1-G(t)-G(v)-2G(w)+G(s)+2G((1+t-v)/2)\). All arguments used in the last two terms are in \([0,1/2]\); \(G\) is decreasing there. A rational cell upper is
\[
 U_4=1-G(t_1)-G(v_1)-2G(X_1/2)+G(t_0+v_0)
               +2G((1+t_0-v_1)/2).
\]
If \(U_4<0\), the inequality for the normalized expression and the actual quotient product lower \(z(X_0-z)\) give negative magnitude at least \(K_4=-4U_4 z(X_0-z)/X_1^2\). The factor \(4/X_1^2\) accounts for the product of the equal widths in the normalized comparison. This argument never assumes equipartition of actual prime angles.

## 3. Literal cell sum and overlap convention

On each counted cell use the minimum of the four displayed positive \(K_r\)'s and discard cells where this minimum is nonpositive. The remaining source is an actual subset of the negative band \(A\), with value at least this minimum times \(\log x\). Multiply (3) by this weight and sum each cell once. The half-open boxes and unique two least primes prevent multiplicity. The attached checker integrates the prime harmonics downward on mesh \(1/1000\), lower bounds each logarithm by its finite positive atanh series, and rounds each cell downward. Its exact lower is \(33390005752037/10^{15}>.0333\) (5858 cells). This proof applies to either reflected central interval of the same length, giving (1).

In (2) the actual overlap \(\langle A,A\rangle\) is retained and counted only once. Either genuine prime cross in (1) has no tiny factor on either arm for thresholds below \(.040\); however replacing the whole negative-band union by one restricted to an opposite rough gate requires a **new** transfer for that restriction or an explicit signed overlap correction. In particular (1) is not added to any unsigned bound as if it paid the rest of the \(.040\) to \(.105\) exterior.

Run:

    python3 -OB check_middle_prime_rebate.py
