# A certified sextic Smale bound with at least three real critical points

Let \(P\) be a real-coefficient polynomial of degree six, and let \(x\) be real with \(P'(x)\ne0\). Let \(S(P,x)\) be the least modulus of the normalized critical secant
\[
 \frac{P(c)-P(x)}{(c-x)P'(x)},\qquad P'(c)=0.
\]
The minimizing critical point is allowed to be nonreal.

**Theorem.** If \(P'\) has at least three real zeros counted with multiplicity, then \(S(P,x)<81/100\). Conversely there is such a sextic, with exactly three real critical points, for which \(S(P,0)>800003/10^6\). In particular the quintic benchmark \(4/5\) does not extend to this sextic class. These are bounds, not an identification of the exact optimum.

The all-real-critical theorem of [Hinkkanen and Kayumov](https://doi.org/10.1007/s00365-009-9079-6) gives \(2/3\) when all five zeros of \(P'\) are real. The new case dealt with below has a nonreal conjugate pair. Compare [Charalambides (2026)](https://aixiv.online/abs/2611.02831), which reports the bound \(17/20\) for unrestricted complex sextics. The present improvement to \(81/100\) requires both the real base point and the specified root pattern. It makes no claim about the degree-six unrestricted optimum.

## 1. Two compact four-parameter domains

By normalizing the input and output affinely we can set \(x=0\), \(f(0)=0\), and \(f'(0)=1\), preserving real coefficients. Write the reciprocals of the critical points as \(w_j\), \(0\le j\le4\), so
\[
 f'(z)=\prod_{j=0}^4(1-w_jz).
\]
No critical point equals zero since \(f'(0)=1\); no reciprocal equals zero in degree six. Rescaling \(f(z)\mapsto f(sz)/s\) for a real \(s\ne0\) multiplies the reciprocals by \(s\) without changing the ratios. Normalize their maximum modulus to one. If the maximum is real, also reflect if needed to arrange
\[
 (w_0,\ldots,w_4)=(1,r,s,z,\overline z),
\]
where \(-1\le r\le s\le1\) and \(z\) is in the closed upper unit half-disk (shard 0). If it occurs in the nonreal pair, reflect if needed so the upper representative \(a\) of that pair has nonnegative real part. Then arrange
\[
 (w_0,\ldots,w_4)=(a,\overline a,r,s,t),
\]
where \(-1\le r\le s\le t\le1\) and \(a\) is on the closed first-quadrant unit arc (shard 1). That arc is parameterized by \(a=(1-u^2+2iu)/(1+u^2)\) for \(0\le u\le1\), with speed \(2/(1+u^2)\le2\). Cases of a tied maximal modulus are already covered. The two domains include all multiplicities and conservatively allow zero reciprocals and pair limits on the real axis.

## 2. The certificate

For \(w_j\ne0\), let \(h_j=f(1/w_j)/(1/w_j)\). Integration of the derivative gives the homogeneous polynomial
\[
 G_j=60w_j^4h_j
 =30w_j^4-10e_1^{(j)}w_j^3+5e_2^{(j)}w_j^2-3e_3^{(j)}w_j+2e_4^{(j)},
\tag{1}
\]
where \(e_k^{(j)}\) is elementary symmetric in the four other reciprocals. Indeed the contribution of degree \(k\) in the four remaining factors has integral \(\int_0^1(1-y)y^k\,dy=1/((k+1)(k+2))\). Omit one of the conjugate pair since their ratios have equal modulus.

On a parameter box, construct enclosures of each \(|G_j|\) and \(|w_j|^4\). A ratio is certifiably below \(81/100\) when these enclosures give
\[
 5\,\operatorname{upper}|G_j| <243\,\operatorname{lower}|w_j|^4,\qquad
 \operatorname{lower}|w_j|^4>0.
\]
An inconclusive box is split at the midpoint of its longest interval and both closed children are checked. The only other pruning tests are incompatibility with the prescribed real order or upper unit half-disk. No hypothesis on ratios being of equal modulus, no extremizer classification, and no use of the broader \(5/6\) local theorem enter this calculation.

The program encloses each complex value by a disk with center and radius dyadic at scale \(2^{-17}\). Arc centers use the rational stereographic formula and its exact speed bound, with a radius correction for rounding both center coordinates. For \(e_k^{(j)}\), when a conjugate pair is present in full the generating factors are grouped as \(1+2\Re(z)X+|z|^2X^2\); its real coefficients use interval bounds, not independent complex variation of the two roots. Disk products use the sum \(|c_1|r_2+|c_2|r_1+r_1r_2\), rounded upward, plus both center rounding errors. Nominal square roots only propose a candidate integer: a pair of exact integer square comparisons verifies enclosure. Quotients with non-dyadic denominators are similarly checked by exact multiplication. The code rejects arithmetic outside its allowed integer range.

The replay commands are `node verify_smale_sextic_three_real_critical.js Infinity 0` and `node verify_smale_sextic_three_real_critical.js Infinity 1`. They exhaust both closed domains with no pending boxes:

| Shard | Visited boxes | Order or disk exclusions | Strict ratio certificates | Maximum depth |
| --- | ---: | ---: | ---: | ---: |
| 0 | 3,967,203 | 37,894 | 1,945,708 | 38 |
| 1 | 7,569,701 | 35,079 | 3,749,772 | 39 |

Because the cover is finite and each ratio certificate has positive lower denominator and strict upper ratio, the supremum on this subclass is also strictly less than \(81/100\). The numerical value of that strict margin is not needed.

## 3. A rational example beyond \(4/5\)

Use the five reciprocals
\[
 w=\left(1,-\frac{940749}{10^6},-\frac{87397}{10^6},
         \frac{16905+974002i}{10^6},\frac{16905-974002i}{10^6}\right)
\]
and let \(f(0)=0\) with the specified derivative. This is a real-coefficient sextic with exactly three real critical points and no reciprocal zero. To verify the strict bound, let \(W_j=10^6w_j\); the right side of (1) is homogeneous of degree four in the reciprocals. The five strict comparisons are
\[
 10^{12}|G_j(W)|^2>(60\cdot800003)^2|W_j|^8 .
\]
Both sides are integers. The program independently verifies these inequalities using Gaussian integers before starting either replay. Hence every ratio exceeds \(800003/10^6>4/5\).

## 4. A simple analytic family above the quintic value

The lower phenomenon is not confined to the rational fixture. For small nonzero real \(\epsilon\), set
\[
 f_\epsilon(z)=z-\frac{z^5}{5}
 +\epsilon\left(\frac{z^6}{6}+\frac{z^2}{30}+\frac{z^4}{15}\right)
 +\frac{11}{120}\epsilon^2z^3 .
\]
Then \(f_\epsilon\) has exactly three real critical points, and
\[
 S(f_\epsilon,0)=\frac45\left(1+\frac{\epsilon^2}{720}
                       +O(|\epsilon|^3)\right)>\frac45
\]
for all sufficiently small nonzero real \(\epsilon\).

Indeed
\[
 f'_\epsilon(z)=1-z^4+\epsilon\left(z^5+\frac z{15}+\frac{4z^3}{15}\right)
                          +\frac{11}{40}\epsilon^2 z^2 .
\]
At each fourth root \(t\) of unity, the simple root of the derivative at \(\epsilon=0\) continues to a root \(c_t=t(1+\epsilon L_t/4+O(\epsilon^2))\), where \(L_t=(16/15)t+(4/15)t^3\). The roots near \(1,-1\) are real by uniqueness and conjugation; the other two are nonreal. By the sum of the five roots of \(f'_\epsilon\), the fifth is \(c_*=1/\epsilon+O(1)\) and is real. Its ratio is asymptotic to \(-1/(30\epsilon^4)\), by the two highest terms of \(f_\epsilon(c_*)/c_*\).

Eliminating \(c_t^4\) by its critical-point equation gives
\[
 \frac{f_\epsilon(c_t)/c_t}{4/5}
 =1+\epsilon\left(\frac{c_t}{40}+\frac{c_t^3}{60}
                         -\frac{c_t^5}{24}\right)
       +\frac{11}{240}\epsilon^2 c_t^2 .
\]
Let \(V_t=(t^3-t)/60\) and \(W_t=(1/40-5/24)t+(1/20)t^3\). Substituting the expansion of \(c_t\) and taking the real part of the logarithm around 1 gives
\[
 \log\left|\frac{f_\epsilon(c_t)/c_t}{4/5}\right|
 =\Re\left(\epsilon V_t+
   \epsilon^2\left(\frac{L_tW_t}{4}+\frac{11t^2}{240}-\frac{V_t^2}{2}\right)\right)
   +O(|\epsilon|^3).
\]
For real \(t\), \(V_t=0\) and \(L_tW_t/4=-2/45\); for imaginary \(t\), \(V_t^2=-1/900\) and \(L_tW_t/4=7/150\). In both cases the real linear term is zero and the quadratic coefficient is exactly \(1/720\). The bounded four ratios therefore all have the asserted expansion, while the fifth is too large to attain the minimum.
