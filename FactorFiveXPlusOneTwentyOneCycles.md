# The positive \(5x+1\) map has no additional cycles with at most 21 local minima

Use the shortcut map \(T(x)=x/2\) for even \(x\) and \(T(x)=(5x+1)/2\) for odd \(x\). A local minimum is counted once per least period; an **\(m\)-cycle** means a positive finite orbit with \(m\) such minima, not an orbit of period \(m\).

**Theorem.** The only positive cycles with \(m\le21\) are the three known cycles, whose global minima are \(1,13,17\). Thus any other positive cycle has at least 22 local minima. No conclusion is made about nonperiodic orbits, negative cycles, or the \(3x+1\) map.

[Simons, Acta Arithmetica 131 (2008), §4, Lemma 16 and table (43)](https://www.impan.pl/shop/publication/transaction/download/product/82891?download.pdf=) gave the three cycles and the exclusion through \(m=7\) for \(5x+1\). We keep his two-logarithm lower bound, but use the **sum of all chained heights**, rather than replacing all heights by the largest. A new second bound truncates the geometric sum at each small local minimum. It reduces the large-minimum part of the proof to 22 exact linear-form candidates, without searching parity words. The small-minimum part is a bounded exact local-minimum census, not an assertion that trajectories must converge.

## 1. Block formula and sum of heights

Each \(T\)-cycle begins at an odd local minimum, continues through a nonempty consecutive block of odd states, then through a nonempty even block back to an odd local minimum. List the successive odd minima as \(x_0,\dots,x_{m-1}\) cyclically, let the block lengths be \(k_i,\ell_i\ge1\), and set \(y_i=3x_i+1,\ K=\sum k_i,\ L=\sum \ell_i,\ \rho=\log_2 5\). On an odd step \(3T(x)+1=5(3x+1)/2\), so \(k_i=v_2(y_i)\). The block identity is
\[
y_{i+1}=5^{k_i}2^{-k_i-\ell_i}y_i+1-2^{-\ell_i}.
\]
Taking the product of \(y_{i+1}/(y_{i+1}-1+2^{-\ell_i})\) over \(i\) yields
\[
0<\lambda=(K+L)\log2-K\log5
   <\sum_{i=0}^{m-1}\frac1{y_i-1}.                         \tag{1}
\]
Indeed the individual ratio is \(1+(1-2^{-\ell_i})/(y_{i+1}-1+2^{-\ell_i})\). This is the usual block log inequality.

Write \(S_j=1+\rho+\cdots+\rho^{j-1}\). Since \(2^{k_i}\le y_i\), the transition also gives \(y_{i+1}<y_i^\rho/2+1\le y_i^\rho\). Take \(x_0\) to be the global minimum and sum \(\log_2 y_i\le\rho^i\log_2 y_0\). We obtain
\[
K\le S_m\log_2 y_0,\qquad
\lambda<\frac{m}{y_0-1}\le\frac{4m}{3}
                 \exp\left(-K\frac{\log2}{S_m}\right),     \tag{2}
\]
using \(y_0\ge4\). The coefficient \(S_m\) differs from \(m\rho^{m-1}\), the size of the coarser exponent denominator in Simons's equation (36).

For a stronger estimate when **\(x_0>X=2^{29}\)**, write \(a=3/4\). We have \((\rho-1)a<1983/2000\) and \(2^{-(\rho-1)a}-1/2>1/400\); the latter follows from \(e^t\ge 1+t\) and \(\log2>69/100\). Since \(y_i^\rho>400\), we get
\[
              \log_2 y_{i+1}-a\ \le\ \rho(\log_2 y_i-a).
\]
If at least \(r\) of the minima satisfy \(y_i\le 2^H\), divide the circular list into \(r\) segments starting at these minima; segment lengths \(b_j\ge1\) sum to \(m\). Then
\[
 K\le am+(H-a)\sum_{j=1}^r S_{b_j}
  \le am+(H-a)(S_{m-r+1}+r-1).                            \tag{3}
\]
For the second inequality, moving one position from a shorter segment of length at least two to the longest segment does not decrease the sum, because the differences \(S_{b+1}-S_b=\rho^b\) increase. This yields the right-hand side after \(r-1\) lengths become one.

With \(M=21\), (1) supplies the number of “small” minima to which (3) can be applied. If
\[
  \lambda>\frac{r-1}{3X}+\frac{M-r+1}{2^H-1},              \tag{4}
\]
there are at least \(r\) minima with \(y_i\le2^H\), provided \(2^H-1>3X\). Otherwise (1), using \(m\le M\), bounds the sum by the right-hand side of (4). The proofs of (3) and (4) do not require \(r\) to equal \(m\).

## 2. Exhaust the large-minimum linear forms

Assume \(x_0>X\) and \(m\le21\). Then \(0<\lambda<M/(3X)\). The bound \(S_M<36{,}444{,}000\) follows by bracketing \(\rho<2.321929\). Use Simons's equation (38), a two-logarithm estimate valid here since \(p=5,q=1\) and all minima exceed the paper's \(X_0=10^6\). For \(K\ge3\cdot10^{13}\) it implies
\[
 \log\lambda>-40(\log K+2)^2.
\]
In contrast, (2) gives \(\log\lambda<4-(69/100)K/36{,}444{,}000\). The linear bound is strictly smaller than the logarithmic one at \(K=3\cdot10^{13}\), and the difference increases afterwards (differentiate; \((\log K+2)/K\) is decreasing). Thus \(K<3\cdot10^{13}\).

For clarity, the remaining approximation step requires only the following elementary unimodular bracket rule. Given an upper pair \((p,k)\) with gap \(g=p\log2-k\log5>0\) and a lower pair \((q,l)\) with gap \(-h<0\), where \(pl-qk=1\), any pair \((P,K)\) with \(K>0\) and \(\lambda=P\log2-K\log5>0\) has unique integer coordinates \(v,w\) in this basis. We have
\[
 v=\frac{hK+l\lambda}{\log2}>0,\qquad
 w=\frac{gK-k\lambda}{\log2}.
\]
If \(K<k+l\), then \(w\le0\); hence \(\lambda=vg-wh\ge g\). Apply the rule to:

| upper \((p,k)\) | lower \((q,l)\) | applicable for \(K<\) | resulting lower bound for \(\lambda\) |
|---|---|---:|---:|
| \((19293579461887,8309292395561)\) | \((53548351813079,23062019849360)\) | \(3\cdot10^{13}\) | \(2.8\cdot10^{-15}\) |
| \((3792010281,1633129936)\) | \((1344399137,579001193)\) | \(2.1\cdot10^9\) | \(1.10\cdot10^{-9}\) |

At the first lower bound, (2) gives \(K<2.1\cdot10^9\) (at that value the upper bound is \(<28e^{-39}<2.8\cdot10^{-15}\)). At the second, (2) gives \(K<1.3\cdot10^9\) (at that value the upper bound is \(<28e^{-24}<1.10\cdot10^{-9}\)). One may use \(e^3>20\) for both comparisons.

Now use the upper and lower basis pairs
\[
      (138463487,59632978),\qquad (241187130,103873643).
\]
Again the determinant is 1 and the signs are opposite. The formulas for \(v,w\), \(K<1.3\cdot10^9\), and \(\lambda<M/(3X)\) give \(1\le v\le4\), \(-1\le w\le11\). The rational verifier linked below uses the finite series for \(\log2\) and \(\log(5/4)\) with rigorous remainder bounds to check the brackets and all 52 cells. Exactly 22 pairs survive \(0<K<1.3\cdot10^9,\ 0<\lambda<M/(3X)\). Applying (4) at \(H=40\) and checking (3) at the largest allowed \(m=M\) excludes 21. The remaining pair is
\[
          (P,K)=(1103212007,475127550),\qquad (v,w)=(1,4),
          \qquad \lambda\approx1.17428\cdot10^{-9}.
\]
For this pair, (4) at \(H=40\) forces at least two small minima, while (3) at \(H=60,r=3\) excludes three minima even up to \(2^{60}\). Thus exactly two minima are at most \(2^{60}\), and the other terms in (1) sum to less than \(19/(2^{60}-1)\). The rational verifier checks
\[
 \lambda > \frac{1}{(17/10)2^{30}-1}+\frac{1}{3X}+\frac{19}{2^{60}-1}.
\]
As either of the two small minima contributes at most \(1/(3X)\), the other must have \(y<(17/10)2^{30}<2^{154/5}\). Therefore both satisfy the small cutoff with \(H=154/5\). Applying (3) with \(r=2\) and \(m\le21\) then gives \(K<475127550\), a contradiction. The large-minimum case is closed.

## 3. Exact bounded scan, and scope

For each positive odd \(x<X\), the scan applies the successor on local minima at most 21 times, starting with \(x\). This successor uses \(k=v_2(3x+1)\); the even peak is \(((3x+1)5^k/2^k-1)/3\), after which one removes every factor of two. It is defined for every positive odd \(x\), whether or not the orbit is bounded. If the successor falls strictly below \(x\), \(x\) cannot be the global cycle minimum. Otherwise the first return to \(x\), if any within the tested number of transitions, is exactly the number of local minima of that cycle. A global minimum cannot be even, since halving it would give a smaller point in the same orbit.

The scan returned only \((x,m)=(1,1),(13,1),(17,2)\). Written as shortcut orbits these are
\[
 (1,3,8,4,2),\qquad(13,33,83,208,104,52,26),\qquad
 (17,43,108,54,27,68,34).
\]
There are \(2^{28}=268{,}435{,}456\) tested odd starts in eight nonoverlapping shards. The program uses exact arithmetic on bounded integers and switches to BigInt before any larger arithmetic would affect the result; its fast and literal implementations were compared on 35,290 ordinary and wide integer inputs. There is no exclusion by timeout or unspecified stopping length. Nonperiodic orbits are not classified.

## Reproduce

```sh
python3 verify_factor_five_x_plus_one_21_form_bounds.py
for shard in 0 1 2 3 4 5 6 7; do
    node verify_factor_five_x_plus_one_21_cycle_scan.js "$shard" || exit 1
done
```

Use regular Python (not `-O`) and Node.js 18+. See [the rational verifier](verify_factor_five_x_plus_one_21_form_bounds.py) and [the cycle scan](verify_factor_five_x_plus_one_21_cycle_scan.js). The eight scan shards are independent and may be run in parallel. The proof is an exact scoped exclusion, not a Lean formalization.
