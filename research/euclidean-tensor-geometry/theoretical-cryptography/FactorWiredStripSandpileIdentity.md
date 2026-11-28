# Independent end profiles for wired rectangular sandpile identities

Consider the ordinary \(w\times n\) square-grid rectangle of nonsink vertices, with one edge to a common sink for each missing grid neighbor. Thus each nonsink vertex has degree four and stable heights \(0,1,2,3\). We prove an explicit finite threshold for a decomposition into two fixed end profiles and a central block consisting of height two. It works for every width \(w\), with an aspect-ratio bound asymptotic to \(\sqrt2\), and gives the exact independent-front threshold at each fixed width by one bounded stabilization.

[Le Borgne and Rossin (2002)](https://doi.org/10.1016/S0012-365X(02)00347-3) already proved a three-region decomposition with a uniform middle for long rectangles; their abstract states the long-side condition \(n>2w\). The strengthening here is the explicit smaller sufficient threshold and the separate exact gluing/collision statement. No conclusion is drawn about the existence of a proportional central square on arbitrary square boards, and no sharp universal aspect-ratio claim is made.

## 1. Result and normalization

Let
\[
M_w=\left\lfloor\frac{(w+1)^2}{4}\right\rfloor,\qquad
b_w=\min\left\{b\in\mathbb Z_{\ge0}:\frac{b(b+3)}2\ge M_w-1\right\}.
\]
There is a finite sequence \(E_w\) of \(f_w\le b_w+1\) height columns depending only on \(w\), for which the identity on every \(n\ge2f_w\) is exactly
\[
           (E_w,\ \underbrace{\mathbf 2,\ldots,\mathbf2}_{n-2f_w},
                       \operatorname{reverse}(E_w)).       \tag{1}
\]
In particular \(n\ge2b_w+2\) suffices, and \(n-2b_w-2\) complete central columns are guaranteed to be all two. The cutoff \(2b_w+2=\sqrt2\,w+O(1)\) does not contain any hidden dependence on \(n\).

The sequence \(E_w\) is obtained by adding \(r(w+1-r)\) grains at row \(r\) of the first column of the uniform two configuration on the single fixed \(w\times(b_w+2)\) rectangle, and stabilizing. Keep the columns up to and including the last column changed from all two. The resulting one-sided odometer has its last nonzero column at \(f_w-1\), where zero is allowed if there are no firings. Two independent copies of that odometer stabilize the two-end source for every \(n\ge2f_w\), but do **not** stabilize it at \(n=2f_w-1\).

To prove the representation of the source, write \(\Delta=4I-A\) for the reduced Laplacian and take \(\phi_r=r(w+1-r)\), with \(\phi_0=\phi_{w+1}=0\). For \(F(r,j)=\phi_r\),
\[
        (\Delta F)(r,j)=2+\phi_r(\mathbf1_{j=1}+\mathbf1_{j=n}).
                                                              \tag{2}
\]
The one-dimensional vertical difference equals two, and each end boundary adds one copy of \(\phi_r\). When \(n=1\) the two indicators are both one, as required.

Uniform two is recurrent: every nonempty vertex subset has a vertex minimizing row plus column, hence with at most two neighbors in the subset; this is the no-forbidden-subconfiguration criterion. The added end source in (2) is nonnegative, so stabilization preserves recurrence. Also (2) is in the integer image of the reduced Laplacian. Therefore its stabilization is the unique recurrent representative of the zero class, i.e. the identity. For burning, stabilization and this correspondence, see [Holroyd et al., *Chip-Firing and Rotor-Routing on Directed Graphs*](https://personal.math.ubc.ca/~holroyd/papers/sand.pdf) and [Járai, *Sandpile Models*](https://www.emis.de/ft/46900).

## 2. A finite integer barrier

Put \(b=b_w\). For a one-sided source \(\sigma(r,j)=2+\phi_r\mathbf1_{j=1}\) on any width-\(w\) strip of length at least \(b+1\), try the integer nonnegative firing vector
\[
  v(r,j)=
  \begin{cases}
  (b+1-j)(b+2-j)/2 & 1\le j\le b,\\
  0 & j>b .
  \end{cases}                                               \tag{3}
\]
For \(b\ge1\) its horizontal contribution to \(\Delta v\) is \(b(b+3)/2\) at \(j=1\), \(-1\) at \(2\le j\le b+1\), and \(0\) beyond. This is just the second difference of the triangular numbers and the zero boundary on the left. Its vertical contribution is nonnegative: the profile is constant along each column, and missing vertical neighbors add nonnegative terms. Thus \(\sigma-\Delta v\le3\) everywhere by the definition of \(b\). The case \(b=0\) means \(w=1\), and already \(\sigma\le3\).

Least action now bounds every legal odometer by \(v\). For completeness, at the first attempted firing exceeding \(v\), that site's firing count equals \(v\), while all its incoming-neighbor counts are at most those in \(v\). Hence its current height is at most the corresponding component of \(\sigma-\Delta v\), which is at most 3, so the firing is not legal. The actual receiving columns are therefore contained in \(1,\dots,b+1\).

Let \(R\) be the last column with a positive firing in the stabilized one-sided run, or 0 if there is no firing. If \(R\ge1\), column \(R+1\) starts at height two; it never fires, and it receives a chip at at least one row from column \(R\). Thus it is the last column which changes from all two. If \(R=0\), column 1 already differs from all two and there are no changes later. In both cases \(f_w=R+1\). The legal one-sided sequence and its stabilized heights through column \(f_w\) are unchanged if the strip length is replaced by any length at least \(f_w\): none of the discarded or appended columns ever fires, and every neighbor of a firing vertex that lies in the grid is still present.

With both end sources and \(n\ge2f_w\), apply the two one-sided firing sequences, reflected on the right. Their affected columns are disjoint. No site outside them is changed, all end heights are stable, and (2) proves (1).

If \(R\ge1\) and \(n=2f_w-1=2R+1\), the two copied firing sequences are still legal, but their affected regions meet in a single column, which they do not fire. At a row where column \(R\) of the left-front odometer fires, that common column receives at least one grain from each side at the same row, and its height is at least four. Thus the sum of the two one-sided odometers is not stabilizing at this length. At \(R=0,w=1\) the two source increments already make the sole site unstable at \(n=1\). This is a sharp statement about additivity of the fixed two end odometers, not a claim that each smaller board lacks all height-two columns.

The barrier also bounds the computation of \(E_w\) by \(\sum_{r,j}v(r,j)=O(w^4)\) individual firings on \(O(w^2)\) sites. In particular computing the nonconstant data for the identity of an arbitrarily long strip requires no stabilization on its full length.

## 3. Full formulas for widths at most five

Encode each column by its heights from the top row through the middle, with vertical reflection determining the remainder. The data for the two independent ends are:

| \(w\) | \(E_w\) from the left edge inward | smallest universal gluing cutoff \(2f_w\) |
|---:|:---|---:|
| 1 | `3` | 2 |
| 2 | `1 3` | 4 |
| 3 | `03 12 33` | 6 |
| 4 | `22 13 33` | 6 |
| 5 | `220 113 133 333` | 8 |

For the remaining shorter lengths in increasing order, the following are the successive **half-strip column lists**, running from the left edge up to the center (including the middle column for odd length). Complete each list by horizontal reflection.

| \(w\) | Shorter identities |
|---:|:---|
| 1 | `0` |
| 2 | `3`; `2`; `2 1` |
| 3 | `32`; `21`; `21 10`; `03 23`; `03 23 12` |
| 4 | `32`; `13`; `02 33`; `23 32`; `23 32 21` |
| 5 | `322`; `132`; `021 332`; `232 321`; `232 321 210`; `221 131 331`; `221 131 331 220` |

The [standard-library checker](verify_factor_wired_strip_identity.py) computes these finite entries by legal integer topplings, tests recurrence by burning, and cross-checks complete boards using the classical two-stabilization formula \(I=(6-6^\circ)^\circ\) for degree four (with \(6\) the constant vector). The general width theorem rests on (2)–(3), not on these finite checks or an extrapolation.
