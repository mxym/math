# Gaussian fluctuations of the peak in a random tree

Draw a labeled tree uniformly on $n$ vertices. Count its independent sets of each size, and let $M_n$ be **any** index achieving the largest count. The [previous theorem](../PROOF.md) gives the common center $\mu n$; the [second-moment result](../square-root/README.md) bounds deviations about it. This note identifies their limiting distribution:
$$
\frac{M_n-\mu n}{\sqrt n}\ \Rightarrow\ N(0,\sigma^2),
\qquad \operatorname{Var}(M_n)/n\longrightarrow\sigma^2,
\qquad \sigma^2\ge e^{-10}/216>0 .
$$
The same holds for the tree's conditional mean independent-set size $A(T_n)$. Every maximizing index is $o(\sqrt n)$ from that mean, uniformly over tree shapes. Thus the fluctuation comes from which tree was drawn, not from an additional sample of an independent set. No variance estimate beyond the stated bound, convergence rate, or Gaussian local limit is claimed.

The [proof](PROOF.md) approximates occupations by finite local statistics, applies the additive-tree CLT of Ralaivaosaona–Šileikis–Wagner, and implements their fringe-replacement idea with two ten-vertex shapes that shift the mean by exactly $1/6$. A prior theorem of Fang–Lu–Nevo–Yao–Zheng gives the separate within-tree mode/mean comparison. [Sources and scope](SOURCES.md) distinguish these results. See the [independent internal audit](REVIEW.md). AI-assisted work, not externally peer-reviewed; no guarantee of priority.

From this directory, using only Python 3's standard library:

~~~sh
sha256sum -c SHA256SUMS
python -B -O clt_check.py | diff - AUTHOR-CHECKS.txt
python -B -O independent_clt.py | diff - CHECKS.txt
~~~
