# Exponential laws are not sharp for either of Steinerberger's two linear tail-ratio benchmarks

**Yongxian Zhang.** Research draft, November 19, 2026. AI-assisted and internally checked, not externally peer reviewed.

### Question and answer

In [Steinerberger, *A sharp estimate for probability distributions*, §1.3](https://arxiv.org/pdf/1801.00663), take iid absolutely continuous nonnegative X,Y with unbounded support. Write
$$
 G(t)=\frac{\Pr(X+Y\ge2t,\ \min(X,Y)\le t)}
 {\Pr(X+Y\ge2t,\ \min(X,Y)\ge t)},\qquad t>0.
$$
Exponential laws have $G(t)=2t/\mathbb EX=(2\log2)t/\mathrm{med}(X)$ at every $t$. The author asks whether, for each noncompactly supported absolutely continuous law, some $t>0$ reaches the median-normalized comparison, and likewise for the mean-normalized comparison when the mean exists.

**Counterexample.** Take the single common law
$$
 S(t)=\Pr(X>t)=\exp(-5t-t^2/2),\qquad 0\le t<\infty .
$$
Its density $(5+t)S(t)$ is strictly positive throughout $[0,\infty)$, its support is unbounded, and it has all moments and a unique median. We prove
$$
 \sup_{t>0}G(t)/t\le 10+\frac{3}{28}
 <\min\left\{\frac{2\log2}{\mathrm{med}(X)},\frac{2}{\mathbb EX}\right\}.
$$
Thus both proposed constants fail, each separately, for every choice of threshold in the same example. The [companion argument](UNIVERSAL.md) proves that smaller positive universal constants do work at a suitable finite threshold. Neither result contradicts the different estimate already proved in §1.2 of the source.

### Exact convolution

Continuity ensures that boundaries have probability zero. The denominator defining $G(t)$ is $S(t)^2$, and the numerator is $\Pr(X+Y\ge2t)-S(t)^2$. Conditioning on $X$, then writing $x=t+u$, gives
$$
 1+G(t)=\frac{S(2t)}{S(t)^2}
       +\int_0^{2t}(5+x)\frac{S(x)S(2t-x)}{S(t)^2}\,dx
       =e^{-t^2}+(5+t)\int_{-t}^t e^{-u^2}\,du .
$$
Here $S(x)S(2t-x)/S(t)^2=e^{-(x-t)^2}$ and the odd part integrates to zero. Using $1-e^{-t^2}=\int_{-t}^{t}|u|e^{-u^2}\,du$, write
$$
 \frac{G(t)}{t}=\frac5t\int_{-t}^t e^{-u^2}\,du
  + \int_{-t}^t\left(1-\frac{|u|}{t}\right)e^{-u^2}\,du. \tag{1}
$$

### A uniform bound at every positive threshold

For $0<t\le1$, integrating $e^{-u^2}\le1-u^2+u^4/2$ gives
$$
 \frac1t\int_{-t}^t e^{-u^2}\,du
  \le 2-\frac23t^2+\frac15t^4\le 2-\frac7{15}t^2 .
$$
The triangle-weighted integral in (1) is at most its unweighted triangle mass $t$. Hence
$$
 G(t)/t \le 10+t-\tfrac73t^2 \le 10+3/28 .
$$
For $t\ge1$, the normalized first integral equals $\int_{-1}^1e^{-t^2v^2}\,dv$ and decreases in $t$, so is at most $2-7/15=23/15$. The second integral in (1) is at most $\int_\mathbb R e^{-u^2}du=\sqrt\pi<2$. Therefore $G(t)/t<5(23/15)+2=29/3<10$. These estimates prove the uniform upper bound without numerical integration.

### The two normalizations

The median $m$ satisfies $5m+m^2/2=\log2$, so $2\log2/m=10+m$. At $m_0=3/25$ the left side of the median equation is $3/5+9/1250<2/3<\log2$; the last strict inequality follows for example by integrating $1/x$ on $[1,2]$ and applying strict Jensen. Thus $m>3/25>3/28$.

Finally,
$$
 \mathbb EX=\int_0^\infty e^{-5t} e^{-t^2/2}\,dt
 \le\int_0^\infty e^{-5t}(1-t^2/2+t^4/8)\,dt
 =\frac15-\frac1{125}+\frac3{3125}
 =\frac{603}{3125}.
$$
The Taylor inequality $e^{-x}\le1-x+x^2/2$ holds for all $x\ge0$. In particular
$2/\mathbb EX\ge 6250/603>283/28 = 10+3/28$. Both conclusions follow.
