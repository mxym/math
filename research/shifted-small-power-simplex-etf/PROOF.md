# Balanced repetitions minimize a shifted contact energy

## 1. A bound on the unit sphere of any real inner-product space

Let $\ell\ge2$, $N=k\ell+m\ge\ell$, with $k\ge1$ and $0\le m<\ell$. Put
$$M=(\ell-m)\binom{k}{2}+m\binom{k+1}{2},\qquad p_*=\frac{1}{8\ell^2(M+1)^2}.$$
Let $Y$ be a subset of the unit sphere of a real inner-product space. Suppose it contains $\ell$ vertices of a regular simplex: the inner product of any two different vertices is $-1/(\ell-1)$. Define
$$D(u,v)=\frac{1+(\ell-1)\langle u,v\rangle}{\ell}.$$

**Theorem.** For $0<p\le p_*$, the minimum over $Y^N$ of $\sum_{i<j}|D(y_i,y_j)|^p$ is $M$. Its minimizers are precisely the configurations obtained by taking $k$ or $k+1$ copies of every vertex of **some** such simplex in $Y$, in any order.

**Proof.** A balanced repeated simplex has exactly $M$ within-vertex pairs, each of cost one. Every other pair costs zero. This constructs a minimizer once we have proved the lower bound. If $M=0$, then $N=\ell$, and zero cost forces every pair to have inner product $-1/(\ell-1)$; this case holds for all $p>0$.

Assume $M>0$. Set $b=4\ell^2(M+1)$ and $\eta=b^{-2}$. On the $N$ indices (including indices of repeated points) join $i,j$ when $|D(y_i,y_j)|<\eta$. This graph is $K_{\ell+1}$-free. In fact any $s$ unit vectors $u_1,\dots,u_s$ satisfy
$$\left\|\sum_i u_i\right\|^2
=\frac{s(\ell-s)}{\ell-1}+\frac{2\ell}{\ell-1}\sum_{i<j}D(u_i,u_j).\tag{1}$$
For $s=\ell+1$ mutually adjacent indices, the right-hand side is bounded above by $(\ell+1)(\ell^2\eta-1)/(\ell-1)<0$.

By Turán's theorem and its equality characterization, there are at least $M$ nonedges, and at least $M+1$ if the graph is not a balanced complete $\ell$-partite graph. In the latter case each nonedge costs at least $\eta^p$. Since $p\le[2b(M+1)]^{-1}$,
$$\eta^p=e^{-2p\log b}\ge1-2p\log b>1-2pb\ge\frac{M}{M+1}.$$
Thus this case costs strictly more than $M$.

It remains to analyze the extremal graph; the graph identity alone does not fix its vector realization. All $\ell$ parts are nonempty. Let $h$ be the largest $|D|$ of a pair from distinct parts, so $0\le h<\eta$. For any transversal $u_1,\dots,u_\ell$ (one representative per part), (1) gives
$$\left\|\sum_{a=1}^{\ell}u_a\right\|^2\le \ell^2h.$$
For $u,v$ in one part, choose common representatives of every other part. Subtract the two transversal sums and use the triangle inequality to obtain $\|u-v\|\le2\ell\sqrt h$. Hence
$$1\ge D(u,v)=1-\frac{\ell-1}{2\ell}\|u-v\|^2\ge1-2\ell(\ell-1)h>0,$$
as $2\ell(\ell-1)\eta<1$. Since $p\le1$, each of the $M$ within-part pairs costs at least its $D(u,v)$. Their total cost is therefore at least $M-2M\ell(\ell-1)h$.

If $h>0$, one cross-part pair costs
$$h^p\ge\sqrt h>bh>2M\ell(\ell-1)h.$$
Here $p\le1/2$ and $h<b^{-2}$. This gives a strict total surplus. If $h=0$, the transversal inequality forces copies within each part to be identical, and different parts have exactly the simplex inner product. The parts are balanced. These are precisely the configurations already seen to cost $M$. This completes the proof.

## 2. The two energies of Glazyrin and Park

1. **Spherical points.** Take $d\ge2$, $\ell=d+1$ and $Y=\mathbb S^{d-1}$. A regular simplex of the required size exists, and $|\langle u,v\rangle+1/d|^p=(1+1/d)^p|D(u,v)|^p$. Passing from unordered to ordered off-diagonal pairs gives minimum $2M(1+1/d)^p$, with precisely the balanced repetitions of a regular simplex. The kernel is signed before the shift, so independent sign choices are not appropriate.
2. **Real projective lines.** Suppose a real equiangular tight frame of $\ell$ unit vectors $\varphi_i$ spans $\mathbb R^d$, $d\ge2$, with coherence $\alpha=|\varphi_i\cdot\varphi_j|$ for $i\ne j$. The frame operator satisfies $S=\sum_i\varphi_i\varphi_i^T=(\ell/d)I$. From $\operatorname{tr}(S^2)=\ell+\ell(\ell-1)\alpha^2=\ell^2/d$ we get
   $$\alpha^2=\frac{\ell-d}{d(\ell-1)}.$$
   On the whole sphere use the map into traceless symmetric matrices with Frobenius inner product
   $$y(x)=\frac{xx^T-I/d}{\sqrt{1-1/d}}.$$
   Its values are unit vectors and $\langle y(x),y(w)\rangle=(d\langle x,w\rangle^2-1)/(d-1)$. Substitution shows
   $$D(y(x),y(w))=\frac{\langle x,w\rangle^2-\alpha^2}{1-\alpha^2}.$$
   Take $Y$ to be the image of the sphere, not the entire matrix sphere. The given ETF supplies $\ell$ points in $Y$ forming an admissible regular simplex. The theorem gives the ordered minimum $2M(1-\alpha^2)^p$. In the equality case the $\ell$ distinct lifted representatives form a simplex with sum zero by (1); the corresponding unlifted projectors therefore sum to $(\ell/d)I$. The lines are equiangular with coherence $\alpha$ and span a tight frame. Every unit vector giving one of the projectors is one of two signs, so the characterization is exactly balanced repetitions of the lines of some ETF, with arbitrary signs. The original ETF itself attains the minimum. For $\alpha=0$ the original energy is the ordinary frame energy with exponent $2p$, not $p$.

[Conjecture 5.2](https://arxiv.org/pdf/1901.06096) asks for $1\le m<\ell$; the proof also allows $m=0$. For $N<\ell$, an appropriate subset of an available simplex already attains zero for any $p>0$. No assertion that such a subset extends every zero-energy optimizer to an ETF is needed or made.
