# A five-state certificate for the quantum Jensen entropy gaps

We use the ordinary, unnormalized trace and natural logarithms. Put $M=(P+Q)/2$ for two density matrices. For an entropy $H$, its symmetric Jensen gap is
$$J_H(P,Q)=H(M)-\tfrac12 H(P)-\tfrac12 H(Q).$$
For $q\ne1$, write $H_T(P)=(\operatorname{Tr}P^q-1)/(1-q)$ and $H_R(P)=\log(\operatorname{Tr}P^q)/(1-q)$. At $q=1$ both entropies are $-\operatorname{Tr}(P\log P)$. These definitions are not the Tsallis centroid distance.

A kernel $J$ has **negative type** if $\sum_{i,j}c_ic_jJ(P_i,P_j)\le0$ for every finite list and every choice of real coefficients with $\sum_i c_i=0$. This is necessary for $J$ to be squared Hilbert distance: the contrast of squared distances of points $v_i$ in a real Hilbert space is $-2\|\sum_i c_i v_i\|^2$. By Schoenberg's criterion it is also sufficient for a symmetric zero-diagonal kernel. A violation does **not** imply failure of the triangle inequality for $\sqrt J$.

## 1. Five matrices, two fourth differences

Let $Z=\operatorname{diag}(1,-1)$, $X=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$ and
$$N_k=\cos(2\pi k/3)Z+\sin(2\pi k/3)X,\qquad k=0,1,2.$$
Each $N_k$ has eigenvalues $\pm1$, and $(N_i+N_j)/2$ has eigenvalues $\pm1/2$ if $i\ne j$. Indeed $X^2=Z^2=I$ and $XZ+ZX=0$, while the three coefficient vectors lie $120^\circ$ apart on the unit circle.

Set $x=1/12$, $y=1-2x=5/6$, $t=1/60$. In the order $+,-,0,1,2$ take the five states
$$P_\pm=(x\pm t)I_2\oplus (y\mp2t),\qquad P_k=(xI_2+tN_k)\oplus y,$$
with coefficients $c=(3,3,-2,-2,-2)$. All five states are real, strictly positive and of trace one. Their $2\times2$ upper blocks are denoted $A_i$; they need not have trace one. The coefficients are not probabilities and sum to zero.

For $f\in C^4((0,\infty))$, write
$$D_h f(z)=f(z-2h)-4f(z-h)+6f(z)-4f(z+h)+f(z+2h).$$
The midpoint trace contrast is exactly
$$\boxed{\ \sum_{i,j}c_ic_j\operatorname{Tr} f\!\left(\frac{P_i+P_j}{2}\right)=-6D_{t/2}f(x)+9D_t f(y).\ }\tag{1}$$

Here is the counting argument. There are two diagonal pole pairs and two ordered off-diagonal pole pairs, each with weight 9. There are three diagonal trine pairs and six ordered off-diagonal trine pairs, each with weight 4. Each of the twelve ordered pole–trine pairs has weight $-6$. A pole paired with a trine gives upper eigenvalues $x,x\pm t$; different trines give $x\pm t/2$. Adding the weights with spectral multiplicity gives:

| $j$ | $-2$ | $-1$ | $0$ | $1$ | $2$ |
|---|---:|---:|---:|---:|---:|
| Upper eigenvalue $x+jt/2$ | $-6$ | $24$ | $-36$ | $24$ | $-6$ |
| Scalar eigenvalue $y+jt$ | $9$ | $-36$ | $54$ | $-36$ | $9$ |

This proves (1). The first term alone is the midpoint trace contrast of the unnormalized blocks $A_i$. For $z>2h>0$, four applications of the fundamental theorem of calculus give
$$D_h f(z)=\int_{[-h/2,h/2]^4}f^{(4)}(z+s_1+s_2+s_3+s_4)\,ds_1\,ds_2\,ds_3\,ds_4.\tag{2}$$
Thus, when $f^{(4)}$ is decreasing, this lies between $h^4 f^{(4)}(z+2h)$ and $h^4 f^{(4)}(z-2h)$.

## 2. Tsallis: the same states work for all orders below two

Use $f_q(z)=z^q/(q-1)$ for $q\ne1$, and $f_1(z)=z\log z$. Then $J_{H_T}(P,Q)$ is the mean of the two endpoint traces of $f_q$ minus its trace at the midpoint. For $0<q<2$,
$$f_q^{(4)}(z)=q(2-q)(3-q)z^{q-4}>0; \tag{3}$$
at $q=1$ this gives $2/z^3$. The derivative decreases in $z$. Since $(y-2t)/(x+t)=8$,
$$\frac{f_q^{(4)}(x+t)}{f_q^{(4)}(y-2t)}=8^{4-q}>64>24.$$
By (1)–(2) the midpoint contrast is at most
$$t^4\left[9f_q^{(4)}(y-2t)-\tfrac38 f_q^{(4)}(x+t)\right]<0.$$
The endpoint terms cancel because $\sum c_i=0$. The contrast of $J_{H_T}$ is the **negative** of the midpoint contrast and is therefore strictly positive. This establishes simultaneous failure for every $0<q<2$ with the specified five states and coefficients.

At $q=2$ expansion under the trace gives $J_{H_T}(P,Q)=\tfrac14\operatorname{Tr}((P-Q)^2)$, a squared Hilbert distance. For $d>3$, zero-padding preserves every gap. A full-rank witness in higher dimensions is obtained by $P_i\mapsto (1-\eta)P_i\oplus\eta I_{d-3}/(d-3)$, $0<\eta<1$; its Tsallis gaps are scaled by $(1-\eta)^q$, including the Shannon limit. Thus on the space of $d$-dimensional density matrices for $d\ge3$, $q=2$ is the only Hilbertian Tsallis order in $(0,2]$.

## 3. Rényi: choose the scale after choosing the order

Fix $0<q<1$. Write $A_{ij}=(A_i+A_j)/2$. The fourth derivative of $g(z)=z^q$ is $q(q-1)(q-2)(q-3)z^{q-4}<0$. The first term in (1) and (2) therefore gives
$$T_q:=\sum_{i,j}c_ic_j\operatorname{Tr}(A_{ij}^q)=-6D_{t/2}g(x)>0.\tag{4}$$

Put $R_i(\varepsilon)=\varepsilon A_i\oplus(1-\varepsilon\operatorname{Tr}A_i)$ for $0<\varepsilon<1/\max_i\operatorname{Tr} A_i$. All five states are strictly positive of trace one. Their midpoints $M_{ij}(\varepsilon)$ have the same form with $A_{ij}$, so
$$\operatorname{Tr}(M_{ij}(\varepsilon)^q)=(1-\varepsilon\operatorname{Tr}A_{ij})^q+\varepsilon^q\operatorname{Tr}(A_{ij}^q)=1+\varepsilon^q\operatorname{Tr}(A_{ij}^q)+O_q(\varepsilon).$$
Taking the logarithm, the error becomes $O_q(\varepsilon+\varepsilon^{2q})=o_q(\varepsilon^q)$. There are only 25 midpoint terms. Cancelling the single-state contributions gives
$$\lim_{\varepsilon\downarrow0}\varepsilon^{-q}\sum_{i,j}c_ic_j J_{H_R}(R_i(\varepsilon),R_j(\varepsilon))=\frac{T_q}{1-q}>0.$$
For each **fixed** $q$, all sufficiently small positive $\varepsilon$ work. No single value of $\varepsilon$ is proved here to work for all $q$. The states embed into larger dimensions by zero-padding. The endpoint $q=1$ is the already known Shannon case.

## 4. Why five is the minimum

[Sra, Theorem B.1](https://hexagonmath.org/pdf/2610.00602v1#page=14) shows that every four density matrices satisfy negative type for the Tsallis Jensen gap for $0<q\le2$, and for the Rényi Jensen gap for $0<q\le1$. A list of fewer than four can be augmented with a coefficient of zero. Combining that prior theorem with the strict contrasts above gives a minimum of five at each claimed order, not a new proof of the four-point lower bound. See the [scope and antecedents](README.md#what-was-known) for the Shannon and near-Shannon cases.
