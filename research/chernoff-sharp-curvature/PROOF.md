# The sharp strong-log-concavity constant of Chernoff's density

Let $Z=\arg\max_{t\in\mathbb R}\{W(t)-t^2\}$ for standard two-sided Brownian motion, let $f$ be its density, and write $\kappa(x)=-(\log f)''(x)$. We give a computer-assisted proof of the *sharp* conjecture of Balabdaoui and Wellner (2014, Conjecture 3.1). Ordinary log concavity (Balabdaoui–Wellner) and strong log concavity with an unspecified global constant (Zhang–Zhou 2026) are prior results. The finite arithmetic in this proof is reproducible by running `python3 -B -O cert.py` with the standard library only.

**Theorem.** For every $x\ne0$, $\kappa(x)>\kappa(0)$, and
$$3.4051898<\kappa(0)<3.4051899.$$
In particular the least Gaussian scale for which $f/\varphi_\sigma$ is log-concave is exactly $\sigma=1/\sqrt{\kappa(0)}$; all larger scales work. This follows by taking two logarithmic derivatives. The theorem does not assert that $\kappa$ is globally increasing on the positive half-line.

## 1. Two existing analytic inputs

Write $f(x)=C g(x)g(-x)$, with the one-sided Airy factor normalized to be a density. Let
$$M(s)=\int_{\mathbb R}e^{sx}g(x)\,dx =\frac{\operatorname{Ai}(0)}{\operatorname{Ai}(2^{-1/3}s)},\qquad F(s)=1/M(s).$$
This is the Groeneboom transform in Zhang–Zhou, arXiv:2607.18619, (1)–(3), with precisely the standard Brownian/drift convention above. We use their Theorem 1 (6): **$\kappa(x)>4|x|$**. Therefore it suffices to bound $\kappa(0)<4$ and to prove the strict comparison on $0<x\le1$; $\kappa$ is even. Their equation (9), from the classical Airy product, gives positive pole magnitudes $\lambda_j$ and
$$
 \frac{|M(a+iu)|}{M(a)}
 =\prod_{j\ge1}\frac{\lambda_j+a}{\sqrt{(\lambda_j+a)^2+u^2}},
 \qquad a> -\lambda_1.
 \tag{1}
$$
There are no nonreal Airy zeros. We only need $\lambda_1>1$ and ten pole magnitudes less than $17$; these are checked below rather than trusting numerical zero tables.

## 2. Exact Airy samples

Write $F(s)=\sum a_j s^j$. The Airy equation gives $F''(s)=s F(s)/2$, $a_0=1$, $a_2=0$, and $a_{j+3}=a_j/[2(j+2)(j+3)]$. From [DLMF §9.2](https://dlmf.nist.gov/9.2#ii),
$$a_1=-\sqrt[3]{3/2}\,I_1/I_0,\qquad I_k=\int_0^\infty u^k e^{-u^3}\,du=\tfrac13\Gamma((k+1)/3).$$
In `gamma_int` the two integrals on $[0,5]$ are computed by integrating the first 560 terms of the Taylor polynomial in $-u^3$. The error is at most the integral of the absolute first omitted term (Taylor remainder); beyond 5 it is at most $e^{-125}/3<(3/8)^{125}/3$ because $u^k\le u^2$ there and $e>8/3$. The cube root is enclosed by integer bisection. This proves $-1<a_1<-1/2$. Both nonzero residue-class series at $s=-v$, $0\le v\le1$, alternate with decreasing absolute terms, the first starting with 1 and the second with $-a_1v$. Thus $F(-v)>0$ on this interval. Evaluating the real series rigorously shows alternating signs starting with positive at zero for the successive arguments $s=-v$, $v=4,6,8,9,11,12,13,14,16,17$. In particular $\lambda_1>1$ and $\lambda_{10}<17$. We also verify $F(1),F(-1)>1/4$, so $M(1),M(-1)<4$.

For samples $u=j/16$, $0\le j\le512$, `Fval` sums terms of the two nonzero residue classes through indices below 660, applying the phase $i^j$ at imaginary arguments. At real arguments it uses their real sign. The absolute ratios within each series in the remaining tail are at most $32^3/[2(662)(663)]<1/2$. Adding twice the sum of the bounds for the next two terms thus encloses both the real and imaginary remainder. Real and imaginary parts of $M(iu)$ are obtained by conjugation and division by the squared modulus; all denominators are certified nonzero.

## 3. A finite Fourier formula with uniform error for all derivatives needed

Use $G=2\pi g$, so that
$$G^{(k)}(x)=\int_{\mathbb R}(-iu)^kM(iu)e^{-iux}\,du.$$
Put $h=1/16$, $T=32$, $L=160$ and $u_j=jh$. For $0\le k\le4$, $|x|\le1$ define the real polynomial
$$
 P_k(x)=h\sum_{|j|\le T/h}(-iu_j)^kM(iu_j)\sum_{l=0}^L\frac{(-iu_j x)^l}{l!}.
$$
We establish **$|G^{(k)}(x)-P_k(x)|<10^{-14}$ uniformly** by separating three errors:

1. **Aliasing from the infinite lattice.** For $a=\pm1$, each factor of (1) is at most one; retaining ten and using $\lambda_{10}<17$ gives $|M(a+iu)|\le4\min(1,(18/|u|)^{10})$. Inverting the Fourier transform of $e^{ax}g(x)$ and differentiating the absolutely integrable formula yields
$$
 |G^{(k)}(x)|\le C e^{-|x|},\qquad C=32(1+18^{10}/5).
$$
Indeed take $a$ with the sign of $x$; the integrand is bounded by $|a+iu|^k|M(a+iu)|$. Split at $|u|=1$, using $|a+iu|^k\le4\max(1,|u|^4)$. Formula (1) with $a=0$ gives the same polynomial decay in the unshifted Fourier formula. The periodization of $G^{(k)}$ with period $2\pi/h$ converges absolutely and uniformly on compact sets, and its absolutely summable Fourier coefficients give $h\sum_{j\in\mathbb Z}(-iu_j)^k M(iu_j)e^{-iu_jx}$. (This follows by integrating over one period, unfolding and using Fourier inversion; constants are for $G=2\pi g$.) All nonzero period translates together contribute at most
$$2C(3/8)^{95}/(1-(3/8)^{96}),$$
since $2\pi/h>96$ and $|x|\le1$.
2. **Discarded high frequencies on the lattice.** Divide the product (1) at $a=0$ between $u\ge T$ and $T$. All ratios are at most one; each of the first ten is at most $\sqrt{17^2+T^2}/u<37/u$. Put $A=|\Re M(iT)|+|\Im M(iT)|$, with its upper endpoint determined at the previous step. For $k\le4$, the two-sided omitted lattice sum, by the integral test for $u^{-6}$, is at most $2A37^{10}/(5T^5)$. The retained endpoints $\pm T$ are not counted in this error.
3. **Replacing phases by polynomials.** The integral Taylor remainder of $e^{-iux}$ has modulus at most $T^{L+1}/(L+1)!$. On the imaginary axis $|M(iu)|\le1$; all retained samples together have total weight $2T+h<2T+1$. Thus the uniform polynomial error is at most $(2T+1)T^{L+5}/(L+1)!$.

The sum of these three rational upper bounds, using the computed enclosure for $A$, is explicitly compared to $10^{-14}$ in the script. This avoids assuming that quadrature accuracy at chosen real sample points extends across an interval.

## 4. Complete interval certificate and conclusion

All numerical claims made here use rational or dyadic integer bounds with directed rounding, not floating-point arithmetic. Dyadic endpoints are integer multiples of $2^{-320}$. Products use the minimum and maximum of all four endpoint products, rounded outward. Division checks that zero is not enclosed. Squaring an interval crossing zero uses zero as its lower endpoint. `mom` encloses the (real) coefficients $h\sum_j (-iu_j)^rM(iu_j)/r!$ using conjugate symmetry and $r=0,\ldots,164$. Multiplying by $(l+k)!/l!$ recovers the coefficient of $x^l$ in $P_k$. Horner evaluation on a closed interval followed by symmetric inflation by $10^{-14}$ encloses the corresponding derivative of $G$ on the entire interval.

Set $v=-(\log G)''$. On a cell, normalize the enclosures for $G',G'',G''',G^{(4)}$ by the same positive enclosure for $G$ to obtain $b,c,d,e$. Then
$$v=b^2-c,\qquad v''=-e+4bd+3c^2-12b^2c+6b^4.$$
The factorization of $f$ implies $\kappa(x)=v(x)+v(-x)$. The certificate checks the following three strict inequalities:
- At the singleton $0$, $3.4051898<2v(0)<3.4051899$.
- On $[0,1/8]$, in 128 closed dyadic subintervals, $v''(x)+v''(-x)>0$. Since $\kappa'(0)=0$ by evenness, this implies $\kappa(x)>\kappa(0)$ for $0<x\le1/8$.
- On $[1/8,1]$, in 582 closed dyadic subintervals, the lower bound on $v(x)+v(-x)$ exceeds the **upper** bound on $\kappa(0)$.

The exact bisection covers both endpoints of every cell; neither an unproved sign nor a zero denominator can be ignored. A depth cap aborts on failure. Applying the cited bound $\kappa(x)>4|x|$ off the unit interval completes the proof for every real $x$. No expression for the sharp constant other than its exact Airy logarithmic derivative at the origin is needed.
