# One common sign on both genuine bounded-rank inputs

For every fixed integer $R\ge2$ and $\epsilon>0$, there is an explicit score $J_R$ on the actual summands such that for each sufficiently large prescribed even $P$
$$
 \left|G(P)-X_P-\sum_{x\in I,\,(x,P)=1}J_R(x)J_R(P-x)\right|<\epsilon X_P,\qquad
       J_R(x)\le0\quad (\Omega(x)\le R).                           \tag{1}
$$
Notation: $I=[P/3,2P/3]$, $G$ counts true central two-prime pairs with their two logs, $X_P=|I|\mathfrak S(P)$. Both actual legs have the same score; every adverse (negative) summand in (1) has at least one input with $>R$ prime factors. This is a modification of, not a simultaneous strengthening of, the [complementary half-divisor score](https://github.com/mxym/math/commit/bf13a6e1d1a9b35bdea274481e7a9c4e2d26a1b8): semiprimes need not vanish for the new score. Neither $R\to\infty$ at a fixed roughness nor any bound on the adverse higher-rank population follows.

## Physical score and its sign

Choose sufficiently small $0<\theta<1/20$ after $R,\epsilon$. Put $\eta=\theta^2$, $W=P^\eta$, $A=P^\theta$, $D=P^{1/2-\theta}$, $Y(x)=\mathbf1_{P^-(x)>W}$, $\phi_R(u)=(1-2u)_+^R$ for $u\ge0$. Define
$$
 F(x)=Y(x)\bigg[\sum_{d|x,\,d\le A}\mu(d)\log(x/d)
        +\sum_{d|x,\,A<d\le D}\mu(d)(\log x)\phi_R(\log d/\log x)\bigg],
 \qquad K(x)=Y(x)\Lambda(x)-F(x).
$$
Set $J_R$ to zero outside squarefree $W$-rough composites, to $K(x)$ on ranks $>R$ there, and on their ranks $2\le k\le R$ put
$$
 J_R(x)=-(\log x)\sum_{d|x}\mu(d)\phi_R(\log d/\log x).                \tag{2}
$$
Independently of any target averaging, the divisor sum in (2) is nonnegative. For $x=r_1\cdots r_k$ let $v_i=\log r_i/\log x$; its value is $(-1)^k\Delta_{v_1}\cdots\Delta_{v_k}\phi_R(0)$, for $\Delta_h f(u)=f(u+h)-f(u)$. The $k$th derivative of $\phi_R$ has sign $(-1)^k$ on the positive line in the a.e. sense, including at $k=R$ where it is a bounded step. The finite-difference formula integrates that derivative over $\prod_i[0,v_i]$; the sign in (1) follows. One could not extend this sign to arbitrarily many derivatives of this fixed compactly supported power.

## Why the calibrated main survives

The derivative of $\phi_R$ at the origin is $-2R$, **not** $-1$. We do not use an unpatched extrapolation: on every $d\le A$ the actual source uses the old $\mu(d)\log(x/d)$. Write $F_0,K_0$ for the patched *flat* medium coefficients in [the bounded-rank transfer, §§1–3](https://github.com/mxym/math/commit/bf13a6e1d1a9b35bdea274481e7a9c4e2d26a1b8). The difference $E_0=F-F_0$ is an actual medium divisor convolution with $A<d\le D$, $x=db$ and weight $\mu(d)(\log x)[\phi_R(\log d/\log x)-1]$ on $W$-rough inputs. Both slots have fixed polynomial length and the multiplier is bounded times $\log x$, with bounded $R$-dependent variation in the normalized log variables. All coupled constraints separate on relative log-fine boxes exactly as for the earlier source calculation; since $\log x\asymp\log P$, the unnormalized within-box variation is $O_R((\log P)^{-B})$ on mesh $1+(\log P)^{-B}$. This also holds for the sign-split weights.

Under the source sieve principal the change in the normalized $d$ multiplier is
$$ e^{-\gamma_E}\eta^{-1}\int_{\theta/\eta}^{(1/2-\theta)/\eta}
            [\phi_R(\eta u)-1]\rho'(u)\,du+o_{\theta,R}(1).
$$
Its magnitude in limsup is at most $\eta^{-1}\rho(\theta/\eta)$, uniformly with the original input target-unit masks and central archimedean log. The ordinary mean of $E_0$, needed on the other side, is likewise bounded by $\eta^{-1}\rho(\theta/\eta)$ in limsup: its integrand has the additional rough cofactor density $\omega(1/\eta-u)\le1$ and no singular endpoint. Thus the new $F$ has the same $1+o_{\theta\downarrow0}(1)$ calibrated multiplier as $F_0$, and $K=K_0-E_0$ has ordinary signed mean tending to zero. The absolute masses of the separate polynomial convolutions remain $O(\eta^{-2})$, from the ordinary positive rough cofactor estimate. Opening the actual short $d$ and sieving the free factor at $P^{\theta/2}$ stays strictly inside the square-root rail ($de\le P^{1/2-\theta/2}$). Its relative fixed error $\Delta(1/(2\theta))$ times the $O(\eta^{-4})$ absolute budget tends to zero faster than any fixed power of $\theta$. The earlier source argument therefore yields $G=X_P+\langle K,K\rangle_P+o_{\theta\downarrow0}(1)X_P+o_{P;\theta,R}(X_P)$. This notation takes the $P$ limit first.

## Replacing the actual bounded-rank mixed terms

Set $S=J_R-K$. Discard squareful rough rows at power cost at fixed $\eta$ as before. On rank $2\le k\le R$ each of the at most $2^R$ divisor weights differs by $O_R(\theta\log P)$ between the patched and ideal scores: on $d\le A$ use $|1-u-\phi_R(u)|\ll_R u$; on $d>D$ an ideal nonzero weight has $u\in[1/2-O(\theta),1/2]$ and is $O_R(\theta^R)$. The actual prime rows both have score zero. Hence $|S|\ll_R\theta\log P$ on its support, with no exceptional square-root strip at all. Selecting the largest prime factor and summing the others harmonically gives $m_{|S|}\ll_R\theta(1+\log(1/\eta))^{R-1}+o_{P;\theta,R}(1)$ in units of $|I|$. These are ordinary marginals, not yet reflected errors.

Use the **true finite-rank source transfer** in the cited §§1,3. Its hypotheses persist: finitely many factor-comparison jumps in $A,D$ and ordering, piecewise Lipschitz log scores on each independent factor rectangle, also after absolute and positive parts. The argument proves centered distribution to every fixed $P^{1/2-c}$ for these specific sources and controls the narrow boundary rectangles by their positive envelopes. It does not cover arbitrary product masks. The signed short-divisor principal just evaluated, plus the positive upper sieve for the reflected true prime, give $|\langle K,S\rangle_P|/X_P\ll_R m_{|S|}+o_{P;\theta,R}(1)$ for small $\theta$. The independent upper bound for $|\langle S,S\rangle_P|/X_P$ costs at most $O_R((1+\log(1/\eta))^{R-1}m_{|S|})+o_{P;\theta,R}(1)$ by opening all partner primes below $P^{1/(10R)}$ and upper-sieving the partner cofactor. As before, its local density at a prime in that opened product is $1/r$ instead of $1/(r-1)$, and every modulus tested is $<P^{.32}$. Thus the *actual* error in replacing both legs tends to zero: expand $\langle K,K\rangle=\langle J_R,J_R\rangle-2\langle K,S\rangle-\langle S,S\rangle$. Choosing $\theta$ and then $P$ proves (1). A complete fixed-target lower bound remains open; in particular (1) does not bound a signed higher-rank interaction by its marginal frequency.
