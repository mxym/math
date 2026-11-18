# Exact two-adic valuations for a family of elementary symmetric Boolean polynomials

This note proves the formula proposed in [Castro, González, Medina, Negrón and Rubio, Conjecture 6.1, p. 9 (2017)](https://ccom.uprrp.edu/~labemmy/Wordpress/wp-content/uploads/2022/12/Raul-Oscar-paper.pdf), on the natural degree domain. It does not resolve the general Cusick–Li–Stănică conjecture.

Write $v=v_2$ with $v(0)=+\infty$, and let $w(u)$ be the number of ones in the binary expansion of $u$. The elementary symmetric polynomial $\sigma_{n,k}$ of degree $1\le k\le n$ over $\mathbb F_2$ is the sum of all squarefree degree-$k$ monomials in $n$ variables. On an input of Hamming weight $j$, its value is $\binom jk\bmod 2$. Write $W$ for the number of inputs on which it is one. Its exponential sum is

$$
S=\sum_{x\in\mathbb F_2^n}(-1)^{\sigma_{n,k}(x)}=2^n-2W.
$$

By Lucas's theorem, $W$ is the sum of $\binom nj$ over $0\le j\le n$ whose binary expansion contains every set bit of $k$.

**Theorem.** Let $a,s,i$ be integers with $a\ge2$, $s\ge0$, $i\ge 2^{s+1}+s$. Let $r\in\{0,1\}$, let $m$ be positive odd, and set
$$
n=2^a(2^i-1)+r,\qquad k=2^a(2^{i-s}m-1).
$$
Assume $1\le k\le n$, equivalently $m\le2^s$. For $\ell=\lfloor\log_2m\rfloor$,
$$
v(S)=
\begin{cases}
2(2^s-1)+r+1,&m=1,\\
2^{s-\ell}-w(m)+\ell+r+1,&m>1.
\end{cases}
$$
In particular, $S\ne0$ on this family. The two branches correspond to $\ell=0$ and $\ell\ge1$ in the original statement's leading-bit decomposition $m=2^\ell+q$, $0\le q<2^\ell$.

## 1. Binomial sums with prescribed zero bits

**Lemma.** Let $P=2^p$, $p\ge1$, and let $N$ be a positive multiple of $P$. On the low $p$ bits of $j$ prescribe bits $0$ and $p-1$ to be zero (the same bit if $p=1$), and prescribe any subset of the intermediate bits also to be zero. Leave $f$ bits unrestricted. Let $W_p$ be the sum of $\binom{N-1}j$ over all $0\le j<N$ obeying these prescriptions. Then
$$
v(W_p)=N/2^{p-1}-2+f. \tag{1}
$$

**Signed half-period.** Suppose $p\ge2$. Put $e=P/2$, $T=N/e$ (a positive even integer), and work with degree-$<e$ representatives in $R=\mathbb Z[x]/(x^e+1)$. Define $U=(1+x)^e/2$ in $R$. This division is integral: the constant and $x^e$ cancel, and all interior coefficients are even. For $0<k<e$, put $t(k)=\log_2(e)-v(k)$ and set $t(0)=0$. If $u_k=[x^k]U$, then
$$
v(u_k)=t(k)-1\quad(0<k<e)
$$
because $\binom ek=(e/k)\binom{e-1}{k-1}$ and the latter binomial is odd. Also $u_0=0$ and $U\equiv x^{e/2}\pmod2$.

We claim that $U^T=\sum_{k=0}^{e-1}c_k x^k$ has odd $c_0$ and $v(c_k)\ge t(k)$ for $k>0$. Indeed, $2^{t(k)}$ is the additive order of $k$ modulo $e$, so $t((i+j)\bmod e)\le\max(t(i),t(j))$. In $U^2$ two distinct positive exponents $i,j$ contribute together with order $t(i)+t(j)-1\ge\max(t(i),t(j))$. A diagonal contribution has order $2(t(i)-1)\ge t(2i\bmod e)$. Reduction modulo $x^e+1$ changes only signs at wraps. Since $U^2\equiv1\pmod2$, its constant term is odd. The coefficient divisibility conditions $2^{t(k)}\mid c_k$ are multiplicatively closed by the additive-order bound. Taking the positive integral power $(U^2)^{T/2}$ proves the claim.

Let $F\subseteq\{0,\ldots,e-1\}$ be the permitted residues in the lower half-period. All are even and $|F|=2^f$. For $B(x)=\sum_{j=0}^{e-1}(-x)^j$ we have $(1+x)B=2$ in $R$. Let $v_k=\sum_{r\in F}[x^r](x^k B)$, taking coefficients after reduction. Then $v_0=2^f$; and for $0<k<e$, the terms that wrap land at $r<k$, so
$$
v_k=(-1)^k\bigl(2^f-2\,|\{r\in F:r<k\}|\bigr).
$$
The cut at $k$ lies between blocks of length $2^{v(k)}=e/2^{t(k)}$. At most $t(k)$ freely varying bit positions lie in the upper prefix. For each permissible upper prefix below the cut, the number of choices of lower bits is thus divisible by $2^{\max(0,f-t(k))}$. If $1\le t(k)\le f$, both terms of the parenthesis are divisible by $2^{f-t(k)+1}$. If $t(k)>f$, then $2^{f+1}\mid c_k$ already. Thus $2^{f+1}\mid c_kv_k$ for all $k>0$, whereas $v(c_0v_0)=f$.

Since $(1+x)^N=2^T U^T$ and $(1+x)B=2$, cancellation of 2 in the free abelian group $R$ gives $(1+x)^{N-1}=2^{T-1} U^T B$. The sum $V$ of its coefficients on $F$ therefore has
$$
v(V)=T-1+f. \tag{2}
$$

**Recover the unsigned sum.** Induct on $p$. For $p=1$ the even-index sum is $2^{N-2}$, including $N=2$. For $p\ge2$ take the same sum of coefficients on $F$ in $\mathbb Z[x]/(x^e-1)$ instead, and call it $H$. In a given class modulo $e$, $H$ adds its two classes modulo $2e$, while $V$ subtracts the upper from the lower. Consequently $2W_p=H+V$.

Let $p'-1$ be the highest prescribed zero below $p-1$; it exists since bit 0 is required. Put $g=p-p'\ge1$. All $g-1$ intervening bits are free, so $H$ is exactly the ordinary restricted sum with period $2^{p'}$ and $f'=f-(g-1)$ free bits. The multiplicities already occur in that sum over $0\le j<N$. By induction and (2),
$$
v(H)-v(V)=\bigl(2^gT-2+f-(g-1)\bigr)-(T-1+f)
=(2^g-1)T-g>0
$$
because $T\ge2$. Hence $v(2W_p)=v(V)$, proving (1).

## 2. Reduction to the lemma

Set $A=2^a$, $L=2^s$, $M=i-s\ge2L$, $D=2^{a+M}$, $d=a+M$, $N=LD$. Thus $n=N-A+r$ and $k=mD-A$. The low $d$ bits of $k$ are those of $D-A$; its higher bits encode $m-1$. Every selected layer of weight $j\le n$ has the unique form
$$
j=uD-A+b,\qquad 1\le u\le L,\quad 0\le b<A,
$$
where $u-1$ contains all set bits of $m-1$, with the upper endpoint additionally subject to $j\le n$. By binomial symmetry consider $t=n-j=hD+r-b$, $h=L-u$. The high word $u-1=L-1-h$ is the $s$-bit complement of $h$. The allowed anchors are therefore those $0\le h<L$ having no set bits in common with $m-1$. For $h=0$ only $b\le r$ is allowed; for $h>0$ every $b$ is allowed. When $s=0$ the high word is empty.

Every negative offset $t=hD-w$, $1\le w\le A-1-r$, has $h\ge1$. Both $w$ and $A-r-w$ lie in $[1,A-1]$. Thus both $hD-w$ and $n-t=(L-h)D-(A-r-w)$ have every bit $a,\ldots,d-1$ set. Adding them produces at least $d-a=M$ binary carries. By Kummer's theorem, $2^M\mid\binom nt$. Only offset 0 and (when $r=1$) offset 1 remain modulo $2^M$.

For $t=hD$, descending from row $N-1$ to $n$ gives
$$
\binom nt=\binom{N-1}t\prod_{j=1}^{A-r-1}\left(1-\frac{t}{N-j}\right).
$$
Each factor is 1 modulo $2^{M+1}$ in the two-adic integers: $v(N-j)=v(j)\le a-1$ and $D\mid t$. At $h=0$ the factors equal 1. For $r=1$, also
$$
\binom n{t+1}=\binom nt\frac{n-t}{t+1}\equiv n\binom nt\pmod{2^M}
$$
since $D\mid t$ and $t+1$ is odd. The largest potential anchor plus $r$ is $(L-1)D+r\le n$. Hence, writing $h\mathbin{\&}(m-1)=0$ for disjoint binary supports, we have
$$
W\equiv C_r W_*\pmod{2^M},\qquad
W_*=\sum_{\substack{0\le h<L\\ h\mathbin{\&}(m-1)=0}}\binom{N-1}{hD},\qquad
C_0=1,\quad C_1=n+1=N-A+2. \tag{3}
$$
In particular $v(C_r)=r$, using $a\ge2$.

All low $d$ bits in $W_*$ are fixed at zero. If $m=1$ there are no other fixed bits; with $P=D$, $f=0$, (1) gives $V_0:=v(W_*)=2L-2$. If $m>1$, then $1\le\ell\le s-1$ and bit $d+\ell$ is the highest prescribed zero. We use $P=2^{d+\ell+1}$, a divisor of $N$. Of the $\ell$ positions $d,\ldots,d+\ell-1$, exactly $w(m)-2$ are constrained: subtracting one from odd $m$ removes its bottom bit, and the set bit at the top lies outside this list. Thus (1) gives
$$
V_0=2^{s-\ell}-2+(\ell-w(m)+2)=2^{s-\ell}-w(m)+\ell.
$$
In this branch $s\ge2$ and $w(m)\ge2$, so $V_0\le L/2+s-3\le2L-2$. In either branch $V_0+r\le2L-1<M$. Equation (3) therefore yields $v(W)=V_0+r$ exactly. Since $n>2L\ge V_0+r+1$, it follows that $v(2^n-2W)=V_0+r+1$, proving the theorem.
