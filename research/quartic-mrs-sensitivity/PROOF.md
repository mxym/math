# Exact sensitivity of the two nonconsecutive quartics of width four

Let $S\subseteq\mathbb Z_n$ be a four-element support. The Boolean function $f_{S,n}$ is the XOR of the quartic monomials indexed by the **distinct** translates of $S$. Its sensitivity $s(S,n)$ is the largest, over binary inputs, number of bit positions whose individual flip changes the function. We answer two infinite families of the general quartic problem explicitly posed in [Li–Zhang, §10](https://arxiv.org/pdf/2610.17006v2).

For $A=\{0,1,2,4\}$ and $B=\{0,1,3,4\}$, define
\[
 d=(0,2,1,1,2,1),\qquad
 e=(0,0,1,2,3,4,5,6,7,8,8),
\]
with both tuples indexed from zero. The exact values are
\[
 s(A,n)=n-d_{n\bmod6}\quad(n\ge9);
 \qquad s(B,n)=10\lfloor n/11\rfloor+e_{n\bmod11}\quad(n\ge7).
\]
For $n=5,6,7,8$, the values for $A$ are $4,6,4,7$, and for $B$ are $4,4,6,7$. The latter includes a short orbit at $n=6$ consisting of three monomials. In particular $s(B,n)/n\to10/11$, unlike the previously known consecutive family, whose insensitive deficit is bounded. These are all nonconsecutive normalized width-four supports up to reflection. The conclusions also give exact formulas for all dilations, as explained below.

## 1. Derivative as a local score

Fix a set of integer offsets $S\subseteq[0,L]$ with endpoints 0 and $L$. For $n>2L$, the support has a unique largest circular gap (from $L$ to 0), so the orbit has full length $n$. Each coordinate $j$ belongs to the four distinct orbit monomials beginning at $j-a$ for $a\in S$. The Boolean derivative in coordinate $j$ is
\[
 D_j(x)=\bigoplus_{a\in S}\prod_{b\in S\setminus\{a\}}x_{j+(b-a)}.
\]
Regard $D_j(x)$ as the integer 0 or 1 after evaluating the XOR. Its evaluation uses a window of length $2L+1$. The sensitivity at $x$ is the ordinary integer sum $\sum_{j\in\mathbb Z_n}D_j(x)$.

Consider the binary de Bruijn graph on words of length $2L$, with an edge for appending each bit and dropping the oldest. On that edge the length-$2L+1$ window is known, so give the edge weight $D$ from the center position. This uses high-order bits for older entries in the verifier; the bit relative to the center at offset $b-a$ has numerical index $L-(b-a)$. A length-$n$ periodic word gives a closed walk of weight equal to its sensitivity. Conversely the overlap rule determines every state on a closed walk from the last $2L$ input bits of its periodic label sequence, even if $n<2L$. Thus the score is exactly the maximum diagonal entry of the $n$-th max-plus matrix power. The identification with sensitivity as stated applies to $n>2L$. For smaller $n$ use the distinct-orbit truth table, or remove duplicate derivative templates modulo $n$ before assigning weights.

## 2. Finite matrix equalities certify the infinite formulas

Normalize each edge by $w=qD-p$. Use absence weight $-\infty$, multiplication as addition, addition as maximum. Let $C$ be the resulting $256\times256$ matrix for $L=4$, and put
\[
 M_n(u,v)=\max\{\text{normalized total weight of a length }n
                    \text{ walk from }u\text{ to }v\}.
\]
Initialize $M_0(u,u)=0$ with all other entries absent. If $v$ is the binary integer encoding the target state, its two possible predecessors are $v\mathbin{\mathrm{div}}2$ and $(v+256)\mathbin{\mathrm{div}}2$. Apply
\[
 M_{n+1}(u,v)=\max_{a\to v}\bigl(M_n(u,a)+w(a,v)\bigr).
\]
With this recurrence, the supplied finite certificate verifies the **whole matrices**
\[
 C^{27}=C^{33}\quad(A,\ p=q=1), \qquad
 C^{31}=C^{42}\quad(B,\ p=10,\ q=11).
\]
Each equality is checked at all 65,536 entries, not merely on diagonal maxima. An equality $C^T=C^{T+P}$ implies equality after any further power by multiplication by the same $C^k$. Since $\max_u M_n(u,u)=q\,s(S,n)-pn$ for $n\ge9$, the stated increment is $6$ per six steps for $A$, and $10$ per eleven for $B$, starting from their respective equality thresholds. The verifier checks every diagonal maximum from $n=9$ through the transient and one full tail period. This determines every later value by induction. It independently enumerates the complete truth table for $5\le n\le8$, deduplicating the orbit supports. For every larger checked length through the power equality, an independent exact search on the actual finite-period ANF confirms an attaining input and excludes every higher sensitivity. It cuts a binary prefix only when the number of already evaluated insensitive coordinates exceeds the available budget; those outputs cannot change when more variables are assigned. The negative-infinity sentinel implementation treats the sentinel separately; the largest possible path magnitude in these calculations is at most $420$, well separated from the sentinel.

## 3. Reflection and dilation

Reflecting a support permutes the input variables and preserves sensitivity. The remaining width-four nonconsecutive set $\{0,2,3,4\}$ is the reflection of $A$ about 2. These, plus $B$, exhaust the choices of two internal positions from $\{1,2,3\}$. A translation of the generator does not change its orbit.

For a positive integer $t$, put $g=\gcd(n,t)$ and $m=n/g$. When $m\ge5$, the four offsets in $tA$ or $tB$ remain distinct. Each residue class modulo $g$ gives one independent block of $m$ coordinates. Writing a variable in that coset by its index in the progression with step $t$, the distinct orbit summands on that block are exactly the distinct translates of $A$ or $B$ in $\mathbb Z_m$. Distinct cosets use disjoint coordinates. The overall function is the XOR of the $g$ disjoint block functions; a flip changes the whole output iff it changes its own block. Therefore sensitivity is additive over blocks, and maximizing each independently gives $s(tS,n)=g\,s(S,m)$ for $S=A,B$. This includes the short orbit of $B$ when $m=6$.

## 4. A general finite-width consequence

For any fixed normalized support (of any fixed degree), the local derivative graph above gives exact sensitivity once $n>2L$; a finite number of smaller cases can be handled separately by distinct orbit. It also gives an effective eventual affine-periodic formula. This is an application of the classical max-plus cyclicity theorem; an elementary argument suffices here.

All states of the graph communicate (append the bits of the target), and there is a loop at the all-zero state. Let $p/q$ be the largest mean weight of a simple cycle, written as a reduced rational. For the normalized integer edge weight $qD-p$, every directed cycle has nonpositive sum, and at least one cycle has sum zero. Deleting cycles from a path shows that its normalized weight is bounded above by the largest weight of a simple path. For a uniform lower bound on optimum path weights of every sufficiently large length and every endpoints $u,v$, fix a path from $u$ through the zero state to some fixed critical cycle vertex, and another from that vertex to $v$. Fill any required remaining length by repeating the critical cycle and using the zero loop for the residue modulo its length. Only a bounded number of zero loops are needed and the critical cycles do not change the weight. Thus all long normalized matrix powers have entries in a single bounded set of integers; the deterministic power recurrence eventually repeats a matrix. The maximum diagonal entry is then periodic, and undoing the normalization gives the rational-slope affine-periodic law.

This supplies an exact finite procedure for every fixed support, not a uniform closed form for arbitrary quartic supports with growing width. In the two families above, the explicit matrix equalities eliminate any reliance on an unproved recurrence or extrapolation. The fractional-slope family shows why restricting attention to bounded deficits would miss real behavior.
