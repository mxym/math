# Proof: the unrestricted Segre clan equation

Let $F=\mathbb F_q$, $q=2^n$, $n\ge3$ odd, $N=q-1$, and $T:F\to\mathbb F_2$ the absolute trace. All logarithms of indices below are avoided: residues of exponents are taken modulo $N$, and bit positions modulo $n$. We prove that **every** function $G:F\to F$ with $G(0)=0$ and

$$T\!\left(\frac{(x+y)(G(x)+G(y))}{x^6+y^6}\right)=1\quad(x\ne y)\tag{1}$$

is $X^5+C^2X+CX^3$ for some $C\in F$. No bound on its degree, no symmetry and no monomial assumption is imposed. The geometric reduction is in [README.md](README.md). The only computer-assisted lemma is the exact finite-language equality in §5, with two separate, short, executable verifications.

## 1. Remove the known solutions

Since $3\nmid N$, the sixth-power map permutes $F$. For $x\ne y$, put $p=xy$ and $D=x^2+xy+y^2$. We have $x^6+y^6=(x+y)^2D^2\ne0$. Expansion gives

$$\frac{(x+y)(x^5+y^5)}{x^6+y^6}=1+(p/D)^2+p/D,\qquad
\frac{(x+y)(C^2(x+y)+C(x^3+y^3))}{x^6+y^6}=(C/D)^2+C/D.$$

Taking traces proves that $X^5$ is a particular solution and $C^2X+CX^3$ a homogeneous one. Expand $G-X^5$ in the unique polynomial representative of degree $<q$. Choose $C$ such that $C^2$ is the linear coefficient and subtract that homogeneous solution. The result has the form $H=\sum_{i=1}^{N}c_iX^i$ with $c_1=0$; the constant is zero because $H(0)=0$. It suffices to prove all $c_i=0$.

For $y\ne0$ write $x=ry$, $r\ne1$. The homogeneous equation is

$$T\left(\sum_{i=1}^{N}c_i\frac{1+r^i}{A(r)}\,y^{i-5}\right)=0,\qquad A(R)=\frac{1+R^6}{1+R}=1+R+R^2+R^3+R^4+R^5.\tag{2}$$

This includes $r=0$. All original pairs occur in this way up to interchange. The only zero of $A$ on $F$ is $1$.

## 2. Decompose the trace into field-linear binary systems

Exponent residues $0,\ldots,N-1$ index an $F$-basis of functions on $F^*$, by the $N$-root bound. Fix such a residue $e$. For each $t=0,\ldots,n-1$, let $i_t\in\{1,\ldots,N\}$ be the **unique** index such that $(i_t-5)2^t\equiv e\pmod N$. Write $b_t=c_{i_t}^{2^t}\in F$ and $L(Z)=\sum_t b_t Z^{2^t}$. Formula (2), after expanding $T(z)=\sum_t z^{2^t}$, says exactly that the coefficient of $y^e$ vanishes, for each $e$. At $r=0$ this means $\sum_t b_t=0$. For $r\in F^*\setminus\{1\}$ the coefficient condition is

$$L(P(r))=r^eL(P(1/r)),\qquad P(r)=1/A(r).\tag{3}$$

Indeed $i_t2^t\equiv e+5\cdot2^t$, and the palindromic identity $A(1/r)=r^{-5}A(r)$ gives $P(1/r)=r^5P(r)$. Set $P(1)=0$. Equation (3) now holds at $r=1$ identically, without using (2) at its pole. Thus (2) is equivalent to these systems for all $e$ **with their induced vectors** $b$. We may classify the relaxed vector space of all $b\in F^n$ for each fixed $e$; any relations forced when $i_t$ repeats can only restrict the result. This point includes short doubling orbits and $e=0$, where indeed all $i_t=5$.

Represent $P$ in $F[R]/(R^N-1)$ by $\sum_{j=0}^{N-1}p_jR^j$; this ring is exactly the algebra of functions on $F^*$. Let $S=\sum_{j=0}^{N-1}R^j$. Its value is 1 at 1 ($N$ is odd), zero elsewhere. Thus $AP=1+S$. Multiplying by $1+R$, using $(1+R)S=0$ in the ring, gives

$$(1+R^6)P=1+R,\qquad p_j+p_{j-6}=[j=0]+[j=1].\tag{4}$$

Let $K=(5N+1)/6=(5q-4)/6$, the representative of $6^{-1}$ modulo $N$. It is even since $q\equiv8\pmod{12}$. In the cyclic order $j=6k$, (4) has precisely two jumps, at $k=0,K$, so its solutions are $p_{6k}=a+[0\le k<K]$ when $k$ is the representative in $[0,N-1]$. As $0=P(1)=Na+K=a$ in characteristic two, we obtain

$$p_{6k}=[0\le k<K]\in\mathbb F_2.\tag{5}$$

Write $X=L(P)=\sum x_j R^j$. Since the $p_j$ are binary, $x_j=\sum_t b_t p_{2^{-t}j}$. Equation (3) is $X(R)=R^e X(R^{-1})$ in the ring, i.e. $x_j=x_{e-j}$ for all $j$. Accordingly (3), with the additional row $\sum b_t=0$, is an **ordinary linear system in the variables $b_t$, with coefficients in $\mathbb F_2$**. Its kernel over $F$ is the $F$-span of the kernel over $\mathbb F_2$, by binary row reduction (or expand each $b_t$ in an $\mathbb F_2$-basis). We can therefore classify **binary** masks $b$; this is not an assumption about the coefficients of $H$.

## 3. Exact coding of the binary system by cyclic words

Fix $g=6^{-1}e\pmod N$. In $x_{6k}=x_{6(g-k)}$, both indices on the reduced scale range over residues modulo $N$. Use $n$-bit integers with positions numbered $0,\dots,n-1$ starting at the **least** significant bit. A residue has its canonical representation $0,\ldots,N-1$; the second binary representation $N$ of zero is discussed below.

For a word encoding $k$, let $u_i(k)$ be the real binary fraction whose periodic expansion begins with bit $i$, then $i-1$, and so on cyclically. Thus for a canonical word $u_{n-1}(k)=k/N$. Put $h_i(k)=[u_i(k)>5/6]$ and $\beta_i=b_{i+1}$ (cyclic $i$). Because $k\ge K$ iff $k/N>5/6$ and multiplying the index by $2^{-t}$ rotates original bit $t-1$ to the top, we have $p_{6\cdot2^{-t}k}=1-h_{t-1}(k)$. The constants cancel in the two reflected coefficients. The binary system is therefore exactly:

$$\sum_i\beta_i=0\pmod2,\qquad
\sum_i\beta_i\big(h_i(k)+h_i(l)\big)=0\pmod2
\quad\text{whenever } k+l\equiv g\pmod N.\tag{6}$$

The complement and all subscripts in (6) apply to a fixed choice of orientation; the change from $b$ to $\beta$ must not be omitted.

For odd $n$ the periodic fractions never equal $1/3$ or $2/3$ since $3\nmid N$. Classify $u_{i-1}$ as A, B, C according as it belongs to $[0,1/3)$, $(1/3,2/3)$, $(2/3,1]$. On appending the new more significant bit $a$ at position $i$, the new fraction is $(a+u_{i-1})/2$. Its class and output $h_i$ are therefore given by

| prior | next on 0 | next on 1 | output on 0 | output on 1 |
|---|---|---|---|---|
| A | A | B | 0 | 0 |
| B | A | C | 0 | 0 |
| C | B | C | 0 | 1 |

There is just one consistent cyclic class trajectory for each word of odd length. Indeed it contains adjacent equal bits cyclically (an odd cycle cannot alternate); $00$ sends all classes to A and $11$ sends all to C. The actual real fractions furnish one such trajectory. This argument also covers the constant words representing 0 and 1 as fractions.

## 4. The 18-state parity transducer

The input alphabet consists of the four letters $z_i=2g_i+\beta_i$, read least significant first. States are $(s,v,c)\in\{\mathrm A,\mathrm B,\mathrm C\}^2\times\{0,1\}$, the two previous fraction classes and the cyclic carry. On an input letter, guess the two bits $a,d$ of $k,l$ subject to

$$a+d+c=g_i+2c',\qquad c'\in\{0,1\}.$$

Update the two classes by the table and the carry to $c'$. The edge label in $\mathbb F_2$ is $\beta_i([s=\mathrm C]a+[v=\mathrm C]d)$. For the whole input, consider all paths whose terminal **18-state vertex** equals their initial vertex. Their accumulated edge parities are exactly the possible witness parities in (6), in the sense that an odd closed path exists if and only if there is a violating pair.

Here are the representation details for that last equivalence. Summing the carry equations with weights $2^i$ on a closed path gives $k+l=g+Nc_0$. Hence every path gives a legitimate modular pair. For canonical $0\le k,l,g<N$ with this congruence, $k+l-g$ is 0 or $N$. Choose $c_0=(k+l-g)/N$ and use ordinary binary addition of $k+l+c_0=g+q c_0$; this supplies the required carry cycle since $q=N+1$. The classes close by the preceding paragraph. A path may use the redundant all-ones word for residue zero: its $h_i$ are all one rather than all zero. This flips its weighted sum by $\sum\beta_i=0$ and cannot produce a false odd witness. We do **not** assert every choice of redundant representations admits a carry cycle; for example $k=l=N,g=0$ does not. Only canonical coverage and legitimacy of additional paths are needed. The enumeration also allows the input word $g=N$. For this redundant input, every canonical pair summing to $N$ as integers closes with $c_0=0$; the sole remaining canonical pair $(0,0)$ for this residue has identical outputs and cannot violate (6). Thus testing this extra input does not change the mathematical conclusion.

## 5. All-length finite language lemma (computer-assisted)

**Lemma.** For every odd length $n\ge3$ and even marked parity $\sum\beta_i=0$, the 18-state graph has no odd closed path on $z_0\cdots z_{n-1}$ if and only if either all marks vanish or the word is a cyclic rotation of

$$1(02)^k03,\qquad k\ge0.\tag{7}$$

The two independently implemented finite closures supplied with this proof verify the lemma. Neither construction has any upper bound on word length.

* **Forward certificate.** Encode each word by its exact relation on start vertex, end vertex and path parity. For each of the 18 start vertices store a 36-bit row; bit $j+18p$ denotes an attainable endpoint $j$ at parity $p$. Initial rows encode the identity. Appending a letter replaces each set bit by the union of the possible next endpoints, adding its parity to the edge parity. Number vertex $(s,v,c)$ by $2(3s+v)+c$ with A,B,C numbered 0,1,2. There is an odd closed path iff start row $i$ has bit $18+i$. Starting at identity and appending every letter to each newly discovered relation until closure gives exactly **4,917** relations. To compare against (7), track zero marks, mark parity, length parity, length capped at 3, first and last letter, internal pair legality, and number of letter 1 capped at two. The allowed cyclic pairs are $31,10,02,03,20$. Taken with exactly one letter 1, these are equivalent to (7): start at 1, proceed to 0, perform zero or more $2,0$ steps, then the sole 3 returns to 1. The reachable product has **25,906** states; **6,498** have eligible length/parity, of which **34** accept; direct and target acceptance agree at every eligible state. These numbers count product states, not words. [`verify_language.py`](verify_language.py) reconstructs the whole closure; equality follows by induction on the length of an input because every letter-transition was explored from every reachable state.
* **Independent reverse certificate.** [`verify_reverse.py`](verify_reverse.py) reads the word in the opposite order, prepends edges and stores separate even/odd endpoint masks. It computes each class update by the integer formula $\lfloor(3a+s)/2\rfloor$ for class number $s$. Eligible parity and length are incorporated into the acceptance language itself. The comparison machine does not use the list of allowed letter pairs: in most-significant-first order the nonzero pattern requires exactly one cyclic $00$ in the $g$-track, no $11$, with the second zero and the next position marked. Its cyclic boundary is checked by revisiting the first two digits. The two reachable deterministic machines have **8,833** and **1,839** states. Partition refinement by acceptance and the four destination classes, followed by canonical rooted numbering, gives *identical transition tables and accepting sets* with **19** states each, in five refinement rounds. This independently proves equality for every finite input.

## 6. Decode the solutions and remove the gauge

The base word of (7) of length $n=2k+3$ has LSB-first marks at positions $0,n-1$, corresponding to $b_0=b_1=1$, all other $b_t=0$. Its $g$ track has binary integer value $g_0=2(q-2)/3$: its set positions are $2,4,\dots,n-1$. Then $6g_0\equiv -4\pmod N$. Rotating both tracks shifts the bits by some $s$, i.e. multiplies both encoded words by $2^s$ modulo $N$. Thus the only nonzero binary vectors occur for

$$e=-4\cdot 2^s\pmod N,\quad b_s=b_{s+1}=1,\quad b_t=0\ (t\notin\{s,s+1\}).\tag{8}$$

For fixed $e$ the shift $s$ is unique modulo $n$, since $2$ has exact order $n$ modulo $2^n-1$ (for $0<j<n$, $0<2^j-1<N$). In particular $e=0$ permits no nonzero vector, as $N\ge7$. As a direct check of the allowed masks, for $u=P(r)$ and $u'=r^5u$ one has $(u')^2+u'=r^4(u^2+u)$ by multiplication by $A(r)^2$; its Frobenius powers yield (8). The general linear system over $F$ therefore has zero kernel except in (8), where it is the $F$-line generated by this binary vector.

For an exceptional $e$, the index $i_s$ is exactly 1 because $(1-5)2^s=e$. Its entry $b_s=c_1^{2^s}=0$ by the prior gauge normalization. Hence even the exceptional vector for the actual $H$ is zero. Every $e$ therefore has zero induced vector; taking $e=i-5$ and $t=0$ gives $c_i=0$ for every $1\le i\le N$. This proves the claimed arbitrary-function theorem. ∎
