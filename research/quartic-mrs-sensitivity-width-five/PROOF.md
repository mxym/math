# Exact sensitivity of every width-five quartic cyclic monomial

Let \(D\) be a four-element subset of \(\mathbb Z_n\). Write \(S_D(n)\) for the maximum sensitivity of the Boolean XOR of the monomials indexed by the **distinct** cyclic translates of \(D\). The sensitivity at an input counts the number of coordinates whose individual flip changes the output. We determine \(S_D(n)\) for every normalized support with integer endpoints 0 and 5, for all \(n\ge6\). This is one precise width slice of the arbitrary-quartic problem in [Li–Zhang, Section 10](https://arxiv.org/pdf/2610.17006v2).

Write a four-digit string for its support. There are six normalized supports of width five, with four reflection types:
\[
 0125\leftrightarrow0345,\quad 0135\leftrightarrow0245,\quad
 0145\leftrightarrow0145,\quad 0235\leftrightarrow0235.
\]
The identities follow from the reflection \(a\mapsto5-a\) on the support, which is a permutation of the input coordinates combined with a choice of starting point for the orbit.

## 1. Exact answers

Tuples are indexed starting at zero. For \(0125\), for every \(n\ge35\),
\[
 S_{0125}(n)=n-d_1[n\bmod6], \qquad d_1=(0,3,2,3,3,2).
\]
For \(0135\), for every \(n\ge10\),
\[
 S_{0135}(n)=n-d_2[n\bmod6], \qquad d_2=(0,1,1,2,2,2).
\]
For \(0145\), for **every** \(n\ge6\),
\[
 S_{0145}(n)=n-d_3[n\bmod66],
\]
where \(d_3\) is the tuple shown here on six successive rows of length 11:
\[
\begin{array}{rrrrrrrrrrr}
0&3&2&3&2&1&0&1&2&3&2\\
1&0&2&2&1&2&1&0&3&2&3\\
0&1&0&3&2&3&2&1&0&3&2\\
3&2&1&0&1&2&1&2&1&0&3\\
0&3&2&1&0&3&2&1&2&1&0\\
3&2&2&2&1&0&1&2&3&2&1
\end{array}
\]
For \(0235\), writing \(n=24q+r\), for every \(n\ge17\),
\[
 S_{0235}(n)=22q+e[r],
 \qquad
 e=(0,0,0,2,2,4,4,6,6,8,8,10,10,10,12,12,14,14,16,16,18,18,20,20).
\]

For \(n=6,7,8,9,10\), the four respective sensitivity rows are:
\[
\begin{array}{c|rrrrr}
0125&6&4&7&8&8\\
0135&6&6&7&8&8\\
0145&6&6&6&6&8\\
0235&4&6&6&8&8
\end{array}
\]
In particular the original distinct-orbit convention gives four monomials for \(0145\) at \(n=8\), and three monomials for \(0235\) at \(n=6\). Repeated translates are not cancelled in these definitions. For \(0125\) the remaining interval \(n=11,\ldots,34\) is
\[
(9,12,12,12,13,15,15,18,17,18,19,20,21,24,22,24,25,26,27,30,29,30,30,32).
\]
For \(0235\) the remaining interval \(n=11,\ldots,16\) is \((10,10,10,12,12,12)\).

The least periods of the eventual zero-slope normalized sequences are \(6,6,66,24\), respectively. The first three families have leading sensitivity slope 1, whereas \(0235\) has slope \(11/12\).

## 2. Exact certificate for the infinite formulas

For \(n\ge11\) the largest circular gap of the support is the wrap-around gap from 5 to 0, unique because its length is \(n-5>5\). The orbit is full. The XOR at an input of the monomials containing \(x_j\), computed before and after flipping \(x_j\), changes by
\[
 D_j(x)=\bigoplus_{a\in D}\prod_{b\in D\setminus\{a\}}x_{j+b-a}.
\]
This is the ordinary binary indicator of a sensitive site. Its whole dependence is inside the eleven-site window about \(j\). Summing the indicators as integers gives sensitivity at a fixed word.

Use the de Bruijn graph of ten-bit words. A transition appends one bit and drops the oldest bit; its eleven-bit window gives the derivative at the center. A marked binary word of period \(n\) produces one closed walk whose edge weights are these indicators. Conversely, the state at any marked time of a closed walk is the previous ten bits of its repeated label word, so no closed walk introduces a false sensitivity value. In particular the maximum sensitivity is the maximum diagonal entry of the \(n\)-th max-plus power with those edge weights.

For clarity, the implementation computes each edge score by directly XORing the four center-containing monomials on that eleven-bit window **before and after flipping its center bit**. It does not use a separate assumed list of derivative monomials. Bits are numbered with the oldest at 0 and the newest at 10. There are exactly two predecessor windows of target vertex \(v\), encoded by \(2v\) and \(2v+1\); the low ten bits of a window are its predecessor state.

Normalize an edge weight \(d\in\{0,1\}\) to \(w=q_0d-p_0\). Let \(C\) be the resulting \(1024\times1024\) max-plus matrix and \(M_k\) its \(k\)-th power, with \(M_0\) the max-plus identity. For each source and target, the program computes the maximum of the two predecessor entries plus their normalized edge weights. An absent path stays absent. For \(n\ge11\), the maximum diagonal entry is exactly
\[
 \Delta_n=q_0 S_D(n)-p_0n .
\]
The certificate independently verifies the following equalities of whole matrices, each at 1,048,576 integer entries:

| Support | \(p_0,q_0\) | Power equality | Normalized repeating period |
|---|---:|---|---:|
| 0125 | 1, 1 | \(C^{75}=C^{81}\) | 6 |
| 0135 | 1, 1 | \(C^{40}=C^{46}\) | 6 |
| 0145 | 1, 1 | \(C^{72}=C^{138}\) | 66 |
| 0235 | 11, 12 | \(C^{42}=C^{66}\) | 24 |

Each equality \(C^t=C^{t+P}\) proves the identical equality at every later exponent by right multiplication. The program checks each finite diagonal value through the corresponding power equality, including all residues in the tail, and prints the initial intervals where the final formula does not suffice. Recovering \(S_D(n)\) from \(\Delta_n\) now proves the formulas for every \(n\ge11\). Direct truth tables supply all shorter lengths and verify the two advertised early extensions of the formulas. To see that each printed period is least in the tail, check all proper divisors of the displayed period against the explicit normalized residue tuple, as the program does. Two eventual periods would imply their greatest common divisor is also an eventual period (on a repeated word, this follows by composing rotations). Hence excluding proper divisors suffices.

## 3. Independent checks and dilation

For every length \(6\le n\le20\), the verifier independently builds the actual truth table from the set of distinct translates and maximizes using explicit individual flips. This is independent of derivative weights and matrix orientation. The tests check the short-orbit cardinalities listed above. The corrupted-weight negative control adds 36 to the all-zero loop in the \(0235\) normalized graph; the deliberately damaged graph fails the proposed full-matrix periodicity, while the arithmetic division check is still applicable.

For a dilation \(tD\) on \(n\) bits, put \(g=\gcd(t,n)\) and \(m=n/g\). If the four offsets are distinct modulo \(m\), every coset of the subgroup generated by \(t\) carries a copy of the \(m\)-bit shape, in cyclic step-\(t\) coordinates. Distinct orbit terms within each coset deduplicate just as in the \(m\)-bit function. Because the coordinate blocks are disjoint and combined by XOR, a coordinate flip changes the result iff it changes its own block. Thus maxima add:
\[
 S_{tD}(n)=g S_D(m).
\]
For \(m\ge6\) this uses the formulas above. If \(m=5\), 0 and 5 coincide so no shape remains quartic. If \(m=4\), only \(0235\) retains four distinct residues; it reduces to a single product of all four bits, with sensitivity 4. For \(m\le3\) no quartic can survive. Reflected supports follow under the same coordinate permutations. This establishes the stated width-five slice but makes no all-width structural classification claim.
