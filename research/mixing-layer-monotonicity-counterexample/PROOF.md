# Exact failure of generic mixing-layer monotonicity

## 1. Model and statement

Let \(F\) be the additive group \(\mathbb F_2^3\), represented by the integers \(0,\ldots,7\), with addition written as XOR. On \(F\), use the bijection
\[
S=(0,4,7,2,3,5,6,1),
\]
meaning \(S(0)=0,S(1)=4,\ldots,S(7)=1\). On the two-word state \(F^2\), let
\[
\mathcal S(x,y)=(S(x),S(y)),\qquad
L(x,y)=(x,x+y).
\]
The shear \(L\) is invertible, with \(L^{-1}=L\), and is linear over every realization of \(F\) as \(\mathbb F_8\): its matrix is
\[
\begin{pmatrix}1&0\\1&1\end{pmatrix}.
\]

For \(K\in F^2\), write \(A_K(X)=\mathcal S(X+K)\). Let \(K_0,K_1,K_2\) be independent and uniform in \(F^2\). Compare the keyed permutation families
\[
C_0=A_{K_2}\circ A_{K_1}\circ A_{K_0},\qquad
C_L=A_{K_2}\circ A_{K_1}\circ L\circ A_{K_0}.
\]
Thus \(C_L\) is obtained from \(C_0\) by inserting one invertible linear mixing layer. For the distinct inputs \(0\) and \(\delta=(3,3)\), the statistical distances of their output pairs from the uniform distribution on ordered distinct pairs in \(F^2\) are
\[
\Delta(C_0)=\frac{109}{252},\qquad
\Delta(C_L)=\frac{19}{36},
\]
so
\[
\Delta(C_L)-\Delta(C_0)=\frac{2}{21}>0. \tag{1}
\]

The source paper counts rounds with a final S-box layer and no final mixing; our construction is best described unambiguously as three keyed S-box layers with one inserted internal mixing layer.

## 2. Reduction to a difference distribution

Let \(Y,Y'\) be the two states immediately before the final keyed S-box layer, and put \(D=Y+Y'\ne 0\). For an independent uniform final key \(K_2\), the final pair is
\[
\bigl(\mathcal S(Y+K_2),\mathcal S(Y'+K_2)\bigr).
\]
Apply the bijection \(\mathcal S^{-1}\) to both entries and then map
\[
(a,b)\longmapsto(a,a+b).
\]
The resulting pair is
\[
(Y+K_2,D).
\]
Conditional on all previous randomness, the first component is uniform; moreover, it is independent of \(D\), because \(K_2\) is independent and uniform. A uniform ordered distinct pair is carried by the same bijections to the product of a uniform first component and a uniform nonzero difference. Therefore the full output-pair distance is exactly the distance of the law of \(D\) from the uniform law on the 63 nonzero states.

This is why the last keyed S-box layer need not be enumerated in the transition proof. The independent checker nevertheless enumerates it directly.

## 3. Exact difference table

For \(d,e\in F\), put
\[
N_d(e)=\bigl|\{u\in F:S(u)+S(u+d)=e\}\bigr|.
\]
Direct substitution in the eight-entry table gives, with columns \(e=0,\ldots,7\),
\[
\begin{array}{c|rrrrrrrr}
d&0&1&2&3&4&5&6&7\\ \hline
0&8&0&0&0&0&0&0&0\\
1&0&0&0&0&2&2&2&2\\
2&0&0&0&0&2&2&2&2\\
3&0&0&4&4&0&0&0&0\\
4&0&4&0&4&0&0&0&0\\
5&0&0&0&0&2&2&2&2\\
6&0&0&0&0&2&2&2&2\\
7&0&4&4&0&0&0&0&0
\end{array}. \tag{2}
\]
A fresh uniform word key makes the output difference transition from \(d\) to \(e\) with probability \(N_d(e)/8\), independently in the two words.

Starting at \((3,3)\), after the first keyed S-box layer each word difference is independently 2 or 3, each with probability \(1/2\).

### No inserted layer

The four first-step possibilities \((2,2),(2,3),(3,2),(3,3)\) each have probability \(1/4\). By (2), a word difference 2 has four equiprobable successors \(4,5,6,7\), while a word difference 3 has two equiprobable successors \(2,3\). Their supports are disjoint. Hence after the second keyed S-box layer the nonzero-state distribution has
\[
\begin{array}{c|ccc}
\text{probability}&1/64&1/32&1/16\\ \hline
\text{number of states}&16&16&4
\end{array}. \tag{3}
\]
It has support 36.

### Inserted shear

The shear sends the four equally likely differences to
\[
(2,0),(2,1),(3,1),(3,0).
\]
Using (2) again, their successor supports are disjoint and the resulting histogram is
\[
\begin{array}{c|rrrr}
\text{probability}&1/64&1/32&1/16&1/8\\ \hline
\text{number of states}&16&8&4&2
\end{array}. \tag{4}
\]
It has support 30.

## 4. Total variation

The uniform nonzero-difference probability is \(1/63\). In both (3) and (4), only the \(1/64\) atoms lie below it. Thus total variation is the total deficit:
\[
\Delta(C_0)=\frac{27}{63}
  +16\left(\frac1{63}-\frac1{64}\right)
  =\frac{109}{252},
\]
and
\[
\Delta(C_L)=\frac{33}{63}
  +16\left(\frac1{63}-\frac1{64}\right)
  =\frac{133}{252}=\frac{19}{36}.
\]
Their difference is (1).

This finite example disproves only a universal rule saying that inserting an arbitrary invertible linear layer can never increase pairwise-independence distance. It says nothing about the real AES S-box, the AES mixing layer, the insertion pattern used in the 192-round conjecture, or AES with its deployed key schedule.
