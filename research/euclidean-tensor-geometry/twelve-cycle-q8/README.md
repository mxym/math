# Alternating twelve-cycle: full rank in dimension eight and all larger powers of two

**Yongxian Zhang.** AI-assisted proof development and independent internal replay; no external peer review claimed.

Let \(F_{12}(q)\) be the maximum complex rank of the alternating flattening on the periodic twelve-cycle, with the same local tensor at all sites and with physical and virtual dimensions both \(q\). An explicit integer tensor gives
\[
F_{12}(8)=8^6=262144.
\]
Consequently \(F_{12}(2^m)=2^{6m}\) for every \(m\ge2\). The previously known binary result is \(F_{12}(2)=48\); \(F_{12}(1)=1\) trivially. This classifies the powers of two, not all dimensions. See also the [distinct dimension-seven certificate](../twelve-cycle-q7/README.md).

## Integer slices

Identify the eight labels with the elements of \(\mathbb F_2[u]/(u^3+u+1)\), encoded by bits \(1,u,u^2\). Addition is XOR and multiplication by \(u\) has order seven on nonzero labels. These operations only permute indices. The actual matrix entries of our tensor are integers, and the proof computes their ranks over \(\mathbb F_{43}\), not characteristic two.

Set \(A_a e_x=w(a,x)e_{x+a}\). The rows of \(w(a,x)\), in bit-encoding order, are
~~~text
40 40 40 40 40 40 40 40
12 39  2 38 38 30 15 27
12 30 39 38  2 27 38 15
12 15 27 39 30 38  2 38
12 27 30  2 39 15 38 38
12  2 38 15 38 39 27 30
12 38 15 30 27 38 39  2
12 38 38 27 15  2 30 39
~~~
There are ten orbits under \((a,x)\mapsto(ua,ux)\). As in the dimension-seven proof, use \(M_{a,b}=\operatorname{tr}(A_{b_5}A_{a_5}\cdots A_{b_0}A_{a_0})\), and let \(R\) move the first letter to last. Then \(M^\mathsf{T}=MR\), \(MR=RM\), and \(M\) commutes with the simultaneous multiplication \(S\) of all letters by \(u\). The last identity follows by conjugating every \(A_a\) by the virtual label permutation. Each entry is a sum over eight starting states, obtained by following the twelve alternating letters and multiplying the visited weights. A path returns to its start exactly when the XOR of the two word charges is zero. Thus \(M\) preserves each charge; all seven nonzero charges have the same block ranks by \(S\).

## Exact block check

In \(\mathbb F_{43}\), \(3\) has order \(42\). Write \(\zeta=3^7\) and \(\eta=3^6\) for roots of orders six and seven. Rotation splits every charge into indices \(j\) with eigenvalues \(\zeta^j\). In charge zero also split the multiplier into indices \(k\) with eigenvalues \(\eta^k\). The orbit basis uses coefficient \(\zeta^{-jr}\eta^{-km}\) at \(R^rS^m v\), with one eligible representative per orbit (discard any orbit where two assignments conflict). For nonzero charge use only \(R\). The matrix of \(M\) is obtained by summing along each weighted column orbit and evaluating at each row representative. This decomposition is a direct sum because \(43\nmid42\) and the roots split the two finite-order operators. Transposition and \(M^\mathsf T=MR\) identify ranks of \((j,k)\) and \((-j,-k)\) in each charge. For nonzero charges this means check just \(j=0,1,2,3\). In charge zero, check \(k=0, j=0,1,2,3\) and \(k=1,2,3\) with all six \(j\).

All checked blocks are full rank in two implementations. The dimensions (and exact ranks) are:
 
| Charge | Multiplier index | Rotation indices \(j=0,1,2,3,4,5\) |
|---|---|---|
| \(1\) (representative of all nonzero) | not used | \(5464,5460,5460,5464,5460,5460\) |
| \(0\) | \(0\) | \(794,768,792,768,792,768\) |
| \(0\) | each \(k\ne0\) | \(793,768,792,768,792,768\) |

For an independent dimension count, if a rotation has cycles of length \(\ell\), the fixed-word count under that rotation is \(8^{6/\ell-1}\) in every charge for odd \(\ell\); for even \(\ell\) it is \(8^{6/\ell}\) in charge zero and zero otherwise. Composing with a nontrivial multiplier fixes only the all-zero word, since an orbit with a nonzero label must have \(\ell\) divisible by seven. Projecting these traces to characters gives the table. The C++17 and Node checkers reduce the integer weights modulo 43 and eliminate the exact finite-field blocks. The full determinant is therefore nonzero modulo 43, and hence over \(\mathbb C\). It cannot have rank beyond \(8^6\).

~~~sh
g++ -O3 -std=c++17 -fopenmp c12q8.cpp -o c12q8
./c12q8
# The independent Node checker's arguments are charge, rotation, multiplier:
node check-fast.js 1 3 0
~~~

## Powers of two and product closure

Using slices \(A_a\otimes B_b\) realizes the Kronecker product of the two alternating matrices up to row and column reorderings. Thus the dimensions where full rank holds are closed under multiplication. The [Gesmundo–Landsberg–Walter square-dimension result, Remark I.6](https://arxiv.org/html/1801.09106#S1.SS4) gives \(F_{12}(4)=4^6\). Every integer \(m\ge2\) has the form \(2a+3b\) with \(a,b\ge0\); the product of the dimension-four and dimension-eight witnesses gives full rank at \(2^m\). Multiplication by any previously full-rank dimension gives further exact families. The exceptional binary value \(48\) follows from the [known binary alternating result](https://github.com/mxym/math/releases/tag/periodic-ti-quantum-max-flow-v1.0.0).
