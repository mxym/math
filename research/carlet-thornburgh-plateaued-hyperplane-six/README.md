# Which six-variable Boolean functions extend to a plateaued function?

**Theorem (complete, certificate-based classification for six input variables).**
Write \(W_f\) for the unnormalized Walsh transform of a Boolean function
\(f:\mathbb F_2^6\to\mathbb F_2\), and put
\[
M(f)=\{|W_f(u)|:u\in\mathbb F_2^6,\ W_f(u)\ne0\}.
\]
Then \(f\) is the restriction to an affine hyperplane of a seven-variable
plateaued Boolean function, up to affine identification of the hyperplane,
if and only if
\[
|M(f)|=1,\qquad M(f)=\{8,16\},\qquad\text{or}\qquad M(f)=\{16,32\}.
\]
There are exactly **569 extended-affine (EA) classes** satisfying this
condition: 11 plateaued classes, 556 mixed-spectrum classes with \(M(f)=\{8,16\}\),
and two with \(M(f)=\{16,32\}\), out of 150,357 classes. These are orbit
counts, not counts of individual functions. The parent plateaued amplitude
is forced to be 16 or 32 in the two mixed cases, respectively.

This determines the six-variable case of the fifth class in Carlet and
Thornburgh's [2026/386](https://eprint.iacr.org/2026/386), as explicitly posed
in the [September revision, Conclusion, p. 20 (archived November 14)](https://opencryptology.org/2026/386/versions/20261114T034025Z.pdf).
We denote the class by \(\mathrm{RP}_6\). No claim is made for seven or more
input variables, or for the distinct third class (restrictions of
**partially** bent parents).

## 1. Exhaustive analytic reduction to two mixed profiles

For \(u,x\in\mathbb F_2^n\), use \(W_f(u)=\sum_x(-1)^{f(x)+u\cdot x}\), and
call \(f\) plateaued if \(M(f)\) has one element. If an invertible affine
change of parent coordinates takes the given hyperplane to \(t=0\), the
two resulting halves are \(f,h\); conversely a concatenation
\(g(x,0)=f(x), g(x,1)=h(x)\) is an allowed extension. Its spectrum is
\[
 W_g(u,0)=W_f(u)+W_h(u),\qquad W_g(u,1)=W_f(u)-W_h(u).
\]
If \(g\) has plateaued amplitude \(A\), taking the half-sum gives
\(W_f(u)\in\{0,\pm A/2,\pm A\}\). If \(f\) is not plateaued it must
realize both positive absolute levels \(A/2,A\). In the other
direction a plateaued \(f\) always extends with \(h=f\): the parent
satisfies \(W_g(u,0)=2W_f(u)\), \(W_g(u,1)=0\).

For the seven-variable parent, Parseval gives
\[
kA^2=128^2,\qquad 1\le k=|\{v:W_g(v)\ne0\}|\le128.
\]
Thus the integer \(A\) is a power of two, \(A^2\ge128\), and \(A\le128\);
the exhaustive list is \(16,32,64,128\). The six-variable Walsh
coefficients are even integers (sums of 64 signs) and have modulus at
most 64. All candidate half-levels above are even. For \(A=128\), the
value 128 cannot occur, so \(f\) cannot be mixed. For \(A=64\),
one coefficient of modulus 64 already exhausts the complete child
Parseval sum \(64^2\), also ruling out a mixed spectrum. The only
remaining mixed profiles are therefore \(\{8,16\}\) and \(\{16,32\}\).
No amplitude cutoff or assumption on the algebraic degree is used in
the enumeration.

Extended-affinity preserves \(M(f)\): input invertible affine maps and
output affine additions permute frequencies and may flip signs. It also
preserves extendability. If \(f'(x)=f(Bx+b)+\ell(x)\), with \(B\)
invertible and \(\ell\) affine, then
\(g'(x,t)=g(Bx+b,t)+\ell(x)\) is plateaued whenever \(g\) is and restricts
to \(f'\) at \(t=0\). The inverse map gives the converse. Consequently it
is sufficient to give one valid witness for every eligible catalogue
representative.

## 2. Exact modular criterion for constructing witnesses

This step explains how to reduce witness discovery to small-modulus
equations; the final certificate is checked directly, not by trusting
the search. It applies for any mixed pair \(\{a,2a\}\) with \(p=N/a\)
a power of two and \(N=2^n\). Take \(w=W_f/a\), and write \(X,Y,Z\) for
the positions where \(|w|=2,|w|=1,w=0\), respectively. A candidate
normalized spectrum \(z=W_h/a\) must have

* \(z=0\) on \(X\);
* \(z\in\{\pm1\}\) on \(Y\);
* \(z\in\{0,\pm2\}\) on \(Z\), with exactly \(|X|\) nonzero entries there.

Indeed, both \(w+z\) and \(w-z\) must take values in \(\{0,\pm2\}\);
solving these two conditions pointwise gives the listed possibilities,
and the nonzero count on \(Z\) follows from equality of the two
Parseval energies. Conversely, the listed possibilities guarantee
the pointwise condition and \(\sum_u z_u^2=\sum_u w_u^2=p^2\).

Let \(H\) have entries \(H_{xu}=(-1)^{u\cdot x}\). The problem left is
exactly that \(z\) is the normalized Walsh spectrum of a Boolean
function. Necessity of \(Hz\equiv p\pmod{2p}\) is immediate from
\(Hz=p(-1)^h\). For sufficiency, the congruence makes every entry
have modulus at least \(p\); by \(H^\mathsf{T}H=NI\) and the fixed
energy, \(\sum_x(Hz)_x^2=Np^2\), so each entry has modulus exactly
\(p\). Its sign gives \(h\), and inversion gives \(W_h=az\).

Because \(z,w\) agree modulo 2 at each position, \(v=(z-w)/2\) is
integral. Since \(Hw=p(-1)^f\), the congruence is equivalent to
\(Hv\equiv0\pmod p\). Write \(S\) for the support of \(x\) and
\[
B_J(v)=\sum_{u:J\subseteq\operatorname{supp}(u)}v_u,\qquad
p=2^s.
\]
Expanding the signs gives
\[
 (Hv)_x=\sum_{J\subseteq S}(-2)^{|J|} B_J(v).
\]
The subset summation is unitriangular over the integers, with integer
Möbius inverse, and so vanishes modulo \(p\) at all \(S\) exactly when
its coefficients vanish modulo \(p\). Equivalently,
\[
 B_J(v)\equiv0\pmod{2^{s-|J|}}\quad (|J|<s).
\]
For six variables this is one condition modulo 8, six modulo 4 and
15 modulo 2 for \(a=8\); for \(a=16\) it is one modulo 4 and six modulo
2. In the latter case the six modulo-2 conditions can be combined as a
bitwise XOR of the positions with odd \(v_u\). The search used the
support and sign conditions and these modular filters. For the two
\(a=16\) representatives, deterministic enumeration of small high
supports and low-sign profiles \((\mathrm{xor},\#\text{flips}\bmod4)\)
is already sufficient.

## 3. Finite certificates, enumeration, and independent verification

We use Joanne Fuller's complete classification of EA classes on six
variables as an external input. The proof of completeness is
not a property inferred by the local scripts. Maiorana enumerated the
orbits of cosets of \(\mathrm{RM}(1,6)\) under invertible affine input
maps, and Fuller independently computed and verified representatives
for all 150,357 orbits. An invertible affine input map \(T\) induces
an action on these cosets because \(T\) preserves the subspace of
affine functions. The coset of \(f'\) is in the orbit of the coset
of \(f\) exactly when \(f'=f\circ T+\ell\) for some such \(T\) and
affine \(\ell\). This is exactly the EA relation used in Section 1,
not a quotient omitting the output affine offsets.

| \(M(f)\) | Number of entries with the larger modulus (mixed only) | EA classes |
|---|---:|---:|
| \(\{8\},\{16\},\{32\},\{64\}\) | — | 4, 5, 1, 1 respectively |
| \(\{8,16\}\) | 4, 6, 7, 8, 9, 10, 12 | 8, 49, 81, 214, 103, 83, 18 respectively |
| \(\{16,32\}\) | 1, 2 | 1, 1 respectively |

\(\mathrm{RP}_6\) thus consists of 569 EA classes; the other 149,788
are excluded by Section 1. For every eligible nonplateaued
representative, [witnesses.tsv](witnesses.tsv) stores just its Fuller
class ID and one 64-bit truth table \(h\). In particular:

| Fuller ID | \(f\), low bit first by index | \(h\), low bit first by index | Parent amplitude |
|---:|---|---|---:|
| 1326 | 00000000000f0fff | af0aaf0aaffaa00a | 32 |
| 1327 | 03000003000303ff | ffcf03cc03cc00cf | 32 |
| 139004 | 88062105410317ff | ab0ec46ef83467a4 | 16 |

A hex integer stores \(f(x)\) in its bit \(x\). Index \(x\) is the
integer whose binary digits are the coordinates. The two unsigned
hex words in the original catalogue represent the low then high
32 bits. The 128-bit truth table for \(g\) is the child integer
\(f+2^{64}h\). The table IDs are the original all-classes sequence
1 through 150,357 (not the separate balanced-classes numbering).
No third-party catalogue is bundled here.

Obtain [the original full archive](https://booleanfunction.github.io/data/n6-classes.zip)
(not the balanced archive) from [Fuller's source page](https://booleanfunction.github.io/equivalence-classes.html).
The ZIP downloaded on 2026-11-27 has 182 entries; byte SHA-256:
\(\texttt{6f1d7c7012d987d2d75a9618dd569959e66928d573c5f9b43db0b4276bcdecf8}\).
Both Python 3.10+ standard-library scripts work offline once this
specific archive is available:

    python3 verify_fwt.py /path/to/n6-classes.zip
    python3 verify_direct.py /path/to/n6-classes.zip

The first implements a butterfly transform, scans every row,
checks the Parseval energy and file-name nonlinearity of each
representative, verifies every mixed witness by a direct 128-point
concatenation transform, and also checks the split relation and the
modular moments. The second independently parses the complete
archive and recomputes all spectra by direct parity-mask Hamming
distances, without any butterfly logic or reuse of the first
checker's code. It also computes the parent autocorrelation \(C\)
from the truth table and checks \(C*C=A^2C\) with unnormalized
XOR convolution. Indeed, the Fourier transform of \(C\) is \(W_g^2\),
so this identity is equivalent to \(W_g^2(u)\in\{0,A^2\}\) for all
\(u\). Both require an exact match between the mixed class IDs
and the witness IDs, confirm the claimed counts, and reject
explicit corrupted-witness controls. The scripts verify supplied
witnesses, not the randomness or exhaustiveness of their discovery.

### Independent catalogue cross-check (optional)

NIST's [Circuits catalogue description](https://github.com/usnistgov/Circuits/blob/12030e3187853d670158608d986568416b425307/data/Readme.md#n6_group_datatxt)
documents a different set of 150,357 representatives in 30,883 groups.
The [original text file](https://raw.githubusercontent.com/usnistgov/Circuits/12030e3187853d670158608d986568416b425307/data/n6_group_data.txt)
is pinned to commit `12030e3187853d670158608d986568416b425307`,
Git blob `20820d1f22423026cb2fea7b8d8573528f481702`; byte SHA-256:
\(\texttt{dad0e32432a48483f00b399a2432316e5d717ad464fca8810dec8f64cc467b6e}\).
It is **not** a byte-for-byte mirror of the representatives: the two
sets of 64-bit literals share only the zero function under the indicated
decodings. However, their full distributions of sorted absolute Walsh
multisets agree, profile by profile, including multiplicities. There
are 2,082 distinct profiles. This is a cross-check of every Walsh
classification count, not a claim to match all EA orbits by their
Walsh profile alone. To reproduce it:

    python3 verify_direct.py /path/to/n6-classes.zip /path/to/n6_group_data.txt

Neither archive is bundled.

## Scope and sources

* Claude Carlet and Darrion Thornburgh, [*Determining those Boolean
  functions whose restrictions to affine spaces are plateaued*,
  ePrint 2026/386](https://eprint.iacr.org/2026/386); see the Conclusion
  in the [time-stamped copy](https://opencryptology.org/2026/386/versions/20261114T034025Z.pdf).
  The fifth-class question is general. This note settles only \(n=6\);
  no dimension-independent sufficiency of a two-level profile is claimed.
* James A. Maiorana, [*A Classification of the Cosets of the Reed–Muller
  Code \(R(1,6)\)*](https://doi.org/10.2307/2938682), Math. Comp. 57
  (1991), 403–414. This provides the complete orbit count.
* Joanne E. Fuller, [*Analysis of Affine Equivalent Boolean Functions
  for Cryptography*](https://eprints.qut.edu.au/15828/), QUT PhD thesis
  (2003), and [*Boolean Functions for Cryptography: affine equivalence
  class data*](https://doi.org/10.5281/zenodo.24217283), data originally
  published 2003, re-released 2026, CC BY 4.0. The pinned archive is
  Fuller's representative set, and its class IDs in the certificate
  follow that source.
* An Braeken, Yuri Borissov, Svetla Nikova and Bart Preneel,
  [ePrint 2004/248](https://eprint.iacr.org/2004/248), §5, study six- and
  seven-variable EA classes and use restrictions as classification
  invariants. This does not classify six-variable restrictions of
  arbitrary plateaued parents. Hodžić, Pašalić, Wei and Zhang,
  [arXiv:1811.04171](https://arxiv.org/abs/1811.04171), study constructing
  plateaued functions from spectral data and using disjoint plateaued
  halves for bent concatenation; their setting does not give the
  six-variable mixed-spectrum recognition theorem here. We did not
  locate the same six-variable classification in these sources or in
  searches through 2026-11-27 for follow-ups to Carlet–Thornburgh.
