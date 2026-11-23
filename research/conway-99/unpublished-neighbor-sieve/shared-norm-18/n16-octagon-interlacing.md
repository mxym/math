# One of the rank-free C8/octagon norm-sixteen overlays is impossible

Fix the orientation and bit convention of the [five-shore core catalogue](n16-five-shore-cores.md). On the cycle-of-eight deficiency deck the positive old sites are bits 0 to 7 with deficiency graph one eight-cycle; a negative old site j+8 is joined to the positive sites in column j of
```
(53,77,83,106,154,166,169,212).
```
Consider the second of the four octagon overlays in the catalogue's lexicographic order. In circular conflict order its eight height-two words are the following bit masks on the sixteen signed old sites:
```
(8707,9345,17600,49248,34864,2328,4364,4614).
```
The conflict octagon forces the eight word sites to be independent (five-shore core theorem). Both old shores are independent. Thus these two lists determine the entire induced adjacency on 24 sites, without requiring any automorphism of a putative full graph.

Its characteristic polynomial is
```
x(x-2)^3(x+2)(x+4)(x^2-4x-8)(x^2+2x-2)^2
   * (x^6-12x^4-4x^3+34x^2+16x-4)^2 .
```
The monic sextic is −1 at 3, so has a real root strictly above 3; the square gives at least two induced adjacency eigenvalues above 3. The global adjacency has only its simple degree eigenvalue 14 above 3. Principal interlacing rules this out at every rank. The [accompanying standard-library verifier](n16-octagon-interlacing.py) recovers the full characteristic polynomial by Newton identities on traces of integral powers and checks the displayed factorization; this statement does not by itself exclude the other three noncube overlays.
