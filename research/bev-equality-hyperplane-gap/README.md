# A sharp hyperplane gap for BEV equality codes

Pai's binary Braun–Etzion–Vardy (BEV) bound says a linear subspace code in ambient dimension \(n\) has at most \(2^n\) codewords. His concluding question asks for a classification at equality. We prove two parts of that classification:

1. **All dimensions \(n\ge5\):** the number of hyperplane codewords is at most \(2^{n-2}\), unless the code is exactly the pencil-and-hyperplane code from Braun–Etzion–Vardy's original Remark 3. That code has \(2^{n-1}\) hyperplanes. The lower endpoint \(2^{n-2}\) is attained by a non-pencil code for each \(n\ge5\).
2. **Ambient dimensions at most four:** the equality sets are classified up to ambient linear equivalence. In dimension four there are exactly three types: the spans of subsets of a fixed basis, the product of the Fano code with a one-dimensional coordinate code, and the pencil-and-hyperplane code. There are respectively 840, 120 and 15 distinct sets on a fixed labelled four-dimensional space.

The pencil and product constructions are known. The conclusions here are the sharp rigidity threshold and the small-dimensional classification of the underlying sets, not a classification of every possible group law on a set or of all equality codes in higher dimension.

The proof is analytic, including the exceptional five-dimensional case. Two standard-library checkers exercise the constructions, the borderline five-dimensional obstruction, and the four-dimensional classification by different representations.

~~~sh
sh replay.sh | diff -u RESULTS.txt -
~~~
