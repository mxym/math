# Two servers per projective line over even fields

Let \(q=2^a\ge4\), \(s\ge1\), and \(N=(q^s-1)/(q-1)\). Choose two distinct nonzero representatives on every projective line of \(\mathbb F_q^s\), one on each of two prescribed sides. **Every list of \(N+1\) nonzero requests has disjoint recovery sets on these \(2N\) servers**, with exactly two singletons and \(N-1\) cross-side pairs. Both coefficients in a pair can be taken nonzero.

This gives \(\mathrm{FB}(s,N+1,q)=2N\) and fills the remaining even-field \(q\ge4,\ s\ge3\) range of [Kılıç–Ravagnani–Salizzoni, Open Problem 3.13](https://arxiv.org/html/2508.02586v2). The odd-field case is [Essayag–Zabokritskiy, Theorem 2.3](https://arxiv.org/html/2611.34382v1); binary equality and dimensions at most two were also already known.

The proof extends the odd-field quotient determinant method of Essayag–Zabokritskiy. The new step is that a stronger falling-factorial valuation bound supplies one more factor of two than the final normalization loses. A direct expansion also yields a congruence for every normalized determinant coefficient. The recovery conclusion is existential; this does not address the separate polynomial-time search question.

Run `sh replay.sh` from this directory. The two standard-library Python checks are exact finite sanity checks, not assumptions of the theorem.
