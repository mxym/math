# Two limit-law counterexamples from oscillating permutation-class counts

A permutation class is closed under taking patterns. For the uniform permutation of length $n$ in such a class, there are two different ways in which a limit law can fail:

* [First-order convergence](FO.md). In one proper class a **single fixed sentence** in the two orders of position and value has probability tending to 1 along some sizes and to 0 along others. This answers Braunfeld–Kukla Question 5.4 in the negative. The class is infinitely based. It does not answer their separate sum-closed Question 5.3.
* [Large deviations](LDP.md). A **different** proper class has a genuine finite exponential growth rate and even an exponentially concentrated deterministic diagonal permuton limit. Nevertheless, the probabilities of atypical diagrams violate the necessary comparison between nested closed and open sets for a speed-$n$ large deviation principle. This answers the speed-$n$ universality part of Borga–Féray–Winkler Problem 6, not the question of all possible speeds.

Both results are short consequences of **Pantone and Vatter’s October 2026 oscillatory class**. Their theorem supplies the hard construction and quantitative gap; see the [source and scope comparison](SOURCES.md). The two unions which expose this gap to first-order logic and to macroscopic deviations are proved here.

This AI-assisted research note has had a separate [internal AI proof review](REVIEW.md), not external peer review. No claim of guaranteed priority. Reproduce the finite consistency checks with Python 3, standard library only:

```
sha256sum -c SHA256SUMS
python3 -BO check.py
```

The [expected output](CHECKS.txt) is a sanity check on the elementary finite computations, not an experimental proof of the asymptotic theorems.
