# Two falsifiable tests of arXiv:2611.09007v1

Status: the two assertions identified below are false. Neither test disputes the binary Goldbach conjecture. Attribution: Qazaqzeh and Rawashdeh, [v1, the argument following (6) and Definition 2.1](https://arxiv.org/html/2611.09007v1). No claim about a later revision.

## A pointwise identity fails in an infinite arithmetic progression

Set N=2n and y=N−x, where x,y are odd and x≥3, y−2≥3. In the notation used immediately after (6), R1 counts the patterns where x,x+2,y−2 are prime and y is composite; R2 counts the patterns where x+2 is prime and x,y,y−2 are composite. The paper asserts R1=R2.

Take N ≡ 100 (mod 210), N≥1150. If x and x+2 are both prime, either x=3 or x≡2 mod 3. In the latter case y−2=N−x−2≡0 mod 3, so for R1 to count x one must have y−2=3. In the latter case y=5 is prime, contradicting the requirement that y be composite. In the exceptional case x=3, y−2=N−5 is a multiple of 5 greater than 5. Thus R1=0. Conversely each prime p in {107,317,947} is 2 mod 105. Put x=p−2. The three distinct interior patterns satisfy 3|x, 5|y, 7|(y−2); all three quotients are >1. Thus R2≥3>R1=0. Only trial division up to 30 is needed to verify the primes. Indeed R2 ≫ N/log N on this progression by counting p≡107 mod 210 below N/2 by the prime number theorem in that fixed progression.

## The claimed universal scale does not even give an upper bound

Let g(m) count ordered pairs of odd primes of sum m. Then

    limsup_{m→∞, m even} g(m) log²(m)/m = ∞.

Proof. Fix an arbitrary even squarefree Q. In (X/2,X] each reduced class mod Q contains (1+o_Q(1))X/(2 φ(Q)log X) primes by the prime number theorem in fixed progressions. Pair each class a with −a. The number of ordered prime pairs so obtained is (1+o_Q(1))X²/(4φ(Q)log² X). Their sums lie in (X,2X] and are divisible by Q, leaving at most X/Q+1 choices. Some m has g(m)≥(1+o_Q(1))QX/(4φ(Q)log² X); hence the limsup is at least Q/(8φ(Q)). Take Q through the even primorials. Euler's divergence of the reciprocal prime product finishes the proof. The limit in X is taken for each fixed Q before Q grows.

Consequently the assertion of growth proportional to n/log² n in the manuscript's nonstandard Definition 2.1 is false. Interpreting its notation as conventional big-O does not rescue the uniform assertion either. The obstruction is the varying local factor, not evidence against positivity.

The elementary finite certificate in check.py verifies the first test; the second is an infinite argument, not an inference from sampled values.
