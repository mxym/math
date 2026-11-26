# Mixing local replacement rules for the shifted Lonely Runner problem

**Yongxian Zhang.** AI-assisted research and internal verification; no external peer review or priority claim.

For \(n\) distinct positive integer moving speeds and arbitrary starting positions, define \(E_n\) by the optimum shifted loneliness \(1/(n+1+E_n)\), as in [Poliakova, arXiv:2609.23952](https://arxiv.org/html/2609.23952v1). Its Theorem 1 gives the linear lower bound with coefficient \(1/287\), and its Table 1 reports the larger coefficient \(1/224\) from a single-rule schedule. Here we prove a quantitative improvement,
\[
 E_n\ge \frac{38281}{5429219}\,n-11 >\frac{n}{142}-11 .
\]
The local replacement rules themselves come from Poliakova; the improvement comes from packing and mixing them at different scales. This is only an asymptotic improvement and does not address the remaining finite gap within 58–94 moving speeds in [Zhang's Question 8.5](https://arxiv.org/html/2608.13599v3#S8); see also the [earlier exact certificates](https://itsdavis.com/solved-conjectures/results/shifted-lonely-runner-counterexamples/).

## 1. Local rules and an exact way to replay them

Start with the \(N\) speeds \(2,4,\ldots,2N\), all at shift zero, with radius \(\delta=1/(N+1)\). This is a \(\delta\)-cover, meaning that every time has some speed within distance \(\delta\) of an integer. Indeed two of \(0,2t,\ldots,2Nt\) are at circular distance at most \(\delta\), by the smallest gap or a repetition. Attribute each time to the smallest original even speed that covers it.

A local rule consists of deleting a designated set of even speeds, shifting some other even speeds, and adding odd speeds at designated shifts. At an odd scale \(b\), multiply all its speeds by \(b\) but leave each shift unchanged. It is admissible if all deleted and shifted speeds are at most \(2N\). Locality means that whenever an original responsible speed is affected by this rule, some shifted or added speed from this same application covers that time. Consequently applications with pairwise disjoint affected and added speeds can be combined: choose the original responsible speed at each time and use its own application's witness, or leave it unchanged if unaffected. No deleted or shifted speed in another application can interfere with that witness.

We use three of Poliakova's local rules: label 0 is Theorem 7's rule, 1 is Table 1's first row, 2 is Table 1's second row. Their respective gains (number removed minus number added) are 1, 2, 3. At scale \(b\), their respective admissibility thresholds are \(96b,120b,216b\le N\). The [exact verifier](verify-shifted-lonely-runner-mixed-packing.js) includes the literal velocities and phases in a compact representation, and checks locality as follows. At an affected responsible speed \(qb\) write \(qbt=k+\delta z\) for integral \(k\) and \(|z|\le1\). Then \(\gcd(k,q/2)=1\): if \(d>1\) divides both, the original even speed \(qb/d<qb\) also covers. For each such \(k\bmod q\), a candidate speed \(vb\) with shift \(\alpha+\beta\delta\) is guaranteed to cover whenever
\[
 vk/q+\alpha\in\mathbb Z,\qquad |(v/q)z+\beta|\le1.
\]
Take the union of these exact closed intervals in \(z\), and check it covers \([-1,1]\). The respective checks run over 184, 536, 882 residue cases. This suffices at every admissible scale and every \(\delta\); it is not sampling times or values of \(\delta\).

## 2. Mix the rules inside independent coprime cores

Every velocity across the three rules has prime factors only in \(\{2,3,5\}\). Group applications by a common core \(c\) with \(\gcd(c,30)=1\), allowing their scales to be \(c\) times any \(3^i5^j\). Applications in distinct cores cannot touch the same speed: stripping the factors \(2,3,5\) from any speed leaves its unique \(c\). Within one core use the following certified options, where each \((\text{rule},s)\) selects scale \(cs\).

| Minimum \(N/c\) | Gain | Applications |
|---:|---:|:---|
|96|1|(0,1)|
|120|2|(1,1)|
|216|3|(2,1)|
|864|4|(0,1), (1,5), (0,9)|
|1080|5|(0,1), (0,9), (2,5)|
|3000|6|(0,1), (2,9), (1,25)|
|5400|7|(0,3), (0,15), (1,27), (2,25)|
|5832|8|(0,3), (0,5), (2,25), (2,27)|
|9720|9|(2,1), (0,45), (2,25), (1,81)|

Use the largest eligible threshold in each core. The verifier checks by integer multiplication that each row has its claimed gain, is admissible, and touches no speed twice. Finding the options is not needed for checking them; no optimality is asserted.

Let \(T_j\) be the nine thresholds and \(A(x)=|\{1\le c\le x:\gcd(c,30)=1\}|\). Thus the saved count is \(G(N)=\sum_j A(N/T_j)\): a core at the \(j\)th threshold contributes \(j\), exactly one for every threshold it passes. The eight residues \(1,7,11,13,17,19,23,29\bmod30\) give \(A(x)\ge(4/15)x-1\) for all \(x\ge0\), by checking the intervals between these residues. It follows that
\[
G(N)\ge c_0 N-9,\qquad c_0=\frac4{15}\sum_{j=1}^9\frac1{T_j}=\frac{38281}{5467500}.
\]
To obtain exactly \(n\) speeds, for \(n>9\) choose \(N=\lfloor(n-9)/(1-c_0)\rfloor\), so \(N-G(N)\le n\). Append distinct new speeds if needed; they cannot worsen a cover. For those \(n\), \(E_n\ge N-n\), which is at least \(c_0n/(1-c_0)-9/(1-c_0)-1\). For small \(n\) the baseline bound \(E_n\ge0\) suffices. Since \(9/(1-c_0)+1<11\) and \(c_0/(1-c_0)>1/142\), this proves the displayed estimate.
