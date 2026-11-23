# Short rooted fields from two marked moments

Use the [rank-32 rooted gluing](rooted-rank32.md) at any vertex o. The graph fields below are integral neutral minus-four eigenfields vanishing on the closed neighborhood of o. Their lengths are ordinary **squared** graph-coordinate norms. There is at least one nonzero such field of norm at most 174. More precisely, either one has norm at most 112, or at least 86 distinct oriented ones have norm at most 174. If the chosen unimodular gluing is rootless, fields of norm at most 192 span the 30-dimensional rooted residual space. These are necessary conditions, not a contradiction.

If the even unimodular lattice U of rank 32 has a norm-two vector, its auxiliary lattice K has minimum 14 and hence the projected graph vector is nonzero. The graph dictionary gives norm at most 112. Otherwise U has 146,880 norm-four vectors and that shell is a spherical 7-design. For the latter fact one can use the classical [extremal-lattice design result](https://www.mathnet.ru/eng/mmj245), or use even harmonic theta series of degrees 2,4,6: their weight-18,20,22 cusp spaces at full level are one-dimensional, and the zero norm-two coefficient makes the weighted series identically zero. Odd moments vanish by antipodes.

For a norm-four vector v, write q=(v,f) with f the auxiliary mark of norm 28. Let Y=2q², so that Y equals 56 times the squared pairing with the unit direction along f. The first three moments of the uniform sphere of squared radius four in dimension 32 give
```
E[Y]=7,
E[Y²]=224²·3/(32·34),
E[Y³]=224³·15/(32·34·36).
```
The polynomial P(Y)=(Y−2)(Y−8)(Y−32) is nonpositive at every allowed value Y≤32 (namely 0,2,8,18,32). Its expectation is 17008/51, so its total on the shell is 48,983,040. The integer square condition and Cauchy give Y≤200. For Y≥50 the polynomial is increasing, with P(200)=6,386,688. Thus at least eight vectors have |q|≥5. Each gives a field of norm 224−4p²−2q²≤174 and no two of these lifts give the same field. Indeed the rooted dictionary shows that a duplicate would require p=±7, and then 4p²+2q²>224.

If no field at this root has norm at most 112, the gluing is rootless and every norm-four v has Y<112. Since q is integral, Y≤98. Replacing the same upper bound by P(98)=570,240 proves the claimed 86 distinct oriented fields.

For the span statement, let z be a unit vector in the residual space, orthogonal to f, and put W=(v,z)². Orthogonal-coordinate sphere moments give
```
E[YW]=896/(32·34),     E[Y²W]/E[YW]=56/3.
```
Thus the shell expectation of Y(Y−18)W is positive. If z were perpendicular to every projected v with |q|≥4, every such summand would vanish, while all others are nonpositive because Y≤18. This is impossible. The projected fields with |q|≥4 therefore span the residual space, and all have norm at most 224−32=192. In particular they contain 30 linearly independent rooted fields. None of these high-|q| lifts can duplicate a field, since at p=±7 the auxiliary contribution is already at least 196+32.
