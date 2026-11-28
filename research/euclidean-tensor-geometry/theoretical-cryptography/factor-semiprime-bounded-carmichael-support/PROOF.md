# Proof

Remove a factor \(2\) directly, and detect a perfect square directly.
It remains to consider distinct odd primes \(p<q\). Put
\[
 g=\gcd(p-1,q-1),\qquad p-1=ga,\qquad q-1=gb, \tag{6}
\]
where \(\gcd(a,b)=1\) and \(a<b\). Then
\[
 \lambda(N)=gab,\qquad
 \frac{N}{\lambda(N)}
 =g+\frac1a+\frac1b+\frac1{gab}. \tag{7}
\]

If \(a=1\), then \(g=p-1\) and \(\lambda(N)=q-1\). Since \(p<q\),
\[
 \left\lfloor\frac N{\lambda(N)}\right\rfloor
 =\left\lfloor\frac{pq}{q-1}\right\rfloor=p. \tag{8}
\]
Thus the floor itself is a factor.

Otherwise \(a\ge2\). Since \(a,b\) are coprime and \(a<b\), we have
\(b\ge3\). Also \(g\) is even. Therefore
\[
 0<\frac1a+\frac1b+\frac1{gab}
 \le\frac12+\frac13+\frac1{12}<1. \tag{9}
\]
Equation (7) gives
\[
 \left\lfloor\frac N{\lambda(N)}\right\rfloor=g. \tag{10}
\]
Consequently
\[
 \varphi(N)=(p-1)(q-1)=g\lambda(N). \tag{11}
\]
Writing \(\Delta=\lfloor N/\lambda(N)\rfloor\), either (8) yields a
factor or (11) yields
\[
 p+q=N+1-\Delta\lambda(N). \tag{12}
\]
The roots of
\[
 X^2-(N+1-\Delta\lambda(N))X+N \tag{13}
\]
are then exactly \(p,q\).

Now enumerate the integers (5). Every prime exponent in
\(\lambda(N)\) is at most \(\lfloor\log_rN\rfloor\), and (1) includes
every prime in its support, so the true value appears in the list.
Apply the two tests (8) and (13) to every candidate, accepting only
positive prime roots whose product is \(N\). Wrong candidates cannot
cause a false output because of these final checks, while the true
candidate succeeds by the preceding argument.

There are exactly at most (2) candidates. Each candidate needs only
integer division, an exact square test, primality tests, and exact
verification, all polynomial in the advised input length. This proves
(3), and (4) follows immediately.
