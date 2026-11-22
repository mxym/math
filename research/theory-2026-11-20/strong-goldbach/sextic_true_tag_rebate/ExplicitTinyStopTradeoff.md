# A second explicit cutoff for the same sharp sextic

Use exactly the score \(G\), the target units and interval, and the
normalization of [the explicit tiny-stop theorem](ExplicitTinyStop.md).
The two options below are separate partitions of the same true sum.
Their coefficients cannot be added.

\[
\begin{array}{c|c|c|c}
 b & \text{both retained least factors} & \text{maximum rank}
   & \text{coefficient before the retained signed term}\\ \hline
 .003 & >N^{.003} &333 &.676\\
 .004 & >N^{.004} &250 &.194
\end{array}
\]
In the first row, \(R_J\ge .676M+
\langle(1-I_b)G,(1-I_b)G\rangle+o(M)\). Neither row estimates
the retained signed term.

For the first row use the same proof with \(b=.003\),
\(\kappa=9/2,\ c=.0135,\ d=.013501,\ w=.018\).
The real sub-root product modulus is still at most
\(N^{1/2-10^{-6}}\); on every actual least certificate
\(h\le N^{c+b}=N^{.0165}\), so the quotient level exponent
\(.499-\log h/L\) is at least \(.4825\), and the least-factor
linear upper parameter is \(>3\). The ordinary Buchstab argument
in the no-hit mass is \((1-t)/b\ge166\) throughout the same
\(t\le1/2\) support. The polynomial principal is
\(m(b)=-.226338196805398\ldots\), and the same factorial
error bound and \(672b^5\) truncation give
\[
 |m_T|<.227,\qquad |c_A|<.228,\qquad |m(R)|<10^{-7}.
\]
The absolute \(D\) ordinary and receiver bounds are respectively
\(.006657\) and \(.007445\). The recomputed ordinary
\(B_V,B_X\) are \(<.009042,\ .017667\).
In the last inequality of the original proof the total strict
debit bound is \(<.278M\). The physical floor \(a\downarrow0\)
and rank, angle, target-unit, and squarefree limits are unchanged;
no argument depends on advancing the fixed \(b\) with \(N\).

The angular integer grid uses \(\tau=b|\xi|\) and \(\kappa\)
only, so the same C++ source proves both rows. To replay the
first without changing the original checker, from this directory
run:

```sh
python -OB - <<'PY'
from pathlib import Path
import hashlib

driver = Path('check_explicit_tiny_stop.py').resolve()
raw = driver.read_bytes()
if hashlib.sha256(raw).hexdigest() != (
    '61d873fed42bf1fec426d999bc5b5c1ff85ae42e33422543a3fc802ab8c325cb'
):
    raise ArithmeticError('different primary cutoff driver')
code = raw.decode()
for a, b in (
    ('b=F(1,250)', 'b=F(3,1000)'),
    ('F(301,1000)', 'F(228,1000)'),
    ('F(300,1000)', 'F(227,1000)'),
    ('F(15765,10**6)', 'F(6657,10**6)'),
    ('F(17632,10**6)', 'F(7445,10**6)'),
    ('F(1982,100000)', 'F(9042,1000000)'),
    ('F(4193,100000)', 'F(17667,1000000)'),
    ('budget<F(76,100)', 'budget<F(278,1000)'),
    ('below .760', 'below .278'),
):
    if code.count(a) != 1:
        raise ArithmeticError('ambiguous second cutoff')
    code = code.replace(a, b)
exec(compile(code, str(driver), 'exec'), {'__file__': str(driver)})
PY
```
