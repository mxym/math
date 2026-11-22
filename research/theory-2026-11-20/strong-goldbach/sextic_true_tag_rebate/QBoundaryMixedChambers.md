# The actual mixed chambers at the rough correction boundary

Keep exactly \(S=G_b+W\), \(b=.003\), the same real
\((x,N)=1\) pairing, and the same fixed target \(N\),
central \(J\), \(L=\log N\), \(M=|J|N\mathfrak S(N)\).
The score is not retuned: its original rough correction
\(Q\) clips every negative \(H\) on the actual
\(P^-(n)>N^{.1251}\) arm.

Let \(\mathcal E_Q\) be **all** original rows on which both
least factors exceed \(N^{.1251}\), with their actual ranks
unrestricted. Keep \(\mathcal F_{\rm all}\) of
[the complete two-tag credit](CompleteTaggedCredit.md).
Let \(\mathcal C_Q\) and its reflection be the same chambers
as [in the mixed proof](MixedTagCredit.md), except that the
untagged left arm now requires \(P^-(x)>N^{.1251}\), the
literal correction boundary. On the opposite arm the tag
still has angle \(.080<t\le .125\), with true quotient floor
\(.170\). There is no rank restriction in any mixed chamber.

**Proposition.** The sum of \(S(x)S(y)\) over the two actual
mixed chambers is \(>.167M+o(M)\), including every adverse
tagged rank. The literal outside sum \(\mathcal R_Q\) on
the complement of \(\mathcal E_Q\), \(\mathcal F_{\rm all}\),
\(\mathcal C_Q\), and its reflection satisfies
\[
                    R_J\ge 1.050M+\mathcal R_Q+o(M).
\]
The four chamber sets are disjoint. This replaces the
previous partition and mixed credit, not adds to it.
The coefficient is not a fraction of the conjecture and
does not give any lower bound on \(\mathcal R_Q\).

On an untagged arm above the genuine \(.1251\) cutoff
the original \(S=[H]_+\), since the .003 gate is passed
and \(W\) requires two much smaller tags. As before
\(0\le [H]_+\le\log n\) on the possible ranks:
ranks five, six, and the additional rank seven are
nonpositive before clipping, by the exact sextic slice
formulas (in rank seven \(b_7''(0)\le0\)); no rank at
least eight is possible on this rough support.
The earlier proofs for rank two, three, and the positive
part of rank four are unchanged. Thus all additional
rows enlarging the old \(\mathcal E\) to \(\mathcal E_Q\)
have nonnegative \(S(x)S(y)\). The same strict \(>.470M\)
credit remains valid for that whole actual self chamber.

For the widened mixed chambers use the **same** actual
mixed proof and weighted capacity inequality with
\(a=.1251,\ c=.170,\ \theta=.499\). Its genuine left
reduced linear lower parameter satisfies
\(3<\theta/a<4\). The full ordinary untagged rough mass
upper is \(.57/a\), with exactly the same elementary
Buchstab bound. For the positive left rank-two/three
witnesses, start the same lower angle boxes at \(.126\)
to keep every box strictly above the real rough floor.
The untested \(.1251\) to \(.126\) strip is included in
the **full** left complement upper \(.57/a-\underline m_L\).
There is no use of a lower sieve for that strip.
The upper right coefficient stays \(2/(\theta-\tau_i)\)
on each actual tag cell. All prime/target units, p-square
upper omissions and two reflected source estimates are
exactly as in the original mixed proof. The right ranks,
their signs, and every ordinary rank 4–6 negative bound
are unchanged. The left rough receiver upper for that
entire adverse contribution is \(2/(3a)\), with a valid
ratio \(>3\) as before.

The same exact rational enumeration, with these literal
changes and no reweighting, gives per orientation a
positive lower \(>.1536205M\) and a negative part upper
\(<.0700834M\). Its two reflected signed lower is
\(>.1670742M\).
The mixed chambers are disjoint since the tagged arm
has an actual least factor at most \(N^{.125}\); this
also excludes overlap with \(\mathcal E_Q\). They cannot
meet \(\mathcal F_{\rm all}\), whose genuine tags are
both below \(.110\) on each arm. \(\mathcal F_{\rm all}\)
and \(\mathcal E_Q\) are disjoint for the same reason.
The actual comparison is therefore the .883 comparison
with the full \(\mathcal E_Q\) instead of the smaller
positive block, plus the replacement mixed \(>.167\)
lower, each subtracted only once from the actual remaining
rows.

The exact second replay uses the same rational certificate
as the original mixed theorem. In this directory run:

```sh
python -OB - <<'PY'
from pathlib import Path
from hashlib import sha256

p = Path('check_mixed_tag_credit.py').resolve()
raw = p.read_bytes()
if sha256(raw).hexdigest() != (
    'c8fd8207b14e251e4ef7044068acc1effd0d6b7e3a2266bdcc8e90b240c0ced6'
):
    raise ArithmeticError('different original mixed checker')
code = raw.decode()
for old, new in (
    ('range(150,500)', 'range(126,500)'),
    ('range(150,334)', 'range(126,334)'),
    ('F(".150")', 'F(".1251")'),
    ('F("3.8")', 'F(".57")/a'),
    ('pos>F(".115328") and neg<F(".058450")',
     'pos>F(".1536205") and neg<F(".0700834")'),
    ('2*(pos-neg)>F(".113")', '2*(pos-neg)>F(".1670742")'),
    ('net > .113', 'net > .1670742'),
):
    if code.count(old) != 1:
        raise ArithmeticError('ambiguous Q-boundary change')
    code = code.replace(old, new)
exec(compile(code, str(p), 'exec'), {'__file__': str(p)})
PY
```
