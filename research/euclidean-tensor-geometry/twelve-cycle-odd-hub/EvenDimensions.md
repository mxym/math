# Quadratic defect bound in even dimensions for the periodic twelve-cycle

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

In the same complex single-shared-tensor periodic twelve-cycle model as the [odd-dimensional proof](README.md), let \(q=2r+2\) with \(r\ge0\). Then the maximum alternating flattening rank obeys
\[
 F_{12}(q)\ge q^6-120r^2-28r-16.
\]
Together with the odd-dimensional bound \(F_{12}(2r+1)\ge q^6-30r^2+r\), this gives \(F_{12}(q)=q^6-O(q^2)\) for the twelve-cycle uniformly over all common dimensions. It is not an exact value in the remaining dimensions. Full rank is already certified for the [squarefree parts \(1,5,6,30\)](../twelve-cycle-covariant/README.md).

## Self-inverse leaf and the exact base count

Adjoin a self-inverse leaf \(h=-h\) to the odd hub construction, adding \(A_h=E_{0,h}+c_hE_{h,0}\) with \(c_h\ne0\). In the [necklace gauge and exterior-power calculation](ExactBaseNecklaces.md) its ratio \(r_h=c_h/c_{-h}=1\); all other ratios and the gauge formula are unchanged. A necklace is balanced for this purpose precisely if each ordinary opposite pair occurs with equal multiplicities, with any number of \(h\)'s. For such a necklace, the unique possible singular character at half-length six is \((-1)^{n-1}\) when the token count is \(n\). It is available for all odd \(n\), and for even \(n\) exactly when the primitive label period is even. Each such singular necklace contributes \(\binom 5{n-1}\) to the base defect.

The following lists all \(h\)-containing contributions. Rows that specify one or two ordinary classes are counts per choice of those classes.

| Non-\(h\) tokens | Total \(h\)-containing contribution |
| --- | ---: |
| None | \(1+10+5=16\), from token counts \(1,3,5\) |
| One copy of an ordinary opposite pair | \(20+30+20+5=75\), from counts \(3,4,5,6\) |
| Two copies of one ordinary opposite pair | \(30+14=44\), from counts \(5,6\) |
| One copy of each of two distinct ordinary opposite pairs | \(120+60=180\), from counts \(5,6\) |

The necklaces in the latter three rows have full period except that at \(n=6\) in the third row, six of the 90 words repeat a period-three word. They give no singular character and are excluded; the remaining 84 words form 14 eligible necklaces. Thus the extra \(h\)-containing base defect is exactly \(16+119r+180\binom r2\). Direct modular trace ranks confirm these counts at \(q=2,4\).

## The same local jet lifts the same classes

Keep the perturbation from the odd proof on ordinary leaves only. An unmarked \(h\) excursion is a dimer having one \(h\) letter on each parity side, so the number of \(h\)'s is preserved by the entire transfer (also at positive orders used here). In a direct trace between two no-\(h\) words, an \(h\) leaf cannot be visited; its only outgoing spoke is labeled \(h\). No-\(h\) base complements and Schur intermediates are consequently unchanged. The nonsingular quadratic blocks of the odd proof lift the same zero-core balanced types. Keep a base minor of the guaranteed rank in every additional block with \(h\), omitting its unresolved residual dimensions. The new total defect is at most
\[
 (30r^2-r)+16+119r+180\binom r2=120r^2+28r+16.
\]
This proof uses the same local modular jet certificates, not a numerical scan of even dimensions. For any fixed half-length \(s\), the analogous hub witness, with the self-inverse leaf when needed, still gives \(q^s-O_s(q^{\lfloor s/2\rfloor})\): a balanced necklace of length \(n\) uses at most \(\lfloor n/2\rfloor\) ordinary classes, and an \(h\)-containing one uses at most \(\lfloor(n-1)/2\rfloor\).
