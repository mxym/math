# Actual retained-list assembly in the input-reference program

Four new mathematical modules implement concrete structural list append
and reverse-map with an accumulator. Each recursive tail result is stored
once. Their retained control traces have exact value, copied-cell and
list-spine fee theorems. The modeled fee is one for the terminal case and
four per copied spine cell; annotations are not a timing measurement.
Inverse-label calls are counted separately from this fee.

assembleStoppedInput and assembleCorrectedInput use these actual programs
for output-word assembly and the retained expression/evaluation/decision
list concatenations. assembledInputCorrection and assembledInputPairWord
execute those routines during the selected correction branches. A whole
program-record equality is proved internally against inputTracedPairWord,
including evaluations, cache-read records and decisions. This is not a
reconstruction pass after executing the previous word program.

Retained payload-list mass and actual assembly trace fees are bounded by
8192^depth*(L+2*(n+1)+2). At depth=clog2(p+1), the actual list-spine fee and
separate inverse-label call count are at most
8192*(L+2*(n+1)+2)*(p+1)^13. No numerical operand-height hypothesis is needed
for these structure bounds.

assembledInputCachedRun builds the same eager packet caches and runs this
new assembled recursion directly. Its erase equals the whole inputCachedRun
result. Its numerical Boolean/cache traversal charge is transported through
that internally proved record equality and combined with its own concrete
assembly trace. The resulting partial online fee is degree338, with the
previous coefficient increased by 8192*(L+2*(n+1)+2). This coefficient and
bound are derived internally, rather than supplied as a cost certificate.

This scope charges list spines only, with opaque payloads retained by value
references in the source model. Base score vectors, AST/closure creation,
provider/eager-cache generation, all other allocation, payload copying under
a concrete machine encoding, table/inverse-label provider costs, general
Nat/precision/index/fuel/control arithmetic and annotation execution remain
separate. These results do not establish complete compiler machine bit-time.
The adjacent MACHINE_COST_GAPS memo describes the next semantic obligations.

Earlier committed numerical/core inputs remain byte exact. OWNED feedback,
standard aggregate builds and independent fresh/trust-zero replay are
different evidence levels; prior audit scopes do not automatically cover
these newly added successors.
