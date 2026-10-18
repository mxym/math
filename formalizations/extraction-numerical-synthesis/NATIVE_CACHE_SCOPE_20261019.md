# Native list-spine cache successor

Three separate new modules implement actual structural list lookup, retain
the executed hit/miss/recursive frames, and prove its output and local fee.
The exact list/option/record fee is 4(min(index,length)+1). Precision packet
read defaults after an actual list miss, without a host comparison against
the precision bound. Gate-label and precision lookup are both explicit; a
complete gate-packet read has local fee at most 4(m+P+5). Returned values are
shared immutable binary packet data in this source-level model.

nativeLinearCachedRun uses these actual read algorithms and its whole result
record equals nativeCachedRun. Its word, length, error and numerical Boolean
degree338 theorems therefore concern the same final numerical value. The
degree338 fee is explicitly numerical evaluation/decision only; the new
cache-spine fees remain per-query traces. No total AST-building/query count
or full-machine allocation/index/control/counter time has been inferred from
those per-query bounds. Provider generation and cache construction remain
separate too. Future whole request accumulation must connect to an actual
instrumented evaluation/construction program, not an assumed ghost count.

All previously committed numerical and frozen core sources remain byte
exact. OWNED feedback, guarded aggregate compilation and independent fresh
or trust-zero evidence are distinct. This new scope is not retroactively
part of a previous independent audit.
