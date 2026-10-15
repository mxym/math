"""Exact finite decoder constraints, discovery only; no asymptotic inference.

Z3 SAT witnesses are checked using plain integer operations. UNSAT without
an independently checkable proof would remain a solver report, not SC0 refutation.
No auxiliary message bits, domain side channel, ordering or proper restriction
is imposed in the general model.
"""
import itertools, json, time
from pathlib import Path
import z3

def submasks(mask):
    x=mask
    while True:
        yield x
        if x==0: break
        x=(x-1)&mask

def vcdim(n,C):
    return max((a.bit_count() for a in range(1<<n)
                if len({c&a for c in C})==1<<a.bit_count()),default=-1)

def samples(n,C):
    return sorted({(a,c&a) for c in C for a in range(1<<n)},
                  key=lambda p:(p[0].bit_count(),p))

def solve(n,C,d=None,proper=False,timeout_ms=20000,fixed=None):
    C=tuple(sorted(set(C)))
    if not C: raise ValueError('Nonempty class required')
    if any(c<0 or c>=1<<n for c in C): raise ValueError('Not binary rows')
    if d is None: d=vcdim(n,C)
    S=samples(n,C)
    messages=[s for s in S if s[0].bit_count()<=d]
    bits=max(n,1)
    h={t:z3.BitVec(f'h_{t[0]}_{t[1]}',bits) for t in messages}
    solver=z3.Solver(); solver.set(timeout=timeout_ms)
    for (a,b),v in h.items():
        solver.add(v&a==b)
        if proper: solver.add(z3.Or([v==c for c in C]))
        if fixed and (a,b) in fixed: solver.add(v==fixed[(a,b)])
    for a,b in S:
        options=[h[(u,b&u)]&a==b for u in submasks(a)
                 if u.bit_count()<=d]
        solver.add(z3.Or(options))
    start=time.monotonic(); result=solver.check(); elapsed=time.monotonic()-start
    record={'n':n,'C':list(C),'d':d,'actual_vcdim':vcdim(n,C),
            'proper_restriction':proper,'samples':len(S),'messages':len(messages),
            'solver_result':str(result),'elapsed_seconds':elapsed,
            'timeout_ms':timeout_ms,'general_model':not proper and not fixed}
    if result==z3.sat:
        model=solver.model()
        decoder={t:model.eval(v,model_completion=True).as_long() for t,v in h.items()}
        failures=[(a,b) for a,b in S if not any(
            decoder[(u,b&u)]&a==b for u in submasks(a) if u.bit_count()<=d)]
        assert not failures
        assert all((v&a)==b for (a,b),v in decoder.items())
        if proper: assert all(v in C for v in decoder.values())
        record['plain_integer_witness_verified']=True
        record['decoder']=[{'mask':a,'labels':b,'output':v} for (a,b),v in decoder.items()]
    elif result==z3.unknown: record['unknown_reason']=solver.reason_unknown()
    return record

if __name__=='__main__':
    cases=[
      (3,[1,2,4]),
      (4,[0,1,2,3,4,5,6,8,9,10,12]),
      (5,[1,2,4,8,16]),
      (5,[0,3,6,12,24,17]),
      (6,[1,2,4,8,16,32]),
    ]
    output=[]
    for n,C in cases:
        record=solve(n,C,timeout_ms=20000)
        output.append(record)
        print(json.dumps({k:v for k,v in record.items() if k!='decoder'}),flush=True)
    path=Path(__file__).parent/'INITIAL_FINITE_CONTROLS.json'
    path.write_text(json.dumps({'solver':z3.get_version_string(),'results':output,
        'scope':'Only listed finite classes; SAT is checked by a separate plain-integer pass. No universal theorem or exhaustive class search.'},indent=2)+'\n')
