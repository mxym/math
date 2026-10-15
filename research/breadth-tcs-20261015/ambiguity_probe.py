"""Test the additional two-total-parent structure; not the total-class SC0.

An UNSAT candidate would defeat only a proposed size-(d-1) ambiguity lemma.
No such report counts as a mathematical refutation without a checked proof.
"""
from pathlib import Path
import json
import time
import z3
import finite_cegis as fc

HERE=Path(__file__).parent

def remove_bit(c,i):
    return (c & ((1<<i)-1)) | ((c>>(i+1))<<i)

def sample_complex(n,C):
    return {(a,c&a) for c in C for a in range(1<<n)}

def solve_partial(n,P,k=1,timeout=3000):
    messages=sorted(s for s in P if s[0].bit_count()<=k)
    H={t:z3.BitVec(f'p_{t[0]}_{t[1]}',n) for t in messages}
    solver=z3.Solver(); solver.set(timeout=timeout)
    for (a,b),v in H.items():
        solver.add(v&a==b)
    for a,b in P:
        solver.add(z3.Or([H[(u,b&u)]&a==b for u,lab in messages
                          if not(u&~a) and lab==(b&u)]))
    before=time.monotonic(); sat=solver.check()
    result={'result':str(sat),'elapsed':time.monotonic()-before,
            'samples':len(P),'messages':len(messages),'k':k,
            'model':'General labeled improper decoder for this PARTIAL complex only.'}
    if sat==z3.sat:
        model=solver.model(); decoder={t:model.eval(v,model_completion=True).as_long() for t,v in H.items()}
        assert all(h&a==b for (a,b),h in decoder.items())
        assert all(any(h&a==b for (u,lab),h in decoder.items()
                       if not(u&~a) and lab==(b&u)) for a,b in P)
        result['all_partial_faces_plain_integer_verified']=True
    elif sat==z3.unknown:
        result['reason']=solver.reason_unknown()
    return result

def main():
    records=[]
    for n in [6,7,8,9]:
        for seed in range(41,51):
            C=fc.maximal_class(n,2,seed)
            for i in range(n):
                C0={remove_bit(c,i) for c in C if not((c>>i)&1)}
                C1={remove_bit(c,i) for c in C if (c>>i)&1}
                if not C0 or not C1:
                    continue
                P=sample_complex(n-1,C0)&sample_complex(n-1,C1)
                result=solve_partial(n-1,P)
                result.update({'parent_n':n,'parent_VC':2,'seed':seed,'split_coordinate':i,
                               'parent_C':C,'parent_class_size':len(C),
                               'max_ambiguous_face_size':max(a.bit_count() for a,b in P)})
                records.append(result)
                with (HERE/'AMBIGUITY_PROBE_PROGRESS.jsonl').open('a') as f:
                    f.write(json.dumps(result)+'\n')
                if result['result']=='unsat':
                    failure={'record':result,'C0':sorted(C0),'C1':sorted(C1),'P':[list(s) for s in sorted(P)],
                             'status':'Discovery UNSAT report only. It is not independently certified and does not refute SC0 for total VC classes.'}
                    (HERE/'AMBIGUITY_UNSAT_DISCOVERY.json').write_text(json.dumps(failure,indent=2)+'\n')
                    print(json.dumps({'first_unsat':result},indent=2),flush=True)
                    return
            print(json.dumps({'n':n,'seed':seed,'tested':len(records),'last':records[-1]['result']}),flush=True)
    (HERE/'AMBIGUITY_PROBE_SUMMARY.json').write_text(json.dumps({'records':records,'scope':'Only listed finite VC-two total parents and their split partial complexes. No universal lemma or full SC0 result.'},indent=2)+'\n')

if __name__=='__main__':
    main()
