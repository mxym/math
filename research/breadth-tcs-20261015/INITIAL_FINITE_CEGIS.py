"""Exact shared-decoder discovery, with finite DAG coverage certificates.

The synthesized examples are controls only. Neither absence of counterexamples
nor this algorithm's termination for a finite class proves SC0. General-model
UNSAT is only reported as a solver claim unless separately certified.
"""
from pathlib import Path
from itertools import combinations
import argparse
import hashlib
import json
import random
import time
import z3

def masks_at_most(n, d):
    return [sum(1 << i for i in a) for j in range(d+1)
            for a in combinations(range(n), j)]

def vc_exact(n,C):
    # Small n diagnostic; synthesis does not use a misdeclared dimension.
    return max(a.bit_count() for a in range(1 << n)
               if len({c&a for c in C}) == 1 << a.bit_count())

def maximal_class(n,d,seed):
    rng = random.Random(seed)
    large = [a for a in masks_at_most(n,d+1) if a.bit_count() == d+1]
    # Map projected masks to compact labels, not bit positions in [n].
    positions = [[i for i in range(n) if (a>>i)&1] for a in large]
    def pat(c,p):
        return sum(((c>>i)&1)<<j for j,i in enumerate(p))
    seen = [0] * len(large)
    full = (1 << (1 << (d+1))) - 1
    rows = list(range(1 << n)); rng.shuffle(rows)
    C=[]
    for c in rows:
        updated = [s | (1<<pat(c,p)) for s,p in zip(seen,positions)]
        if full not in updated:
            C.append(c); seen=updated
    C.sort()
    assert vc_exact(n,C) == d
    # Any formerly rejected row remains rejected under enlargement of C.
    return C

def coverage_dag(n,C,d,decoder,small_masks,deadline=None):
    """Either an actual failed realizable sample, or an exact finite DAG."""
    nodes={}
    visited=0
    def visit(a,b):
        nonlocal visited
        key=(a,b)
        if key in nodes:
            return None
        visited += 1
        if deadline is not None and time.monotonic() > deadline:
            raise TimeoutError('Exact sample verification deadline exceeded')
        good = next((u for u in small_masks if not (u & ~a)
                     and decoder[(u,b&u)] & a == b), None)
        if good is None:
            return key
        children=[]
        bits=good
        while bits:
            bit=bits & -bits; bits-=bit
            child=(a^bit,b&~bit)
            failed=visit(*child)
            if failed is not None:
                return failed
            children.append(child)
        nodes[key]={'mask':a,'labels':b,'message_mask':good,
                    'message_labels':b&good,'children':children}
        return None
    full=(1<<n)-1
    for c in C:
        failed=visit(full,c)
        if failed is not None:
            a,b=failed
            assert any(c&a == b for c in C)
            assert not any(decoder[(u,b&u)]&a == b for u in small_masks
                           if not (u&~a))
            return {'counterexample':list(failed),'visited_nodes':visited}
    return {'nodes':list(nodes.values()),'visited_nodes':visited,
            'roots':[[full,c] for c in C]}

def synthesize(n,C,d,budget=120,round_cap=1000,seed=0):
    C=sorted(set(C)); actual=vc_exact(n,C)
    if d != actual:
        raise ValueError('This probe expects the actual VC dimension')
    small=masks_at_most(n,d)
    messages=sorted({(a,c&a) for a in small for c in C})
    H={t:z3.BitVec(f'h_{t[0]}_{t[1]}',max(n,1)) for t in messages}
    solver=z3.Solver(); solver.set(random_seed=seed)
    for (a,b),v in H.items():
        solver.add(v&a == b)
    known=set()
    def add(a,b):
        assert (a,b) not in known
        assert any(c&a == b for c in C)
        known.add((a,b))
        solver.add(z3.Or([H[(u,b&u)]&a == b for u in small if not (u&~a)]))
    full=(1<<n)-1
    for c in C:
        add(full,c)
    started=time.monotonic(); deadline=started+budget
    history=[]
    record={'n':n,'C':C,'d':d,'actual_VC':actual,'general_improper_model':True,
            'no_side_information':True,'message_count':len(messages),
            'budget_seconds':budget,'round_cap':round_cap,'history':history,
            'scope':'Only this listed finite class. No proof of SC0 or its negation.'}
    for k in range(round_cap):
        remaining=deadline-time.monotonic()
        if remaining <= 0:
            record['status']='budget_exhausted'; break
        solver.set(timeout=max(1,int(1000*remaining)))
        sat=solver.check()
        state={'round':k,'constraints':len(known),'solver':str(sat)}
        history.append(state)
        if sat != z3.sat:
            record['status']='solver_'+str(sat)
            if sat == z3.unknown:
                record['unknown_reason']=solver.reason_unknown()
            else:
                record['UNSAT_limit']='Solver report without independently checked refutation. Not a claimed counterexample.'
            break
        model=solver.model()
        decoder={t:model.eval(v,model_completion=True).as_long() for t,v in H.items()}
        try:
            checked=coverage_dag(n,C,d,decoder,small,deadline)
        except TimeoutError as e:
            record['status']='verifier_budget_exhausted'; record['timeout']=str(e); break
        state['verification_visited_nodes']=checked['visited_nodes']
        if 'counterexample' in checked:
            a,b=checked['counterexample']
            assert (a,b) not in known
            state['failed_sample']=[a,b]
            add(a,b)
        else:
            record['status']='sat_with_DAG_certificate'
            record['decoder']=[{'mask':a,'labels':b,'output':v}
                               for (a,b),v in sorted(decoder.items())]
            record['certificate']=checked
            record['synthesized_sample_constraints']=[list(s) for s in sorted(known)]
            break
    else:
        record['status']='round_cap_exhausted'
    record['elapsed_seconds']=time.monotonic()-started
    return record

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--n',type=int,default=8)
    parser.add_argument('--d',type=int,default=2)
    parser.add_argument('--seed',type=int,default=41)
    parser.add_argument('--budget',type=int,default=120)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    C=maximal_class(args.n,args.d,args.seed)
    result=synthesize(args.n,C,args.d,args.budget,seed=args.seed)
    result['class_generation']={'method':'Greedy maximal VC-d class over the complete binary n-cube. Every absent row was rejected while inserting earlier rows, so rejection persists in the final class.','seed':args.seed}
    result['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()
                      if k not in ['history','decoder','certificate','synthesized_sample_constraints']},indent=2))
    print('rounds',len(result['history']),flush=True)

if __name__ == '__main__':
    main()
