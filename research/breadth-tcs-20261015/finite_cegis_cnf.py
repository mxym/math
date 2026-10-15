"""Exact general-decoder CEGIS in Boolean CNF; finite research only."""
import hashlib,itertools,json,sys,threading,time
from pathlib import Path
from pysat.solvers import Solver
import finite_cegis as fc


def run(root,budget=600):
    previous=json.loads((root/'CEGIS_N12_D2_SEED107.json').read_text())
    second=json.loads((root/'CEGIS_N12_D2_SEED107_LOCAL_SEED.json').read_text())
    n=previous['n']; d=previous['d']; C=previous['C']
    if second['C']!=C: raise ValueError('class mismatch')
    if fc.vc_exact(n,C)!=d: raise ValueError('actual dimension mismatch')
    small=fc.masks_at_most(n,d)
    messages=sorted({(a,c&a) for a in small for c in C})
    nxt=0
    def var():
        nonlocal nxt
        nxt+=1
        return nxt
    bits={(t,i):var() for t in messages for i in range(n) if not (t[0]>>i)&1}
    solver=Solver(name='glucose42')
    known=set(); clauses=0
    def clause(lits):
        nonlocal clauses
        solver.add_clause(lits); clauses+=1
    def add(a,b):
        if (a,b) in known: return
        if not any(c&a==b for c in C): raise ValueError('nonrealizable constraint')
        known.add((a,b))
        if a.bit_count()<=d: return # own message is normalized
        choices=[]
        for u in small:
            if u&~a: continue
            t=(u,b&u); z=var(); choices.append(z)
            for i in range(n):
                if ((a&~u)>>i)&1:
                    x=bits[t,i]
                    clause([-z,x if (b>>i)&1 else -x])
        clause(choices)
    full=(1<<n)-1
    for c in C: add(full,c)
    for old in [previous,second]:
        for step in old['history']:
            for a,b in step.get('failed_samples',[]): add(a,b)
    for a in fc.masks_at_most(n,3):
        if a.bit_count()==3:
            for b in {c&a for c in C}: add(a,b)
    started=time.monotonic(); deadline=started+budget
    rec={'n':n,'C':C,'d':d,'actual_VC':d,'message_count':len(messages),
         'general_improper_model':True,'no_side_information':True,
         'budget_seconds':budget,'solver':'pysat-glucose42','history':[],
         'scope':'Only this listed finite class, full original shared decoder constraints. No universal or negative conclusion from timeout.',
         'seed_inputs_sha256':{p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in ['CEGIS_N12_D2_SEED107.json','CEGIS_N12_D2_SEED107_LOCAL_SEED.json']},
         'source_sha256':{p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in ['finite_cegis_cnf.py','finite_cegis.py']}}
    for step in range(10000):
        rem=deadline-time.monotonic()
        if rem<=0: rec['status']='budget_exhausted'; break
        timer=threading.Timer(rem,solver.interrupt); timer.daemon=True;timer.start()
        result=solver.solve_limited(expect_interrupt=True)
        timer.cancel()
        state={'round':step,'constraints':len(known),'variables':nxt,'clauses':clauses,'solver_result':result}
        rec['history'].append(state)
        if result is not True:
            rec['status']='solver_unknown' if result is None else 'solver_unsat_without_checked_refutation'
            break
        positive={x for x in solver.get_model() if x>0}
        decoder={t:t[1]|sum((1<<i) for i in range(n) if not(t[0]>>i)&1 and bits[t,i] in positive) for t in messages}
        try: checked=fc.coverage_dag(n,C,d,decoder,small,deadline,batch_limit=64)
        except TimeoutError:
            rec['status']='verifier_budget_exhausted';break
        state['verification_visited_nodes']=checked['visited_nodes']
        if 'counterexamples' in checked:
            state['failed_samples']=checked['counterexamples']
            for a,b in checked['counterexamples']: add(a,b)
        else:
            rec['status']='sat_with_DAG_certificate'
            rec['decoder']=[{'mask':a,'labels':b,'output':v} for (a,b),v in sorted(decoder.items())]
            rec['certificate']=checked
            rec['synthesized_sample_constraints']=[list(x) for x in sorted(known)]
            break
    else:rec['status']='round_cap_exhausted'
    rec['elapsed_seconds']=time.monotonic()-started
    solver.delete()
    return rec

if __name__=='__main__':
    root=Path(__file__).resolve().parent
    rec=run(root,600)
    p=root/'CEGIS_N12_D2_SEED107_CNF.json'
    p.write_text(json.dumps(rec,indent=2)+'\n')
    print(json.dumps({k:v for k,v in rec.items() if k not in ['C','history','decoder','certificate','synthesized_sample_constraints']},indent=2))
    print('rounds',len(rec['history']))
