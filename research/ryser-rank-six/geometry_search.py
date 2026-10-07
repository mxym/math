"""Mixed triple/single or pair/double splits with consistent shared retained points."""
import argparse,itertools,json,time
from pathlib import Path
from threading import Timer
from pysat.formula import IDPool
from pysat.card import CardEnc,EncType
from pysat.solvers import Solver
from search import cover_at_most
from verify_witness import check_edges

q=5
points=list(itertools.product(range(q),repeat=2))
def intercept(p,g):
 x,y=p
 return (y-g*x)%q if g<q else x

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--family',choices=('triple','mixed'),default='mixed')
 ap.add_argument('--seconds',type=int,default=240)
 ap.add_argument('--output',default='candidate.json')
 a=ap.parse_args()
 if a.seconds<=0:ap.error('need positive time')
 pool=IDPool();clauses=[]
 opt=lambda g,k:pool.id(('option',g,k))
 split=lambda g,b:pool.id(('split',g,b))
 merge=lambda g,pair:pool.id(('merge',g,pair))
 active=lambda i:pool.id(('active',i))
 label=lambda i,g,v:pool.id(('label',i,g,v))
 options={};split_opts={};merge_opts={};inactive={i:[] for i in range(25)}
 for g in range(6):
  opts=[]
  for count,kret in (((1,3),) if a.family=='triple' else ((1,3),(2,2))):
   for splits in itertools.combinations(range(q),count):
    if g in (0,5) and 0 not in splits:continue
    lines=[[i for i,p in enumerate(points) if intercept(p,g)==b] for b in splits]
    for retained_sets in itertools.product(*(list(itertools.combinations(line,kret)) for line in lines)):
     for pair in itertools.combinations([v for v in range(q) if v not in splits],2):
      opts.append((splits,retained_sets,pair))
  options[g]=opts
  clauses+=CardEnc.equals([opt(g,k) for k in range(len(opts))],1,vpool=pool,encoding=EncType.seqcounter).clauses
  for k,(splits,retained_sets,pair) in enumerate(opts):
   o=opt(g,k);clauses.append([-o,merge(g,pair)])
   for b in splits:
    clauses.append([-o,split(g,b)]);split_opts.setdefault((g,b),[]).append(o)
   merge_opts.setdefault((g,pair),[]).append(o)
   regular=[v for v in range(q) if v not in splits and v not in pair]
   kret=3 if len(splits)==1 else 2
   for i,p in enumerate(points):
    c=intercept(p,g)
    if c in splits:
     slot=splits.index(c);retained=retained_sets[slot]
     if i in retained:
      v=1+len(regular)+slot*kret+retained.index(i);clauses.append([-o,active(i)])
     else:
      v=5;inactive[i].append(o);clauses.append([-o,-active(i)])
    else:v=0 if c in pair else 1+regular.index(c)
    clauses.append([-o,label(i,g,v)])
 for (g,b),ls in split_opts.items():clauses.append([-split(g,b)]+ls)
 for g in range(6):
  for b in range(q):
   if (g,b) not in split_opts:clauses.append([-split(g,b)])
 for g in range(6):
  for pair in itertools.combinations(range(q),2):
   ls=merge_opts.get((g,pair),[])
   clauses.append([-merge(g,pair)]+ls)
 for i in range(25):
  clauses.append([active(i)]+inactive[i])
  for g in range(6):clauses+=CardEnc.equals([label(i,g,v) for v in range(6)],1,vpool=pool,encoding=EncType.seqcounter).clauses
 for i,j in itertools.combinations(range(25),2):
  p,r=points[i],points[j]
  common=[g for g in range(6) if intercept(p,g)==intercept(r,g)]
  if len(common)!=1:raise RuntimeError('affine line uniqueness')
  g=common[0];b=intercept(p,g)
  restores=[merge(d,tuple(sorted((intercept(p,d),intercept(r,d))))) for d in range(6) if d!=g]
  clauses.append([-active(i),-active(j),-split(g,b)]+restores)
 print('Encoded',pool.top,'variables,',len(clauses),'clauses',flush=True)
 start=time.monotonic();models=0;cuts=set();bound=a.seconds
 with Solver(name='g4',bootstrap_with=clauses) as solver:
  while time.monotonic()-start<bound:
   timer=Timer(min(20,bound-(time.monotonic()-start)),solver.interrupt)
   timer.start();sat=solver.solve_limited(expect_interrupt=True);timer.cancel();solver.clear_interrupt()
   if sat is None:continue
   if not sat:
    print('STRUCTURED ENCODING UNSAT; no certificate or unrestricted conclusion',flush=True);break
   positive={v for v in solver.get_model() if v>0}
   selected={g:next(options[g][k] for k in range(len(options[g])) if opt(g,k) in positive) for g in range(6)}
   actual=[]
   for i,p in enumerate(points):
    allowed=all(intercept(p,g) not in selected[g][0] or
                i in selected[g][1][selected[g][0].index(intercept(p,g))]
                for g in range(6))
    if (active(i) in positive)!=allowed:raise RuntimeError('activity encoding')
    if not allowed:continue
    edge=[]
    for g,(splits,retained_sets,pair) in selected.items():
     c=intercept(p,g);regular=[v for v in range(q) if v not in splits and v not in pair]
     if c in splits:
      slot=splits.index(c);kret=3 if len(splits)==1 else 2
      v=1+len(regular)+slot*kret+retained_sets[slot].index(i)
     else:v=0 if c in pair else 1+regular.index(c)
     if label(i,g,v) not in positive:raise RuntimeError('label decoding')
     edge.append(v)
    actual.append(tuple(edge))
   edges=sorted(set(actual));models+=1
   if not all(any(a==b for a,b in zip(e,f)) for e,f in itertools.combinations(edges,2)):raise RuntimeError('intersection encoding')
   for g,(splits,retained_sets,pair) in selected.items():
    if not all(active(i) in positive for retained in retained_sets for i in retained):raise RuntimeError('retained membership')
   cover,_=cover_at_most(edges)
   if cover is None:
    checked=check_edges(edges)
    Path(a.output).write_text(json.dumps({'edges':edges,'selected':selected,'vertex_bound':6,'checked_five_vertex_sets':checked},indent=2)+'\n')
    print('INDEPENDENTLY CHECKED RANK-SIX WITNESS',flush=True);return
   cover=sorted(set(cover));cover+=list(v for v in range(36) if v not in cover)[:5-len(cover)]
   key=tuple(sorted(cover))
   if key in cuts:raise RuntimeError('ineffective cover cut')
   cuts.add(key);avoid=[]
   for i in range(25):
    z=pool.id(('avoid',len(cuts),i));avoid.append(z)
    literals=[active(i)]+[-label(i,v//6,v%6) for v in key]
    for lit in literals:solver.add_clause([-z,lit])
    solver.add_clause([z]+[-lit for lit in literals])
   solver.add_clause(avoid)
   if models%100==0:print(models,'structured models;',round(time.monotonic()-start,1),'s',flush=True)
 print('Finished',models,'structured models;',len(cuts),'cover cuts',flush=True)

if __name__=='__main__':main()
