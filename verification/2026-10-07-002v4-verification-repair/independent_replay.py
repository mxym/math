#!/usr/bin/env python3
"""Independent audit: no submitted checker or generator is imported.

Ideal membership is the multiplication image modulo Q, rather than adjugate
congruences. Complete graphs use actual lifted coordinates, rather than the
submitted potential propagation. Robust-cover controls enumerate intersections
of constraint lines rather than clipping polygons.
"""
import argparse
import hashlib
import itertools
import json
import math
from collections import deque
from fractions import Fraction as F
from pathlib import Path

STEPS = tuple((x,y) for x in (-1,0,1) for y in (-1,0,1) if (x,y)!=(0,0))
GP = ((1,1),(2,1),(2,-1),(3,2),(3,-2))
RP = ((0,1),(3,1),(3,-1))

def need(ok, message):
    if not ok:
        raise ValueError(message)

def integers(x):
    if isinstance(x, dict):
        return all(integers(v) for v in x.values())
    if isinstance(x, list):
        return all(integers(v) for v in x)
    return isinstance(x, str) or type(x) is int

def factors(n):
    return [p for p in range(2,n+1) if n%p==0 and all(p%d for d in range(2,math.isqrt(p)+1))]

def radicals(limit):
    return [n for n in range(1,limit) if all(n%(p*p) for p in factors(n))]

def mul(a,b,v):
    return (a[0]*b[0]+v*a[1]*b[1], a[0]*b[1]+a[1]*b[0])

def image(q,g,v):
    return {((g[0]*x+v*g[1]*y)%q,(g[1]*x+g[0]*y)%q) for x in range(q) for y in range(q)}

def prime_image(q,p,v):
    roots=[s for s in range(p) if (s*s-v)%p==0]
    if roots:
        return {(x,y) for x in range(q) for y in range(q) if any((x+s*y)%p==0 for s in roots)}
    return {(x,y) for x in range(q) for y in range(q) if x%p==0 and y%p==0}

def maximal_allowed(q,v):
    banned=set()
    for p in factors(q):
        banned.update(prime_image(q,p,v))
    return {(x,y) for x in range(q) for y in range(q)}-banned

class Order:
    def __init__(self,q,v):
        self.q=q;self.v=v;self.cache={}
        self.cells={(x,y) for x in range(q) for y in range(q)}
    def ideal(self,g):
        g=tuple(g)
        if g not in self.cache:self.cache[g]=image(self.q,g,self.v)
        return self.cache[g]
    def allowed(self,gs):
        banned=set()
        for g in gs:banned.update(self.ideal(g))
        return self.cells-banned

def walk(q,allowed,w):
    z=tuple(w['root']);start=z
    need((z[0]%q,z[1]%q) in allowed,'forbidden root')
    for d in w['steps']:
        need(tuple(d) in STEPS,'non-F8 step')
        z=(z[0]+d[0],z[1]+d[1])
        need((z[0]%q,z[1]%q) in allowed,'forbidden visited point')
    dx=z[0]-start[0];dy=z[1]-start[1]
    need(dx%q==dy%q==0 and (dx,dy)!=(0,0),'closed walk has zero or nonintegral voltage')
    need([dx//q,dy//q]==w['voltage'],'stored voltage differs')
    need(len(allowed)==w['allowed_residues'],'wrong allowed count')
    return len(w['steps'])

def graph(q,allowed,expect_finite,steps=STEPS):
    coords={};sizes=[];edges=0;infinite=False
    for root in sorted(allowed):
        if root in coords:continue
        coords[root]=root;queue=deque([root]);size=0
        while queue:
            r=queue.popleft();size+=1
            for dx,dy in steps:
                s=((r[0]+dx)%q,(r[1]+dy)%q)
                if s not in allowed:continue
                edges+=1;x,y=coords[r];new=(x+dx,y+dy)
                if s in coords:
                    if coords[s]!=new:infinite=True
                else:coords[s]=new;queue.append(s)
        sizes.append(size)
    need(infinite != expect_finite,'unexpected finite/infinite graph')
    return dict(allowed=len(allowed),components=len(sizes),max_component=max([0]+sizes),directed_edges=edges,finite=not infinite)

def cycle_witness(q,allowed,steps):
    coords={};parents={}
    def path(r):
        out=[]
        while parents[r] is not None:
            r,d=parents[r];out.append(d)
        return list(reversed(out))
    for root in sorted(allowed):
        if root in coords:continue
        coords[root]=root;parents[root]=None;todo=deque([root])
        while todo:
            r=todo.popleft()
            for d in steps:
                s=((r[0]+d[0])%q,(r[1]+d[1])%q)
                if s not in allowed:continue
                new=(coords[r][0]+d[0],coords[r][1]+d[1])
                if s not in coords:
                    coords[s]=new;parents[s]=(r,d);todo.append(s)
                elif coords[s]!=new:
                    ds=path(r)+[d]+[(-x,-y) for x,y in reversed(path(s))]
                    z=root
                    for dx,dy in ds:
                        z=(z[0]+dx,z[1]+dy)
                        need((z[0]%q,z[1]%q) in allowed,'scope-control forbidden visit')
                    dx=z[0]-root[0];dy=z[1]-root[1]
                    need(dx%q==dy%q==0 and (dx,dy)!=(0,0),'scope-control bad voltage')
                    return dict(root=list(root),steps=[list(d) for d in ds],voltage=[dx//q,dy//q])
    raise ValueError('no nonzero cycle')

def canonical(g):
    x,y=g
    return min((x,y),(-y,x),(-x,-y),(y,-x))

def divisor_list(primes,ranges,v):
    out=[]
    for es in itertools.product(*ranges):
        if not any(es):continue
        z=(1,0)
        for p,e in zip(primes,es):
            for _ in range(e):z=mul(z,p,v)
        out.append((es,z))
    return out

def arithmetic(root):
    entry=root/'preprints/002-quadratic-order-moats'
    code=entry/'v4/code';report={};total_steps=0;negative_graphs=0
    g=json.loads((code/'period_optimality.json').read_text())
    e=json.loads((code/'endpoint_rigidity.json').read_text())
    r=json.loads((code/'sqrt2_period_endpoint.json').read_text())
    need(all(integers(d) for d in (g,e,r)),'noninteger certificate arithmetic')
    need([x['q'] for x in g['failed_radicals']]==radicals(130),'Gaussian radical coverage')
    need(g['positive_generators']==[list(p) for p in GP],'Gaussian fixed endpoint data')
    for x in g['failed_radicals']:
        a=maximal_allowed(x['q'],-1)
        # Polynomial factorization independently identifies the forbidden union.
        order=Order(x['q'],-1)
        need(order.allowed(x['generators'])==a,'wrong maximal Gaussian ideals')
        total_steps+=walk(x['q'],a,x)
        graph(x['q'],a,False);negative_graphs+=1
    report['gaussian_lower_radicals']=len(g['failed_radicals'])
    order=Order(130,-1)
    divs=sorted({canonical(z) for _,z in divisor_list(GP,(range(3),range(2),range(2),range(2),range(2)),-1)})
    need(len(divs)==47 and e['all_nonunit_divisor_ideals']==[list(z) for z in divs],'Gaussian divisor coverage')
    need(e['prime_generators']==[list(p) for p in GP] and e['period']==130,'Gaussian endpoint constants')
    expected=[c for k in range(5) for c in itertools.combinations(range(5),k)]
    need([tuple(c['indices']) for c in e['proper_prime_subset_failures']]==expected,'Gaussian subset coverage')
    for c in e['proper_prime_subset_failures']:
        gs=[GP[i] for i in c['indices']]
        need(c['generators']==[list(p) for p in gs],'Gaussian subset generator binding')
        a=order.allowed(gs);total_steps+=walk(130,a,c['witness']);graph(130,a,False);negative_graphs+=1
    expected=[]
    for j,p in enumerate(GP):
        for z in divs:
            if order.ideal(z)<order.ideal(p):
                expected.append((j,z,tuple(t for i,t in enumerate(GP) if i!=j)+(z,)))
    got=[(c['prime_index'],tuple(c['replacement']),tuple(map(tuple,c['generators']))) for c in e['proper_subideal_replacement_failures']]
    need(got==expected and len(expected)==123,'Gaussian replacement coverage')
    for c in e['proper_subideal_replacement_failures']:
        a=order.allowed(c['generators']);total_steps+=walk(130,a,c['witness']);graph(130,a,False);negative_graphs+=1
    report['gaussian_endpoint']=graph(130,order.allowed(GP),True)
    report['gaussian_divisors']=len(divs);report['gaussian_subset_failures']=31;report['gaussian_replacements']=123
    need([c['q'] for c in r['lower_period_failures']]==radicals(14),'sqrt2 radical coverage')
    need(r['prime_generators']==[list(p) for p in RP],'sqrt2 endpoint constants')
    for c in r['lower_period_failures']:
        q=c['q'];a=maximal_allowed(q,2)
        need(Order(q,2).allowed(c['generators'])==a,'wrong maximal sqrt2 ideals')
        total_steps+=walk(q,a,c['witness']);graph(q,a,False);negative_graphs+=1
    order=Order(14,2);divs=divisor_list(RP,(range(3),range(2),range(2)),2)
    need([(tuple(c['exponents']),tuple(c['generator'])) for c in r['divisor_ideals_14']]==divs,'sqrt2 divisor coverage')
    need(len({frozenset(order.ideal(z)) for _,z in divs})==11,'distinct sqrt2 divisor ideals')
    pairs=((0,1),(0,2));need(sorted(map(tuple,r['successful_prime_pairs']))==list(pairs),'sqrt2 success labels')
    expected=[c for k in range(3) for c in itertools.combinations(range(3),k) if c not in pairs]
    need([tuple(c['indices']) for c in r['failed_prime_subsets']]==expected,'sqrt2 subset coverage')
    for c in r['failed_prime_subsets']:
        gs=[RP[i] for i in c['indices']]
        need(c['generators']==[list(p) for p in gs],'sqrt2 subset generator binding')
        a=order.allowed(gs);total_steps+=walk(14,a,c['witness']);graph(14,a,False);negative_graphs+=1
    expected=[]
    for pair in pairs:
        for pos,j in enumerate(pair):
            for es,z in divs:
                if order.ideal(z)<order.ideal(RP[j]):
                    expected.append((pair,j,es,z,(RP[pair[1-pos]],z)))
    got=[(tuple(c['success_pair']),c['prime_index'],tuple(c['replacement_exponents']),tuple(c['replacement']),tuple(map(tuple,c['generators']))) for c in r['proper_subideal_replacements']]
    need(got==expected and len(expected)==24,'sqrt2 replacement coverage')
    for c in r['proper_subideal_replacements']:
        a=order.allowed(c['generators']);total_steps+=walk(14,a,c['witness']);graph(14,a,False);negative_graphs+=1
    report['sqrt2_endpoints']=[graph(14,order.allowed([RP[i] for i in pair]),True) for pair in pairs]
    report.update(sqrt2_lower_radicals=9,sqrt2_divisors=11,sqrt2_subset_failures=5,sqrt2_replacements=24,negative_graphs=negative_graphs,total_failure_steps=total_steps)
    # Check frozen potential lists independently using multiplication images.
    for name,v,gs,q in [('gaussian_eight_steps_principal',-1,GP,130),('sqrt2_eight_steps',2,RP[:2],14)]:
        b=json.loads((entry/'v3/certificates_v3'/(name+'.json')).read_text());data=b['data'];cert=b['certificate']
        need(data['u']==0 and data['v']==v and sorted(map(tuple,data['steps']))==list(STEPS),'wrong historical order/steps')
        need([tuple(c['alpha']) for c in data['generators']]==list(gs),'wrong historical generators')
        a=Order(q,v).allowed(gs);rows=cert['potentials'];h={tuple(x[:2]):tuple(x[2:]) for x in rows}
        need(len(h)==len(rows) and set(h)==a and cert['Q']==q,'historical potential coverage')
        for x,y in sorted(a):
            for dx,dy in STEPS:
                s=((x+dx)%q,(y+dy)%q)
                if s in a:
                    px,py=h[(x,y)];sx,sy=h[s]
                    need(s[0]+q*sx==x+q*px+dx and s[1]+q*sy==y+q*py+dy,'historical lifted edge inconsistent')
    # Restoration constants, independently recalculated.
    exceptions=sum(x*x+y*y in (2,5,13) for x in range(-3,4) for y in range(-3,4))
    report['gaussian_exceptions']=exceptions;report['gaussian_irreducible_bound']=exceptions*(1+8*580)
    report['sqrt2_irreducible_bound']=8*2**2*((2*(6+1)+1)**2-1)*(1+8*6)
    larger=STEPS+((-2,0),(2,0),(0,-2),(0,2))
    report['larger_jump_controls']={}
    for label,q,v,gs in [('gaussian',130,-1,GP),('sqrt2',14,2,RP[:2])]:
        a=Order(q,v).allowed(gs)
        report['larger_jump_controls'][label]=dict(graph=graph(q,a,False,larger),witness=cycle_witness(q,a,larger))
    return report

def gap_feasible(points,radii,hole):
    """Independent exact check for a single open interval repeated by Z."""
    left,right=map(F,hole);points=list(map(F,points));radii=list(map(F,radii))
    need(left<right and right-left<1,'one nontrivial periodic hole required')
    lo=min(a-r for a,r in zip(points,radii));hi=max(1+2*a+r for a,r in zip(points,radii))
    gaps=[(right+k,left+k+1) for k in range(math.floor(lo)-2,math.ceil(hi)+2)]
    box=[(-F(1),F(0),F(0)),(F(1),F(0),F(1)),(F(0),-F(1),-F(1)),(F(0),F(1),F(2))]
    for selected in itertools.product(gaps,repeat=len(points)):
        lines=list(box)
        for a,r,(l,u) in zip(points,radii,selected):
            lines.extend([(F(1),a,u+r),(-F(1),-a,-l+r)])
        for (a,b,c),(d,e,f) in itertools.combinations(lines,2):
            det=a*e-b*d
            if not det:continue
            x=(c*e-b*f)/det;t=(a*f-c*d)/det
            if all(A*x+B*t<=C for A,B,C in lines):
                errors=[min(max(x+t*a,l),u)-(x+t*a) for a,(l,u) in zip(points,selected)]
                need(all(abs(z)<=r for z,r in zip(errors,radii)),'invalid independently generated error')
                for a,z in zip(points,errors):
                    val=x+t*a+z
                    need(not any(left+k<val<right+k for k in range(math.floor(val)-2,math.floor(val)+2)),'witness lies in open hole')
                return {'valid':False,'witness':dict(x=str(x),t=str(t),errors=list(map(str,errors)))}
    return {'valid':True}

def analytic_controls():
    tests=[]
    for radius in ['0','1/100','1/81','1/80','1/79','1/50']:
        r=F(radius);answer=gap_feasible(['1/8','1/4'],[r,r],['1/10','1'])
        need(answer['valid']==(r<F(1,80)),'sharp uncertainty threshold')
        tests.append(dict(radius=radius,**answer))
    answer=gap_feasible(['1/8','1/4'],['0','0'],['1/8','1'])
    need(not answer['valid'],'open endpoint failure lost');tests.append(dict(case='open-endpoint',**answer))
    # Independent density failure beyond the profile hypotheses:
    # A={2^-n}; phi(a)=2^(-1/a); Psi(n)=2^n. In L consecutive integer
    # bins at most 1+floor(log2 L) powers of two can occur, so d*=0.
    tests.append(dict(case='flat-profile-density-control',input_density=1,output_max_count_bound='1+floor(log2 L)',output_density=0,profile='2^(-1/a)'))
    # Puiseux error scaling and the dyadic coefficient transfer, exactly.
    a=F(1,16);k=3;q=5;b=2**k*a*a;omega=a
    need(b*(F(q,2**k)*omega)==q*a*a*omega,'coefficient normalization')
    tests.append(dict(case='coefficient-normalization',a=str(a),k=k,q=q,error=str(q*a*a*omega)))
    return tests

def main():
    parser=argparse.ArgumentParser();parser.add_argument('repo',type=Path);parser.add_argument('--output',type=Path)
    args=parser.parse_args();result=dict(status='PASS',arithmetic='exact integer and rational',finite=arithmetic(args.repo),analytic_controls=analytic_controls())
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
