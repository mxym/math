"""Prime-element periodic-sieve certificates, a NEW format (standard library).
No dependence on the older split-pair verifier. Never run an unbounded search.
Resource policy: at most 32 generators, 64 steps, 65536 quotient cells,
and primes <= 1000000. This policy limits this implementation, not the theorem.
"""
from collections import deque
from math import isqrt, lcm
import json
from pathlib import Path

FORMAT = 'quadratic-prime-element-sieve-v1'
MAX_CELLS = 65536

def require(condition, message):
    if not condition:
        raise ValueError(message)

def integer(x):
    return type(x) is int and abs(x).bit_length() <= 128

def pair(x):
    return isinstance(x, (list, tuple)) and len(x) == 2 and all(integer(t) for t in x)

def prime(p):
    return integer(p) and 2 <= p <= 1000000 and all(p % d for d in range(2,isqrt(p)+1))

def norm(x,u,v):
    a,b=x
    return a*a+u*a*b-v*b*b

def prepare(data):
    require(data.get('format') == FORMAT, 'Wrong format')
    u,v=data['u'],data['v']
    require(integer(u) and integer(v), 'Invalid order parameters')
    disc=u*u+4*v
    require(disc < 0 or isqrt(disc)**2 != disc, 'Not a quadratic field')
    require(isinstance(data['steps'],list) and len(data['steps']) <= 64,'Step resource limit')
    require(all(pair(d) for d in data['steps']), 'Invalid step')
    steps=tuple(tuple(d) for d in data['steps'])
    require(len(set(steps)) == len(steps) and (0,0) not in steps,'Repeated or zero step')
    require(all((-a,-b) in steps for a,b in steps),'Asymmetric steps')
    generators=data['generators']
    require(isinstance(generators,list) and len(generators)<=32,'Generator resource limit')
    Q=1; maps=[]
    for entry in generators:
        p,alpha=entry['p'],entry['alpha']
        require(prime(p) and pair(alpha),'Invalid prime or generator')
        a,b=alpha
        require(abs(norm(alpha,u,v))==p,'Generator does not have prime absolute norm')
        # A = [[a,vb],[b,a+ub]]. Either nonzero adjugate row annihilates A mod p.
        rows=[((a+u*b)%p,(-v*b)%p),((-b)%p,a%p)]
        row=next((r for r in rows if r!=(0,0)),None)
        require(row is not None,'Zero multiplication matrix modulo p')
        require((row[0]*a+row[1]*b)%p==0 and
                (row[0]*v*b+row[1]*(a+u*b))%p==0,'Invalid kernel row')
        maps.append((p,row));Q=lcm(Q,p)
        require(Q*Q<=MAX_CELLS,'Quotient resource limit exceeded')
    allowed={(a,b) for a in range(Q) for b in range(Q)
             if all((r[0]*a+r[1]*b)%p for p,r in maps)}
    return Q,steps,allowed

def edges(r,Q,steps,allowed):
    for a,b in steps:
        x,y=r[0]+a,r[1]+b;s=(x%Q,y%Q)
        if s in allowed:
            yield s,((x-s[0])//Q,(y-s[1])//Q)

def make_certificate(data):
    Q,steps,allowed=prepare(data)
    h={}
    for root in sorted(allowed):
        if root in h:continue
        h[root]=(0,0); todo=deque([root])
        while todo:
            r=todo.popleft()
            for s,k in edges(r,Q,steps,allowed):
                value=(h[r][0]+k[0],h[r][1]+k[1])
                if s in h:
                    if h[s]!=value:return None
                else:h[s]=value;todo.append(s)
    return {'format':FORMAT,'Q':Q,'potentials':[[*r,*h[r]] for r in sorted(h)]}

def verify_certificate(data,certificate):
    Q,steps,allowed=prepare(data)
    require(certificate.get('format')==FORMAT,'Wrong certificate format')
    require(integer(certificate['Q']) and certificate['Q']==Q,'Wrong modulus')
    rows=certificate['potentials']
    require(isinstance(rows,list) and len(rows)<=MAX_CELLS,'Invalid potential list')
    require(all(isinstance(r,list) and len(r)==4 and all(integer(x) for x in r) for r in rows),'Invalid potential row')
    h={tuple(r[:2]):tuple(r[2:]) for r in rows}
    require(len(h)==len(rows) and set(h)==allowed,'Incomplete or duplicated allowed set')
    for r in allowed:
        for s,k in edges(r,Q,steps,allowed):
            require(h[s]==(h[r][0]+k[0],h[r][1]+k[1]),'Inconsistent potential')
    return True

def statistics(data,certificate):
    verify_certificate(data,certificate)
    Q,steps,allowed=prepare(data)
    unseen=set(allowed); sizes=[]; directed_edges=0
    while unseen:
        todo=[unseen.pop()];size=0
        while todo:
            r=todo.pop();size+=1
            for s,k in edges(r,Q,steps,allowed):
                directed_edges+=1
                if s in unseen:unseen.remove(s);todo.append(s)
        sizes.append(size)
    # Any positive upper bound for avoiding-component size is valid.
    B=max([1]+sizes);Delta=len(steps)
    H=max([0]+[abs(x) for d in steps for x in d])
    if data['generators']:
        # Exceptional norms lie in the 2*k values +/- selected primes.
        k=len({g['p'] for g in data['generators']})
        V=(2*(B+1)*H+1)**2-1
        E=max(1,8*k*k*V)
        bound=max(B,E*(1+Delta*B))
    else:bound=B
    result=dict(Q=Q,allowed_residues=len(allowed),directed_edges=directed_edges,
                quotient_component_sizes=sorted(sizes),avoiding_bound=B,
                irreducible_component_bound=bound)
    if data['u']==0 and data['v']==-1 and data['generators']:
        # Gaussian exceptions have one of the selected positive prime norms.
        primes={g['p'] for g in data['generators']}
        R=isqrt(max(primes))
        # Bound this optional enumeration as strictly as the quotient work.
        if (2*R+1)**2<=MAX_CELLS:
            count=sum(a*a+b*b in primes for a in range(-R,R+1) for b in range(-R,R+1))
            result['finite_exception_count']=count
            result['finite_exception_component_bound']=max(B,count*(1+Delta*B))
    return result

if __name__=='__main__':
    here=Path(__file__).parent
    for name in ('gaussian_four_steps','sqrt2_four_steps','gaussian_eight_steps','sqrt2_eight_steps'):
        bundle=json.loads((here/(name+'.json')).read_text())
        print(name,json.dumps(statistics(bundle['data'],bundle['certificate']),sort_keys=True))
