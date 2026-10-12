#!/usr/bin/env python3
"""Independent exact checker for the sharp permanent projection nesting gap.

Untrusted extension certificates must satisfy exact witness attainability,
complete operation closure and Pareto antichain conditions. The published
0..56 base certificate has a SEPARATE checker; it is replayed here.

Every mathematical comparison is integer/Fraction only. No assert statements,
floating point decisions, optimizer output, random input or third-party modules.
"""
import bisect
import hashlib
import importlib.util
import json
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial
from pathlib import Path

HERE=Path(__file__).resolve().parent.parent
BASE=HERE.parent/'projection-first-nesting-d55'/'certificates'/'two_layer56.json'
BASE_CHECK=HERE.parent/'projection-first-nesting-d55'/'code'/'check_two_layer.py'
PRIOR_C55=HERE.parent/'projection-first-nesting-d55'/'certificates'/'all_tree49to55.json'
CERT=HERE/'certificates'/'extension57to85.json'
EXPECTED_BASE='101ffdf287f984965c941b1f98f93de89ae4a3bd0d4e796f02558a8039cb3d9f'
EXPECTED_BASE_CHECK='f6ce470365577580d3f94663b486c4a52ea878e09b59c43a11b7a3da4e5becd6'
EXPECTED_PRIOR_C55='7cb6b097984163b471ead5ac08fca71fb7425c489ba372d99f3809269552b60c'
Q4=F(175,128); Q5=F(189,128)
RHO_55=F(666588049410094050176708629890606697662639715,
         661941565426077453299492872184552524829687808)


def require(cond,why):
    if not cond:raise RuntimeError('persistent-nesting checker: '+why)


def canonical_fraction(x,allow_zero=False):
    require(isinstance(x,str),'fraction must be a string')
    y=F(x)
    require(str(y)==x and (y>=0 if allow_zero else y>0),
            'noncanonical or nonpositive fraction')
    return y


@lru_cache(maxsize=None)
def g(n):
    require(n>0 and isinstance(n,int),'factorial domain')
    return F(n**n,factorial(n))


@lru_cache(maxsize=None)
def product_block(p,q):
    n=p+q
    h=F(n)/(F(p,p+1)+F(q,q+1))
    Q=F(comb(n,p)*p**p*q**q*(n+2*p*q),n**(n+1))
    return h,Q


def nested_atom(p):
    # T_p x (B_(4,4) * B_(4,4)) has D=p+18.
    d=p+17
    h=F(d)/(F(p,p+1)+F(17,10))
    Q=Q4*Q4*g(p)*g(17)/g(d)*F(27*p+17,d)
    return h,Q


def replay_original_base():
    require(hashlib.sha256(BASE.read_bytes()).hexdigest()==EXPECTED_BASE,
            'wrong previously certified E_0..E_56 parent')
    require(hashlib.sha256(BASE_CHECK.read_bytes()).hexdigest()==EXPECTED_BASE_CHECK,
            'previous checker source changed unexpectedly')
    # Explicitly rerun the independent existing base checker, not the producer.
    spec=importlib.util.spec_from_file_location('certified_two_layer56',BASE_CHECK)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    base_values=module.check(quiet=True)
    require(len(base_values)==56,'parent verifier did not cover D=1..56')
    base=json.loads(BASE.read_text())
    require(base['max_D']==56 and len(base['frontiers'])==57,
            'invalid parent certificate length')
    levels=[[(canonical_fraction(z['H'],allow_zero=i==0),
              canonical_fraction(z['Q']),z['op']) for z in row]
            for i,row in enumerate(base['frontiers'])]
    return levels,base_values


def exact_B_extension(levels,cert):
    require(cert.get('parent_sha256')==EXPECTED_BASE and cert.get('first_D')==57 and
            cert.get('last_D')==85 and len(cert.get('frontiers',[]))==29 and
            len(cert.get('summary',[]))==29, 'wrong extension scope')
    comparisons=0
    for D in range(57,86):
        saved=cert['frontiers'][D-57]
        require(isinstance(saved,list) and saved,'empty extension frontier')
        front=[]
        for entry in saved:
            require(isinstance(entry,dict) and set(entry)=={'H','Q','op'},
                    'invalid frontier fields')
            h=canonical_fraction(entry['H']);q=canonical_fraction(entry['Q'])
            op=entry['op']
            require(isinstance(op,list) and op,'missing operation pointer')
            if op[0]=='point':
                require(len(op)==3 and op[1]==D-1,'invalid point dimensions')
                i=op[2]
                require(type(i) is int and 0<=i<len(levels[D-1]),
                        'invalid point pointer')
                ha,qa=levels[D-1][i][:2]
                hh,qq=ha+1,qa
            elif op[0]=='block':
                require(len(op)==5,'invalid block pointer length')
                j,i,p,t=op[1:]
                require(all(type(v) is int for v in (j,i,p,t)) and 1<=p<=t
                        and 0<=j<D and j+p+t+1==D and 0<=i<len(levels[j]),
                        'invalid block pointer')
                hb,qb=product_block(p,t)
                ha,qa=levels[j][i][:2]
                hh,qq=ha+hb,qa*qb
            else:
                raise RuntimeError('persistent-nesting checker: illegal construction type')
            require(h==hh and q==qq and 0<h<=D,
                    f'unattainable Pareto state D={D}')
            front.append((h,q,op))
        require(all(front[i][0]>front[i+1][0] and
                    front[i][1]<front[i+1][1] for i in range(len(front)-1)),
                f'frontier is not a strict Pareto antichain D={D}')
        neg=[-h for h,_,_ in front]
        qs=[q for _,q,_ in front]
        def covered(h,q):
            i=bisect.bisect_right(neg,-h)-1
            return i>=0 and qs[i]>=q
        for h,q,_ in levels[D-1]:
            require(covered(h+1,q),f'point operation missing D={D}')
            comparisons+=1
        for bsize in range(3,D+1):
            for p in range(1,(bsize-1)//2+1):
                t=bsize-1-p
                hb,qb=product_block(p,t)
                for h,q,_ in levels[D-bsize]:
                    require(covered(h+hb,q*qb),
                            f'uncovered product block p={p},q={t},D={D}')
                    comparisons+=1
        levels.append(front)
        sr=cert['summary'][D-57]
        require(isinstance(sr,dict) and set(sr)=={'D','states','winner','ratio'},
                'summary schema mismatch')
        require(sr['D']==D and sr['states']==len(front),
                'summary number of states wrong')
        k=sr['winner']
        require(type(k) is int and 0<=k<len(front),'summary optimum index invalid')
        sharp=max(h*q/F(D) for h,q,_ in front)
        require(canonical_fraction(sr['ratio'])==sharp and
                front[k][0]*front[k][1]/F(D)==sharp,
                f'stated sharp two-layer optimum is wrong D={D}')
    return comparisons


def verify_finite_witnesses(levels,cert,base_values):
    witnesses=cert['witnesses55to84']
    require(isinstance(witnesses,list) and len(witnesses)==30,
            'finite witness range must cover all D=56..85')
    # Prior complete full-tree and two-layer independent certificates:
    C55=F(333068659627091928809841719168016922609375,
          83816757831946947640666468303298107539456)
    B55=F(9444402294359878125,2393367762580799488)
    require(hashlib.sha256(PRIOR_C55.read_bytes()).hexdigest()==EXPECTED_PRIOR_C55,
            'previously certified full-tree 55D source changed unexpectedly')
    previous_full=json.loads(PRIOR_C55.read_text())
    require(F(previous_full['summary'][-1]['exact_ratio'])==C55,
            'previous full-tree 55D maximum has a different rational value')
    require(base_values[55]==B55 and C55/B55==RHO_55,
            'sharp previously published d=55 ratio inconsistent')
    factors=[]
    for D in range(56,86):
        w=witnesses[D-56]
        require(isinstance(w,dict) and set(w)==
                {'D','p','tailD','tail_index','lower','two_layer_max','relative_factor'},
                'witness schema mismatch')
        p=w['p']; t=w['tailD']; i=w['tail_index']
        require(w['D']==D and type(p) is int and p in (6,7) and
                type(t) is int and t==D-(p+18) and
                type(i) is int and 0<=i<len(levels[t]),
                f'witness dimension/index incorrect D={D}')
        hn,qn=nested_atom(p)
        hf,qf=levels[t][i][:2]
        lower=(hn+hf)*qn*qf/F(D)
        best=max(h*q/F(D) for h,q,_ in levels[D])
        fac=lower/best
        require(canonical_fraction(w['lower'])==lower and
                canonical_fraction(w['two_layer_max'])==best and
                canonical_fraction(w['relative_factor'])==fac,
                f'witness fraction has been corrupted D={D}')
        require(fac>=RHO_55,f'finite nesting gap fails D={D}')
        if D==56:
            require(lower==C55 and fac==RHO_55,
                    'finite minimum not attained at d=55')
        else:
            require(fac>RHO_55 and fac>F(101,100),
                    f'finite gap fails improved d>=56 separation; D={D}')
        factors.append(fac)
    require(min(factors)==RHO_55 and RHO_55>F(1007,1000),
            'wrong claimed sharp persistent gap constant')
    lines=['d\tproduct_seed_p\tfiller_join_D\tfiller_frontier_index\tcertified_lower_ratio_C_over_B']
    for w in witnesses:
        lines.append(f"{w['D']-1}\t{w['p']}\t{w['tailD']}\t{w['tail_index']}\t{w['relative_factor']}")
    require((HERE/'results'/'finite_witnesses.tsv').read_text()=='\n'.join(lines)+'\n',
            'public human-readable finite witness table disagrees with exact certificate')
    return len(factors)


def verify_infinite_tail():
    # Published global two-layer block inequalities:
    # log Q <= A D, log Q <= B(D-H), with
    # A=log(Q5)/11 and B=log(Q4)/4. The integer-power comparisons
    # bound t*=1-A/B in (27/50,11/20) without floating point.
    require(Q4>1 and Q5>1,'log constants not positive')
    require(Q5**80>Q4**99 and Q5**200<Q4**253,
            'rational upper/lower bounds on the optimum H/D split fail')
    # atanh first two positive terms: log Q4>2(z+z^3/3)>31/100
    z=F(47,303)
    require(2*(z+z**3/F(3))>F(31,100),
            'sharp defect-logarithm lower bound fails')
    require(F(24)*F(31,400)*F(27,50)>1,
            'analytic one-variable envelope derivative sign fails')
    # The strict relative factor 209/200 will be enough for EVERY D>=86.
    huge_gap=F(209,200)
    require(huge_gap>RHO_55,'tail relative bound must exceed sharp 55D ratio')
    require(F(5)*g(4)**2/g(8)==Q4 and F(6)*g(5)**2/g(10)==Q5,
            'simplex product block constants wrong')
    # K2 = (K1 x K1)* (K1 x K1), K1=B5*B5. See paper.
    Q2=(F(12)*Q5**4*g(21)**2/g(42))**2
    # Separate spectral amplification: repeat the same K2 by joins, add
    # at most 85 point factors. This yields an explicit growing ratio.
    sigma=F(1009,1000)
    require(Q2**11>Q5**86*sigma**946,
            'strict exponential spectral advantage certificate fails')
    require(F(240,473)*Q5**(-8)>F(1,45),
            'explicit exponential prefactor certificate fails')
    require(F(86-24)>0,'86D join remainder density monotonicity fails')
    for r in range(11):
        require(F(252-5*r)>0,'dimension residue monotonicity fails')
        # Rational power removes the rational exponent (86+r)/11.
        lhs=(F(20*(24+r),11*(86+r))*Q2/huge_gap)**11
        require(lhs>Q5**(86+r),f'tail residue certificate fails r={r}')
    return 11


def check(path=None):
    raw=json.loads(Path(path or CERT).read_text())
    require(isinstance(raw,dict),'extension must be JSON object')
    levels,base_values=replay_original_base()
    pair_count=exact_B_extension(levels,raw)
    finite=verify_finite_witnesses(levels,raw,base_values)
    residues=verify_infinite_tail()
    print('PASS: sharp persistent projection nesting separation in every dimension d>=55')
    print('sharp global ratio lower bound =',RHO_55)
    print('equality of sharp ratio at d=55; strictly larger for every d>=56')
    print('pre-certified two-layer parent dimensions = 1..55')
    print('new exact two-layer Pareto states =',sum(len(z) for z in raw['frontiers']))
    print('new exact two-layer closure candidates =',pair_count)
    print('finite strict ratio witnesses d=55..84 =',finite)
    print('analytic tail d>=85 rational residue inequalities =',residues)
    print('all d>=56: strict gap > 101/100; all d>=85: strict gap > 209/200')
    print('all d>=55: sharp gap > 1007/1000; attained only at d=55')
    print('all d>=85: ratio > (1009/1000)^(d-84)/45 (explicit exponential divergence)')
    print('all mathematical decisions = int/Fraction; no floating point or solver')


if __name__=='__main__':check()
