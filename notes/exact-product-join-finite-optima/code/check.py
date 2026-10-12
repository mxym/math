#!/usr/bin/env python3
"""Independently replays exact frontiers and exhaustively checks their closure.

Certificate-produced state lists are UNTRUSTED until:
1) every retained state is attained via exact product/join recurrence;
2) retained states form a Pareto antichain;
3) all binary operations on certified frontiers are dominated by a retained state;
4) per-dimension exact optima are recomputed and witness shapes confirmed.
The inductive completeness argument is in ../paper.md.
"""
import bisect
import json
import sys
from pathlib import Path
from fractions import Fraction as F
from math import factorial


def require(b, why):
    if not b:
        raise RuntimeError(why)


def parse_fraction(v):
    require(isinstance(v,str),'non-string rational')
    x=F(v)
    require(str(x)==v and x>0,'noncanonical or nonpositive rational')
    return x


def calc_rational(r,s,a,b,kind,constants):
    # Formula independently written from the 005 v2 calculus in (D,H,Q).
    ha,qa=a;hb,qb=b
    if kind=='join':
        return ha+hb,qa*qb
    d=r+s
    hp=F(d)*ha*hb/(r*hb+s*ha)
    q=qa*qb*constants[r]*constants[s]/constants[d]*F(s*ha+r*hb,d)
    return hp,q


def simple_join_atoms(states,d,i):
    kind,*args=states[d][i][2]
    if kind=='point':return [('point',)]
    r,a,s,b=args
    if kind=='join':
        return simple_join_atoms(states,r,a)+simple_join_atoms(states,s,b)
    left=simple_join_atoms(states,r,a)
    right=simple_join_atoms(states,s,b)
    if all(x==('point',) for x in left+right):
        return [('simplex_product',min(r,s),max(r,s))]
    return [('nested_product',r,s)]


def witness_description(atoms):
    pts=0; products={}; nested=0
    for t in atoms:
        if t[0]=='point':pts+=1
        elif t[0]=='simplex_product':products[t[1:]]=products.get(t[1:],0)+1
        else:nested+=1
    return {'join_points':pts,
            'simplex_products':[{'p':p,'q':q,'count':count} for (p,q),count in sorted(products.items())],
            'other_product_atoms':nested}


def is_dominated(h,q,sorted_neg_h,qs):
    # H decreases strictly and Q increases strictly along the frontier.
    idx=bisect.bisect_right(sorted_neg_h,-h)-1
    return idx>=0 and qs[idx]>=q


def check(filepath):
    cert=json.loads(Path(filepath).read_text())
    require(isinstance(cert,dict),'certificate must be an object')
    N=cert['max_dimension']
    require(N==48,'wrong certified range')
    raw=cert['states'];summary=cert['summary']
    require(len(raw)==N+1 and len(summary)==N,'incomplete level list')
    require(len(raw[0])==1,'point base must contain exactly one state')
    constants=[F(1)]+[F(d**d, factorial(d)) for d in range(1,N+1)]
    states=[]
    candidate_count=0
    table_lines=['dimension\tsharp_R_over_simplex\tjoin_points\tsimplex_product_factors']
    for d,entry in enumerate(raw):
        require(isinstance(entry,list) and entry,'empty level')
        level=[]
        for record in entry:
            require(set(record)=={'H','Q','op'},'unexpected/missing fields')
            h=parse_fraction(record['H']);q=parse_fraction(record['Q'])
            op=record['op']
            require(isinstance(op,list) and op,'malformed construction pointer')
            if d==0:
                require(op==['point'] and h==1 and q==1,'invalid base point')
            else:
                require(len(op)==5 and op[0] in ('join','product'),'bad operation')
                tag,r,i,s,j=op
                require(all(isinstance(z,int) and not isinstance(z,bool) for z in (r,i,s,j)), 'noninteger operation')
                require(0<=r<=s<d and r+s+(tag=='join')==d,'dimension mismatch')
                if tag=='product':require(r>=1,'nontrivial product must have positive factors')
                require(0<=i<len(states[r]) and 0<=j<len(states[s]),'parent out of range')
                hh,qq=calc_rational(r,s,states[r][i][:2],states[s][j][:2],tag,constants)
                require((hh,qq)==(h,q),f'false attainable state: dimension {d}')
                require(F(2)<=h<=d+1,'invariant state range wrong')
            level.append((h,q,op))
        if d>0:
            require(all(level[j][0]>level[j+1][0] and level[j][1]<level[j+1][1]
                        for j in range(len(level)-1)),f'non-Pareto frontier at dimension {d}')
        states.append(level)
        if d==0:continue
        Hneg=[-h for h,_,_ in level]
        vals=[q for _,q,_ in level]
        # All joins from smaller frontiers must lie below this frontier.
        for r in range(d):
            s=d-r-1
            if r>s:break
            for ha,qa,_ in states[r]:
                for hb,qb,_ in states[s]:
                    h=ha+hb;q=qa*qb
                    require(is_dominated(h,q,Hneg,vals),f'uncovered JOIN split ({d},{r},{s})')
                    candidate_count+=1
        # All genuine products from smaller frontiers are checked separately.
        for r in range(1,d):
            s=d-r
            if r>s:break
            C=constants[r]*constants[s]/constants[d]
            for ha,qa,_ in states[r]:
                for hb,qb,_ in states[s]:
                    h=F(d)*ha*hb/(r*hb+s*ha)
                    q=qa*qb*C*F(s*ha+r*hb,d)
                    require(is_dominated(h,q,Hneg,vals),f'uncovered PRODUCT split ({d},{r},{s})')
                    candidate_count+=1
        item=summary[d-1]
        require(item['dimension']==d and item['frontier_size']==len(level),f'summary size wrong at {d}')
        v=[h*q/F(d+1) for h,q,_ in level]
        opt=max(v);i=item['best_index']
        require(isinstance(i,int) and 0<=i<len(level) and v[i]==opt,'wrong optimum pointer')
        require(F(int(item['ratio_num']),int(item['ratio_den']))==opt,'wrong optimum fraction')
        atoms=simple_join_atoms(states,d,i)
        description=witness_description(atoms)
        require(description==item['optimal_structure'],'false optimal shape')
        ratio_text=str(opt)
        factors=';'.join(f'T{z["p"]}xT{z["q"]}^{z["count"]}' for z in description['simplex_products']) or '-'
        table_lines.append(f'{d}\t{ratio_text}\t{description["join_points"]}\t{factors}')
        require(all(t[0]!='nested_product' for t in atoms),
                f'optimal witness not join of simplex products at dimension {d}')
        if d<=13:require(opt==1,'simplex wrong in dimensions 1 through 13')
        if d==14:require(opt==F(385,384),'historical dimension-14 witness disagree')
    # Independently derived exact example in dimension 48: join of 3(T4xT4)
    # and 2(T5xT5); each product has Q=175/128, 189/128, H=5,6.
    require(F(5)*constants[4]**2/constants[8]==F(175,128), 'T4 product computation fails')
    require(F(6)*constants[5]**2/constants[10]==F(189,128), 'T5 product computation fails')
    bound=F(27,49)*F(175,128)**3*F(189,128)**2
    assert_expected=F(105488578125,34359738368)
    require(bound==assert_expected,'independent 48D formula invalid')
    require(F(int(summary[-1]['ratio_num']),int(summary[-1]['ratio_den']))==bound,
            'dimension-48 result differs from explicit five-block witness')
    require(bound>3,'dimension-48 sharp constant not above 3')
    table_path=Path(__file__).resolve().parent.parent/'results'/'optima.tsv'
    require(table_path.read_text()=='\n'.join(table_lines)+'\n', 'displayed optimum table disagrees with exact certificate')
    print('PASS: exact all-tree Pareto-frontier certificate through dimension 48')
    print('verified frontier states =',sum(len(z) for z in states))
    print('binary operation candidates replayed =',candidate_count)
    print('sharp dimensions 1..13 = simplex value')
    print('sharp dimension 14 = 385/384 times simplex')
    print('sharp dimension 48 = 105488578125/34359738368 times simplex')
    print('one sharp 48D body = (T4 x T4)^(*3) * (T5 x T5)^(*2)')
    print('every dimension 1..48 has an optimal join of simplex products')
    print('all decisions = exact Fraction arithmetic; no floating point / solver / assert checks')


if __name__=='__main__':
    default=Path(__file__).resolve().parent.parent/'certificates'/'frontiers48.json'
    check(sys.argv[1] if len(sys.argv)>1 else default)
