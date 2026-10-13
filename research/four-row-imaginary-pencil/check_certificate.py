#!/usr/bin/env python3
"""Exact full-matrix verification of the four-row imaginary-boundary certificate.

Only standard-library rational arithmetic is used. No SDP solver, floating-point
eigensolver or sampled input matrix is a proof premise.
"""
from pathlib import Path
from fractions import Fraction
from collections import defaultdict
import argparse,copy,hashlib,itertools,json
from quadratic_field import R,C

TUPLES=list(itertools.product(range(4),repeat=4))
INDEX={x:i for i,x in enumerate(TUPLES)}
PERMUTATIONS=list(itertools.permutations(range(4)))
def sign(p):return (-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))
GROUP=[(r,c) for r in PERMUTATIONS for c in PERMUTATIONS if sign(r)==sign(c)]
def require(ok,message):
    if not ok:raise ValueError(message)

def mm(a,b):
    return [[sum((x*y for x,y in zip(row,col)),C()) for col in zip(*b)] for row in a]
def adjoint(a):return [[x.conj() for x in col] for col in zip(*a)]
def read_matrix(data):
    require(data and len(data[0])>0,'Empty certificate matrix')
    width=len(data[0]);require(all(len(row)==width for row in data),'Ragged certificate matrix')
    return [[C.read(x) for x in row] for row in data]

def verify_factors(data):
    blocks=[]
    for bi,record in enumerate(data['blocks']):
        group=record['group'];N=read_matrix(record['N']);Z=read_matrix(record['Z']);L=read_matrix(record['LDL_L'])
        d=[R(*x) for x in record['LDL_diagonal']]
        n=len(Z);require(len(N)==len(group) and len(N[0])==n,'N dimensions differ')
        require(len(Z[0])==n and len(L)==n and len(L[0])==n and len(d)==n,'LDL dimensions differ')
        require(all(x.sign()==1 for x in d),'An ordered-field LDL pivot is not strictly positive')
        D=[[C(d[i]) if i==j else C() for j in range(n)] for i in range(n)]
        require(mm(mm(L,D),adjoint(L))==Z,'Exact positive LDL identity failed')
        Q=mm(mm(N,Z),adjoint(N))
        subset=record['subset'];require(set(subset)<=set(range(4)),'Invalid transpose subset')
        require(len(set(group))==len(group) and all(0<=j<256 for j in group),'Invalid support indices')
        blocks.append((subset,group,Q))
        print('POSITIVE_FACTOR_PASS',bi,'size',n,flush=True)
    return blocks

def verify_identity(data,blocks):
    beta=R(*data['beta']);constant=R(*data['constant_squared'])
    require(beta==R(Fraction(3,2),Fraction(-1,3)),'Certificate has the wrong actual boundary coefficient')
    require(constant==R(Fraction(9,4)),'Certificate has the wrong sharp constant')
    summed={}
    # Explicitly average all 288 group elements; no orbit reduction is trusted.
    for bi,(subset,support,Q) in enumerate(blocks):
        entries=[]
        for j,a in enumerate(support):
            for k,b in enumerate(support):
                if not Q[j][k]:continue
                oa=tuple(TUPLES[b][i] if i in subset else TUPLES[a][i] for i in range(4))
                ob=tuple(TUPLES[a][i] if i in subset else TUPLES[b][i] for i in range(4))
                entries.append((oa,ob,Q[j][k]))
        for row,col in GROUP:
            for a,b,value in entries:
                aa=INDEX[tuple(col[a[row[i]]] for i in range(4))]
                bb=INDEX[tuple(col[b[row[i]]] for i in range(4))]
                key=(aa,bb);summed[key]=summed.get(key,C())+value
        print('FULL_GROUP_AVERAGE_PASS',bi,flush=True)
    v=[C(1,beta*sign(x)) if len(set(x))==4 else C() for x in TUPLES]
    for j in range(256):
        for k in range(256):
            expected=(C(constant) if j==k else C())-v[j]*v[k].conj()
            actual=summed.get((j,k),C())/len(GROUP)
            require(actual==expected,f'Full matrix identity failed at ({j},{k})')
    return {'group_order':len(GROUP),'full_matrix_entries':256**2,
            'positive_blocks':len(blocks),'positive_factor_sizes':[len(z['Z']) for z in data['blocks']]}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--certificate',type=Path,default=Path(__file__).with_name('imaginary_boundary_certificate.json'))
    ap.add_argument('--negative-controls',action='store_true')
    args=ap.parse_args();data=json.loads(args.certificate.read_text())
    blocks=verify_factors(data);report=verify_identity(data,blocks)
    rejected=[]
    if args.negative_controls:
        bad=copy.deepcopy(data);bad['blocks'][0]['Z'][0][0][0]=str(Fraction(bad['blocks'][0]['Z'][0][0][0])+Fraction(1,10**6))
        try:verify_factors(bad)
        except ValueError:rejected.append('corrupt_Gram_coefficient')
        else:raise ValueError('Wrong Gram coefficient accepted')
        bad=copy.deepcopy(data);bad['blocks'][0]['LDL_diagonal'][0]=['-1','0']
        try:verify_factors(bad)
        except ValueError:rejected.append('negative_LDL_pivot')
        else:raise ValueError('Negative LDL pivot accepted')
        bad=copy.deepcopy(data);bad['beta']=['1','0']
        try:verify_identity(bad,blocks)
        except ValueError:rejected.append('wrong_boundary_parameter')
        else:raise ValueError('Wrong boundary coefficient accepted')
    report.update({'status':'EXACT_FULL_MATRIX_IDENTITY_AND_POSITIVE_FACTORS_PASS',
                   'certificate_sha256':hashlib.sha256(args.certificate.read_bytes()).hexdigest(),
                   'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   'field_source_sha256':hashlib.sha256(Path(__file__).with_name('quadratic_field.py').read_bytes()).hexdigest(),
                   'negative_controls':rejected,
                   'scope':'Exact universal boundary inequality certificate; convexity and determinant extension are written proofs.'})
    Path(__file__).with_name('exact-certificate-replay.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)

if __name__=='__main__':main()
