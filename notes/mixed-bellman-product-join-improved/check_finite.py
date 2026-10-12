#!/usr/bin/env python3
"""Independent exact verification of all mixed-potential finite rectangles.

Inputs are rational candidate tangent points, not floating inequalities.
Standard library only. Python -O keeps all checks active.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse,json,time

ALPHA=F(271,6250);BETA=F(5453,1000000);TARGET=ALPHA+BETA
NLOG=20
DYADIC_DEN=2**96


def require(condition,message):
    if not condition:raise ArithmeticError(message)


def rat(x):return {'numerator':str(x.numerator),'denominator':str(x.denominator)}


def atanh_log_bounds(y):
    require(1<=y<=2,'atanh range violation')
    z=(y-1)/(y+1);z2=z*z;power=z;lo=F(0)
    for i in range(NLOG):
        lo+=2*power/(2*i+1);power*=z2
    hi=lo+2*power/((2*NLOG+1)*(1-z2))
    return lo,hi


LOG2=atanh_log_bounds(F(2))


def outward_round(interval):
    lo,hi=interval
    lnum=(lo.numerator*DYADIC_DEN)//lo.denominator
    hnum=-((-hi.numerator*DYADIC_DEN)//hi.denominator)
    return F(lnum,DYADIC_DEN),F(hnum,DYADIC_DEN)


def log_bounds(x):
    require(x>0,'nonpositive log input')
    y=F(x);k=0
    while y>=2:y/=2;k+=1
    while y<1:y*=2;k-=1
    lo,hi=atanh_log_bounds(y)
    if k>=0:return outward_round((lo+k*LOG2[0],hi+k*LOG2[1]))
    return outward_round((lo+k*LOG2[1],hi+k*LOG2[0]))


def add_intervals(x,y):return x[0]+y[0],x[1]+y[1]


def scale_interval(k,x):
    return (k*x[0],k*x[1]) if k>=0 else (k*x[1],k*x[0])


def tangent(r,s,h,j,logc):
    n=r+s;x=F(r*j+s*h,n);v=r*h+s*j
    a4=F(1,(r+1)**3)-F(r,n*(n+1)**3)
    b4=F(1,(s+1)**3)-F(s,n*(n+1)**3)
    require(a4>0 and b4>0,'nonpositive quartic coefficient')
    g2=h*h/F(r+1)+j*j/F(s+1)-v*v/F(n*n*(n+1))
    g4=a4*h**4+b4*j**4
    gh=F(s,n)/x-ALPHA*(2*h/F(r+1)-F(2*r,n*n*(n+1))*v)-4*BETA*a4*h**3
    gj=F(r,n)/x-ALPHA*(2*j/F(s+1)-F(2*s,n*n*(n+1))*v)-4*BETA*b4*j**3
    support=gh*((r+1 if gh>=0 else 2)-h)+gj*((s+1 if gj>=0 else 2)-j)
    logx=log_bounds(x)
    correction=-ALPHA*g2-BETA*g4+TARGET+support
    return (logc[0]+logx[0]+correction,logc[1]+logx[1]+correction),[gh,gj],support


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('certificate',nargs='?',type=Path,
                        default=Path(__file__).resolve().with_name('mixed_finite_points.json'),
                        help='Rational point certificate (default: supplied sibling file).')
    parser.add_argument('--report',type=Path)
    parser.add_argument('--quiet',action='store_true')
    args=parser.parse_args()
    data=json.loads(args.certificate.read_text())
    require(data.get('schema')==1,'unsupported schema')
    require(data.get('alpha')==[271,6250] and data.get('beta')==[5453,1000000]
            and data.get('T')==[48813,1000000],'constant mismatch')
    require(data.get('dimension_max')==199,'dimension maximum mismatch')
    den=data.get('denominator')
    require(type(den) is int and den>0,'denominator malformed')
    rows=data.get('points');require(type(rows) is list and len(rows)==19900,'point coverage size failed')
    start=time.monotonic()
    logs={i:log_bounds(F(i)) for i in range(1,399)}
    facts={0:(F(0),F(0))}
    for i in range(1,399):facts[i]=add_intervals(facts[i-1],logs[i])
    index=0;worst=None;positive_support_count=0
    for r in range(1,200):
        for s in range(r,200):
            row=rows[index]
            require(type(row) is list and len(row)==4 and all(type(v) is int for v in row),
                    f'row malformed at {index}')
            require(row[:2]==[r,s],f'coverage failed at {index}')
            h=F(row[2],den);j=F(row[3],den)
            require(2<=h<=r+1 and 2<=j<=s+1,f'point outside box {r},{s}')
            n=r+s
            logc=(F(0),F(0))
            for coefficient,interval in [(r,logs[r]),(s,logs[s]),(-n,logs[n]),
                                         (1,facts[n]),(-1,facts[r]),(-1,facts[s])]:
                logc=add_intervals(logc,scale_interval(coefficient,interval))
            value,grads,support=tangent(r,s,h,j,logc)
            require(value[1]<0,f'tangent certificate failed {r},{s}')
            if worst is None or value[1]>worst['upper']:
                worst={'r':r,'s':s,'upper':value[1],'lower':value[0],
                       'h':h,'j':j,'grad_h':grads[0],'grad_j':grads[1],'support':support}
            if support>0:positive_support_count+=1
            index+=1
        if not args.quiet and r%20==0:
            print(json.dumps({'completed_r':r,'rectangles':index,'elapsed_seconds':round(time.monotonic()-start,1)}),flush=True)
    require(index==19900,'coverage count mismatch')
    require(worst['upper']<0,'strict finite sign failed')
    report={'claim':'All finite mixed-potential rectangles 1 <= r <= s <= 199 have a strictly negative rational tangent upper bound',
            'rectangles':index,'log_series_terms':NLOG,'log_dyadic_denominator':DYADIC_DEN,'point_denominator':den,
            'alpha':rat(ALPHA),'beta':rat(BETA),'T':rat(TARGET),
            'positive_support_count':positive_support_count,'uniform_upper_margin':rat(worst['upper']),
            'worst':{key:(rat(value) if isinstance(value,F) else value) for key,value in worst.items()}}
    if args.report:args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)

if __name__=='__main__':main()
