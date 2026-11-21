from fractions import Fraction as F

def check(flag, msg):
    if not flag:
        raise SystemExit(msg)

v0=tuple(map(F,('.139','.139','.139','.139','.0135','.0525','.1000','.2780')))
v1=tuple(map(F,('.139','.1347','.1381','.1385','.0220','.0591','.1015','.2671')))
check(sum(v0)==sum(v1)==1,'source sums')
q1=tuple(map(F,('.4255','.4265')))
qc=tuple(map(F,('.4287','.4290')))
for j in range(4):
    marks=[i for i in range(8) if i!=j]
    lo,hi=q1 if j==0 else qc
    centered=0
    for mask in range(128):
        b=[marks[i] for i in range(7) if (mask>>i)&1]
        u0=sum(v0[i] for i in b)
        u1=sum(v1[i] for i in b)
        check(u1<lo or u1>hi,f'target endpoint seam: {j} {b}')
        check(min(abs(u1-lo),abs(u1-hi))>=F('.0006'),f'endpoint box margin: {j} {b}')
        if u1<lo:
            check(u0<=F('.4305'),f'interpolation below: {j} {b}')
            centered-=(-1)**len(b)
        else:
            check(u0>=F('.4305'),f'interpolation above: {j} {b}')
    check(centered==(-1 if j==0 else 2),f'sign: {j}, {centered}')

theta=F(7,32)
boxes=(
    ((0,1,1,2,0,2,1,2),'.4990','.5301'),
    ((0,1,1,1,2,2,2,2),'.5294','.5556'),
    ((0,1,1,2,2,0,1,2),'.5360','.5691'),
    ((0,1,1,2,1,0,1,2),'.5630','.5826'),
)
front=F('.4995')
for lab,low,high in boxes:
    low,high=F(low),F(high)
    check(low<front<high,'gap in contiguous distribution')
    front=high
    for tau in (F(0),F('.0001')):
        a,b,c=(sum(v0[i]+tau*(v1[i]-v0[i]) for i in range(8) if lab[i]==j)
               for j in range(3))
        for d in (low,high):
            rail=(a,F(2,3)-a-b,c-b,d-c,a+b-d,1+d-2*a-3*b,
                  2-2*theta+(2+theta)*d-(7-4*theta)*a-(4-theta)*b,
                  2+2*d-7*a-4*b-theta)
            check(min(rail)>F('.00035'),f'Jain: {lab}, {tau}, {d}, {rail}')
check(2*F('.430500001')*F('.396500001')/F('.569499999')<F('.600'),'high contribution')
check(6*F('.121')-F('.600')>F('.125'),'matched net margin')
print('all rational checks pass')
