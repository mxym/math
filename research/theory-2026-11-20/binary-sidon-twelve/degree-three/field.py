from itertools import combinations
def check(v,why):
    if not v:raise ValueError(why)
def mul(x,y):
    z=0
    while y:
        if y&1:z^=x
        y>>=1;x<<=1
        if x&64:x^=67
    return z
gm=[[mul(x,y)for y in range(64)]for x in range(64)]
iv=[0]+[gm[x].index(1)for x in range(1,64)]
p3=[gm[gm[x][x]][x]for x in range(64)]
def testconics():
    # Norm of a+bY for Y^2+Y+32=0 is a^2+ab+32b^2
    from collections import Counter
    C=[[x+64*y for x in range(64)for y in range(64)if gm[x][x]^gm[x][y]^gm[32][gm[y][y]]==1],[x+64*iv[x]for x in range(1,64)]]
    for j,A in enumerate(C):
        check(len(A)==65-2*j,"model conic size")
        control=A if j else [0]+A
        check(len({x^y for x,y in combinations(control,2)})==len(control)*(len(control)-1)//2,"conic Sidon")
        c=Counter(x^y^z for x,y,z in combinations(A,3))
        vals=Counter(c[t]for t in range(4096)if t not in A)
        check(vals==([{0:1,9:910,10:780,11:780,12:1170,13:390},{8:882,9:756,10:882,11:1134,12:378,21:1}][j]),"exact triple distribution")
        if not j:check(c[0]==0,"the exceptional point is the nucleus")
        print("conic",j,"triples",sorted(vals.items()),flush=True)
