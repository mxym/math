"""Limited exact checks of single/double deletion accounting. No simulation or proof by sampling."""
from itertools import combinations
from random import Random


def must(ok, message):
    if not ok:
        raise RuntimeError(message)


def det(a,b,c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])


def inside(p, triangle):
    a,b,c=triangle
    vals=(det(a,b,p),det(b,c,p),det(c,a,p))
    return min(vals)>0 or max(vals)<0


def star(x, pts):
    return {frozenset((p,q)) for p,q in combinations(pts,2)
            if not any(inside(w,(x,p,q)) for w in pts if w!=p and w!=q)}


def parts(x, pts, y):
    old=star(x, pts)
    births={p for p in pts if not any(inside(q,(x,y,p)) for q in pts if q!=p)}
    deaths={pair for pair in old if inside(y,(x,*pair))}
    return births, deaths


def generic_set(seed):
    gen=Random(seed)
    pts=[(0,0)]
    while len(pts)<10:
        y=(gen.randrange(-50,51),gen.randrange(-50,51))
        if y not in pts and all(det(a,b,y)!=0 for a,b in combinations(pts,2)):
            pts.append(y)
    return pts


def main():
    checks=0
    cloud=[(0,0), *((100*i,100*i*i) for i in range(1,10)), (2,11)]
    must(all(det(a,b,c) for a,b,c in combinations(cloud,3)),"collinear grid")
    births, deaths=parts(cloud[0], cloud[1:-1], cloud[-1])
    must(len(deaths)==20 and len(births)<len(deaths),"both signs matter")
    for pts in [cloud,*[generic_set(i) for i in range(3)]]:
        for x in pts:
            others=[u for u in pts if u!=x]
            full=star(x,others)
            for y,z in combinations(others,2):
                T=[u for u in others if u!=y and u!=z]
                for i,j in [(y,z),(z,y)]:
                    added, killed=parts(x,[*T,j],i)
                    delta=len(full)-len(star(x,[*T,j]))
                    must(delta==len(added)-len(killed),"signed deletion")
                    base_added,base_killed=parts(x,T,i)
                    b_j,_=parts(x,T,j)
                    exceptional=sum(inside(i,(x,j,w)) for w in b_j)
                    must(abs(delta)<=len(base_added)+len(base_killed)+1+exceptional,"pair ledger")
                    checks+=1
    print(f"PASS {checks} oriented two-mark checks; explicit insertion: {len(births)} births, {len(deaths)} deaths.")
    print("Finite integer-coordinate bookkeeping only; the iid moment theorem is analytic.")


if __name__=="__main__":
    main()
