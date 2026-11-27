"""Exact rational integration of the proposed piecewise affine density."""
from fractions import Fraction as F


def raw_tent(u):
    return max(F(0), 1-abs(u))


def choices(length, scenario):
    m = int(length)
    r = length-m
    if scenario == 'convex':
        return ((r+1)/2,), (1-r)/2, 1, m
    if scenario == 'concave':
        w = (1-r)/2
        c = (r+1)/2
        return (c-w/2,c+w/2), w/4, -1, 2*m
    if m % 2:
        return ((r+1)/2,), (1-r)/2, 1, m
    if r:
        return (r/2,), r/2, 1, m+1
    raise ValueError('an even length is not a strict absolute-loss case')


def representation(length, scenario):
    mids, half, sign, copies = choices(length, scenario)
    amp = half/(4*length*length)
    bumps = [c+j for j in range(int(length)+1) for c in mids
             if 0 <= c+j-half and c+j+half <= length]
    assert len(bumps) == copies
    grid = sorted({F(0),length} | {c+k*half/2 for c in bumps for k in range(-2,3)})
    density = []
    for t in grid:
        q = F(0)
        for c in bumps:
            u = (t-c)/half
            q += sign*(2*raw_tent(2*u)-raw_tent(u))
        density.append(1/length+amp*q)
    vals = dict(zip(grid,density))
    assert min(density) > 0
    assert all(vals[length-x] == y for x,y in vals.items())
    return [(a,b,c,d) for a,b,c,d in zip(grid,grid[1:],density,density[1:])], half, amp, copies


def restrict(L, x, y):
    mid = (x+y)/2
    for a,b,c,d in L:
        if a < mid < b:
            m = (d-c)/(b-a)
            return (c+m*(x-a), c+m*(y-a))
    return F(0), F(0)


def exact_tv(L, h):
    right = [(a+h,b+h,c,d) for a,b,c,d in L]
    cuts = sorted({x for S in (L,right) for a,b,_,_ in S for x in (a,b)})
    area = F(0)
    for x,y in zip(cuts,cuts[1:]):
        a,b = restrict(L,x,y)
        c,d = restrict(right,x,y)
        u,v = a-c,b-d
        if u*v >= 0:
            area += (y-x)*(abs(u)+abs(v))/2
        else:
            area += (y-x)*(u*u+v*v)/(2*(abs(u)+abs(v)))
    return area/2


def moment(L, center, power, absolute=False):
    out = F(0)
    for a,b,c,d in L:
        beta = (d-c)/(b-a)
        alpha = c+beta*(center-a)
        x,y = a-center,b-center
        S = [(x,y)] if not x < 0 < y else [(x,F(0)),(F(0),y)]
        for l,h in S:
            v = alpha*(h**(power+1)-l**(power+1))/(power+1)
            v += beta*(h**(power+2)-l**(power+2))/(power+2)
            out += -v if absolute and h <= 0 else v
    return out


def main():
    lengths = tuple(map(F,('5/4','3/2','2','7/3','5/2','3','11/3','4','45/11','7')))
    hs = sorted({F(a,b) for b in (7,11,13,16,17) for a in range(b+1)})
    count, witnesses = 0, 0
    for L in lengths:
        for scenario in ('convex','concave','absolute'):
            if scenario == 'absolute' and L.denominator == 1 and L % 2 == 0:
                continue
            f, a, amp, copies = representation(L,scenario)
            assert moment(f,L/2,0) == 1 and moment(f,L/2,1) == 0
            for h in hs:
                tv = exact_tv(f,h)
                assert tv <= 1/L
                assert tv == 1/L if h==1 else tv < 1/L
                count += 1
            if scenario == 'convex':
                target = L*L/12-amp*copies*a**3/8
                assert moment(f,L/2,2) == target
                if L == 2:
                    assert target == F(1,3)-F(1,1024)
                witnesses += 1
            elif scenario == 'absolute':
                assert moment(f,L/2,1,True) == L/4-amp*a*a/6
                witnesses += 1
            else:
                # Negative bumps raise quadratic cost, a control for their sign.
                assert moment(f,L/2,2) == L*L/12+amp*copies*a**3/8
    f,_,_,_ = representation(F(3,2),'convex')
    alpha = F(2,5)
    assert alpha+(1-alpha)*exact_tv(f,F(1)) == F(4,5)
    assert alpha+(1-alpha)*exact_tv(f,F(11,12)) < F(4,5)
    # Over-amplification is not certified by the theorem and can break DP.
    excessive = [(a,b,1/F(2)+16*(c-1/F(2)),1/F(2)+16*(d-1/F(2)))
                 for a,b,c,d in representation(F(2),'convex')[0]]
    assert min(min(c,d) for _,_,c,d in excessive) > 0
    assert exact_tv(excessive,F(3,4)) == F(9,16) > F(1,2)
    print('exact rational: shifts', count, '; mass, symmetry, and', witnesses,
          'closed rational cost checks; mixed atom and excessive bump controls PASS')


if __name__ == '__main__':
    main()
