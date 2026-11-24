"""A rank-38 five-way hit. Run alongside original_site_populations.py."""
from original_site_populations import calc

def check():
    o,w,c,g,u,ub,red=calc(38,[],export=True)
    M=c((2,22));Y1=c((0,14));Y2=c((0,28))+2*c((3,39))
    def tangent(h):
        return 9*Y2+18*Y1-(369+10*h)*M+(5*h*h-4158)*o
    def fano(h):
        return 2*g((0,20))-42*h*g((0,14))+4158*h*(h+1)*o
    terms=[
        (181842466307040,ub["compat(-2, 36, -1)"]),
        (11747825033427360,u[1,21]),(75660469167332160,u[2,26]),
        (3912774510366720,u[1,25]),(23482391284800,ub["mark((3, 39), 1)"]),
        (893311332480,ub["mark((3, 53), 1)"]),
        (10140870246312960,ub["nonneg('W', (-4, 44, 1))"]),
        (27610835440705920,ub["nonneg('W', (-3, 33, 0))"]),
        (37713923468076240,ub["nonneg('W', (-3, 35, 1))"]),
        (14884734419729760,w((4,44))),(56062503914344200,Y1),
        (31944441705281,tangent(100)),(759721761239,tangent(128)),
        (6162424026660,fano(3))]
    absent={(0,16):57854421692723520,(1,27):1498350197232000,
            (3,37):17991153219653280,(2,28):24152381777508480,
            (0,18):122045124955294080,(2,30):7621788655926720}
    s=16924142964305920*o
    for x,v in terms:
        assert isinstance(x,int) and x>0
        s+=x*v
    for k,x in absent.items():s-=x*u[k]
    assert not any(red(s))
    assert not any(red(g((0,20))-344*w((0,20))))
    print("Rank 38: weighted sum of the six unit masses equals",16924142964305920,"plus nonnegative terms.")
    print("U016 <= U127 gives a five-way hit: 018, 127, 228, 230, or 337.")
if __name__=='__main__':check()
