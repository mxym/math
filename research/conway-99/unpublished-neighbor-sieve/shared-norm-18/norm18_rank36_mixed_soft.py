"""Two rank-36 same-N18 lower rows for the soft occupied-seed inequality."""
from original_site_populations import calc

def check():
    o,w,c,g,u,ub,red=calc(36,[],export=True);p=2402
    G=lambda k:p*u[divmod(k,100)]
    S=w((1,23))-99*o-7*w((0,14))
    x=12*G(18)+14*G(16)+G(26)+9*G(121)+2*G(125)+2*G(230)+G(337)-1008840*o
    x-=G(20)+4*p*w((0,22))+5*p*w((2,28))+2*p*w((3,35))+p*S
    x-=14*g((0,14))+33614*c((0,14))
    assert not any(red(x))
    y=10*G(18)+18*G(16)+G(26)+9*G(121)+2*G(226)+G(337)+2*G(125)-797464*o
    y-=5*G(20)+2*p*w((0,22))+2*p*w((2,22))+p*w((2,28))+2*p*w((3,33))+2*p*w((3,35))+p*S
    y-=12*g((0,14))+28812*c((0,14))
    assert not any(red(y))
    assert (1008840-14*5196)//12==78008
    assert (797464-18*5196+9)//10==70394
    assert 2*((55440*90+49*5196)//162)==64742
    print('Soft-seed upper 64742; rank-36 lower 78008 or 70394, same oriented N18.')
if __name__=='__main__':check()
