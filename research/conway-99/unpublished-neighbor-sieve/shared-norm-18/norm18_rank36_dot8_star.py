"""Two rank-36 lower bounds for the actual oriented N18. Exact native elimination."""
from original_site_populations import calc

def check():
    one,w,c,glob,u,ub,red=calc(36,[],export=True)
    p=2402
    N=lambda k:p*u[k]
    S=w((1,23))-99*one-7*w((0,14))
    # Upper G121=5544+28P<=29372, P<=851.
    z=12*N((0,18))+N((0,26))+14*N((0,16))+N((3,37))+2*N((1,25))+2*N((2,30))
    z-=744492*one+p*w((0,20))+4*p*w((0,22))+5*p*w((2,28))+2*p*w((3,35))
    z-=p*S+14*glob((0,14))+33614*c((0,14))+9*(29372*one-glob((1,21)))
    assert not any(red(z))
    assert 12*62041==744492
    # Second identity is positive on all graphs under the stated absences.
    B=20726484; L=3846719880
    z=B*N((0,18))-(B*55666+L)*one
    for k,v in {(0,26):1142323944,(0,16):25337420136,(1,27):415670904,
                (3,37):6509093328,(2,28):3134465880,(0,24):917554392,
                (2,30):2250779688}.items():z+=v*u[k]
    for k,v in {(2,26):27388074792,(3,33):4190577240,
                (3,35):4864885896,(4,44):7115665584}.items():z-=v*w(k)
    z-=7405087368*(w((2,22))-c((2,22)))+1419221700*S
    z-=523971*glob((0,14))+29027132001*c((0,14))
    for k,v in [('compat(-1, 23, -1)',78546819582),
                ('mark((2, 36), -2)',176311604),
                ("nonneg('C', (-4, 46, -1))",17454848796)]:z-=v*ub[k]
    assert not any(red(z))
    assert 185*B<L<186*B
    print('Rank 36: on the two stated faces oriented N18 >= 62042 or 55852, respectively.')
if __name__=='__main__':check()
