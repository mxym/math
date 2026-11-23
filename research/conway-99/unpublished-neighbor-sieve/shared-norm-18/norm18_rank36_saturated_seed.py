"""Native rank-36 chart, same oriented N18 versus the no-16/no-unit-127 cap."""
from original_site_populations import calc

def check():
    o,w,c,g,u,ub,red=calc(36,[],export=True)
    B=32401736;T=1161489967988
    z=2402*B*u[0,18]-T*o
    for k,v in {16:26917177104,337:12422495460,228:12911091084,24:4303053292,230:4965135768}.items():
        z+=v*u[divmod(k,100)]
    z-=32317800276*u[1,21]+71867330776*u[2,26]+996503328*u[1,27]
    z-=13410308352*w((4,44))
    # At rank 36 no N14 fields exist, so its negative is a valid zero row.
    z+=13038669*g((0,14))
    for k,v in [('compat(-2, 22, 1)',62597210508),('compat(-1, 23, -1)',147550567626),
        ('mark((2, 36), -2)',331202172),("nonneg('W', (-3, 33, 0))",5955845472),
        ("nonneg('W', (-3, 35, 1))",28267999452),("nonneg('W', (-2, 32, 0))",1953748368),
        ("nonneg('C', (-4, 46, -1))",32789015028),("nonneg('C', (0, 14, -1))",294998754897)]:z-=v*ub[k]
    assert not any(red(z))
    assert 2*((T+2*B-1)//(2*B))==35848>35298
    print('Rank-36: same oriented N18 >=35848; if U127=0, <=35298.')
if __name__=='__main__':check()
