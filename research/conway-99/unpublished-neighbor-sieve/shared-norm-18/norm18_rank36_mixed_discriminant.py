"""Two original rank-36 same-shell lower comparisons, native exact arithmetic."""
from original_site_populations import calc

def check():
    o,w,c,g,u,ub,red=calc(36,[],export=True)
    F=2402*u[0,16];N=2402*u[0,18]
    z=42*(151*N+75*F-9042952*o)
    for k,v in {20:11752986,26:1059282,226:7465416,24:1815912,230:3631824}.items():z+=v*u[divmod(k,100)]
    z-=151326*u[1,21]+756630*u[3,37]+4791990*w((2,28))+1916796*w((3,35))
    z-=3294172*c((0,14))+8617175*w((0,14))
    for k,v in [('compat(-4, 46, 2)',223054524),('compat(-1, 23, -1)',23928366),
        ('mark((2, 36), -2)',9604),("nonneg('W', (-1, 23, -1))",44042229),
        ("nonneg('C', (-4, 46, -1))",29375181),("nonneg('C', (-4, 46, 1))",1111473)]:z-=v*ub[k]
    assert not any(red(z))
    # b is number of unordered dot-10 pairs. A priori m<=21 already;
    # the two elementary quadratic estimates work for every m>=0.
    for k,cut,soft,hard in [(8,70,26,33),(9,84,30,39)]:
        assert max(k*m-max((m-1)**2//4,(m*(m-8)+1)//2) for m in range(22))==cut
        assert [max(k*m-m*(m-1)//2 for m in range(l+1)) for l in (4,6)]==[soft,hard]
    assert 2*((29*55440*70+47*55440*84)//(2*(29*72+47*81)))==56220
    assert 2*((9042952-75*5196+301)//302)==57308
    print("Rank-36 mixed: same oriented N18 >=57308 versus <=56220.")
if __name__=='__main__':check()
