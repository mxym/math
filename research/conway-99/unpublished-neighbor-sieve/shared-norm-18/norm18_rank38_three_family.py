"""Rank-38 three-family lower, from the native exact site-pair-of-cusps chart."""
from original_site_populations import calc

HOT={(0,18):1085141120,(0,26):45559360,(3,37):107685760}
RAW={(0,20):120111040,(0,24):28992320,(2,22):185290096,
     (2,26):99402240,(3,33):95260480,(3,35):53842880}
C0=4715981872

def check():
    one,w,c,glob,u,ub,red=calc(38,[],export=True)
    assert all(v>0 for tab in (HOT,RAW) for v in tab.values())
    S=w((1,23))-99*one-7*w((0,14))
    E=w((3,39))-231*one-22*w((2,22))-S
    z=-C0*one
    for k,v in HOT.items():z+=v*u[k]
    for k,v in RAW.items():z-=v*w(k)
    z-=74551680*u[1,25]+1248*glob((2,22))
    z-=390481*glob((0,14))+134256031*c((0,14))
    z-=674240*ub['n16']+16567040*ub['lift']+8801240*E
    for k,v in [('compat(-4, 46, 0)',6378372),
                ("nonneg('W', (-4, 46, 0))",6018012),
                ("nonneg('C', (-4, 46, 1))",7747740)]:
        z-=v*ub[k]
    assert not any(red(z))
    num=344*C0; den=HOT[0,18]
    print('Rank 38 must hit N18, U026 or U337; absent both other families, N18 >=',
          2*((num+2*den-1)//(2*den)))
if __name__=='__main__':check()
