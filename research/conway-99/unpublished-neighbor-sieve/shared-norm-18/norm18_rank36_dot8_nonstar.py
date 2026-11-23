"""Three same-oriented-N18 comparisons against the nonstar packing theorem."""
from original_site_populations import calc

def check():
    one,w,c,g,u,ub,red=calc(36,[],export=True);p=2402
    N=lambda k:p*u[k]
    S=w((1,23))-99*one-7*w((0,14))
    R={k:w(divmod(k,100)) for k in [20,22,222,226,228,333,335,444]}
    R.update(S=S,M=w((2,22))-c((2,22)),N=g((0,14)),Y=c((0,14)),
             nofan=(-1)*g((0,14)),lift=ub['lift'],compat=ub['compat(-1, 23, -1)'],
             edge=ub['mark((2, 36), -2)'],slot=ub["nonneg('C', (-4, 46, -1))"],
             cap=29372*one-g((1,21)),
             sq=5544*one+3*N((1,27))-2*N((2,26))-3*N((0,16)))
    data=[
      (36,110260,
       {26:9608,16:26422,127:69658,125:14412,230:9608},
       {22:19216,222:24020,228:38432,335:9608,'S':14412,'N':60,'Y':144060,'sq':9,'cap':52}),
      (1671996,3535285356,{26:115396884,16:2215499112,337:600144504,228:588715788},
       {20:842568756,22:11529600,226:1938990480,333:692583072,335:473218020,444:461688420,
        'M':484444968,'S':34761744,'Y':1777088145,'lift':11529600,'compat':5138576982,
        'edge':11534404,'slot':1141905996,'nofan':16485}),
      (27328116,114947163360,{26:1973262216,16:30806860608,337:8240262768,230:5055412536},
       {22:5505326352,226:30123414744,228:4846352064,333:1732408872,335:5817086736,444:5367172920,
        'M':8789215848,'S':269576460,'Y':28872584433,'lift':449913816,'compat':93228468102,
        'edge':209267044,'slot':20717437356,'nofan':1702197})]
    lows=[]
    for b,L,hot,pos in data:
        z=b*N((0,18))-(48004*b+L)*one
        for k,v in hot.items():
            assert v>0
            z+=v*u[divmod(k,100)]
        for k,v in pos.items():
            assert v>0
            z-=v*R[k]
        assert not any(red(z))
        lows.append(48004+2*((L+2*b-1)//(2*b)))
    print('Rank-36 nonstar lower comparisons:',lows,'versus 48004.')
if __name__=='__main__':check()
