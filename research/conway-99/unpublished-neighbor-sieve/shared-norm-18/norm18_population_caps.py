"""Exact all-rank N18 caps in fixed extensions. Run beside higher_moments.py."""
from fractions import Fraction as Q
from higher_moments import rows

CERT=[{"rows":[[121,7148971339055],[125,1120712395698],[129,1436124542],[131,182712704664],[133,14601187358],[135,14530591527],[232,642440182727],[234,272233811843],[335,584356478223],[341,82906411098],[345,17383602327],[452,99770669719],[454,21920245438],["W14cap",56383725274443]],"cap":5805113314040460,"den":17122871911320},{"rows":[[26,4139072500],[121,104489211340],[127,1830136360],[131,2870978880],[234,2661267420],[341,1036189680],[345,536376940],[444,7557005845],[452,1167320565],["W14cap",577478218940],["C339",155920980],["T199",4621819]],"cap":75103554564422,"den":378203480076}]

def verify():
    original=rows();keys=sorted(set().union(*original))
    for fixed,c in enumerate(CERT):
        eq=original+([{(0,16):1},{(0,20):1}] if fixed else [])
        piv={}
        for r in eq:
            v=[Q(r.get(k,0)) for k in keys]
            for i,a in sorted(piv.items()):
                t=v[i];v=[x-t*y for x,y in zip(v,a)]
            if any(v):
                i=next(j for j,x in enumerate(v) if x);piv[i]=[x/v[i] for x in v]
        special={'W14cap':{(0,0):4,(0,14):-1},
                 'C339':{(3,39):1,(0,0):-132,(2,22):-22,(1,23):-1,(0,14):7}}
        if fixed:
            j=199;special['T199']={(0,0):88*j*j,(0,18):420-176*j,(0,28):70,(0,24):200}
        out={(0,0):c['cap'],(0,18):-c['den']}
        for key,w in c['rows']:
            assert w>0
            r={divmod(key,100):1} if isinstance(key,int) else special[key]
            for k,x in r.items():out[k]=out.get(k,0)-w*x
        assert set(out)<=set(keys)
        z=[Q(out.get(k,0)) for k in keys]
        for i,a in sorted(piv.items()):
            t=z[i];z=[x-t*y for x,y in zip(z,a)]
        assert not any(z)
        frac=Q(c['cap'],c['den'])
        print('W018 <=',frac, '; oriented H count <=',2*((4*frac.numerator)//frac.denominator))
if __name__=='__main__':verify()
