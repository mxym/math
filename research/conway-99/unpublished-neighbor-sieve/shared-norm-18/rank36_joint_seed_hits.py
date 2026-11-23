"""Twenty-nine certified necessary rank-36 support clauses; no LP, no search."""
import json
from fractions import Fraction
from pathlib import Path
from original_site_populations import calc

def check():
    o,w,c,g,u,ub,red=calc(36,[],export=True)
    G=lambda k:2402*u[divmod(k,100)]
    N=G(18);F=G(16)
    # Each entry gives (nonnegative row, exact prior absence requirements).
    guide={str(key):(v,set()) for key,v in ub.items()}
    guide.update({k:(z,set(deps)) for k,z,deps in [
        ('root',-1*g((0,14)),()),('22',w((0,22)),()),('444',w((4,44)),()),
        ('Y1',c((0,14)),()),('SCm',g((2,22)),()),('SCM0',c((2,22)),()),
        ("SC('w', (2, 34))",w((2,34)),()),
        ('21cap',29372*o-G(121),()),('sq',5544*o+3*G(127)-2*G(226)-3*F,()),
        ('no20F',5196*o-F,(20,)),('capboth',12320*o-N,(16,20)),
        ('star',54476*o-N,(16,)),('nest',29842*o-N,(16,127)),
        ('mixed9',4656960*o-29*F-81*N,(20,26,121))]})
    # In the final mixed row, unit 026=121=0 is equivalent to RAW G026=0.
    for (a,t),v in u.items():guide['abs'+str(100*a+t)]=(-1*v,{100*a+t})
    cert=json.loads(Path(__file__).with_name('rank36-joint-seed-hits.json').read_text())
    assert len(cert)==29 and len({tuple(h) for h,_,_ in cert})==29
    row0=red(o)
    pool={name:red(guide[name][0]) for _,_,terms in cert for name,_ in terms}
    for h,d,terms in cert:
        h=set(h);assert d>0 and len(terms)==len(dict(terms))
        z=[d*v for v in row0];needed=set()
        for name,weight in terms:
            assert isinstance(weight,int) and weight>0
            needed.update(guide[name][1]);z=[a+weight*b for a,b in zip(z,pool[name])]
        # U127=0 implies N16=0 by the proven rank-free positive-edge lift.
        # Some charts use that implication to replace a premise 016 by 127.
        assert h==needed or (127 in h and 16 in needed and h==(needed-{16})|{127})
        assert not any(z),(sorted(h),z)
    print('29 exact rank-36 support clauses; 14 three-type must-hit sets.')
    assert sum(len(h)==3 for h,_,_ in cert)==14
    return [set(h) for h,_,_ in cert]

if __name__=='__main__':
    hs=check()
    from rank36_five_candidates import E,h39,h49,new,bulk,run
    sup=run(h39+h49+list(map(set,new+bulk))+hs)
    assert list(map(len,sup))==[0,0,0,0,0,22,119,253,272,163,56,11,1]
    print('Necessary support counts by size 0..12:',list(map(len,sup)))
    print('Size five:');print('\n'.join(' '.join(f'{k:03}'for k in s)for s in sup[5]))
    assert [s for s in sup[5]if 18 not in s]==[(20,125,127,226,337)]
