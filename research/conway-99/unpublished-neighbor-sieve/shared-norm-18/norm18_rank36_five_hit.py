"""Rank36 5-type must-hit via the actual oriented norm-18 count."""
from rank36_four_hit_sets import engine, P

def check():
    assert P==2402
    R,C,D,o=engine()
    den=8429899495
    num=104248536974733
    terms=[
        (2556429271106,R['w',(3,33)]),
        (1612023573249,R['w',(3,35)]),
        (1281804597497,R['w',(4,44)]),
        (2590642804582,R['Y1']),
        (1450423520,R['Y3']),
        (3678795393,R['Ct',34]),
        (36159,R['G',15000]),
        (80688058247,C['no20/24']) ]
    other={(0,16):-58165845786840,(0,20):391390238960,
           (0,24):164211997390,(1,21):1292458678105,
           (1,27):926441792,(2,26):5128202734392,
           (2,28):-2567141254326,(3,37):-1283078454961}
    assert all(c>0 for c,r in terms)
    assert {k for k,v in other.items() if v<0}=={(0,16),(2,28),(3,37)}
    assert all(den*P*x-num*y==
               sum(c*r[i] for c,r in terms)+sum(c*D[k][i] for k,c in other.items())
               for i,(x,y) in enumerate(zip(D[0,18],o)))
    assert 12366*den<num<12368*den and 12320*den<num
    return True
if __name__=='__main__':
    assert check()
    print("Rank36 must hit 016, 020, 024, 228 or 337: oriented N18 >= 12368 but <= 12320 otherwise.")
