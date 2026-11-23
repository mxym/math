"""Rank-free graph-population form of the coclique Sidon cut."""
from flint import fmpq_mat
from higher_moments import rows

def main():
    r=rows()
    keys=sorted(set().union(*r))
    t={(0,0):7117,(0,14):168,(0,22):48,(0,24):16,(1,23):-4,(2,22):-288,
       (3,33):96,(3,35):56,(4,44):62,(4,46):4,(4,48):3,
       (0,16):593,(0,18):-500,(0,20):-84,(1,21):112,(1,25):52,
       (2,26):304,(2,28):12,(2,30):-92,(3,37):-72}
    assert set(t)<=set(keys)
    m=[[z.get(k,0) for k in keys] for z in r]
    assert fmpq_mat(m).rref()[1]==fmpq_mat(m+[[t.get(k,0) for k in keys]]).rref()[1]
    # All coordinates of Y and S here have untouched raw=unit counts, or
    # unrestricted W counts at (1,23),(3,33),(3,35).
    y={(0,0):1000,(0,14):-8,(0,16):200,(0,18):88,(0,20):64,
       (0,22):24,(3,33):48,(0,24):8,(3,35):16}
    slack={(0,0):545,(0,14):154,(3,35):24,(4,44):62,(4,48):3}
    s={(1,23):1,(0,0):-99,(0,14):-7}
    k={a:y.get(a,0)+int(a==(0,14))+2088*int(a==(0,0))-144*int(a==(2,22))
        -2*s.get(a,0)+2*int(a==(4,46)) for a in keys}
    w={a:v for a in keys if (v:=2*k[a]+slack.get(a,0)-t.get(a,0))}
    assert w=={(0,16):-193,(0,18):676,(0,20):212,(1,21):-112,
               (1,25):-52,(2,26):-304,(2,28):-12,(2,30):92,(3,37):72}
    print("Rank-free four-family lower bound verified:",w)

if __name__=="__main__":main()
