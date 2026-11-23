"""Verify an exact row of the untouched parent harmonic system; no LP."""
from flint import fmpq_mat
from higher_moments import rows
from rank36_three_types import UNIT


def main():
    allowed = {(0,24),(0,26),(1,27)}
    orig = rows()
    keys = sorted(set().union(*orig) - (UNIT-allowed))
    rr = [[r.get(k,0) for k in keys] for r in orig]
    E={(0,0):7117,(0,14):168,(0,22):48,(0,24):16,(1,23):-4,(2,22):-288,
       (3,33):96,(3,35):56,(4,44):62,(4,46):4,(4,48):3}
    assert set(E)<=set(keys)
    prem=fmpq_mat(rr).rref()[1]
    assert fmpq_mat(rr+[[E.get(k,0) for k in keys]]).rref()[1]==prem
    # Det-49 scalar, per extension, on the face.
    Y={(0,0):1000,(0,14):-8,(0,22):24,(3,33):48,(0,24):8,(3,35):16}
    S={(1,23):1,(0,0):-99,(0,14):-7}
    K={k:Y.get(k,0)+int(k==(0,14))+2088*int(k==(0,0))
           -144*int(k==(2,22))-2*S.get(k,0)+2*int(k==(4,46)) for k in keys}
    extra={(0,0):545,(0,14):154,(3,35):24,(4,44):62,(4,48):3}
    assert all(2*K[k]+extra.get(k,0)==E.get(k,0) for k in keys)
    print("Full harmonic row span:",prem,"; nonnegative expression = -545")


if __name__=="__main__":
    main()
