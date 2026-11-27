#!/usr/bin/env python3
"""Field-free exhaustive slot-gap and degree checks on every orbit through n=19."""
import argparse


def check(n):
    assert n%2 and n>=5
    q=1<<n; N=q-1; D=q//4+4; seen={0}; cycles=0; shorter=0; peak=0
    for e in range(1,N):
        if e in seen: continue
        orb=[]; w=e
        while w not in seen:
            orb.append(w);seen.add(w);w=2*w%N
        assert w==e and n%len(orb)==0
        # 1 <= i <= N: positive representative of w+5, i=1 removed by the gauge.
        labels=[((w+4)%N)+1 for w in orb]; slots=[i<=D and i!=1 for i in labels]
        if not any(slots): continue
        # Repetitions here deliberately cover proper-subfield/short orbits.
        slots*=n//len(orb); labels*=n//len(orb)
        assert any(not slots[k] and not slots[(k+1)%n] for k in range(n))
        # Reverse the doubled orbit (t increases when the input weight is halved).
        slots.reverse(); labels.reverse()
        start=next(k for k in range(n) if slots[k] and not slots[k-1] and not slots[k-2]); j=labels[start]
        occupied=[t for t in range(n) if slots[(start+t)%n]]; J=max(occupied); M=1<<J
        assert J<=n-3 and j+5*(M-1)<=7*q//8-1<N
        for t in occupied:
            i=labels[(start+t)%n]; assert (i*(1<<t)-j-5*((1<<t)-1))%N==0
        cycles+=1; shorter+=len(orb)<n; peak=max(peak,J)
    assert len(seen)==N
    print(f'n={n:2} D={D:6} occupied_orbits={cycles:6} short={shorter:4} max_J={peak:2} PASS',flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('n',nargs='*',type=int)
    for k in p.parse_args().n or range(5,20,2):check(k)
