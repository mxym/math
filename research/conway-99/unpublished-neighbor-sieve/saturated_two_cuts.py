#!/usr/bin/env python3
"""Optional local contraction tally; run beside connected_saturated_five_rank.py."""
from connected_saturated_five_rank import ks,cyc
def main():
 counts=[]
 for n in (2,4,6,8,10,12):
  tot=bad=0
  for K in ks(n):
   edges,_=cyc(K);masks=[(1<<i)|(1<<j) for i,j in edges]
   tot+=1;bad+=any(sum((v&a).bit_count()==1 for a in masks)==2 for v in range(2,1<<n,2) if v.bit_count()%2==0)
  counts.append((n,tot,bad));print(n,tot,bad)
 assert counts==[(2,1,0),(4,2,1),(6,5,3),(8,19,13),(10,81,64),(12,580,465)]
if __name__=='__main__':main()
