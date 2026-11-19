"""Supplement to the full finite proof in verify_profiles.py; standard library."""
from verify_profiles import profiles,numerator
from itertools import product
def need(test):
 if not test:raise ArithmeticError('entrywise identity failed')
if __name__=='__main__':
 n=0
 for p in ('2143','2413','2431','3412','4231'):
  for x,y in product(*profiles(p)):
   if p=='2143':degree,a=0,-2*('1' not in x and '1' not in y)
   elif p=='2413':degree,a=0,3
   elif p=='2431':degree,a=1,1
   elif p=='3412':degree,a=1,2
   else:degree,a=2,sum(h not in x and t not in y for h,t in [('231','312'),('312','231')])
   need(numerator(p,x,y)==(((degree,a),(degree+1,-a)) if a else ()))
   n+=1
 print(n,'labelled two-endpoint cancellation identities verified; PASS.')
