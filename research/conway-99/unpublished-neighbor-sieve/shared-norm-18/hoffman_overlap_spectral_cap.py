"""The two native inequalities used in the rank-42 Hoffman-span obstruction."""
from original_site_populations import calc
from rank36_three_types import UNIT
import sympy as sm

def main():
 o,w,c,g,u,ub,red=calc(42,[],export=True)
 absrows=sm.Matrix([red(u[k]) for k in sorted(UNIT-{(0,18),(1,21),(1,25)})])
 nul=sm.Matrix.hstack(*absrows.nullspace())
 rows={str(k):v for k,v in ub.items()}
 rows.update({'S':w((1,23))-99*o-7*w((0,14)), 'r14':w((1,21))-14*o,
              '446':w((4,46)), 'X14':w((0,14))})
 data=[
 (2*(3*w((2,22))-w((4,46)))-w((0,14))-131*o,2033500,
 [("nonneg('W', (-4, 44, 2))",15632760),("nonneg('W', (-3, 35, 1))",40139550),
  ("nonneg('W', (-2, 34, -1))",15632760),("nonneg('W', (-1, 23, -1))",36333660),
  ("nonneg('W', (-1, 29, 1))",8811),('S',3664190),('r14',116534470)]),
 (g((0,18))-181*o,7452704460,
 [('compat(-4, 46, -1)',6125625198),('compat(-3, 39, 1)',199036629),
  ('mark((0, 42), 3)',4199085),('mark((3, 39), 1)',31777318),
  ("nonneg('W', (-4, 44, 0))",25600164),("nonneg('W', (-4, 44, 1))",25600164),
  ("nonneg('W', (-4, 46, 1))",1048651494),("nonneg('W', (-3, 35, 1))",21782851398),
  ("nonneg('W', (-1, 23, -1))",179819234595),('446',2268448363),('X14',44096836401)])]
 for target,den,coef in data:
  y=den*target
  for name,h in coef:
   assert int(h)==h and h>0
   y-=h*rows[name]
  assert not any(sm.Matrix([red(y)])*nul)
 print('Rank 42, unit support inside {018,121,125}: N18>=181 unconditionally;')
 print('at r>=14, 2(3M-W446)-W014>=131. The graph span gives <=114.')
if __name__=='__main__':main()
