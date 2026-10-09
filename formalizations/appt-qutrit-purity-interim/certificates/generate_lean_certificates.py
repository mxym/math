"""Parent-authored deterministic Lean source generator. No proof placeholders.
All generated identities are to be checked by Lean's ring tactic/kernel.
"""
from pathlib import Path
from fractions import Fraction
import json,ast,re
root=Path(__file__).parent;dest=root/'lean'/'APPT';dest.mkdir(parents=True,exist_ok=True)
def balanced(xs):
 if not xs:return '(0 : ℝ)'
 if len(xs)==1:return xs[0]
 k=len(xs)//2;return '('+balanced(xs[:k])+' + '+balanced(xs[k:])+')'
def prod(xs):return '('+' * '.join(xs)+')' if xs else '(1 : ℝ)'
def rat(c):
 q=Fraction(c);return f'({q.numerator} : ℝ)' if q.denominator==1 else f'(({q.numerator} : ℝ) / {q.denominator})'
def base(name):
 if name.startswith('gprod'):return prod([f'(g {i})' for i in ast.literal_eval(name[5:])])
 if name in ['Adet','Bdet']:return f'(det{name[0]} (outer g))'
 if name.startswith('ratio'):
  m=re.fullmatch(r'ratio\*g(\d+)g(\d+)',name);assert m
  return prod(['(ratio (outer g))',f'(g {int(m[1])-1})',f'(g {int(m[2])-1})'])
 if (m:=re.fullmatch(r'([AB])minor(\d)(\d)\*g(\d+)',name)):
  c,i,j,k=m.groups();return f'(minor{c} (outer g) {i} {j} * g {int(k)-1})'
 m=re.fullmatch(r'([AB])quad(\([^)]*\))\*g(\d+)g(\d+)',name);assert m,name
 c=m[1];v=ast.literal_eval(m[2]);i,j=int(m[3])-1,int(m[4])-1
 return f'(quad{c} (outer g) ![{",".join(map(str,v))}] * g {i} * g {j})'
def expression(name):
 if name.startswith('plain:'):
  exps=list(map(int,name[6:].split(',')));return prod([f'({f"g {i}" if i<9 else ("t" if i==9 else "z")}) ^ {k}' for i,k in enumerate(exps) if k])
 if '*param' in name:
  b,p=name.rsplit('*param',1);return prod([base(b),*[['t','z','(t+z-18)'][i] for i in ast.literal_eval(p)]])
 if (m:=re.fullmatch(r'mixedSquare\*g(\d+)\*(1|t|z|w)',name)):
  return f'((mix g t z)^2 * g {int(m[1])-1} * '+{'1':'1','t':'t','z':'z','w':'(t+z-18)'}[m[2]]+')'
 if (m:=re.fullmatch(r'scoreSquare(-?\d+),(-?\d+)\*g(\d+)\*(1|t|z|w)',name)):
  return f'((({m[1]} : ℝ)*score g t z + ({m[2]} : ℝ)*mix g t z)^2 * g {int(m[3])-1} * '+{'1':'1','t':'t','z':'z','w':'(t+z-18)'}[m[4]]+')'
 return base(name)
def generate(D,uniform=False):
 path=root/('qutrit_uniform_parameter_search.json' if uniform else ('qutrit_cubic_certificate_search.json' if D==9 else f'qutrit_D{D}_cubic_certificate.json' if D==12 else f'qutrit_D{D}_fast_certificate.json'))
 j=json.loads(path.read_text());assert j['exact_certificate'];name='Uniform' if uniform else f'Finite{D}'
 lines=['import APPT.Core','set_option maxRecDepth 100000','set_option maxHeartbeats 0','open scoped BigOperators',f'namespace APPT.{name}','']
 spectrum='!['+', '.join(balanced([f'g {k}' for k in range(i,D)]) for i in range(D))+']'
 lines += [f'noncomputable def spectrum (g : Fin {D} → ℝ) : Fin {D} → ℝ :=',f'  {spectrum}']
 idx=list(range(3))+list(range(D-6,D));lines += [f'noncomputable def outer (g : Fin {D} → ℝ) : Fin 9 → ℝ :=', '  !['+', '.join(f'spectrum g {i}' for i in idx)+']']
 args=f'(g : Fin {D} → ℝ)'+(' (t z : ℝ)' if uniform else '')
 appl='g t z' if uniform else 'g'
 lines += [f'noncomputable def total {args} : ℝ := (∑ i, spectrum g i)'+(' + t*outer g 2 + z*outer g 3' if uniform else ''), f'noncomputable def squareTotal {args} : ℝ := (∑ i, (spectrum g i)^2)'+(' + t*(outer g 2)^2 + z*(outer g 3)^2' if uniform else '')]
 if uniform:lines += ['noncomputable def mix (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := t*outer g 2-z*outer g 3','noncomputable def score (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := 9*total g t z-4*(9+t+z)*(outer g 2+outer g 3)']
 terms=[f'({rat(e["coefficient"])} * {expression(e["name"])})' for e in j['terms']]
 lines += [f'noncomputable def rhs {args} : ℝ :=', '  '+balanced(terms),'']
 target=f'(9*(total g t z)^2-8*(9+t+z)*squareTotal g t z)*total g t z' if uniform else f'({D+8}*(total g)^2-{(D+2)**2}*squareTotal g)*total g'
 defs=['rhs','total','squareTotal','outer','spectrum','detA','detB','minorA','minorB','quadA','quadB','ratio','matA','matB','Matrix.det_fin_three','Matrix.mulVec','dotProduct','Fin.sum_univ_succ']+(['mix','score'] if uniform else [])
 lines += [f'theorem certificate_identity {args} : {target} = rhs {appl} := by','  simp ['+', '.join(defs)+']','  <;> ring','']
 hypotheses=f'(hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef)\n    (hB : (matB (outer g)).PosSemidef)'+ (' (ht : 0 ≤ t) (hz : 0 ≤ z)\n    (hw : 0 ≤ t+z-18)' if uniform else '')
 lines += [f'theorem certificate_nonneg {args} {hypotheses} :',f'    0 ≤ {target} := by',f'  rw [certificate_identity]']
 for i in range(D):lines += [f'  have hg{i} : 0 ≤ g {i} := hg {i}']
 for c in ['A','B']:
  lines += [f'  have hd{c} := det{c}_nonneg (outer g) h{c}']
  for i,k in [(0,1),(0,2),(1,2)]:lines += [f'  have hm{c}{i}{k} := minor{c}_nonneg (outer g) h{c} {i} {k}']
 vectors=set()
 for e in j['terms']:
  m=re.search(r'([AB])quad(\([^)]*\))',e['name'])
  if m:vectors.add((m[1],ast.literal_eval(m[2])))
 if uniform:vectors.add(('A',(1,1,1)))
 for c,v in sorted(vectors):lines += [f'  have hq{c}{"".join(map(str,v))} := quad{c}_nonneg (outer g) h{c} ![{",".join(map(str,v))}]']
 if uniform:lines += ['  have hr : 0 ≤ ratio (outer g) := by','    simp [ratio, quadA, matA, Matrix.mulVec, dotProduct,','      outer, spectrum, Fin.sum_univ_succ] at hqA111 ⊢','    linarith']
 lines += ['  dsimp only [rhs]','  positivity','']
 if uniform:
  lines += [f'theorem normalized_bound {args} {hypotheses} (hT : total g t z = 1) :','    squareTotal g t z ≤ 9 / (8*(9+t+z)) := by','  have h := certificate_nonneg g t z hg hA hB ht hz hw','  rw [hT] at h','  have hp : 0 < (8 : ℝ)*(9+t+z) := by positivity','  apply (le_div_iff₀ hp).2','  nlinarith']
 else:
  lines += [f'theorem normalized_bound {args} {hypotheses} (hT : total g = 1) :',f'    squareTotal g ≤ ({D+8} : ℝ)/{(D+2)**2} := by','  have h := certificate_nonneg g hg hA hB','  rw [hT] at h','  nlinarith']
 lines += ['',f'end APPT.{name}',''];(dest/(name+'.lean')).write_text('\n'.join(lines));print(name,'bytes', (dest/(name+'.lean')).stat().st_size)
for D in [9,12,15,18,21,24]:generate(D)
generate(9,True)
