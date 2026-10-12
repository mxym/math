#!/usr/bin/env python3
"""Exact negative-parameter control and source-statement preservation checks."""
from fractions import Fraction as F
from pathlib import Path
import difflib, hashlib, json, re
ROOT = Path(__file__).resolve().parent.parent

def require(ok, description):
    if not ok:
        raise RuntimeError(description)

def main():
    original = (ROOT/'originals/entropy.tex').read_text()
    corrected = (ROOT/'originals/entropy.corrected.tex').read_text()
    public = (ROOT/'entropy.tex').read_text()
    old = r'\E e^{\theta|X|^2}\le(1-2\theta/a)^{-k/2}\quad(2\theta<a).'
    new = r'\E e^{\theta|X|^2}\le(1-2\theta/a)^{-k/2}\quad(0\le\theta<a/2).'
    require(original.count(old)==1, 'unique original helper-domain statement')
    require(corrected == original.replace(old,new), 'correction is exactly one helper-domain change')
    require(public.count(new)==1 and old not in public, 'public helper domain is corrected')
    for environment in ['theorem','corollary','lemma','proof']:
        pattern = r'\\begin\{'+environment+r'\}.*?\\end\{'+environment+r'\}'
        require(re.findall(pattern,public,re.S)==re.findall(pattern,corrected,re.S),
                'public '+environment+' statements/proofs must match audited corrected source')
    mathematical_start = r'\section{Positive-curvature and one-step estimates}'
    mathematical_end = r'\section{Verification and proved boundaries}'
    require(public.split(mathematical_start,1)[1].split(mathematical_end,1)[0]
            ==corrected.split(mathematical_start,1)[1].split(mathematical_end,1)[0],
            'all estimates, examples and sharpness/obstruction arguments match corrected audited source')
    theorem_start = r'\section{The precise theorem}'
    require(public.split(theorem_start,1)[1].split(r'\section{Sources and proof dependencies}',1)[0]
            ==corrected.split(theorem_start,1)[1].split(r'\section{Source audit and standard inputs}',1)[0],
            'all definitions, hypotheses and conditional integrability assumptions are unchanged')
    editorial_patch=''.join(difflib.unified_diff(corrected.splitlines(True),public.splitlines(True),
                            fromfile='originals/entropy.corrected.tex',tofile='entropy.tex'))
    require(editorial_patch==(ROOT/'public_editorial.patch').read_text(), 'editorial patch records all public edits exactly')
    # Gaussian moment formula: E exp(theta X^2)=(1-2 theta variance)^(-1/2).
    a, variance, theta = F(1), F(1,2), F(-1)
    require(1/variance >= a, 'counterexample curvature meets a=1')
    require(2*theta < a, 'original clause admits theta=-1')
    require(not (F(0)<=theta<a/2), 'corrected domain rejects theta=-1')
    lhs_squared=1/(1-2*theta*variance)
    rhs_squared=1/(1-2*theta/a)
    require(lhs_squared==F(1,2) and rhs_squared==F(1,3), 'exact squared Gaussian moments')
    require(lhs_squared>rhs_squared, 'original negative-theta bound is strictly false')
    # Positive-domain controls and the exact downstream min(c/16,a/4).
    controls=0
    for aa in [F(1,7),F(1),F(9,2)]:
        for cc in [F(1,11),F(1),F(25)]:
            tt=min(cc/16,aa/4)
            require(0<tt<=aa/4<aa/2 and 8*tt<=cc/2, 'downstream parameter is positive and valid')
            for vv in [1/(4*aa),1/(2*aa),1/aa]:
                for th in [F(0),tt,aa/3]:
                    require(1/(1-2*th*vv)<=1/(1-2*th/aa), 'positive square-moment Gaussian control')
                    controls+=1
    require(r'\theta=\min\{c/16,a/4\}' in public, 'public downstream parameter definition')
    report={'status':'PASS','negative_theta_control':{'a':'1','variance':'1/2','theta':'-1',
        'actual_moment':'1/sqrt(2)','false_original_bound':'1/sqrt(3)',
        'squared_actual':'1/2','squared_bound':'1/3','corrected_domain_rejects':True},
        'positive_gaussian_controls':controls,'one_line_mathematical_correction_only':True,
        'theorem_corollary_lemmas_and_proofs_match_audited_corrected_source':True,
        'scope':'Exact finite controls and unchanged statements; the analytic proof is in entropy.tex.'}
    print(json.dumps(report,indent=2,sort_keys=True))

if __name__=='__main__':
    main()
