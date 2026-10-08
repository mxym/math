#!/usr/bin/env python3
"""Read-only package checks and exact rational sanity tests, not a proof audit."""
from pathlib import Path
from fractions import Fraction as F
from math import comb, factorial
import hashlib, json, re, subprocess
P = Path(__file__).resolve().parent
manifest = json.loads((P/'INPUT_MANIFEST.json').read_text())
checked=[]
for item in manifest['inputs']:
    rel=item['packaged_path']
    if rel:
        assert hashlib.sha256((P/rel).read_bytes()).hexdigest()==item['sha256'], rel
        checked.append(rel)
tex_files=[P/'main.tex',*sorted((P/'sections').glob('*.tex'))]
tex='\n'.join(f.read_text() for f in tex_files)
assert not [c for c in tex if ord(c)<32 and c not in '\n\t\r']
labels=re.findall(r'\\label\{([^}]+)\}',tex)
assert len(labels)==len(set(labels)), 'duplicate labels'
assert set(re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',tex))<=set(labels), 'missing label'
# Exact beta integral after expanding powers in the height variable.
beta_count=0
for q in range(7):
    for j in range(q+1):
        for rho in [F(1,5),F(1,2),F(4,5)]:
            a=q-j
            coeff={}
            for i in range(a+1):
                for l in range(j+1):
                    coeff[i+l]=coeff.get(i+l,F(0))+comb(a,i)*(-rho)**(a-i)*comb(j,l)*(-1)**l
            value=sum(c*(1-rho**(s+1))/F(s+1) for s,c in coeff.items())
            value*=F(comb(q,j))*rho**j/(1-rho)**q
            assert value==(1-rho)*rho**j/F(q+1)
            beta_count+=1
# Core determinant formula, printed defect formula, and exact pyramid conversion.
core_count=0
for m in range(2,10):
    for t in [F(1,17),F(1,5),F(1,2),F(4,5)]:
        c=F(1,factorial(m-1)); q=t**(m-1); b=1-q
        H=c**m*b**(m-1)*(m+1+(m-1)*q)
        L=c**(m+1)*b**(m-1)*(1+(m-1)*q-(m-1)*t**m-q*t**m)
        V=(1-t**m)/factorial(m)
        a=L/(m*V*H); e=a-F(1,m+1)
        printed=t**(m-1)*(m*(m-1)-(m+1)*(m-2)*t-2*t**m)/((m+1)*(1-t**m)*(m+1+(m-1)*t**(m-1)))
        assert e==printed and e>0
        delta=m+1-1/a
        assert delta==(m+1)**2*e/(1+(m+1)*e)
        if m==2:
            assert e==2*t/(3*(3+t)) and delta==2*t/(1+t)
        for d in range(m,m+5):
            a_d=a
            for _ in range(d-m): a_d=a_d/(1+a_d)
            n=d+1
            assert n-1/a_d==delta
            assert a_d-F(1,n)==delta/(n*(n-delta))
        core_count+=1
pdf=P/'vertex_excess_sharp_exponent.pdf'
assert pdf.is_file()
pdftext=subprocess.check_output(['pdftotext',str(pdf),'-'],text=True)
assert '??' not in pdftext, 'unresolved PDF reference'
info=subprocess.check_output(['pdfinfo',str(pdf)],text=True)
pages=int(re.search(r'^Pages:\s+(\d+)',info,re.M).group(1))
print(json.dumps({'status':'PASS','scope':'Source hashes, references, and exact rational transcription checks; not independent mathematical or formal verification','snapshot_files_checked':len(checked),'tex_files_checked':len(tex_files),'unique_equation_and_section_labels':len(labels),'beta_integral_cases':beta_count,'core_formula_cases':core_count,'pdf_pages':pages,'pdf_sha256':hashlib.sha256(pdf.read_bytes()).hexdigest()},indent=2))
