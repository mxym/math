#!/usr/bin/env python3
"""Factor small polynomial identities from exact integer coefficient merging.
All generated identities must pass Lean's kernel; this generator is not trusted.
"""
from pathlib import Path
from fractions import Fraction
import json, re, ast, hashlib
import argparse, tempfile
from certificate_polynomials import certificate_context, expression
HERE = Path(__file__).resolve().parent

def emit_sparse(ctx):
    root, D, uniform = ctx['root'], ctx['D'], ctx['uniform']
    assert uniform
    terms, weights, polys, target, Q = (ctx[k] for k in ('terms','weights','polys','target','Q'))
    name = 'Uniform'
    directory = root/'APPT/UniformSparse'
    directory.mkdir(parents=True, exist_ok=True)
    def key(e): return sum(x*4**i for i,x in enumerate(e))
    def encode(p): return {key(e):int(c) for e,c in p.items()}
    def add(ps):
        out={}
        for p in ps:
            for k,c in p.items(): out[k]=out.get(k,0)+c
        return out
    def lit(p): return '['+', '.join(f'({k}, {c})' for k,c in sorted(p.items()))+']'
    def balanced(xs,op):
        if len(xs)==1:return xs[0]
        k=len(xs)//2;return f'({op} {balanced(xs[:k],op)} {balanced(xs[k:],op)})'
    args='(g : Fin 9 → ℝ) (t z : ℝ)'
    app='g t z'
    hyp='(hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18)'
    happ='hg hA hB ht hz hw'
    targetexpr='(9*(total g t z)^2-8*(9+t+z)*squareTotal g t z)*total g t z'
    defs='total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score'
    def header(imports):
        return '\n'.join('import '+s for s in imports)+'\nset_option maxRecDepth 100000\nset_option maxHeartbeats 8000000\nset_option linter.unusedSimpArgs false\nset_option linter.unusedVariables false\nopen scoped BigOperators\nnamespace APPT.Uniform\nopen CoefficientMerge\n\n'
    def write(mod, text): (directory/(mod+'.lean')).write_text(text+'\nend APPT.Uniform\n')
    body=(HERE/'templates/UniformData.lean.txt').read_text()
    (directory/'Data.lean').write_text(body)
    modules={'APPT.CoefficientMerge':['APPT.Core'], 'APPT.UniformSparse.Data':['APPT.CoefficientMerge']}
    groups=[];pending=[];cost=0
    for i,p in enumerate(polys):
        c=max(1,len(p)//10)
        if pending and (len(pending)>=20 or cost+c>50):
            groups.append(pending);pending=[];cost=0
        pending.append(i);cost+=c
    if pending:groups.append(pending)
    nodes=[]
    for no, ids in enumerate(groups):
        mod=f'Leaf{no:03d}'; decl=f'sparseBlock{no:03d}'
        body=header(['APPT.UniformSparse.Data'])
        pgroup=add([encode(polys[i]) for i in ids])
        pieces=[];nonnegs=[]
        for i in ids:
            raw=expression(terms[i]['name']); atom=f'atom{i:04d}'; poly=f'coeff{i:04d}'
            unweighted={k:c//weights[i] for k,c in encode(polys[i]).items()}
            assert all(c % weights[i]==0 for c in encode(polys[i]).values())
            body+=f'def {poly} : CoefficientMerge.Poly :=\n  {lit(unweighted)}\n'
            body+=f'noncomputable def {atom} {args} : ℝ := {raw}\n'
            body+=f'theorem {atom}_identity {args} : {atom} {app} = CoefficientMerge.eval (monomial {app}) {poly} := by\n  norm_num [{atom}, {poly}, CoefficientMerge.eval, monomial, {defs}]\n  <;> ring\n'
            body+=f'theorem {atom}_nonneg {args} {hyp} : 0 ≤ {atom} {app} := by\n'
            body+=''.join(f'  have hg{k} : 0 ≤ g {k} := hg {k}\n' for k in range(9))
            s=terms[i]['name']
            for c in ('A','B'):
                if c+'det' in s:body+=f'  have hd{c} := det{c}_nonneg (outer g) h{c}\n'
                for k,l in ((0,1),(0,2),(1,2)):
                    if f'{c}minor{k}{l}' in s: body+=f'  have hm := minor{c}_nonneg (outer g) h{c} {k} {l}\n'
            for m in re.finditer(r'([AB])quad(\([^)]*\))',s):
                v=ast.literal_eval(m[2]);body+=f'  have hq := quad{m[1]}_nonneg (outer g) h{m[1]} ![{",".join(map(str,v))}]\n'
            if 'ratio' in s:body+='  have hr := ratio_nonneg g hg hA\n'
            body+=f'  dsimp only [{atom}]\n  positivity\n'
            c=weights[i]; piece=f'(CoefficientMerge.scale ({c} : Int) {poly})'
            pieces.append(piece)
            body+=f'theorem weighted{i:04d}_nonneg {args} {hyp} : 0 ≤ CoefficientMerge.eval (monomial {app}) {piece} := by\n  rw [CoefficientMerge.eval_scale, ← {atom}_identity]\n  exact mul_nonneg (by norm_num) ({atom}_nonneg {app} {happ})\n\n'
            nonnegs.append(f'(weighted{i:04d}_nonneg {app} {happ})')
        body+=f'def {decl} : CoefficientMerge.Poly :=\n  {lit(pgroup)}\n'
        body+=f'theorem {decl}_data : {decl} = {balanced(pieces,"CoefficientMerge.merge")} := by decide +kernel\n'
        body+=f'theorem {decl}_nonneg {args} {hyp} : 0 ≤ CoefficientMerge.eval (monomial {app}) {decl} := by\n  rw [{decl}_data]\n  try simp only [CoefficientMerge.eval_merge]\n  exact {balanced(nonnegs,"add_nonneg")}\n'
        write(mod,body);m=f'APPT.UniformSparse.{mod}';modules[m]=['APPT.UniformSparse.Data'];nodes.append((m,decl,pgroup))
    leaf_count=len(nodes);joins=0
    while len(nodes)>1:
        nxt=[]
        for i in range(0,len(nodes),2):
            if i+1==len(nodes):nxt.append(nodes[i]);continue
            lm,ld,lp=nodes[i];rm,rd,rp=nodes[i+1];p=add([lp,rp])
            mod=f'Join{joins:03d}';decl=f'sparseJoin{joins:03d}';joins+=1
            body=header([lm,rm])+f'def {decl} : CoefficientMerge.Poly :=\n  {lit(p)}\n'
            body+=f'theorem {decl}_data : {decl} = CoefficientMerge.merge {ld} {rd} := by decide +kernel\n'
            body+=f'theorem {decl}_nonneg {args} {hyp} : 0 ≤ CoefficientMerge.eval (monomial {app}) {decl} := by\n  rw [{decl}_data, CoefficientMerge.eval_merge]\n  exact add_nonneg ({ld}_nonneg {app} {happ}) ({rd}_nonneg {app} {happ})\n'
            write(mod,body);m=f'APPT.UniformSparse.{mod}';modules[m]=[lm,rm];nxt.append((m,decl,p))
        nodes=nxt
    rm,rd,rp=nodes[0]
    tp=encode(target);tp={k:tp.get(k,0) for k in rp}
    if rp!={k:Q*c for k,c in tp.items()}:raise RuntimeError('Final coefficient mismatch')
    body=header([rm])+f'def targetCoeffs : CoefficientMerge.Poly :=\n  {lit(tp)}\n'
    body+=f'theorem target_coefficients : {rd} = CoefficientMerge.scale ({Q} : Int) targetCoeffs := by decide +kernel\n'
    body+=f'theorem target_expansion {args} : {targetexpr} = CoefficientMerge.eval (monomial {app}) targetCoeffs := by\n  norm_num [targetCoeffs, CoefficientMerge.eval, monomial, {defs}]\n  <;> ring\n'
    body+=f'theorem certificate_nonneg {args} {hyp} : 0 ≤ {targetexpr} := by\n  have h := {rd}_nonneg {app} {happ}\n  rw [target_coefficients, CoefficientMerge.eval_scale, ← target_expansion] at h\n  have hq : (0 : ℝ) < ({Q} : Int) := by norm_num\n  exact (mul_nonneg_iff_of_pos_left hq).mp h\n'
    body+=f'theorem normalized_bound {args} {hyp} (hT : total {app} = 1) :\n    squareTotal g t z ≤ 9 / (8*(9+t+z)) := by\n  have h := certificate_nonneg g t z hg hA hB ht hz hw\n  rw [hT] at h\n  have hp : 0 < (8 : ℝ)*(9+t+z) := by positivity\n  apply (le_div_iff₀ hp).2\n  nlinarith\n'
    (root/'APPT/Uniform.lean').write_text(body+'\nend APPT.Uniform\n')
    modules['APPT.Uniform']=[rm]
    # Large joins use the proved primitive-recursive implementation.
    for i in range(106,113):
        p=directory/f'Join{i:03d}.lean'
        text=p.read_text().replace('set_option maxRecDepth', 'import APPT.CoefficientMergeFast\nset_option maxRecDepth',1)
        text=text.replace('CoefficientMerge.merge ', 'CoefficientMerge.fastMerge ').replace('CoefficientMerge.eval_merge]', 'CoefficientMerge.eval_fastMerge]')
        p.write_text(text)
        modules[f'APPT.UniformSparse.Join{i:03d}'].append('APPT.CoefficientMergeFast')
    modules['APPT.CoefficientMergeFast']=['APPT.CoefficientMerge']

    return {'name':'Uniform','terms':len(terms),'leaf_count':leaf_count,'join_count':joins,'input_sha256':hashlib.sha256(ctx['source'].read_bytes()).hexdigest(),'modules':modules}

def generate(root, inputs):
    info=emit_sparse(certificate_context(root,inputs,9,True,20))
    (root/'generated-Uniform.json').write_text(json.dumps(info,indent=2)+'\n')
    return info

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',type=Path,default=HERE.parent)
    ap.add_argument('--inputs',type=Path)
    ap.add_argument('--check',action='store_true')
    args=ap.parse_args();root=args.root.resolve();inputs=(args.inputs or root/'certificates').resolve()
    if args.check:
        with tempfile.TemporaryDirectory(prefix='appt-uniform-generate-') as tmp:
            out=Path(tmp);info=generate(out,inputs)
            paths=[p.relative_to(out) for p in out.rglob('*.lean')]+[Path('generated-Uniform.json')]
            for p in paths:
                if (out/p).read_bytes()!=(root/p).read_bytes(): raise RuntimeError('Generated source mismatch: '+str(p))
        print('DETERMINISTIC_REGENERATION_PASS',len(paths),'files')
    else:
        info=generate(root,inputs)
        print({k:v for k,v in info.items() if k!='modules'})

if __name__=='__main__': main()
