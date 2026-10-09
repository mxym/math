#!/usr/bin/env python3
"""Generate finite APPT certificates using proved sparse polynomial operations.
No generated equality is trusted: every coefficient operation is kernel-checked.
"""
from __future__ import annotations
import argparse, ast, hashlib, json, re, tempfile
from pathlib import Path
from certificate_polynomials import certificate_context, expression
HERE=Path(__file__).resolve().parent

def bal(xs,op):
    if len(xs)==1:return xs[0]
    n=len(xs)//2
    return f'({op} {bal(xs[:n],op)} {bal(xs[n:],op)})'
def clean(p):return {m:int(c) for m,c in p.items() if c}
def add(*ps):
    out={}
    for p in ps:
        for m,c in p.items():out[m]=out.get(m,0)+c
    return clean(out)
def scale(c,p):return clean({m:c*v for m,v in p.items()})
def mul(p,q):
    out={}
    for m,c in p.items():
        for n,d in q.items():
            k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
    return clean(out)
def encode(p):return {tuple(i for i,k in enumerate(e) for _ in range(k)):int(c) for e,c in p.items() if c}
def lit(p):return '['+', '.join('(['+','.join(map(str,m))+f'], {c})' for m,c in sorted(p.items()))+']'
def mlit(m):return '['+','.join(map(str,m))+']'
def clit(p,D):
    assert all(len(m)==3 and all(0<=k<D for k in m) for m in p)
    return '['+', '.join(f'({m[0]*D*D+m[1]*D+m[2]}, {c})' for m,c in sorted(p.items()))+']'

def generate_dimension(root,inputs,D):
    ctx=certificate_context(root,inputs,D,False,40)
    terms,weights,polys,target,Q=[ctx[k] for k in ['terms','weights','polys','target','Q']]
    ns=f'APPT.Finite{D}'
    directory=root/f'APPT/Finite{D}Sparse';directory.mkdir(parents=True,exist_ok=True)
    modules={}; generated=[]
    args=f'(g : Fin {D} → ℝ)'; app='(gapValues g)'; capp=f'(SparsePolynomial.cubeValue {app} {D})'
    hyp='(hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef)'
    def header(imports):
        return '\n'.join('import '+i for i in imports)+f'\nset_option maxRecDepth 100000\nset_option maxHeartbeats 8000000\nset_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\nopen scoped BigOperators\nnamespace {ns}\nopen SparsePolynomial\n\n'
    def write(name,body,imports):
        module=f'{ns}Sparse.{name}';p=directory/(name+'.lean')
        p.write_text(header(imports)+body+f'\nend {ns}\n')
        modules[module]=imports;generated.append(p)
        return module
    def cubic_product(prefix,L,lp,Q,qp,deps):
        """Multiply a linear form and a quadratic form one row at a time."""
        rows=[];terms=list(sorted(lp.items()));row_modules=[];all_evals=[]
        for group_start in range(0,len(terms),4):
            body='';ids=[]
            for k in range(group_start,min(group_start+4,len(terms))):
                m,c=terms[k]; assert len(m)==1
                row=mul({m:c},qp);name=f'{prefix}Row{k:02d}'
                body+=f'def {name} : CoefficientMerge.Poly := {clit(row,D)}\n'
                body+=f'theorem {name}_decode : SparsePolynomial.decodeCubic {D} {name} = SparsePolynomial.monoTimes {mlit(m)} ({c} : Int) {Q} := by decide +kernel\n'
                body+=f'theorem eval_{name} {args} : CoefficientMerge.eval {capp} {name} = ({c} : ℝ)*SparsePolynomial.mon {app} {mlit(m)}*SparsePolynomial.eval {app} {Q} := by\n  rw [← SparsePolynomial.eval_decodeCubic, {name}_decode, SparsePolynomial.eval_monoTimes]\n  norm_num\n'
                rows.append((name,row));ids.append(name);all_evals.append('eval_'+name)
            row_modules.append(write(f'{prefix}Rows{group_start//4:02d}',body,deps))
        product=mul(lp,qp);name=f'{prefix}Coeffs'
        body=f'def {name} : CoefficientMerge.Poly := {clit(product,D)}\n'
        body+=f'theorem {name}_data : {name} = CoefficientMerge.trim {bal([r for r,_ in rows],"CoefficientMerge.fastMerge")} := by decide +kernel\n'
        body+=f'theorem eval_{name} {args} : CoefficientMerge.eval {capp} {name} = SparsePolynomial.eval {app} {L} * SparsePolynomial.eval {app} {Q} := by\n  rw [{name}_data, CoefficientMerge.eval_trim]\n  simp only [CoefficientMerge.eval_fastMerge, '+', '.join(all_evals)+f']\n  generalize hq : SparsePolynomial.eval {app} {Q} = v\n  simp only [{L}, SparsePolynomial.eval]\n  push_cast\n  ring\n'
        module=write(f'{prefix}Product',body,row_modules)
        return module,name,product
    y=[{(j,):1 for j in range(i,D)} for i in range(D)]
    matrices={c:[[encode(p) for p in row] for row in ctx[c]] for c in ['A','B']}
    data=(HERE/f'templates/Finite{D}Definitions.lean.txt').read_text()
    data+=f'\nnoncomputable def gapValues {args} (i : Nat) : ℝ :=\n  if h : i < {D} then g ⟨i,h⟩ else 0\n\n'
    simp_base='SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum'
    for i,p in enumerate(y):
        data+=f'def polyY{i} : SparsePolynomial.Poly := {lit(p)}\n'
        data+=f'theorem eval_polyY{i} {args} : SparsePolynomial.eval {app} polyY{i} = spectrum g {i} := by\n  norm_num [polyY{i}, {simp_base}]\n  <;> ring\n'
    T=add(*y)
    data+=f'def polyTotal : SparsePolynomial.Poly := {lit(T)}\n'
    data+=f'theorem eval_polyTotal {args} : SparsePolynomial.eval {app} polyTotal = total g := by\n  norm_num [polyTotal, total, Fin.sum_univ_succ, {simp_base}]\n  <;> ring\n'
    for c,M in matrices.items():
        for i in range(3):
            for j in range(3):
                name=f'entry{c}{i}{j}'
                data+=f'def {name} : SparsePolynomial.Poly := {lit(M[i][j])}\n'
                data+=f'theorem eval_{name} {args} : SparsePolynomial.eval {app} {name} = mat{c} (outer g) {i} {j} := by\n  norm_num [{name}, {simp_base}, outer, mat{c}]\n  <;> ring\n'
    data_mod=write('Data',data,['APPT.SparsePolynomialCubic'])
    # The second moment is computed in small individual square identities.
    moments='';squares=[]
    for i,p in enumerate(y):
        sq=mul(p,p);squares.append(sq);name=f'square{i}'
        moments+=f'def {name} : SparsePolynomial.Poly := {lit(sq)}\n'
        moments+=f'theorem {name}_data : {name} = SparsePolynomial.trim (SparsePolynomial.mul polyY{i} polyY{i}) := by decide +kernel\n'
        moments+=f'theorem eval_{name} {args} : SparsePolynomial.eval {app} {name} = (spectrum g {i})^2 := by\n  rw [{name}_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY{i}]\n  ring\n'
    S=add(*squares)
    moments+=f'def polySquares : SparsePolynomial.Poly := {lit(S)}\n'
    moments+=f'theorem polySquares_data : polySquares = SparsePolynomial.trim {bal([f"square{i}" for i in range(D)],"SparsePolynomial.merge")} := by decide +kernel\n'
    moments+=f'theorem eval_polySquares {args} : SparsePolynomial.eval {app} polySquares = squareTotal g := by\n  rw [polySquares_data, SparsePolynomial.eval_trim]\n  simp only [SparsePolynomial.eval_merge, '+', '.join(f'eval_square{i}' for i in range(D))+']\n  simp [squareTotal, Fin.sum_univ_succ]\n  <;> ring\n'
    moments_mod=write('Moments',moments,[data_mod])
    # Shared determinant, minor and quadratic-form bases.
    basenames=sorted({t['name'].split('*')[0] for t in terms if not t['name'].startswith('gprod')})
    base_info={};base_mods={};base_evals=[]
    for serial,b in enumerate(basenames):
        c=b[0];M=matrices[c];pname=f'base{serial:02d}'
        expression_math='';body='';base_deps=[data_mod]
        if b.endswith('det'):
            perm=[(0,1,2),(1,2,0),(2,0,1),(2,1,0),(1,0,2),(0,2,1)]
            products=[];evals=[];pair_evals=[];base_deps=[]
            for k,(a,bb,cc) in enumerate(perm):
                pair=f'det{serial:02d}Pair{k}'
                pp=mul(M[1][bb],M[2][cc])
                pairbody=f'def {pair} : SparsePolynomial.Poly := {lit(pp)}\n'
                pairbody+=f'theorem {pair}_data : {pair} = SparsePolynomial.trim (SparsePolynomial.mul entry{c}1{bb} entry{c}2{cc}) := by decide +kernel\n'
                pairbody+=f'theorem eval_{pair} {args} : SparsePolynomial.eval {app} {pair} = mat{c} (outer g) 1 {bb} * mat{c} (outer g) 2 {cc} := by\n  rw [{pair}_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entry{c}1{bb}, eval_entry{c}2{cc}]\n'
                pm=write(f'Det{serial:02d}Pair{k}',pairbody,[data_mod])
                cm,cn,cp=cubic_product(f'det{serial:02d}Term{k}',f'entry{c}0{a}',M[0][a],pair,pp,[pm])
                base_deps.append(cm);products.append((cn,cp));evals.append('eval_'+cn);pair_evals.append('eval_'+pair)
            bp=add(*[scale(1 if k<3 else -1,p) for k,(_,p) in enumerate(products)])
            chunks=[cn if k<3 else f'(CoefficientMerge.scale (-1) {cn})' for k,(cn,_) in enumerate(products)]
            expression_math=f'det{c} (outer g)'
            body+=f'def {pname} : SparsePolynomial.Poly := {lit(bp)}\n'
            body+=f'def {pname}Coded : CoefficientMerge.Poly := {clit(bp,D)}\n'
            body+=f'theorem {pname}_decode : {pname} = SparsePolynomial.decodeCubic {D} {pname}Coded := by decide +kernel\n'
            body+=f'theorem {pname}_data : {pname}Coded = CoefficientMerge.trim {bal(chunks,"CoefficientMerge.fastMerge")} := by decide +kernel\n'
            body+=f'theorem eval_{pname} {args} : SparsePolynomial.eval {app} {pname} = {expression_math} := by\n  rw [{pname}_decode, SparsePolynomial.eval_decodeCubic, {pname}_data, CoefficientMerge.eval_trim]\n  simp only [CoefficientMerge.eval_fastMerge, CoefficientMerge.eval_scale, '+', '.join(evals+pair_evals+[f'eval_entry{c}{i}{j}' for i in range(3) for j in range(3)])+f']\n  simp only [det{c}, Matrix.det_fin_three]\n  push_cast\n  ring\n'
            nn=f'det{c}_nonneg (outer g) h{c}'
        elif 'minor' in b:
            i,j=map(int,b[-2:]);bp=add(mul(M[i][i],M[j][j]),scale(-1,mul(M[i][j],M[j][i])))
            formula=f'SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.mul entry{c}{i}{i} entry{c}{j}{j}) (SparsePolynomial.scale (-1) (SparsePolynomial.mul entry{c}{i}{j} entry{c}{j}{i})))'
            expression_math=f'minor{c} (outer g) {i} {j}'
            body+=f'def {pname} : SparsePolynomial.Poly := {lit(bp)}\n'
            body+=f'theorem {pname}_data : {pname} = {formula} := by decide +kernel\n'
            body+=f'theorem eval_{pname} {args} : SparsePolynomial.eval {app} {pname} = {expression_math} := by\n  rw [{pname}_data]\n  simp only [SparsePolynomial.eval_trim, SparsePolynomial.eval_merge, SparsePolynomial.eval_scale, SparsePolynomial.eval_mul, '+', '.join(f'eval_entry{c}{a}{bb}' for a in range(3) for bb in range(3))+f']\n  simp only [minor{c}]\n  push_cast\n  ring\n'
            nn=f'minor{c}_nonneg (outer g) h{c} {i} {j}'
        else:
            v=ast.literal_eval(b[b.index('('):]);bp=add(*[scale(v[i]*v[j],M[i][j]) for i in range(3) for j in range(3)])
            vec='!['+','.join(map(str,v))+']';expression_math=f'quad{c} (outer g) {vec}'
            body+=f'def {pname} : SparsePolynomial.Poly := {lit(bp)}\n'
            body+=f'theorem eval_{pname} {args} : SparsePolynomial.eval {app} {pname} = {expression_math} := by\n  norm_num [{pname}, {simp_base}, quad{c}, mat{c}, outer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]\n  <;> ring\n'
            nn=f'quad{c}_nonneg (outer g) h{c} {vec}'
        body+=f'theorem {pname}_nonneg {args} {hyp} : 0 ≤ SparsePolynomial.eval {app} {pname} := by\n  rw [eval_{pname}]\n  exact {nn}\n'
        bm=write(f'Base{serial:02d}',body,base_deps);base_mods[b]=bm;base_info[b]=(pname,bp,expression_math)
    # Certificate leaves. Monomials cost one; PSD terms are charged by sparse size.
    groups=[];pending=[];cost=0
    for i,p in enumerate(polys):
        c=max(1,len(p)//15)
        if pending and (len(pending)>=80 or cost+c>160):groups.append(pending);pending=[];cost=0
        pending.append(i);cost+=c
    if pending:groups.append(pending)
    nodes=[]
    for no,ids in enumerate(groups):
        body='';dependencies={data_mod};pieces=[];nonnegs=[]
        for i in ids:
            term=terms[i]['name'];p=scale(1,encode(polys[i]));w=weights[i]
            assert all(c%w==0 for c in p.values());unweighted={m:c//w for m,c in p.items()}
            pname=f'atom{i:04d}';raw=expression(term)
            if term.startswith('gprod'):
                factors=ast.literal_eval(term[5:]);base=None
            else:
                b=term.split('*')[0];base,bp,base_value=base_info[b];dependencies.add(base_mods[b])
                factors=[int(k)-1 for k in re.findall(r'g(\d+)',term.split('*',1)[1])] if '*' in term else []
            body+=f'def {pname} : SparsePolynomial.Poly := {lit(unweighted)}\n'
            if base is None:
                body+=f'theorem eval_{pname} {args} : SparsePolynomial.eval {app} {pname} = {raw} := by\n  norm_num [{pname}, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]\n  <;> ring\n'
            else:
                body+=f'theorem {pname}_data : {pname} = SparsePolynomial.monoTimes {mlit(sorted(factors))} 1 {base} := by decide +kernel\n'
                body+=f'theorem eval_{pname} {args} : SparsePolynomial.eval {app} {pname} = {raw} := by\n  rw [{pname}_data, SparsePolynomial.eval_monoTimes, eval_{base}]\n  norm_num [SparsePolynomial.mon, gapValues]\n  <;> ring\n'
            body+=f'theorem {pname}_nonneg {args} {hyp} : 0 ≤ SparsePolynomial.eval {app} (SparsePolynomial.scale ({w} : Int) {pname}) := by\n  rw [SparsePolynomial.eval_scale, eval_{pname}]\n'
            for k in sorted(set(factors)):body+=f'  have hg{k} : 0 ≤ g {k} := hg {k}\n'
            if base:
                body+=f'  have hb := {base}_nonneg g hg hA hB\n  rw [eval_{base}] at hb\n'
            body+=f'  have ht : 0 ≤ {raw} := by positivity\n  exact mul_nonneg (by norm_num) ht\n'
            coded=f'{pname}Coded'
            body+=f'def {coded} : CoefficientMerge.Poly := {clit(unweighted,D)}\n'
            body+=f'theorem {coded}_decode : {pname} = SparsePolynomial.decodeCubic {D} {coded} := by decide +kernel\n'
            body+=f'theorem {coded}_nonneg {args} {hyp} : 0 ≤ CoefficientMerge.eval {capp} (CoefficientMerge.scale ({w} : Int) {coded}) := by\n  have h := {pname}_nonneg g hg hA hB\n  rw [SparsePolynomial.eval_scale, {coded}_decode, SparsePolynomial.eval_decodeCubic] at h\n  simpa only [CoefficientMerge.eval_scale] using h\n'
            pieces.append(f'(CoefficientMerge.scale ({w} : Int) {coded})');nonnegs.append(f'({coded}_nonneg g hg hA hB)')
        pg=add(*[encode(polys[i]) for i in ids]);decl=f'block{no:03d}'
        body+=f'def {decl} : CoefficientMerge.Poly := {clit(pg,D)}\n'
        body+=f'theorem {decl}_data : {decl} = CoefficientMerge.trim {bal(pieces,"CoefficientMerge.fastMerge")} := by decide +kernel\n'
        body+=f'theorem {decl}_nonneg {args} {hyp} : 0 ≤ CoefficientMerge.eval {capp} {decl} := by\n  rw [{decl}_data, CoefficientMerge.eval_trim]\n  try simp only [CoefficientMerge.eval_fastMerge]\n  exact {bal(nonnegs,"add_nonneg")}\n'
        mod=write(f'Leaf{no:03d}',body,sorted(dependencies));nodes.append((mod,decl,pg))
    joins=0
    while len(nodes)>1:
        nxt=[]
        for i in range(0,len(nodes),2):
            if i+1==len(nodes):nxt.append(nodes[i]);continue
            lm,ld,lp=nodes[i];rm,rd,rp=nodes[i+1];p=add(lp,rp);decl=f'join{joins:03d}'
            body=f'def {decl} : CoefficientMerge.Poly := {clit(p,D)}\n'
            body+=f'theorem {decl}_data : {decl} = CoefficientMerge.trim (CoefficientMerge.fastMerge {ld} {rd}) := by decide +kernel\n'
            body+=f'theorem {decl}_nonneg {args} {hyp} : 0 ≤ CoefficientMerge.eval {capp} {decl} := by\n  rw [{decl}_data, CoefficientMerge.eval_trim, CoefficientMerge.eval_fastMerge]\n  exact add_nonneg ({ld}_nonneg g hg hA hB) ({rd}_nonneg g hg hA hB)\n'
            mod=write(f'Join{joins:03d}',body,[lm,rm]);nxt.append((mod,decl,p));joins+=1
        nodes=nxt
    # Target polynomial: linear times quadratic avoids cubic ring normalization.
    quadratic=add(scale(D+8,mul(T,T)),scale(-(D+2)**2,S));tp=mul(T,quadratic)
    assert tp==encode(target)
    targetbody=f'def targetQuadratic : SparsePolynomial.Poly := {lit(quadratic)}\n'
    targetbody+=f'theorem targetQuadratic_data : targetQuadratic = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.scale {D+8} (SparsePolynomial.mul polyTotal polyTotal)) (SparsePolynomial.scale (-{(D+2)**2}) polySquares)) := by decide +kernel\n'
    targetbody+=f'theorem eval_targetQuadratic {args} : SparsePolynomial.eval {app} targetQuadratic = {D+8}*(total g)^2-{(D+2)**2}*squareTotal g := by\n  rw [targetQuadratic_data]\n  simp only [SparsePolynomial.eval_trim, SparsePolynomial.eval_merge, SparsePolynomial.eval_scale, SparsePolynomial.eval_mul, eval_polyTotal, eval_polySquares]\n  push_cast\n  ring\n'
    quadratic_mod=write('TargetQuadratic',targetbody,[moments_mod])
    product_mod,product_name,product_poly=cubic_product('targetProduct','polyTotal',T,'targetQuadratic',quadratic,[quadratic_mod])
    assert product_poly==tp
    targetbody=f'def targetCoeffs : CoefficientMerge.Poly := {product_name}\n'
    targetbody+=f'theorem eval_targetCoeffs {args} : CoefficientMerge.eval {capp} targetCoeffs = ({D+8}*(total g)^2-{(D+2)**2}*squareTotal g)*total g := by\n  rw [targetCoeffs, eval_{product_name}, eval_polyTotal, eval_targetQuadratic]\n  ring\n'
    targetmod=write('Target',targetbody,[product_mod]);rm,rd,rp=nodes[0]
    assert rp==scale(Q,tp)
    rootbody=f'theorem target_coefficients : {rd} = CoefficientMerge.scale ({Q} : Int) targetCoeffs := by decide +kernel\n'
    rootbody+=f'theorem certificate_nonneg {args} {hyp} : 0 ≤ ({D+8}*(total g)^2-{(D+2)**2}*squareTotal g)*total g := by\n  have h := {rd}_nonneg g hg hA hB\n  rw [target_coefficients, CoefficientMerge.eval_scale, eval_targetCoeffs] at h\n  have hq : (0 : ℝ) < ({Q} : Int) := by norm_num\n  exact (mul_nonneg_iff_of_pos_left hq).mp h\n'
    rootbody+=f'theorem normalized_bound {args} {hyp} (hT : total g = 1) :\n    squareTotal g ≤ ({D+8} : ℝ)/{(D+2)**2} := by\n  have h := certificate_nonneg g hg hA hB\n  rw [hT] at h\n  nlinarith\n'
    p=root/f'APPT/Finite{D}.lean';p.write_text(header([rm,targetmod])+rootbody+f'\nend {ns}\n');generated.append(p);modules[ns]=[rm,targetmod]
    # Separate exact coefficient computations, then emit typed literal constructors.
    from flatten_numeric_merges import transform_dimension as flatten_merges
    from explicit_coefficient_literals import transform_dimension as explicit_literals
    flatten_merges(root,D)
    explicit_literals(root,D)
    return {'dimension':D,'terms':len(terms),'leaves':len(groups),'joins':joins,'input_sha256':hashlib.sha256(ctx['source'].read_bytes()).hexdigest(),'modules':modules}

def generate(root,inputs,dimensions):
    infos=[generate_dimension(root,inputs,D) for D in dimensions]
    modules={'APPT.Core':[],'APPT.SparsePolynomial':['APPT.Core'],'APPT.CoefficientMerge':['APPT.Core'],'APPT.CoefficientMergeFast':['APPT.CoefficientMerge'],'APPT.SparsePolynomialCubic':['APPT.SparsePolynomial','APPT.CoefficientMergeFast']}
    for x in infos:modules.update(x['modules'])
    result={'cases':[{k:v for k,v in x.items() if k!='modules'} for x in infos],'modules':modules}
    (root/'generated-Finite.json').write_text(json.dumps(result,indent=2)+'\n');return result

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=HERE.parent);ap.add_argument('--inputs',type=Path)
    ap.add_argument('--dimensions',type=int,nargs='+',default=[9,12,15,18,21,24]);ap.add_argument('--check',action='store_true')
    args=ap.parse_args();root=args.root.resolve();inputs=(args.inputs or root/'certificates').resolve()
    if args.check:
        with tempfile.TemporaryDirectory(prefix='appt-finite-replay-') as tmp:
            out=Path(tmp);generate(out,inputs,args.dimensions)
            paths=[p.relative_to(out) for p in out.rglob('*.lean')]+[Path('generated-Finite.json')]
            for p in paths:
                if (out/p).read_bytes()!=(root/p).read_bytes():raise RuntimeError('Generated source mismatch: '+str(p))
        print('FINITE_DETERMINISTIC_REGENERATION_PASS',len(paths),'files')
    else:
        info=generate(root,inputs,args.dimensions);print(json.dumps(info['cases'],indent=2));print('Modules:',len(info['modules']))
if __name__=='__main__':main()
