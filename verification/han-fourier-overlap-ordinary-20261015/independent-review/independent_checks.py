"""Private reviewer-written algebra/integer checks; no author code is executed.

Fourier numerators are constructed by disjoint polynomial multiplication,
not the author's truth-table Walsh transform. Direct truth evaluations and
brute character sums supply separate finite checks. Arbitrary depth is a
written-proof conclusion, not certified by these finite examples.
"""
from pathlib import Path
from datetime import datetime, timezone
from fractions import Fraction as F
import hashlib,json,sys,traceback
import sympy as sp

HERE=Path(__file__).resolve().parent
RUN=HERE/'runs'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
RUN.mkdir(parents=True)
(RUN/'independent_checks.py').write_bytes(Path(__file__).read_bytes())
(RUN/'INPUT_MANIFEST.json').write_bytes((HERE/'INPUT_MANIFEST.json').read_bytes())
OUT={'status':'RUNNING','reviewer_written':True,'author_code_executed':False,
     'private_only':True,'Lean':False,'arbitrary_depth_formally_verified':False,
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'input_manifest_sha256':hashlib.sha256((HERE/'INPUT_MANIFEST.json').read_bytes()).hexdigest(),
     'groups':{},'expected_rejections':[]}

def save():(RUN/'RESULT.json').write_text(json.dumps(OUT,indent=2)+'\n')
def need(b,msg):
    if not b:raise AssertionError(msg)

def gate(a,b,s):return (a+b+s*a*b-s)//2  # s=+1 AND, s=-1 OR

def polynomial_step(nums,s):
    M=len(nums);n=M.bit_length()-1
    out=[0]*(M*M)
    for i,a in enumerate(nums):
        for j,b in enumerate(nums):
            need((a*b)%2==0,'Integral dyadic product numerator')
            out[i|(j<<n)]+=s*a*b//2
    for i,a in enumerate(nums):
        out[i]+=a*M//2;out[i<<n]+=a*M//2
    out[0]-=s*M*M//2
    return out

def direct_truth(n,gates):
    out=[]
    for x in range(1<<n):
        layer=[1 if x&(1<<i) else -1 for i in range(n)]
        for s in gates:layer=[gate(layer[j],layer[j+1],s) for j in range(0,len(layer),2)]
        need(len(layer)==1,'Homogeneous tree has one root')
        out.append(layer[0])
    return out

def direct_spectrum(truth):
    M=len(truth)
    return [sum(v*(-1 if ((~x)&s).bit_count()%2 else 1) for x,v in enumerate(truth))
            for s in range(M)]

def restrict(truth,i,plus):
    out=[]
    for y in range(len(truth)//2):
        low=y&((1<<i)-1);high=y>>i
        x=low|(int(plus)<<i)|(high<<(i+1));out.append(truth[x])
    return out

def physical_influence(truth,i):
    M=len(truth);mask=1<<i
    return F(sum(v!=truth[x^mask] for x,v in enumerate(truth)),M)

def overlap(nums,i):
    M=len(nums);mask=1<<i
    return F(sum(abs(nums[s]*nums[s|mask]) for s in range(M) if not s&mask),M*M)

def restricted_distance(truth,i):
    a=direct_spectrum(restrict(truth,i,True));b=direct_spectrum(restrict(truth,i,False))
    return F(sum(abs(x*x-y*y) for x,y in zip(a,b)),(len(truth)//2)**2)

def reject(name,assertion,observations,why):
    record={'variant':name,'observations':observations,'explanation':why}
    try:need(assertion,name)
    except AssertionError as exc:record.update(status='REJECTED',actual_exception=repr(exc))
    else:raise AssertionError('Incorrect variant passed: '+name)
    OUT['expected_rejections'].append(record)
    (RUN/('REJECTED-'+name+'.json')).write_text(json.dumps(record,indent=2)+'\n')

save()
try:
    c,d,mu,alpha=sp.symbols('c d mu alpha',real=True)
    need(sp.expand((c+d)**2-(c-d)**2-4*c*d)==0,'Restriction factor four')
    symbolic=1
    for s in (1,-1):
        q=(1+s*mu)/2
        need(sp.expand(((1+s*mu)**2+1-mu**2)/4-q)==0,'Sibling Parseval multiplier')
        need(sp.expand(((1+s*(mu+alpha))**2-(1+s*(mu-alpha))**2)/4-s*alpha*(1+s*mu))==0,
             'Signed empty-child contribution')
        u=sp.symbols('u',real=True)
        child_mean=(u+mu+s*u*mu-s)/2
        nu=mu+s*(mu**2-1)/2
        need(sp.expand(child_mean.subs(u,mu+alpha)-nu-q*alpha)==0,
             'New restriction mean and influence factor')
        symbolic+=3
    OUT['groups']['symbolic']={'identities':symbolic,'sympy_version':sp.__version__}

    nums=[0,2];p=F(1,2);leaf_I=F(1);variance_sum=F(0);gates=[]
    rows=[];allcoords=0;restricted_coords=0;cache={}
    for depth in range(5):
        n=1<<depth;M=1<<n;mean=2*p-1
        truth=direct_truth(n,gates)
        need(len(nums)==M and set(truth)<=set((-1,1)),'Actual Boolean tree and dyadic coefficient size')
        need(sum(a*a for a in nums)==M*M,'Polynomial Parseval')
        need(F(nums[0],M)==mean==F(sum(truth),M),'Mean from polynomial, truth and scalar recursion')
        if n<=8:need(nums==direct_spectrum(truth),'All polynomial coefficients versus brute character sums')
        target_R=2*variance_sum+4*abs(mean)
        ratios=[]
        for i in range(n):
            influence=physical_influence(truth,i)
            fourier_I=F(sum(a*a for s,a in enumerate(nums) if s&(1<<i)),M*M)
            A=overlap(nums,i)
            need(influence==fourier_I==leaf_I and influence>0,'Every coordinate physically essential with correct influence')
            need(4*A/influence==target_R,'All-coordinate spectral recurrence')
            need(A/influence>=F(3*depth,8),'Every-coordinate lower bound')
            if n<=8:
                need(restricted_distance(truth,i)==4*A,'Direct restricted spectra versus overlap')
                restricted_coords+=1
            ratios.append(str(A/influence));allcoords+=1
        need(len(set(ratios))==1,'All coordinates share the same overlap/influence ratio')
        rows.append({'depth':depth,'variables':n,'truth_entries':M,'coordinates':n,
            'gate_signs_bottom_to_top':list(gates),'mean':str(mean),'single_coordinate_influence':str(leaf_I),
            'A_over_single_coordinate_I':ratios[0],'L_over_I':str(target_R)})
        cache[depth]={'truth':truth,'nums':nums,'mean':mean,'I':leaf_I,'R':target_R,'variance_sum':variance_sum}
        if depth<4:
            s=-1 if p<=F(1,2) else 1
            q=(1+s*mean)/2
            need(F(1,2)<=q<=F(3,4),'Chosen influence factor retains positive lower bound')
            nums=polynomial_step(nums,s);gates.append(s)
            variance_sum+=1-mean*mean;leaf_I*=q
            p=2*p-p*p if s==-1 else p*p
            need(F(1,4)<=p<=F(3,4),'Bias interval is preserved')
    OUT['groups']['family_examples']={'depths':5,'all_coordinates':allcoords,
        'direct_restriction_coordinates':restricted_coords,'method':'gate-polynomial multiplication and direct truth/edge evaluation',
        'not_author_Walsh_execution':True,'rows':rows}

    # Exhaust all 20 monotone 3-variable functions, not just the counterexample family.
    monotone=[]
    for flags in range(256):
        truth=[1 if flags&(1<<x) else -1 for x in range(8)]
        if all(truth[x]<=truth[x|(1<<i)] for x in range(8) for i in range(3) if not x&(1<<i)):
            monotone.append(truth)
    need(len(monotone)==20,'Monotone three-variable count')
    recurrence_cases=0;dummy_cases=0
    for g in monotone:
        mean=F(sum(g),8)
        for s in (1,-1):
            joined=[gate(g[x&7],g[x>>3],s) for x in range(64)]
            nu=F(sum(joined),64)
            for i in range(3):
                ai=physical_influence(g,i);new_i=physical_influence(joined,i)
                need(new_i==((1+s*mean)/2)*ai,'AND/OR influence recursion on all monotone cases')
                if not ai:
                    need(restricted_distance(g,i)==0 and restricted_distance(joined,i)==0,'Zero influence not divided by')
                    dummy_cases+=1;continue
                up=F(sum(restrict(g,i,True)),4);down=F(sum(restrict(g,i,False)),4)
                need(up==mean+ai and down==mean-ai,'Monotone first-Fourier/influence identity')
                pred=restricted_distance(g,i)/ai-4*abs(mean)+2*(1-mean*mean)+4*abs(nu)
                need(restricted_distance(joined,i)/new_i==pred,'Exact recurrence for both gate signs and all essential coordinates')
                recurrence_cases+=1
    OUT['groups']['exhaustive_monotone_3']={'functions':20,'essential_gate_coordinate_cases':recurrence_cases,
        'zero_influence_cases_checked_without_division':dummy_cases}

    p=F(1,2);I=F(1);R=F(0);V=F(0);deep=[]
    for depth in range(17):
        mu0=2*p-1
        need(F(1,4)<=p<=F(3,4) and I>0,'Exact deep finite bias and essentiality')
        need(R==2*V+4*abs(mu0) and R>=F(3*depth,2),'Exact finite telescoping')
        deep.append({'depth':depth,'bias_denominator_bits':p.denominator.bit_length(),
            'influence_denominator_bits':I.denominator.bit_length(),'lower_bound_checked_exactly':True})
        s=-1 if p<=F(1,2) else 1;q=(1+s*mu0)/2
        pn=2*p-p*p if s==-1 else p*p;mun=2*pn-1
        R=R-4*abs(mu0)+2*(1-mu0*mu0)+4*abs(mun);V+=1-mu0*mu0
        I*=q;p=pn
    OUT['groups']['deep_scalar_recurrence']={'through_depth':16,'finite_only_not_all_depth_computer_proof':True,'rows':deep}

    g=cache[1];L=restricted_distance(g['truth'],0);A=overlap(g['nums'],0)
    reject('omit-restriction-factor-four',L==A,{'L':str(L),'A':str(A)},'The exact normalization is L=4A.')
    wp=direct_spectrum(restrict(g['truth'],0,True));wm=direct_spectrum(restrict(g['truth'],0,False))
    signed=F(sum(a*a-b*b for a,b in zip(wp,wm)),4)
    reject('omit-absolute-values',signed==L,{'signed_difference':str(signed),'true_L':str(L)},'Both restrictions have Parseval mass one; a signed sum cancels.')
    g=cache[3];wrong=2*g['variance_sum']+4*g['mean']
    reject('signed-instead-of-absolute-terminal-mean',wrong==g['R'],
        {'mean':str(g['mean']),'wrong_R':str(wrong),'true_R':str(g['R'])},'The terminal potential must use absolute mean.')
    g=cache[2];n=4;A=overlap(g['nums'],0);total=n*g['I']
    reject('replace-coordinate-by-total-influence',A/total>=F(3*2,8),
        {'A_over_I_i':str(A/g['I']),'A_over_total_I':str(A/total)},'Han uses single-coordinate influence, not FEI total influence.')
    # All five coordinates are essential, but the extra parity sign has zero overlap.
    mixed=[g['truth'][x&15]*(1 if x&16 else -1) for x in range(32)]
    mixed_nums=direct_spectrum(mixed)
    ratios=[overlap(mixed_nums,i)/physical_influence(mixed,i) for i in range(5)]
    reject('one-bad-coordinate-negates-exists-good',all(r>F(1,2) for r in ratios),
        {'all_coordinates_essential':all(physical_influence(mixed,i)>0 for i in range(5)),
         'all_five_ratios':[str(r) for r in ratios]},'Specified bad coordinates do not rule out another essential good coordinate.')
    N=64;and_ratio=2*(1-F(1,1<<(N-1)))
    reject('drop-adaptive-bias-control',and_ratio>=F(3*6,8),
        {'AND_64_ratio':str(and_ratio),'incorrect_depth6_lower':str(F(18,8))},'All-AND composition has ratio below two; the maintained bias interval matters.')
    parity=[(-1 if ((~x)&3).bit_count()%2 else 1) for x in range(4)]
    joined=[gate(parity[x&3],parity[x>>2],1) for x in range(16)]
    actual=restricted_distance(joined,0)/physical_influence(joined,0)
    incorrect=restricted_distance(parity,0)/physical_influence(parity,0)+4
    reject('apply-monotone-identity-to-parity',actual==incorrect,
        {'true_joined_R':str(actual),'wrong_monotone_formula':str(incorrect)},'For nonmonotone parity, first Fourier coefficient is not influence.')
    OUT['status']='PASS'
except BaseException as exc:
    OUT.update(status='FAIL',error=str(exc),traceback=traceback.format_exc());print(OUT['traceback'],flush=True)
finally:
    save();print(json.dumps({'status':OUT['status'],'run':str(RUN),
        'expected_rejections':len(OUT['expected_rejections']),'arbitrary_depth_formal_proof':False}),flush=True)
if OUT['status']!='PASS':sys.exit(1)
