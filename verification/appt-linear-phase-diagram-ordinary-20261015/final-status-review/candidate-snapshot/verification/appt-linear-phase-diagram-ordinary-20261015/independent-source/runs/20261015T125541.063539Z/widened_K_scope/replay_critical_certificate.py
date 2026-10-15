"""Replay every recorded exact box and verify complete rational partitions.
This is an author replay; it is not an independent scientific review.
"""
from pathlib import Path
from fractions import Fraction as F
import datetime as dt
import hashlib
import json
import critical_exact_intervals as m

folder=Path(__file__).parent
certpath=folder/'CRITICAL_EXACT_INTERVAL_CERTIFICATE.json'
cert=json.loads(certpath.read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert cert['source_sha256']==sha(folder/'critical_exact_intervals.py')
assert cert['parameters']['precision_bits']==m.PREC==160
assert cert['parameters']['exp_degree']==m.EXP_N==96
assert cert['parameters']['log_terms']==m.LOG_N==96
assert cert['parameters']['K_lower']==str(m.KL)
assert cert['parameters']['K_upper']==str(m.KU)

def stored(v):
    assert v['scale_bits']==m.PREC
    return m.I(int(v['lo']),int(v['hi']))

counts={}
def replay_cover(name,a,b,mode):
    leaves=cert[name]
    ordered=sorted(leaves,key=lambda p:F(p['x_lo']))
    assert ordered and F(ordered[0]['x_lo'])==a and F(ordered[-1]['x_hi'])==b
    for left,right in zip(ordered,ordered[1:]):assert F(left['x_hi'])==F(right['x_lo'])
    assert all(F(p['x_lo'])<F(p['x_hi']) for p in ordered)
    assert sum(F(p['x_hi'])-F(p['x_lo']) for p in leaves)==b-a
    for leaf in leaves:
        lo=F(leaf['x_lo']); hi=F(leaf['x_hi'])
        x=m.x_interval(lo,hi)
        K=m.I.frac(m.KU) if mode=='upper' else m.KBOX
        vals=m.scalar(K,x,second=(mode=='core'))
        method=leaf['method']
        if method=='inadmissible':
            assert vals['v'].hi<=0
            bound=vals['v']
        elif method=='strict_positive_W':
            assert mode=='upper'
            mid=(lo+hi)/2
            center=m.scalar(K,m.I.frac(mid))['W']
            bound=vals['W'].meet(center+vals['Wx']*(x-m.I.frac(mid)))
            assert bound.lo>m.I.rat(1,10000).hi
        elif method in ['W_excludes_zero','Wx_excludes_zero']:
            assert mode=='outside'
            bound=vals['W' if method=='W_excludes_zero' else 'Wx']
            assert bound.lo>0 or bound.hi<0
        elif method=='strict_positive_Wxx_and_admissible':
            assert mode=='core' and vals['v'].lo>0
            assert vals['v']==stored(leaf['admissible_v'])
            bound=vals['Wxx']
            assert bound.lo>m.I.rat(1,10).hi
        else:raise ValueError(method)
        assert bound==stored(leaf['bound'])
    counts[name]=len(leaves)

replay_cover('upper_full_cover',m.XL,m.XR,'upper')
replay_cover('outside_core_left',m.XL,m.CL,'outside')
replay_cover('outside_core_right',m.CR,m.XR,'outside')
replay_cover('core_convexity_cover',m.CL,m.CR,'core')

constants=cert['constants']
rupper=m.exp_i(m.data(m.I.frac(m.KU))['g'])-1
gplower=m.data(m.I.rat(9,20))['gp']
low_v=m.data(m.I.frac(m.KU*m.XL))['w']-m.data(m.I.frac(m.KL))['g']
log10=m.log_i(m.as_i(10))
assert rupper==stored(constants['r0_Kupper_below_one_twentieth'])
assert rupper.hi<m.I.rat(1,20).lo
assert gplower==stored(constants['gprime_9_over_20_above_11_over_100'])
assert gplower.lo>m.I.rat(11,100).hi
assert low_v==stored(constants['low_x_admissibility_upper']) and low_v.hi<0
assert log10==stored(constants['log10_below_five_halves']) and log10.hi<m.I.rat(5,2).lo
witness=m.scalar(m.I.frac(m.KL),m.I.rat(521,1000))
assert witness['W']==stored(cert['lower_witness']['W'])
assert witness['v']==stored(cert['lower_witness']['v'])
assert witness['v'].lo>0 and witness['W'].hi<m.I.rat(-1,5000).lo
left=m.scalar(m.KBOX,m.I.frac(m.CL))['Wx']
right=m.scalar(m.KBOX,m.I.frac(m.CR))['Wx']
assert left==stored(cert['core_derivatives']['left_Wx']) and left.hi<0
assert right==stored(cert['core_derivatives']['right_Wx']) and right.lo>0

paper=folder/'CRITICAL_UNIQUENESS_CERTIFICATE.md'
result={'utc':dt.datetime.now(dt.timezone.utc).isoformat(),
        'scope':'Author exact leaf replay, not independent review or Lean',
        'paper_sha256':sha(paper),'source_sha256':sha(folder/'critical_exact_intervals.py'),
        'certificate_sha256':sha(certpath),'replayer_sha256':sha(Path(__file__)),
        'leaf_counts':counts,'total_leaves':sum(counts.values()),
        'partitions_complete_with_no_gaps_or_overlaps':True,
        'all_stored_bounds_recomputed_exactly':True,
        'result':'AUTHOR_REPLAY_SUCCESS'}
dest=folder/'CRITICAL_CERTIFICATE_AUTHOR_REPLAY.json'
dest.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))
