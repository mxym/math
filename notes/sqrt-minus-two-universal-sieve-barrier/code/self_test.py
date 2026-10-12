#!/usr/bin/env python3
"""Negative controls for exact connected-shape and modular translations."""
import copy,json,contextlib,io
import check


def reject(label,S,T,edit):
    points=copy.deepcopy(S);local=copy.deepcopy(T)
    edit(points,local)
    with contextlib.redirect_stdout(io.StringIO()):
        try:check.verify(points,local)
        except (ValueError,TypeError,KeyError):pass
        else:raise RuntimeError('mutation undetected: '+label)
    print('REJECTED:',label)

if __name__=='__main__':
    S=json.loads((check.DIR/'connected_shape.json').read_text())
    T=json.loads((check.DIR/'local_shifts.json').read_text())
    reject('deleted shape point',S,T,lambda s,t:s.pop())
    reject('repeated shape point',S,T,lambda s,t:s.__setitem__(0,s[1]))
    reject('missing small-prime certificate',S,T,lambda s,t:t.pop('19'))
    reject('nonprime index inserted',S,T,lambda s,t:t.update({'4':[0,0]}))
    reject('fabricated norm-zero local shift at p19',S,T,
           lambda s,t:t.__setitem__('19',[(-s[0][0])%19,(-s[0][1])%19]))
    print('ALL NEGATIVE CONTROLS PASSED')
