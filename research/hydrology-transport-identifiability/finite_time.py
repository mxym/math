#!/usr/bin/env python3
"""Finite-dwell reconstruction: synthetic numerical check, not a proof.
Uses sampled impulse kernels and three short middle dwells, not high-order
response derivatives. Theorem 5 gives the exact mathematical statement.
"""
from __future__ import annotations
import argparse
import json
import warnings
from pathlib import Path
import numpy as np
from scipy.linalg import expm, logm
from exact import family, Q, E, B, D


def arrays(theta):
    k0, k1 = (np.asarray(v, dtype=float) for v in family(theta))
    q, e, b = (np.asarray(v, dtype=float).ravel() for v in (Q, E, B))
    a = k0 - np.diag(q)
    return a, a + k1 - np.diag(e), a + k1, b, q, e, k0, k1


def kernel_data(a, gw, gz, b, q, h, dwell):
    n = len(b)
    f = expm(h*a)
    r = np.column_stack([np.linalg.matrix_power(f, j)@b for j in range(n)])
    o = np.vstack([q@np.linalg.matrix_power(f, j) for j in range(n)])
    return o@r, [o@expm(dwell*g)@r for g in (a, gw, gz)], q@r


def recover(hankel, insertions, chat, dwell):
    # Only measured kernel data are passed into this function. In particular,
    # neither true rates nor contrast eigenvalues are used in reconstruction.
    hats = [logm(np.linalg.solve(hankel, j))/dwell for j in insertions]
    if any(np.max(np.abs(np.imag(g))) > 1e-7 for g in hats):
        raise ValueError('Nonreal recovered generator')
    a, gw, gz = [np.real(g) for g in hats]
    values, v = np.linalg.eig(gz-gw)
    if np.max(np.abs(np.imag(values))) > 1e-7:
        raise ValueError('Nonreal contrast spectrum')
    v = np.real(v[:, np.argsort(np.real(values))])
    ell = -np.linalg.solve(a.T, chat)
    normalization = ell@v
    if np.min(np.abs(normalization)) < 1e-12:
        raise ValueError('Failed conservation normalization')
    v /= normalization
    ar = np.linalg.solve(v, a@v)
    wr = np.linalg.solve(v, (gw-a)@v)
    zr = np.linalg.solve(v, (gz-a)@v)
    qr, er, gr = chat@v, -wr.sum(axis=0), -zr.sum(axis=0)
    return {'K0': ar+np.diag(qr), 'K1': wr+np.diag(er),
            'b': np.linalg.solve(v, np.eye(len(chat))[:, 0]),
            'q': qr, 'e': er, 'g': gr}


def run(directory):
    directory.mkdir(parents=True, exist_ok=True)
    rows=[]
    for theta in [0, .1]:
        a, gw, gz, b, q, e, k0, k1 = arrays(theta)
        bound=max(np.linalg.norm(g, 1) for g in [a, gw, gz])
        if bound >= np.log(2): raise RuntimeError('Short-dwell condition failed')
        order=np.argsort(e)
        truth={'K0': k0[np.ix_(order, order)], 'K1': k1[np.ix_(order, order)],
               'b': b[order], 'q': q[order], 'e': e[order], 'g': np.zeros(4)}
        for h in [1, 3, 5, 10, 15, 20]:
            hh, jj, cc=kernel_data(a, gw, gz, b, q, h, 1.)
            with warnings.catch_warnings(record=True) as captured:
                warnings.simplefilter('always')
                got=recover(hh, jj, cc, 1.)
            err=max(float(np.max(np.abs(got[k]-truth[k]))) for k in truth)
            rows.append({'theta':theta,'baseline_gap_days':h,'middle_dwell_days':1,
                         'hankel_condition_number':float(np.linalg.cond(hh)),
                         'maximum_absolute_coefficient_error':err,
                         'generator_norm_bound_times_dwell':float(bound),
                         'warnings':[str(w.message) for w in captured]})
            if h==10 and err > 1e-7: raise RuntimeError('Noiseless reconstruction failed')
    report={'status':'PASS','scope':'Synthetic floating-point finite-dwell reconstruction; not field calibration',
            'unknown_parameters_used_by_recover':False,'coefficient_units':'day^-1; input weights dimensionless',
            'warning':'Even the better-spaced Hankel system is ill-conditioned; no noisy robustness claim',
            'experiments':rows}
    (directory/'finite_time.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2,sort_keys=True))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output-dir',type=Path,default=Path(__file__).parent/'results')
    run(p.parse_args().output_dir)
