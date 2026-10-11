#!/usr/bin/env python3
"""Synthetic tests only: no measured catchment data and no forecast-skill claim.
Daily forcing is piecewise constant; states and flux integrals use matrix
exponentials, not an Euler approximation. Float results are illustrations,
not proof certificates. Requires numpy and scipy.
"""
from __future__ import annotations
import argparse
import csv
import json
import platform
from pathlib import Path
import numpy as np
import scipy
from scipy.linalg import expm
from scipy.optimize import minimize_scalar
from exact import family, Q, E, B, A, D, K, moments

def arr(a): return np.array(a,dtype=float)

def forcing(days=730):
    rng=np.random.default_rng(20261011)
    day=np.arange(days)
    p=np.where(rng.random(days)<.30,rng.gamma(1.8,5.0,days),0.0)
    # A controlled, synthetic five-level demand experiment, not observed PET.
    u=np.round(4*(.5+.45*np.sin(2*np.pi*day/365)))/4
    cin=.8+.25*np.cos(2*np.pi*day/79)
    cin[(day%97)<3]+=2
    return p,u,cin

def simulate(theta,p,u,cin,rho=0.0,et_scale=1.0):
    k0,k1=family(theta)
    # family(theta) has K1 = D - T D T^-1; scaling e scales this coefficient.
    k0=arr(k0);k1=et_scale*arr(k1)
    q,e,b=arr(Q)[0],et_scale*arr(E)[0],arr(B)[:,0]
    x=np.zeros(4);zw=np.zeros(4);zs=np.zeros(4)
    output=[];cache={};total=np.zeros(4)
    for pp,uu,cc in zip(p,u,cin):
        if uu not in cache:
            kk=k0+uu*k1;aw=kk-np.diag(q+uu*e);az=kk-np.diag(q+rho*uu*e)
            def affine(aa):
                aug=np.zeros((5,5));aug[:4,:4]=aa;aug[:4,4]=b
                ep=expm(aug);return ep[:4,:4],ep[:4,4]
            mw,gw=affine(aw);ms,gs=affine(az)
            aug=np.zeros((9,9));aug[:4,:4]=aw;aug[:4,4]=b
            aug[5,:4]=q;aug[6,:4]=uu*e
            aug[7,0]=kk[2,0];aug[8,0]=kk[3,0]
            ep=expm(aug);cache[uu]=(mw,gw,ms,gs,ep[5:9,:5])
        mw,gw,ms,gs,integ=cache[uu]
        total+=integ@np.r_[x,pp]
        x=mw@x+gw*pp;zw=mw@zw+gw*pp*cc;zs=ms@zs+gs*pp*cc
        output.append(np.r_[q@x,uu*e@x,x.sum(),q@zw,q@zs,x])
    return np.asarray(output),total

def run(directory:Path):
    directory.mkdir(parents=True,exist_ok=True)
    p,u,cin=forcing();base,base_int=simulate(0,p,u,cin)
    reports=[]
    for theta in [-.09,.10,.12]:
        pred,integrals=simulate(theta,p,u,cin)
        errors=np.max(np.abs(pred[:,:4]-base[:,:4]),axis=0)
        balance=abs(float(np.sum(p)-integrals[0]-integrals[1]-pred[-1,2]))
        reports.append({'theta':theta,'max_abs_water_output_error':errors[:3].tolist(),
                        'max_abs_cotransported_tracer_load_error':float(errors[3]),
                        'retained_solute_relative_rms_difference':float(np.linalg.norm(pred[:,4]-base[:,4])/np.linalg.norm(base[:,4])),
                        'cumulative_1_to_3':float(integrals[2]),'cumulative_1_to_4':float(integrals[3]),
                        'relative_1_to_3_change':float(integrals[2]/base_int[2]-1),
                        'relative_1_to_4_change':float(integrals[3]/base_int[3]-1),
                        'minimum_water_storage':float(pred[:,5:].min()),
                        'water_balance_residual':balance})
        if errors.max()>1e-9 or balance>1e-8 or pred[:,5:].min() < -1e-10:
            raise RuntimeError('Numerical invariance, positivity or water balance check failed')
    grid=np.linspace(-.099,.124,81)
    curves=[];scale=np.mean(base[:,:4]**2,axis=0)
    for theta in grid:
        pred,_=simulate(float(theta),p,u,cin)
        wl=float(np.sum(np.mean((pred[:,:4]-base[:,:4])**2,axis=0)/scale))
        sl=float(np.mean((pred[:,4]-base[:,4])**2)/np.mean(base[:,4]**2))
        curves.append([theta,wl,sl])
    with (directory/'loss_curve.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['theta','water_and_cotransport_loss','retained_solute_loss']);w.writerows(curves)
    pred,_=simulate(.1,p,u,cin)
    with (directory/'synthetic_series.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['day','rain','demand','source_concentration','Q_true','Q_alternative','ET_true','storage_true','retained_true','retained_alternative'])
        w.writerows(np.c_[np.arange(len(p)),p,u,cin,base[:,0],pred[:,0],base[:,1],base[:,2],base[:,4],pred[:,4]])
    # One-parameter calibration is intentionally restricted to the exact
    # observational-equivalence family. This is not full network calibration.
    noiseless=minimize_scalar(lambda t:np.mean((simulate(float(t),p,u,cin)[0][:365,4]-base[:365,4])**2),
                               bounds=(-.099,.124),method='bounded',options={'xatol':1e-12})
    rng=np.random.default_rng(8821);fitted=[]
    sigma=.01*np.sqrt(np.mean(base[:365,4]**2))
    for _ in range(20):
        obs=base[:365,4]+rng.normal(0,sigma,365)
        objective=lambda t:np.mean((simulate(float(t),p[:365],u[:365],cin[:365])[0][:,4]-obs)**2)
        opt=minimize_scalar(objective,bounds=(-.099,.124),method='bounded',options={'xatol':1e-9})
        if not opt.success:raise RuntimeError('Calibration failed')
        fitted.append(float(opt.x))
    # Independent structural/practical diagnostic: raw Hankel moments can be
    # ill-conditioned even when the exact reconstruction theorem applies.
    data=moments(A,B,Q,[[-x for x in row] for row in D],[[0]*4 for _ in range(4)])
    contrast=[]
    for rho in [0,.5,.9,.99,1]:
        a,_=simulate(0,p,u,cin,rho=rho);b1,_=simulate(.1,p,u,cin,rho=rho)
        contrast.append({'ET_tracer_partition':rho,'relative_rms_difference':float(np.linalg.norm(a[:,4]-b1[:,4])/np.linalg.norm(a[:,4]))})
    report={'status':'PASS','data_kind':'Entirely synthetic; no basin observations',
            'integrator':'scipy.linalg.expm, exact constant-forcing linear update up to floating point',
            'seed_forcing':20261011,'days':len(p),'training_days':365,'holdout_days':365,
            'baseline_internal_flux_totals':{'1_to_3':float(base_int[2]),'1_to_4':float(base_int[3])},
            'equivalent_models':reports,'noiseless_theta_estimate':float(noiseless.x),
            'noise_experiment':{'repetitions':20,'noise_sd_fraction_of_training_rms':.01,'theta_mean':float(np.mean(fitted)),
                               'theta_sd':float(np.std(fitted,ddof=1)),'theta_min':min(fitted),'theta_max':max(fitted),
                               'scope':'one-dimensional gauge family only; not full parameter recovery'},
            'partition_contrast_sweep':contrast,'raw_hankel_2norm_condition_number':float(np.linalg.cond(arr(data[1]))),
            'versions':{'python':platform.python_version(),'numpy':np.__version__,'scipy':scipy.__version__}}
    (directory/'synthetic.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2,sort_keys=True))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output-dir',type=Path,default=Path(__file__).parent/'results')
    run(p.parse_args().output_dir)
