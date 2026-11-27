#!/usr/bin/env python3
"""Direct complex-matrix checks using Schmidt references and detector effects."""
import numpy as np
from math import sqrt

rng = np.random.default_rng(69173)
TOL = 5e-7

def herm(a):
    return (a+a.conj().T)/2

def raw(n):
    return rng.normal(size=(n,n))+1j*rng.normal(size=(n,n))

def density(n, rank):
    a = raw(n)[:, :rank]
    r = a @ a.conj().T
    return r/np.trace(r)

def root(a):
    val, vec = np.linalg.eigh(herm(a))
    assert np.min(val) >= -TOL
    return (vec*np.sqrt(np.maximum(val, 0))) @ vec.conj().T

def tn(a):
    return float(np.linalg.svd(a, compute_uv=False).sum())

def trace_dist(a,b):
    return tn(a-b)/2

def effect_on_s(n, tau, dim_s):
    # Weighted partial trace in the memory eigenbasis, independently of the
    # commutator computation.
    val, vec = np.linalg.eigh(tau)
    return sum(p*(v.conj().T @ n @ v)
               for p,k in zip(val,vec.T)
               for v in [np.kron(np.eye(dim_s),k[:,None])])

def eve_states(xi, n):
    # Prepare Schmidt amplitudes on signal/memory : Eve, apply each square
    # root Kraus operator on the former, and discard its output.
    val, vec = np.linalg.eigh(herm(xi))
    psi = vec * np.sqrt(np.maximum(0,val))
    ret = []
    for eff in (n,np.eye(len(n))-n):
        v = root(eff) @ psi
        ret.append(v.T @ v.conj())
    assert abs(np.trace(ret[0]+ret[1])-1) < TOL
    return ret

def bias(xi, n):
    a,b = eve_states(xi,n)
    return tn(a-b)

def effect(n):
    u,_ = np.linalg.qr(raw(n))
    vals = rng.uniform(0,1,n)
    if n>1:
        vals[0],vals[1] = 0,1
    return (u*vals) @ u.conj().T

N = 0
for dim_s,dim_d in [(2,1),(2,2),(2,3),(3,2),(4,3),(5,2)]:
    for i in range(12):
        tau = density(dim_d, 1+i%dim_d)
        rho = density(dim_s, 1+(i//2)%dim_s)
        xi = np.kron(rho,tau)
        n = effect(dim_s*dim_d)
        m = effect_on_s(n,tau,dim_s)
        c = tn(rho @ m-m @ rho)

        # Reflection on the enlarged memory. In this block ordering the
        # private dilation qubit precedes signal/memory; xi1 is its zero block.
        k = 2*n - np.eye(len(n))
        j = np.block([[k,root(np.eye(len(n))-k@k)],
                      [root(np.eye(len(n))-k@k),-k]])
        xi1 = np.kron(np.diag([1,0]),xi)
        assert tn(j@j-np.eye(len(j))) < TOL
        reflected = j @ xi1 @ j
        dd = trace_dist(xi1,reflected)
        g = bias(xi,n)
        assert abs(g-tn(root(xi1) @ root(reflected))) < TOL
        assert abs(g-bias(xi1,(np.eye(len(j))+j)/2)) < TOL
        assert c <= dd+TOL and g*g+dd*dd <= 1+TOL
        # Independent anticommutator observable identity; no purification
        # or fidelity inequality is needed for the corresponding proof.
        val, vec = np.linalg.eigh(1j*(rho @ m-m @ rho))
        sign = np.sign(val) * (abs(val) > 1e-13)
        q = (vec*sign) @ vec.conj().T
        q = np.kron(np.eye(2),np.kron(q,np.eye(dim_d)))
        com = .5j*(j@q-q@j)
        assert tn(j@com+com@j) < TOL
        assert np.max(abs(np.linalg.eigvalsh(herm(com)))) <= 1+TOL
        assert abs(np.trace(xi1@com)-c) < TOL
        N += 1
print(f"direct complex product purifications, dilations, and anticommutation: {N} PASS")

I = np.eye(2)
X = np.array([[0,1],[1,0]])
Y = np.array([[0,-1j],[1j,0]])
Z = np.diag([1,-1])
x_plus, x_minus = (I+X)/2, (I-X)/2
N = 0
for r in (0.,.17,.6,.93,1.):
    for q in (0.,.21,.56,.9,1.):
        for phase in (0.,.32,1.47,3.12):
            zfrac = rng.uniform(-1,1)
            t,y = q*np.cos(phase),q*np.sin(phase)
            s = sqrt(1-q*q)
            z = s*zfrac
            w = (1+zfrac)/2
            rho = (I+r*Z)/2
            branches = [t*X+y*Y+s*Z,t*X+y*Y-s*Z]
            tau = np.diag([w,1-w])
            j = np.kron(branches[0],np.diag([1,0])) + np.kron(branches[1],np.diag([0,1]))
            n = (np.eye(4)+j)/2
            m = effect_on_s(n,tau,2)
            assert tn(m-(I+t*X+y*Y+z*Z)/2) < TOL
            assert abs(np.trace(x_plus@m)-np.trace(x_minus@m)-t) < TOL
            assert abs(np.trace(rho@m)-(1+r*z)/2) < TOL
            assert abs(bias(np.kron(rho,tau),n)**2 - (1-r*r*q*q)) < TOL
            N += 1
print(f"complex flagged saturators, endpoints, and raw observed probabilities: {N} PASS")

N = 0
for r in (.4,.6,.9,1.):
    for t in (-.9,-.7,.7,.9):
        rho = (I+r*Z)/2
        tau = np.diag([.7,.3])
        s = sqrt(1-t*t)
        j = np.kron(t*X,I) + np.kron(s*Z,Z)
        n = (np.eye(4)+j)/2
        base = [np.kron(a,tau) for a in (rho,x_plus,x_minus)]
        trials = [(.01,.02,.03),(.02,.04,.01),(.15,.20,.15)]
        for fractions in trials:
            # Sample arbitrary small correlated perturbations of each joint
            # marginal. Feed precisely the achieved trace distances.
            states = [(1-v)*a+v*density(4,2) for v,a in zip(fractions,base)]
            eta = [trace_dist(a,b) for a,b in zip(states,base)]
            tobs = abs(np.trace(n@(states[1]-states[2])))
            lower_d = max(0,r*max(0,tobs-eta[1]-eta[2])-2*eta[0])
            actual_d = trace_dist(states[0],j@states[0]@j)
            assert lower_d <= actual_d + TOL
            assert bias(states[0],n)**2+lower_d**2 <= 1+TOL
            N += 1
assert lower_d > .1  # ensure even the last fixture is not vacuous
print(f"declared trace-distance perturbed-marginal certificates: {N} PASS")

# A known commuting diagonal effect has a saturating independent realization.
rho = np.diag([.3,.7])
tau = np.diag([.2,.55,.25])
n = np.diag([1.,1.,0.,1.,0.,0.])
m = effect_on_s(n,tau,2)
assert tn(rho@m-m@rho) < TOL
assert abs(bias(np.kron(rho,tau),n)-1) < TOL
print("commuting-effect attainable zero-entropy baseline: PASS")
