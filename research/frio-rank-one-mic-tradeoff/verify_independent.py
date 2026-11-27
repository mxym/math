#!/usr/bin/env python3
"""Independent numerical FRIO brackets with a rank-one ray LP and PSD repair."""
import numpy as np
from scipy.optimize import linprog


def hermitian_basis(r):
    e = np.eye(r)
    basis = [np.outer(row,row) for row in e]
    for j in range(r):
        for k in range(j+1,r):
            h = np.outer(e[j], e[k])
            basis.extend([(h+h.T)/np.sqrt(2), 1j*(h-h.T)/np.sqrt(2)])
    return np.asarray(basis)


def rays(r, rng):
    if r == 1:
        return np.ones((1,1,1))
    if r == 2:
        count = 1400
        z = (2*np.arange(count)+1)/count-1
        ang = np.pi*(3-np.sqrt(5))*np.arange(count)
        vectors = np.column_stack([np.sqrt((1+z)/2), np.exp(1j*ang)*np.sqrt((1-z)/2)])
    else:
        raw = rng.normal(size=(3000,r))+1j*rng.normal(size=(3000,r))
        vectors = raw/np.linalg.norm(raw,axis=1)[:,None]
    vectors = np.vstack([vectors,np.eye(r)])
    return np.einsum("aj,ak->ajk", vectors, vectors.conj())


def ray_lp(lam, effects, q, projectors):
    # Restriction: every conclusive AND inconclusive effect is a positive
    # combination of the sampled projectors. No spectral filter is used here.
    r = len(lam)
    n = len(effects)
    rh = np.diag(lam)
    sigmas = np.sqrt(lam)[None,:,None]*effects[:,:r,:r].conj()*np.sqrt(lam)[None,None,:]
    basis = hermitian_basis(r)
    coords = np.einsum("jkl,alk->ja", basis, projectors).real
    total = np.tile(coords,(1,n+1))
    masses = np.einsum("j,ajj->a",lam,projectors).real
    rate = np.concatenate([np.tile(masses,n),np.zeros(len(masses))])
    rhs = np.r_[np.trace(basis,axis1=1,axis2=2).real,1-q]
    costc = np.einsum("ikl,alk->ia",sigmas,projectors).real.ravel()
    obj = np.r_[costc,np.zeros(len(masses))]
    out = linprog(-obj,A_eq=np.vstack([total,rate]),b_eq=rhs,bounds=(0,None),method="highs")
    assert out.success, out.message
    # Numerical lower witness: reconstruct the original effects and check
    # rate, normalization and positivity directly.
    weights = out.x.reshape(n+1,len(masses))
    assert np.min(weights) >= -1e-9
    primal = np.einsum("ia,akl->ikl",weights,projectors)
    assert np.linalg.norm(primal.sum(axis=0)-np.eye(r)) < 2e-7
    assert np.min(np.linalg.eigvalsh(primal)) > -1e-8
    assert abs(np.trace(rh@primal[:n].sum(axis=0)).real-(1-q)) < 2e-7
    lower = np.einsum("ikl,ilk->",sigmas,primal[:n]).real
    assert abs(lower+out.fun) < 2e-8
    # The ray LP's dual need not be PSD. Repair the actual matrix slacks,
    # including the reject slack, before using the upper bound.
    dual = -out.eqlin.marginals
    Y = np.einsum("k,kij->ij",dual[:-1],basis)
    mu = dual[-1]
    con = Y+mu*rh-sigmas
    shift = max(0,-np.min(np.linalg.eigvalsh(con)),-np.min(np.linalg.eigvalsh(Y)))+1e-10
    Y += shift*np.eye(r)
    assert np.min(np.linalg.eigvalsh(Y+mu*rh-sigmas)) > -1e-9
    assert np.min(np.linalg.eigvalsh(Y)) > -1e-9
    upper = np.trace(Y).real+mu*(1-q)
    assert lower <= upper+1e-8
    return lower,upper


def fourier(d,n):
    return np.exp(2j*np.pi*np.outer(np.arange(d),np.arange(n))/n)/np.sqrt(n)


def effect_table(v):
    return np.einsum("ai,bi->iab", v, v.conj())


def spectral_value(lam,n,q):
    # Sorted prefix formula, not cap-threshold root finding.
    if q == 1:
        return 0.0
    ascending = np.sort(lam)
    for t in range(len(lam),0,-1):
        clipped = (sum(ascending[-t:])-q)/t
        hi = ascending[-t]
        lo = 0 if t == len(lam) else ascending[-t-1]
        if lo-1e-12 <= clipped <= hi+1e-12:
            return (t*np.sqrt(max(0,clipped))+np.sqrt(ascending[:-t]).sum())**2/n
    raise AssertionError("no valid clipping prefix")


def rank_one_mic_path(d,t):
    gen = [np.eye(d,dtype=complex)[:,j] for j in range(d)]
    for j in range(d):
        for k in range(j+1,d):
            gen += [gen[j]+gen[k],gen[j]+1j*gen[k]]
    w = (1-t)*fourier(d,d*d)+t*np.column_stack(gen)
    evals, basis = np.linalg.eigh(w@w.conj().T)
    assert evals.min() > 1e-11
    norm = (basis*evals**(-.5))@basis.conj().T
    return effect_table(norm@w)


def check():
    rng = np.random.default_rng(28041)
    cache = {r:rays(r,rng) for r in (1,2,3)}
    tight = 0
    for d,n,lam,qs in [
        (1,1,[1.0],[0,.27,1]),
        (3,5,[1.0],[0,.5,1]),
        (2,2,[.64,.36],[0,.1,.28,.73,1]),
        (3,5,[.64,.36],[0,.1,.28,.73,1]),
        (4,7,[.52,.29,.19],[0,.1,.23,.43,.82,1]),
        (3,3,[.4,.4,.2],[0,.15,.4,.7,1]),
    ]:
        lam = np.asarray(lam)
        M = effect_table(fourier(d,n))
        assert np.linalg.norm(M.sum(axis=0)-np.eye(d)) < 1e-12
        for q in qs:
            lower,upper = ray_lp(lam,M,q,cache[len(lam)])
            target = spectral_value(lam,n,q)
            assert lower <= target+5e-8 <= upper+1e-7
            assert target-lower < .04 and upper-target < .05
            tight += 1

    # Negative control in a complete rank-one tomography example. These
    # are independently supplied tetrahedral effects, not derived from A.
    xyz = np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]])/np.sqrt(3)
    pauli = np.array([[[0,1],[1,0]],[[0,-1j],[1j,0]],[[1,0],[0,-1]]])
    tetra = (np.eye(2)+np.einsum("jk,kab->jab",xyz,pauli))/4
    assert np.linalg.matrix_rank(np.einsum("jab,kba->jk",tetra,hermitian_basis(2)).real) == 4
    assert np.max(abs(np.linalg.eigvalsh(tetra)-[0,.5])) < 1e-12
    lam = np.array([.98,.02])
    bad_lower,_ = ray_lp(lam,tetra,0,cache[2])
    plateau_lower,plateau_upper = ray_lp(lam,tetra,.98,cache[2])
    target = spectral_value(lam,4,0)
    assert bad_lower > target+.01
    assert plateau_lower <= .01+5e-8 <= plateau_upper+1e-7 and plateau_upper < .012
    b = np.sqrt(lam)/sum(np.sqrt(lam))-.5
    rhs = 4*(1/6)*(b@b)/4
    assert bad_lower/target-1 > rhs

    # A distinct MIC was balanced for the nonflat Q=0 value, rather
    # than for the support plateau. Test both scores with the ray LP.
    lam = np.array([.64,.36])
    v = []
    for sign,phase in [(1,1),(-1,1j)]:
        x = .25 + sign*.17
        y = .25 - sign*.17*4/3
        v.extend([[np.sqrt(x), phase*np.sqrt(y)], [np.sqrt(x), -phase*np.sqrt(y)]])
    tuned = effect_table(np.array(v).T)
    assert np.linalg.norm(tuned.sum(axis=0)-np.eye(2)) < 1e-12
    assert np.linalg.matrix_rank(np.einsum("jab,kba->jk",tuned,hermitian_basis(2)).real) == 4
    lo,hi = ray_lp(lam,tuned,0,cache[2])
    target = spectral_value(lam,4,0)
    assert lo <= target+1e-8 <= hi+2e-8 and target-lo < .002 and hi-target < .002
    lo,_ = ray_lp(lam,tuned,.5,cache[2])
    assert lo > spectral_value(lam,4,.5)+.001

    # Density and effectwise control near a Fourier POVM, for a singular
    # source as well as the full-rank case. In dimension one there is no
    # nontrivial tomography obstruction.
    leeway_cases = 0
    for d in [2,3,4]:
        n = d*d
        F = effect_table(fourier(d,n))
        bf = hermitian_basis(d)
        coord = lambda X: np.einsum("iab,jba->ij",X,bf).real
        assert np.linalg.matrix_rank(coord(F)) < n
        lam = np.array([.81,.19])
        lam_max_ratio = lam[0]/lam[1]
        distances = []
        for t in [.04,.004,.0004]:
            M = rank_one_mic_path(d,t)
            assert np.linalg.norm(M.sum(axis=0)-np.eye(d)) < 3e-12
            assert np.linalg.matrix_rank(coord(M)) == n
            dist = np.max(abs(np.linalg.eigvalsh(M-F)))
            distances.append(dist)
            for q in [0,.2,.65,.95,.995]:
                lo,hi = ray_lp(lam,M,q,cache[2])
                base = spectral_value(lam,n,q)
                assert lo <= base*(1+n*lam_max_ratio*dist)+1e-8
                assert hi >= base-1e-8
                leeway_cases += 1
        assert distances[0] > 5*distances[1] > 25*distances[2]
    print(f"independent PASS: {tight} linear-program / PSD-repaired brackets, including both endpoints")
    print("independent PASS: two distinct single-rate MICs, strict endpoint gaps and tomography control")
    print(f"independent PASS: 3 MIC density paths and {leeway_cases} rate-stability brackets")


if __name__ == "__main__":
    check()
