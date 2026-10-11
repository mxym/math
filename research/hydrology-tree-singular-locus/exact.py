#!/usr/bin/env python3
"""Exact finite diagnostics for the all-tree singular-locus proof.

Uses integer matrices, exact Faddeev--LeVerrier coefficient derivatives and
fraction-free determinants. These checks support, but do not replace, the
arbitrary-size written proof. No third-party package is required.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
import math
from functools import lru_cache
from pathlib import Path


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ArithmeticError(message)


def mm(A, B):
    return [[sum(a*b for a,b in zip(row, col)) for col in zip(*B)] for row in A]


def determinant(M):
    """Bareiss elimination over integers, with explicit exact-divisibility checks."""
    n = len(M)
    if n == 0:
        return 1
    A = [list(row) for row in M]
    sign, old = 1, 1
    for k in range(n-1):
        p = next((j for j in range(k,n) if A[j][k]), None)
        if p is None:
            return 0
        if p != k:
            A[p], A[k] = A[k], A[p]
            sign = -sign
        pivot = A[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                q, r = divmod(A[i][j]*pivot-A[i][k]*A[k][j], old)
                require(r == 0, 'Bareiss division is not exact')
                A[i][j] = q
            A[i][k] = 0
        old = pivot
    return sign*A[-1][-1]


def charpoly_and_derivatives(A, directions):
    """Coefficients of det(sI-A), highest first, and their exact gradients.

    dc_k[A](E)=-tr(B_(k-1) E). This differentiates the actual characteristic
    polynomial, without using the proposed tree factorization or recurrence.
    """
    n = len(A)
    B = [[int(i == j) for j in range(n)] for i in range(n)]
    coeff, jac = [1], []
    for k in range(1,n+1):
        jac.append([-sum(B[i][j]*E[j][i] for i in range(n) for j in range(n))
                    for E in directions])
        AB = mm(A, B)
        val, rem = divmod(-sum(AB[i][i] for i in range(n)), k)
        require(rem == 0, 'Characteristic coefficient not integral')
        coeff.append(val)
        B = [[AB[i][j] + (val if i == j else 0) for j in range(n)] for i in range(n)]
    require(all(x == 0 for row in B for x in row), 'Cayley--Hamilton residual')
    return coeff, jac


def submatrix(A, indices):
    return [[A[i][j] for j in indices] for i in indices]


def resultant(f, g):
    """Sylvester determinant. Coefficients ordered highest first."""
    m, n = len(f)-1, len(g)-1
    if m == 0:
        return f[0]**n
    if n == 0:
        return g[0]**m
    S = [[0]*(m+n) for _ in range(m+n)]
    for i in range(n):
        S[i][i:i+m+1] = f
    for j in range(m):
        S[n+j][j:j+n+1] = g
    return determinant(S)


@lru_cache(None)
def rooted_shapes(n):
    """All unlabeled rooted trees, as multisets of recursively encoded children."""
    if n == 1:
        return ((),)
    candidates = [(k,t) for k in range(1,n) for t in rooted_shapes(k)]
    out = []
    def rec(left, start, acc):
        if left == 0:
            out.append(tuple(acc)); return
        for i in range(start,len(candidates)):
            size, tree = candidates[i]
            if size > left:
                break
            rec(left-size, i, acc+[tree])
    rec(n-1, 0, [])
    return tuple(out)


def edges_of_shape(shape):
    edges, vertices = [], [0]
    def add(tree, parent):
        for child in tree:
            vertex = len(vertices)
            vertices.append(vertex); edges.append((parent,vertex))
            add(child, vertex)
    add(shape,0)
    return edges


def orient(n, edges, root):
    adj = [[] for _ in range(n)]
    for u,v in edges:
        adj[u].append(v); adj[v].append(u)
    parent, order = {root:None}, [root]
    for v in order:
        for w in adj[v]:
            if w not in parent:
                parent[w] = v; order.append(w)
    require(len(order)==n, 'Tree disconnected')
    children = {v:[] for v in range(n)}
    for v in order[1:]:
        children[parent[v]].append(v)
    subtree = {}
    for v in reversed(order):
        subtree[v] = [v] + [x for c in children[v] for x in subtree[c]]
    return parent, children, subtree


def physical_matrix(n, edges, rates, leak_vertex, leak_rate):
    A = [[0]*n for _ in range(n)]
    directions = []
    E = [[0]*n for _ in range(n)]; E[leak_vertex][leak_vertex] = -1
    directions.append(E)
    A[leak_vertex][leak_vertex] -= leak_rate
    for src,dst in [(u,v) for u,v in edges]+[(v,u) for u,v in edges]:
        a = rates[src,dst]
        A[dst][src] += a; A[src][src] -= a
        E = [[0]*n for _ in range(n)]
        E[dst][src] = 1; E[src][src] = -1
        directions.append(E)
    return A, directions


def tree_factors(A, edges, rates, root, leak_vertex):
    n = len(A)
    parent, children, subtree = orient(n,edges,root)
    pl, _, _ = orient(n,edges,leak_vertex)
    directed = math.prod(rates[v,pl[v]] for v in range(n) if v != leak_vertex)
    edgepart = math.prod((rates[parent[v],v]*rates[v,parent[v]])**(len(subtree[v])-1)
                         for v in range(n) if v != root)
    polys = {v:charpoly_and_derivatives(submatrix(A,subtree[v]),[])[0] for v in range(n)}
    branch = math.prod(resultant(polys[a],polys[b])**2
                       for v in range(n) for a,b in itertools.combinations(children[v],2))
    return directed*edgepart*branch, branch


def one_case(n, edges, root, leak_vertex, fixture):
    directed = [(u,v) for u,v in edges]+[(v,u) for u,v in edges]
    if fixture == 0:
        vals = [2+3*i+i*i for i in range(len(directed))]
    elif fixture == 1:
        vals = [(-1 if i%3==0 else 1)*(3+5*i) for i in range(len(directed))]
    elif fixture == 2:
        vals = [1]*len(directed)
    else:
        vals = [2+3*i+i*i for i in range(len(directed))]
        if directed:
            vals[0 if fixture == 3 else len(edges)] = 0
    rates = dict(zip(directed,vals))
    A, E = physical_matrix(n,edges,rates,leak_vertex,7+fixture)
    P, Jp = charpoly_and_derivatives(A,E)
    ix = [v for v in range(n) if v != root]
    Q, Jq = charpoly_and_derivatives(submatrix(A,ix),[submatrix(e,ix) for e in E])
    observed = determinant(Jp+Jq)
    predicted, branch = tree_factors(A,edges,rates,root,leak_vertex)
    require(observed**2 == predicted**2, f'Jacobian mismatch {n,edges,root,leak_vertex,fixture}')
    pl, _, _ = orient(n,edges,leak_vertex)
    away = math.prod(rates[pl[v],v] for v in range(n) if v != leak_vertex)
    res = resultant(P,Q)
    require((observed*away)**2 == res**2, 'Full resultant identity fails')
    # Independent sensitivity diagnostic: the actual root observability and reachability matrices.
    er = [int(v==root) for v in range(n)]
    R, O = [], []
    col, row = er, er
    for _ in range(n):
        R.append(col); O.append(row)
        col = [sum(A[i][j]*col[j] for j in range(n)) for i in range(n)]
        row = [sum(row[i]*A[i][j] for i in range(n)) for j in range(n)]
    require((determinant(R)*determinant(O))**2 == res**2, 'Minimality/resultant check fails')
    return observed, predicted, branch


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n',type=int,default=8)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    require(1 <= args.max_n <= 9, 'Choose max-n from 1 to 9')
    rows, total, zeros = [], 0, 0
    for n in range(1,args.max_n+1):
        for number, tree in enumerate(rooted_shapes(n)):
            edges = edges_of_shape(tree)
            for leak in range(n):
                sign = None
                for fixture in range(5):
                    obs,pred,branch = one_case(n,edges,0,leak,fixture)
                    if pred:
                        ratio = obs//pred
                        require(ratio in (-1,1), 'Not an orientation sign')
                        if sign is None:
                            sign=ratio
                        require(sign==ratio, 'Orientation sign depends on rates')
                    else:
                        zeros += 1
                    rows.append([n,number,leak,fixture,str(obs),str(pred)])
                    total+=1
    # Mutation controls are genuine comparisons with direct Jacobian values.
    rejected = []
    for name, edges, transform in [
        ('omit_return_rate', [(0,1)], lambda f,b:f//6),
        ('halve_branch_multiplicity', [(0,1),(0,2)], lambda f,b:f//math.isqrt(b)),
        ('erase_internal_edge_powers', [(0,1),(1,2)], lambda f,b:f//(2*12)),
    ]:
        n=len(edges)+1
        obs,pred,branch=one_case(n,edges,0,0,0)
        bad=transform(pred,branch)
        require(obs**2 != bad**2, 'Mutation unexpectedly accepted: '+name)
        rejected.append(name)
    # Wrongly closing each deleted-root branch removes its boundary killing.
    # On this star both closed one-vertex polynomials become z, falsely
    # predicting a collision for every choice of rates.
    obs,pred,_=one_case(3,[(0,1),(0,2)],0,0,0)
    wrong=12*20*resultant([1,0],[1,0])**2
    require(obs != 0 and wrong == 0, 'Boundary-diagonal mutation not exposed')
    rejected.append('delete_branch_boundary_loss')
    report={
        'status':'PASS', 'scope':'Exact finite diagnostics, not the arbitrary-size proof',
        'rooted_shape_counts':{str(n):len(rooted_shapes(n)) for n in range(1,args.max_n+1)},
        'matrix_jacobian_cases':total, 'singular_cases':zeros,
        'signed_fixture_orientation_consistency':True,
        'fixtures':['positive','signed','all_equal','zero_forward_edge','zero_reverse_edge'],
        'full_resultant_and_minimality_checks':total,
        'rejected_controls':rejected,
        'case_digest_sha256':hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest(),
    }
    text=json.dumps(report,indent=2,sort_keys=True)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
