#!/usr/bin/env python3
"""A second implementation; imports no author/search/verifier code.

Ring multiplication is polynomial long reduction; determinants use the Leibniz
formula; ideal membership uses exact Fraction Gaussian elimination. Quotient
edges and connected components are reconstructed from scratch. No assertions.
"""
import copy
import hashlib
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent

def need(ok, why):
    if not ok:
        raise ValueError(why)

def ints(value):
    if type(value) is list:
        return all(ints(x) for x in value)
    return type(value) is int

def vector(x):
    need(type(x) is list and len(x) == 3 and ints(x), 'not an integer 3-vector')
    return tuple(x)

def multiply(x, y):
    coefficients = [sum(x[i] * y[k-i] for i in range(3)
                        if 0 <= k-i < 3) for k in range(5)]
    for degree in range(4, 2, -1):
        coefficients[degree-3] += 2 * coefficients[degree]
        coefficients[degree] = 0
    return tuple(coefficients[:3])

def columns(alpha):
    return [multiply(alpha, tuple(int(i == j) for i in range(3)))
            for j in range(3)]

def matrix(alpha):
    c = columns(alpha)
    return [[c[j][i] for j in range(3)] for i in range(3)]

def determinant(a):
    result = 0
    for permutation in itertools.permutations(range(3)):
        inversions = sum(permutation[i] > permutation[j]
                         for i in range(3) for j in range(i+1, 3))
        result += (-1)**inversions * math.prod(a[i][permutation[i]]
                                              for i in range(3))
    return result

def divide_in_ring(x, alpha):
    rows = [[Fraction(z) for z in row] + [Fraction(b)]
            for row, b in zip(matrix(alpha), x)]
    for j in range(3):
        pivot = next((i for i in range(j, 3) if rows[i][j]), None)
        need(pivot is not None, 'singular principal ideal')
        rows[j], rows[pivot] = rows[pivot], rows[j]
        factor = rows[j][j]
        rows[j] = [v/factor for v in rows[j]]
        for i in range(3):
            if i != j:
                factor = rows[i][j]
                rows[i] = [v-factor*w for v, w in zip(rows[i], rows[j])]
    return tuple(row[-1] for row in rows)

def member(x, alpha):
    return all(v.denominator == 1 for v in divide_in_ring(x, alpha))

def verify(data, variant):
    need(type(data) is dict, 'bad root schema')
    expected_generators = [(0,1,0), (1,1,0), (1,0,1)]
    expected_steps = {(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)}
    if variant == 'F6':
        q, root, gamma_expected, sizes_expected = 30, 8, (2,3,1), [2,6]
        expected_format = 'cubic_crt_lift_certificate_v1'
    else:
        need(variant == 'F8', 'unknown variant')
        expected_generators += [(-1,1,1)]
        expected_steps |= {(0,1,1),(0,-1,-1)}
        q, root, gamma_expected, sizes_expected = 330, 128, (6,1,4), [6,9,9,56]
        expected_format = 'cubic_rank_one_f8_lift_certificate_v1'
    need(data['format'] == expected_format, 'bad format')
    need(data['order'] == {'basis':['1','theta','theta^2'],'relation':'theta^3=2'}, 'wrong order')
    generators = [vector(v) for v in data['generators']]
    need(generators == expected_generators, 'wrong generators')
    norms = [abs(determinant(matrix(v))) for v in generators]
    need(ints(data['generator_norms']) and data['generator_norms'] == norms,
         'wrong norm values/types')
    need(norms == ([2,3,5] if variant == 'F6' else [2,3,5,11]), 'bad independent norms')
    gamma = (1,0,0)
    for alpha in generators:
        gamma = multiply(gamma, alpha)
    need(gamma == vector(data['common_ideal_period_generator']) == gamma_expected,
         'wrong product ideal')
    need(type(data['quotient_modulus']) is int and data['quotient_modulus'] == q, 'bad q')
    row = vector(data['quotient_row'])
    need(row == (1,root,root*root % q) and pow(root,3,q) == 2, 'bad quotient ring map')
    phi = lambda x, modulus=q: sum(t*u for t,u in zip(row,x)) % modulus
    ideals = generators + [gamma]
    indices = norms + [q]
    for alpha, index in zip(ideals, indices):
        need(abs(determinant(matrix(alpha))) == index, 'index mismatch')
        need(all(phi(v,index) == 0 for v in columns(alpha)), 'kernel inclusion failed')
        # Inclusion + equal index + phi(1)=1 proves global kernel equality.
    box = list(itertools.product(range(-4,5), repeat=3))
    for point in box:
        for alpha, index in zip(ideals, indices):
            need(member(point,alpha) == (phi(point,index) == 0), 'independent membership failed')
    # An exact second route checks multiplication/index and norm polynomial.
    for point in box:
        a,b,c = point
        need(determinant(matrix(point)) == a**3+2*b**3+4*c**3-6*a*b*c,
             'determinant/norm polynomial disagreement')
    allowed = [s for s in range(q) if all(s % p for p in norms)]
    need(ints(data['allowed_states']) and data['allowed_states'] == allowed, 'wrong allowed states/types')
    need(allowed == [s for s in range(q) if math.gcd(s,q) == 1], 'CRT allowed disagreement')
    sections = {}
    for item in data['lift_sections']:
        s = item['state']
        need(type(s) is int and s in allowed and s not in sections, 'bad section state')
        point = vector(item['point'])
        need(phi(point) == s and all(not member(point,alpha) for alpha in generators),
             'section congruence/ideal exclusion failed')
        sections[s] = point
    need(set(sections) == set(allowed), 'incomplete sections')
    steps = [vector(v) for v in data['steps']]
    need(len(steps) == len(expected_steps) and set(steps) == expected_steps, 'wrong step scope')
    adjacency = {s:set() for s in allowed}
    edge_list = []
    for s in allowed:
        for step in steps:
            t = (s + phi(step)) % q
            if t in adjacency:
                need(tuple(x+y for x,y in zip(sections[s],step)) == sections[t],
                     'nonzero voltage')
                adjacency[s].add(t)
                edge_list.append((s,t,step))
    components = []
    remaining = set(allowed)
    while remaining:
        start = min(remaining)
        stack, component = [start], {start}
        while stack:
            for t in adjacency[stack.pop()] - component:
                component.add(t)
                stack.append(t)
        remaining -= component
        components.append(sorted(component))
    need(ints(data['components']) and sorted(map(sorted,data['components'])) == sorted(components),
         'wrong component partition/types')
    sizes = sorted(map(len, components))
    need(sizes == sizes_expected, 'independent component size disagreement')
    summary = {'allowed_count':len(allowed),'directed_edge_count':len(edge_list),
               'component_sizes':sizes,'maximum_component_size':max(sizes)}
    need(set(data['summary']) == set(summary) and all(ints(v) for v in data['summary'].values())
         and data['summary'] == summary, 'wrong summary/types')
    out = {'variant':variant,'status':'accepted','ideal_indices':indices,
           'multiplication_matrices':[matrix(x) for x in ideals],
           'membership_vectors_checked':len(box),'membership_tests':len(box)*len(ideals),
           'norm_polynomial_points_checked':len(box),**summary,
           'components':components,
           'undirected_edge_count':len(edge_list)//2,
           'quotient_cycle_rank':len(edge_list)//2-len(allowed)+len(components),
           'all_directed_edges_zero_voltage':True}
    if variant == 'F6':
        need(sorted(map(len,adjacency.values())) == [1,1,1,1,2,2,2,2], 'not paths')
        obstruction = data['enlarged_step_obstruction']
        extras = {vector(x) for x in obstruction['added_steps']}
        need(extras == {(0,1,1),(0,-1,-1)}, 'wrong obstruction step set')
        walk = [vector(x) for x in obstruction['walk']]
        need(len(walk) >= 2 and all(all(not member(x,a) for a in generators) for x in walk),
             'invalid obstruction vertices')
        need(all(tuple(y-x for x,y in zip(a,b)) in expected_steps|extras
                 for a,b in zip(walk,walk[1:])), 'invalid obstruction edges')
        displacement = tuple(y-x for x,y in zip(walk[0],walk[-1]))
        need(displacement == vector(obstruction['displacement']) == (0,5,5), 'bad obstruction displacement')
        need(member(displacement,gamma) and displacement != (0,0,0), 'not a nonzero ideal period')
        quotient = divide_in_ring(displacement,gamma)
        out['F8_obstruction_for_F6_sieve'] = {'displacement':displacement,
                                            'period_ideal_coefficient':[int(x) for x in quotient]}
    return out

def mutations(data):
    # Corrupt distinct parts of the certificate. Every case must be rejected.
    cases = []
    def add(name, change):
        d = copy.deepcopy(data)
        change(d)
        cases.append((name,d))
    add('omitted_allowed_state', lambda d:d['allowed_states'].pop())
    add('boolean_allowed_state', lambda d:d['allowed_states'].__setitem__(0,True))
    add('wrong_ring_root', lambda d:d['quotient_row'].__setitem__(1,d['quotient_row'][1]+1))
    add('false_norm', lambda d:d['generator_norms'].__setitem__(0,7))
    add('float_norm', lambda d:d['generator_norms'].__setitem__(0,2.0))
    add('wrong_product', lambda d:d['common_ideal_period_generator'].__setitem__(0,0))
    add('wrong_section_residue', lambda d:d['lift_sections'][0]['point'].__setitem__(0,2))
    add('same_residue_wrong_voltage', lambda d:d['lift_sections'][0]['point'].__setitem__(0,1+d['quotient_modulus']))
    add('missing_section', lambda d:d['lift_sections'].pop())
    add('duplicate_section', lambda d:d['lift_sections'].append(copy.deepcopy(d['lift_sections'][0])))
    add('extra_step', lambda d:d['steps'].append([0,1,-1]))
    add('missing_step', lambda d:d['steps'].pop())
    add('boolean_section_state', lambda d:d['lift_sections'][0].__setitem__('state',True))
    add('wrong_component', lambda d:d['components'][0].pop())
    add('wrong_edge_count', lambda d:d['summary'].__setitem__('directed_edge_count',0))
    return cases

def main():
    result = {'implementation':'independent; standard-library exact arithmetic', 'certificates':[]}
    # Complete two-ideal gate, including directed loops and parallel edges.
    gate_sections = {1:(1,0,0), 5:(1,-1,0)}
    gate_steps = [(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1),(0,1,1),(0,-1,-1)]
    gate_phi = lambda x: (x[0]+2*x[1]+4*x[2]) % 6
    w = (0,1,1)
    gate_edges = []
    for s,point in gate_sections.items():
        for f in gate_steps:
            t = (s+gate_phi(f)) % 6
            if t in gate_sections:
                h = tuple(a+b-c for a,b,c in zip(point,f,gate_sections[t]))
                need(h[0] == 0 and h[1] == h[2], 'gate voltage not rank one')
                gate_edges.append({'from':s,'to':t,'step':f,'voltage':h,'level_jump':h[1]})
    need({abs(e['level_jump']) for e in gate_edges} == {0,1}, 'gate K not one')
    need(abs(determinant(matrix(w))) == 6, 'gate w norm wrong')
    result['rank_one_F8_gate'] = {'modulus':6,'states':[1,5],'H_generator':w,'K':1,
                                  'directed_edges':gate_edges,'V':2,'CRT_primes':[5,11],
                                  'CRT_slab_period':55,'slab_bound':108}
    for name,variant in [('cubic_f6_certificate.json','F6'),('cubic_rank_one_f8_certificate.json','F8')]:
        path = HERE/name
        raw = path.read_bytes()
        data = json.loads(raw)
        out = verify(data,variant)
        out['frozen_sha256'] = hashlib.sha256(raw).hexdigest()
        rejected = []
        for label,corrupt in mutations(data):
            try:
                verify(corrupt,variant)
            except (ValueError,KeyError,TypeError):
                rejected.append(label)
            else:
                raise ValueError('accepted corruption '+label)
        out['corruptions_rejected'] = rejected
        result['certificates'].append(out)
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
