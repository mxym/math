#!/usr/bin/env python3
"""Author exact verifier for the explicit cubic F6 lift certificate.

Public derivative: strict integer metadata validation and extra schema controls.
The original verifier is preserved in original-verifiers/.

Uses only integer arithmetic and the standard library. Does not import a search
or certificate generator. All input checks remain active under python -O.
"""
import json
import math
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def is_int(x):
    return type(x) is int


def vec(x, size=3):
    require(type(x) is list and len(x) == size and all(is_int(v) for v in x),
            'Expected an exact integer vector')
    return tuple(x)


def add(x, y):
    return tuple(a + b for a, b in zip(x, y))


def sub(x, y):
    return tuple(a - b for a, b in zip(x, y))


def mul(x, y):
    z = [0] * 5
    for i in range(3):
        for j in range(3):
            z[i + j] += x[i] * y[j]
    z[0] += 2 * z[3]
    z[1] += 2 * z[4]
    return tuple(z[:3])


def matrix(x):
    a, b, c = x
    return ((a, 2*c, 2*b), (b, a, 2*c), (c, b, a))


def det(m):
    a, b, c = m
    return (a[0]*(b[1]*c[2]-b[2]*c[1])
            - a[1]*(b[0]*c[2]-b[2]*c[0])
            + a[2]*(b[0]*c[1]-b[1]*c[0]))


def adj(m):
    # Transposed cofactor matrix, computed independently of the norm formula.
    out = []
    for i in range(3):
        row = []
        for j in range(3):
            rr = [r for r in range(3) if r != j]
            cc = [c for c in range(3) if c != i]
            minor = m[rr[0]][cc[0]]*m[rr[1]][cc[1]] - m[rr[0]][cc[1]]*m[rr[1]][cc[0]]
            row.append((-1)**(i+j) * minor)
        out.append(tuple(row))
    return tuple(out)


def matvec(m, x):
    return tuple(sum(a*b for a, b in zip(row, x)) for row in m)


def in_principal(x, alpha):
    m = matrix(alpha)
    d = abs(det(m))
    require(d != 0, 'Zero ideal determinant')
    return all(t % d == 0 for t in matvec(adj(m), x))


def norm_polynomial(x):
    a, b, c = x
    return a**3 + 2*b**3 + 4*c**3 - 6*a*b*c


def exact_integer_metadata(data):
    """Reject JSON booleans/floats even when Python numeric equality holds."""
    require(type(data) is dict, 'Expected a certificate object')
    for field in ('generator_norms', 'allowed_states'):
        value = data[field]
        require(type(value) is list and all(is_int(x) for x in value),
                'Expected exact integer list: ' + field)
    require(is_int(data['quotient_modulus']), 'Expected exact integer modulus')
    components = data['components']
    require(type(components) is list and all(
        type(c) is list and all(is_int(x) for x in c) for c in components),
        'Expected exact integer component states')
    summary = data['summary']
    require(type(summary) is dict and set(summary) == {
        'allowed_count', 'directed_edge_count', 'component_sizes',
        'maximum_component_size'}, 'Wrong summary fields')
    for field in ('allowed_count', 'directed_edge_count', 'maximum_component_size'):
        require(is_int(summary[field]), 'Expected exact integer statistic: ' + field)
    sizes = summary['component_sizes']
    require(type(sizes) is list and all(is_int(x) for x in sizes),
            'Expected exact integer component sizes')


def metadata_negative_cases(data):
    """The public derivatives' additional strict-schema controls."""
    import copy
    cases = []
    def changed(change):
        d = copy.deepcopy(data)
        change(d)
        cases.append(d)
    changed(lambda d: d['allowed_states'].__setitem__(0, True))
    changed(lambda d: d['allowed_states'].__setitem__(0, float(d['allowed_states'][0])))
    changed(lambda d: d['generator_norms'].__setitem__(0, 2.0))
    changed(lambda d: d['generator_norms'].__setitem__(0, True))
    changed(lambda d: d.__setitem__('quotient_modulus', float(d['quotient_modulus'])))
    changed(lambda d: d['components'][0].__setitem__(0, float(d['components'][0][0])))
    changed(lambda d: d['components'][0].__setitem__(0, True))
    changed(lambda d: d['summary'].__setitem__('allowed_count', float(d['summary']['allowed_count'])))
    changed(lambda d: d['summary'].__setitem__('directed_edge_count', True))
    changed(lambda d: d['summary']['component_sizes'].__setitem__(0, float(d['summary']['component_sizes'][0])))
    return cases


def verify(data):
    exact_integer_metadata(data)
    require(data['format'] == 'cubic_crt_lift_certificate_v1', 'Wrong format')
    require(data['order'] == {'basis': ['1','theta','theta^2'], 'relation':'theta^3=2'}, 'Wrong order')
    generators = [vec(x) for x in data['generators']]
    require(generators == [(0,1,0),(1,1,0),(1,0,1)], 'Wrong generators')
    norms = [abs(det(matrix(a))) for a in generators]
    require(norms == [2,3,5] == data['generator_norms'], 'Wrong exact norms')
    for a in generators:
        require(det(matrix(a)) == norm_polynomial(a), 'Norm formula mismatch')
    gamma = vec(data['common_ideal_period_generator'])
    require(mul(mul(generators[0], generators[1]), generators[2]) == gamma == (2,3,1), 'Wrong product generator')
    require(abs(det(matrix(gamma))) == 30, 'Wrong product index')
    q = data['quotient_modulus']
    row = vec(data['quotient_row'])
    require(q == 30 and row == (1,8,4), 'Wrong quotient map')
    require(pow(row[1], 3, q) == 2 and row[1]**2 % q == row[2], 'Quotient map is not a ring map')

    def phi(x, modulus=q):
        return sum(a*b for a, b in zip(row, x)) % modulus

    # Inclusion of every ideal image in the claimed kernel; equality follows
    # from the exact determinant/index and the surjective first coefficient.
    for alpha, p in zip(generators, norms):
        m = matrix(alpha)
        require(all(phi(tuple(m[i][j] for i in range(3)), p) == 0 for j in range(3)), 'Wrong prime-ideal kernel')
    m = matrix(gamma)
    require(all(phi(tuple(m[i][j] for i in range(3))) == 0 for j in range(3)), 'Wrong period-ideal kernel')

    allowed = [r for r in range(q) if math.gcd(r,q) == 1]
    require(data['allowed_states'] == allowed, 'Missing or extra quotient states')
    # Independent adjugate membership cross-check for a complete residue system.
    for r in range(q):
        require((r in allowed) == all(not in_principal((r,0,0), a) for a in generators), 'Membership/state mismatch')
    sections = {}
    for item in data['lift_sections']:
        r = item['state']
        require(is_int(r) and r in allowed and r not in sections, 'Duplicate or forbidden lift state')
        y = vec(item['point'])
        require(phi(y) == r, 'Wrong lift congruence')
        require(all(not in_principal(y,a) for a in generators), 'Lift is in an excluded ideal')
        sections[r] = y
    require(set(sections) == set(allowed), 'Incomplete lift section')
    steps = [vec(x) for x in data['steps']]
    exact_steps = {(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)}
    require(len(steps) == 6 and set(steps) == exact_steps, 'Wrong F6 step set')
    adjacency = {r: [] for r in allowed}
    directed_edges = []
    for r in allowed:
        for f in steps:
            s = (r + phi(f)) % q
            if s in sections:
                require(add(sections[r], f) == sections[s], 'Nonzero voltage in supplied section')
                adjacency[r].append(s)
                directed_edges.append([r, s, list(f)])
    components = []
    remaining = set(allowed)
    while remaining:
        start = min(remaining)
        found = {start}
        todo = [start]
        while todo:
            for s in adjacency[todo.pop()]:
                if s not in found:
                    found.add(s)
                    todo.append(s)
        remaining -= found
        components.append(sorted(found))
    require(sorted(sorted(c) for c in data['components']) == sorted(components), 'Wrong components')
    sizes = sorted(len(c) for c in components)
    summary = {'allowed_count':len(allowed), 'directed_edge_count':len(directed_edges),
               'component_sizes':sizes, 'maximum_component_size':max(sizes)}
    require(summary == data['summary'], 'Wrong statistics')

    # Explicit scope obstruction: adding +/- (theta+theta^2) to F6 gives a
    # nonzero-period walk for this same sieve, so its F6 proof cannot be reused.
    obstruction = data['enlarged_step_obstruction']
    extras = [vec(x) for x in obstruction['added_steps']]
    require(set(extras) == {(0,1,1),(0,-1,-1)}, 'Wrong enlarged steps')
    walk = [vec(x) for x in obstruction['walk']]
    require(all(all(not in_principal(x,a) for a in generators) for x in walk), 'Obstruction hits an ideal')
    all_steps = exact_steps | set(extras)
    require(all(sub(b,a) in all_steps for a,b in zip(walk,walk[1:])), 'Wrong obstruction step')
    displacement = sub(walk[-1],walk[0])
    require(displacement == vec(obstruction['displacement']) == (0,5,5), 'Wrong obstruction displacement')
    require(displacement != (0,0,0) and in_principal(displacement,gamma), 'Walk is not a nonzero period')
    return {'status':'accepted','arithmetic':'exact integer arithmetic',
            'period_ideal_index':30, 'common_scalar_period':30,
            **summary,'directed_edges':directed_edges,
            'enlarged_step_obstruction_steps':len(walk)-1,
            'enlarged_step_obstruction_displacement':list(displacement)}


def negative_tests(data):
    import copy
    cases = []
    d = copy.deepcopy(data); d['allowed_states'].pop(); cases.append(d)
    d = copy.deepcopy(data); d['quotient_row'] = [1,7,4]; cases.append(d)
    d = copy.deepcopy(data); d['generator_norms'][2] = 7; cases.append(d)
    d = copy.deepcopy(data); d['lift_sections'][0]['point'] = [3,3,1]; cases.append(d) # same quotient, wrong voltage
    d = copy.deepcopy(data); d['lift_sections'][0]['state'] = True; cases.append(d)
    d = copy.deepcopy(data); d['steps'].append([0,1,1]); cases.append(d)
    d = copy.deepcopy(data); d['enlarged_step_obstruction']['walk'][2] = [1,1,2]; cases.append(d)
    cases.extend(metadata_negative_cases(data))
    for i, d in enumerate(cases):
        try:
            verify(d)
        except (ValueError, KeyError, TypeError):
            continue
        raise ValueError('Negative test was incorrectly accepted: '+str(i))
    return len(cases)


if __name__ == '__main__':
    directory = Path(__file__).resolve().parent
    data = json.loads((directory/'cubic_f6_certificate.json').read_text())
    result = verify(data)
    result['negative_tests_rejected'] = negative_tests(data)
    print(json.dumps(result, indent=2))
