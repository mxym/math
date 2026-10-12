#!/usr/bin/env python3
# Public strict derivative of the preserved original checker.
# All proof-critical checks use require(), which remains active under python -O.
# Historical objects remain separately preserved; public derivatives are hash-pinned.
"""Reproduce algebra, normalization, and source-hash checks for this audit.

Default: offline symbolic checks (requires Python 3 and SymPy).
--source-root PATH: additionally verify the two downloaded pinned source trees.
--fetch-sources PATH: fetch exactly the manifest files, using inherited HTTPS
proxy/CA settings and ordinary TLS verification, then verify them. No git writes.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import platform
from urllib.request import urlopen
import sympy as s


class AuditFailure(RuntimeError):
    """A proof-critical or provenance check failed."""


def require(condition, message):
    if not condition:
        raise AuditFailure(str(message))


def verify_public_audit():
    root = Path(__file__).resolve().parent.parent
    pins = {'audit/AUDIT.txt': 'a5822dd2ebb7b2aba38661fb62c35ad11c79ba892eb45e84d5b8f3a40945c756', 'audit/INDEPENDENT_AUDIT.md': '364851d1823fdab2de46dba0efc607794b66f17ab7a8b25b85c88df4779cb5b9', 'provenance/source-manifest.json': '3f273a37cea10c58f9cb4b248f52a59dcf14e7035f10638c340ff324dd639429', 'provenance/upstream-manifest.json': '6534af9ff1b3aed25b66e781d625d39416c4371c97096ec5c1f2eb5d1df0f743', 'provenance/source-label-map.json': 'bc01cab305cfca0830721f27faa9dc00093663044f7d74c7f862ae3cab2dd300', 'provenance/original-object-pins.json': '377ee878826a289ff5c8cb6dbcc2fbb63812652590bde98a9cdf8a83026c57ee', 'provenance/manuscript-correspondence.json': 'ea3cbea9755dd602567da2996019f8b30cfef0b67e751d4cc4b91f2d39c10ff2'}
    for name, digest in pins.items():
        require(hashlib.sha256((root/name).read_bytes()).hexdigest()==digest, "Public audit/provenance changed: "+name)
    correspondence=json.loads((root/"provenance/manuscript-correspondence.json").read_text())
    for row in correspondence["files"]:
        require(hashlib.sha256((root/row["path"]).read_bytes()).hexdigest()==row["release_sha256"], "Audited manuscript changed: "+row["path"])

def algebra_checks():
    results = {}
    x1, x2, x3, w1, w2, w3, eps = s.symbols('x1 x2 x3 w1 w2 w3 eps', real=True)
    v1, v2, v3, u1, u2, u3 = s.symbols('v1 v2 v3 u1 u2 u3', real=True)
    x = s.Matrix([x1, x2, x3])
    w = s.Matrix([w1, w2, w3])
    v = s.Matrix([v1, v2, v3])
    u = s.Matrix([u1, u2, u3])
    B = (v - u).dot(w)
    norm = w.dot(w)
    vp, up = (v - B * w, u + B * w)
    energy = vp.dot(vp) + up.dot(up) - v.dot(v) - u.dot(u)
    require(s.expand(energy - 2 * (norm - 1) * B ** 2) == 0, 'Failed check: s.expand(energy - 2 * (norm - 1) * B ** 2) == 0')
    require(vp + up == v + u, 'Failed check: vp + up == v + u')
    virial = x.dot(vp - v) + (x + eps * w).dot(up - u)
    require(s.expand(virial - eps * B * norm) == 0, 'Failed check: s.expand(virial - eps * B * norm) == 0')
    angular = x.cross(vp - v) + (x + eps * w).cross(up - u)
    require(all((s.expand(z) == 0 for z in angular)), 'Failed check: all((s.expand(z) == 0 for z in angular))')
    results['collision_energy_jump'] = '2*(|omega|^2-1)*B^2; zero on S^2'
    results['collision_virial_jump'] = 'epsilon*B on S^2'
    results['collision_momentum_and_angular_momentum_jumps'] = 'zero'
    a = s.symbols('a', real=True)
    angular_scalar = s.integrate(2 * s.pi * a ** 2, (a, 0, 1))
    angular_xx = s.integrate(s.pi * (1 - a ** 2) * a ** 2, (a, 0, 1))
    angular_zz = s.integrate(2 * s.pi * a ** 4, (a, 0, 1))
    require(angular_scalar == 2 * s.pi / 3, 'Failed check: angular_scalar == 2 * s.pi / 3')
    require(angular_xx == 2 * s.pi / 15 and angular_zz == 2 * s.pi / 5, 'Failed check: angular_xx == 2 * s.pi / 15 and angular_zz == 2 * s.pi / 5')
    results['sphere_integral_B_squared'] = str(angular_scalar) + '*|g|^2'
    results['unordered_collision_factor'] = '1/2'
    results['collision_stress_tensor_coefficient'] = 'pi/15'
    results['exclusion_ball_volume'] = '4*pi/3'
    births, roots, links = s.symbols('births roots links', integer=True)
    mergers = births - 1 - links
    epsilon_power = -2 * (births - roots) + 2 * mergers + 3 * links
    require(s.expand(epsilon_power - (2 * (roots - 1) + links)) == 0,
            'Connected activity/contact/initial-link scaling changed.')
    results['connected_scaling'] = 'mu^(m-h)*epsilon^(2*(m-1-p)+3*p)=mu^(1-h)*epsilon^p'
    mu = s.symbols('mu', positive=True)
    diagonal, connected = s.symbols('diagonal connected')
    normalized_variance = (mu * diagonal + mu**2 * connected) / (4 * mu**2)
    require(s.simplify(normalized_variance - diagonal/(4*mu) - connected/4) == 0,
            'Two-participant speed record variance normalization changed.')
    results['speed_sum_variance'] = '(1/(4*mu))*integral(F1*y^2)+(1/4)*integral(c2*y1*y2)'
    t = s.symbols('t', real=True)
    E, V, X = s.symbols('E V X', real=True)
    h = s.Function('H')(t)
    integral = s.Function('I')(t)
    matrix = s.Matrix([[1, 0, 0], [t, 1, 0], [t ** 2, 2 * t, 1]])
    Y = matrix * s.Matrix([E, V, X]) + s.Matrix([0, h, 2 * integral])
    require(s.diff(Y[0], t) == 0, 'Failed check: s.diff(Y[0], t) == 0')
    require(s.simplify(s.diff(Y[1], t) - Y[0] - s.diff(h, t)) == 0, 'Failed check: s.simplify(s.diff(Y[1], t) - Y[0] - s.diff(h, t)) == 0')
    require(s.simplify((s.diff(Y[2], t) - 2 * Y[1]).subs(s.diff(integral, t), h)) == 0, 'Failed check: s.simplify((s.diff(Y[2], t) - 2 * Y[1]).subs(s.diff(integral, t), h)) == 0')
    results['triangular_limit_equations'] = "dE=0; dV=E+H'; dX=2V"
    p = s.Integer(42)
    exponent_mean = -1 + s.Rational(21, 20) * (1 - 1 / p)
    exponent_second = -2 + s.Rational(21, 20) * (1 - 2 / p)
    require(exponent_mean == s.Rational(1, 40), 'Failed check: exponent_mean == s.Rational(1, 40)')
    require(exponent_second == -1, 'Failed check: exponent_second == -1')
    results['coupling_mean_exponent_at_p42'] = str(exponent_mean)
    results['coupling_squared_error_exponent_at_p42'] = str(exponent_second)
    results['best_squared_error_exponent_as_p_increases'] = '-19/20'
    results['rare_event_variance_counterexample'] = 'epsilon^(-19/20)*(1-epsilon^(21/20))'
    basis = [s.Integer(1), *list(x), *list(v), v.dot(v), *list(x.cross(v)), x.dot(v), x.dot(x)]
    require(len(basis) == 13, 'Failed check: len(basis) == 13')
    variables = (*list(x), *list(v))
    monomials = sorted(set().union(*(s.Poly(q, *variables).monoms() for q in basis)))
    coefficients = s.Matrix([[s.Poly(q, *variables).coeff_monomial(m) for q in basis]
                             for m in monomials])
    require(coefficients.rank() == 13, 'The thirteen quadratic basis elements are not independent.')
    for q in basis:
        pullback = s.expand(q.subs({x1: x1 + t * v1, x2: x2 + t * v2, x3: x3 + t * v3}, simultaneous=True))
        require(s.diff(pullback, t, 3) == 0, 'Failed check: s.diff(pullback, t, 3) == 0')
    results['independent_quadratic_basis_dimension_and_transport_degree_d3'] = len(basis)
    mass, en, vi, sp = s.symbols('mass en vi sp', real=True)
    Px, Py, Pz, Xx, Xy, Xz = s.symbols('Px Py Pz Xx Xy Xz', real=True)
    P = s.Matrix([Px, Py, Pz])
    Q = s.Matrix([Xx, Xy, Xz])
    raw = [mass, Px, Py, Pz, Xx, Xy, Xz, en, vi, sp]
    insertion = [1, v1, v2, v3, x1, x2, x3, v.dot(v), x.dot(v), x.dot(x)]
    expressions = [en / mass - P.dot(P) / mass ** 2, vi / mass - Q.dot(P) / mass ** 2, sp / mass - Q.dot(Q) / mass ** 2]
    effective = [(v - P).dot(v - P) - (en - P.dot(P)), (x - Q).dot(v - P) - (vi - Q.dot(P)), (x - Q).dot(x - Q) - (sp - Q.dot(Q))]
    for expr, phi in zip(expressions, effective):
        differential = sum((s.diff(expr, r) * k for r, k in zip(raw, insertion)))
        require(s.simplify(differential.subs(mass, 1) - phi) == 0, 'Failed check: s.simplify(differential.subs(mass, 1) - phi) == 0')
    results['intrinsic_per_particle_delta_method_tests'] = 'three effective centered quadratic tests verified'
    return results

def source_checks(root: Path, fetch: bool):
    here = Path(__file__).resolve().parent.parent / 'provenance'
    manifests = [json.loads((here / name).read_text()) for name in ['source-manifest.json', 'upstream-manifest.json']]
    checked = []
    for manifest in manifests:
        commit = manifest.get('pinned_commit', manifest.get('commit'))
        for row in manifest['files']:
            target = root / commit / row['path']
            if fetch:
                with urlopen(row['url'], timeout=30) as response:
                    data = response.read()
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
            data = target.read_bytes()
            require(len(data) == row['bytes'], str(target))
            require(hashlib.sha256(data).hexdigest() == row['sha256'], str(target))
            git_blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\x00' + data).hexdigest()
            require(git_blob == row['git_blob'], str(target))
            for label in row.get('source_labels', []):
                require(('\\label{' + label + '}').encode() in data, (str(target), label))
            checked.append({'path': row['path'], 'git_blob': git_blob})
    label_map=json.loads((here/'source-label-map.json').read_text())
    for row in label_map:
        lines=(root/row['commit']/row['path']).read_text().splitlines()
        require('\\label{'+row['label']+'}' in lines[row['line']-1], 'Source label/line mismatch: '+row['label'])
    require(all((row['equal_newer_commit'] for row in manifests[0]['files'])), "Failed check: all((row['equal_newer_commit'] for row in manifests[0]['files']))")
    return {'checked_files': len(checked), 'all_hashes_match': True, 'source_label_map_entries_verified': len(label_map), 'comparison_commit_equality': 'historical manifest assertion; not freshly fetched'}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path)
    parser.add_argument('--fetch-sources', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--self-test-failure', action='store_true')
    args = parser.parse_args()
    if args.self_test_failure:
        require(False, 'Intentional strict-check failure; optimization must not erase it.')
    verify_public_audit()
    result = {'python': platform.python_version(), 'sympy': s.__version__, 'algebra_checks': algebra_checks(), 'optimization_enabled': not __debug__, 'public_audit': 'audited public derivatives, source provenance, and manuscript hashes match fixed anchors'}
    if args.fetch_sources:
        result['source_checks'] = source_checks(args.fetch_sources, True)
    else:
        result['source_checks'] = source_checks(args.source_root or Path(__file__).resolve().parent.parent/'sources', False)
    serialized = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(serialized)
    print(serialized, end='')
if __name__ == '__main__':
    try:
        main()
    except (AuditFailure, OSError, ValueError) as error:
        raise SystemExit('STRICT CHECK FAILED: ' + str(error))
