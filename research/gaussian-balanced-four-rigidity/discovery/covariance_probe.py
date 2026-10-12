"""Floating discovery only: the balanced covariance Hessian, not a certificate.

The mathematical formula is derived in GLOBAL_COVARIANCE_ROUTE.md. This
program neither proves covariance concavity nor certifies Gaussian CDFs,
prices, eigenvalue signs, or a global search-space cover.
"""
import argparse
from hashlib import sha256
import json
import math
from pathlib import Path
import warnings

import numpy as np
import scipy
from scipy.optimize import root
from scipy.special import ndtr

from stationary_search import BASE, PHI0, cdf2, cdf3, phi2


def trace_free_basis():
    basis = [np.diag([1., -1., 0.]) / math.sqrt(2),
             np.diag([1., 1., -2.]) / math.sqrt(6)]
    for i, j in [(0, 1), (0, 2), (1, 2)]:
        direction = np.zeros((3, 3))
        direction[i, j] = direction[j, i] = 1 / math.sqrt(2)
        basis.append(direction)
    return np.array(basis)


BASIS = trace_free_basis()


def facets(scores, prices):
    """Surface-weighted raw first/second moments of all six facets."""
    records = []
    for i in range(4):
        for j in range(i + 1, 4):
            edge = scores[i] - scores[j]
            length = np.linalg.norm(edge)
            normal = edge / length
            offset = (prices[i] - prices[j]) / length
            others = [k for k in range(4) if k not in (i, j)]
            differences = scores[others] - scores[i]
            tangents = differences - np.outer(differences @ normal, normal)
            lengths = np.linalg.norm(tangents, axis=1)
            unit = tangents / lengths[:, None]
            thresholds = (prices[others] - prices[i]
                          - (differences @ normal) * offset) / lengths
            correlation = float(unit[0] @ unit[1])
            conditional_sd = math.sqrt(1 - correlation**2)
            probability = cdf2(thresholds, correlation)
            derivatives = PHI0 * np.exp(-thresholds**2 / 2) * ndtr([
                (thresholds[1] - correlation * thresholds[0]) / conditional_sd,
                (thresholds[0] - correlation * thresholds[1]) / conditional_sd])
            mixed = phi2(thresholds[0], thresholds[1], correlation)
            threshold_hessian = np.array([
                [-thresholds[0] * derivatives[0] - correlation * mixed, mixed],
                [mixed, -thresholds[1] * derivatives[1] - correlation * mixed]])
            tangent_mean = -unit.T @ derivatives
            first = offset * normal * probability + tangent_mean
            second = (probability * (np.eye(3) - np.outer(normal, normal)
                                      + offset**2 * np.outer(normal, normal))
                      + unit.T @ threshold_hessian @ unit
                      + offset * (np.outer(normal, tangent_mean)
                                  + np.outer(tangent_mean, normal)))
            coefficient = PHI0 * math.exp(-offset**2 / 2) / length
            records.append((i, j, edge, coefficient, probability, first, second))
    return records


def assignment(scores, prices, with_moments=False):
    masses = []
    for i in range(4):
        others = [j for j in range(4) if j != i]
        differences = scores[others] - scores[i]
        lengths = np.linalg.norm(differences, axis=1)
        thresholds = (prices[others] - prices[i]) / lengths
        unit = differences / lengths[:, None]
        masses.append(cdf3(thresholds, unit @ unit.T))
    records = facets(scores, prices)
    weights = np.zeros((4, 4))
    for i, j, _, coefficient, probability, _, _ in records:
        weights[i, j] = weights[j, i] = coefficient * probability
    laplacian = np.diag(np.sum(weights, axis=1)) - weights
    result = np.array(masses), laplacian, laplacian @ scores
    return (*result, records) if with_moments else result


def balanced_value(covariance):
    scores = BASE @ np.linalg.cholesky(covariance)

    def equations(z):
        prices = np.r_[z, -np.sum(z)]
        return assignment(scores, prices)[0][:3] - .25

    def jacobian(z):
        _, laplacian, _ = assignment(scores, np.r_[z, -np.sum(z)])
        return -laplacian[:3, :3] + laplacian[:3, 3, None]

    solution = root(equations, np.zeros(3), jac=jacobian, tol=2e-9)
    prices = np.r_[solution.x, -np.sum(solution.x)]
    masses, laplacian, moments = assignment(scores, prices)
    error = float(np.max(np.abs(masses - .25)))
    if not np.isfinite(error) or error > 2e-7:
        raise RuntimeError('Floating price balance failed: ' + str(error))
    return float(np.sum(scores * moments)), scores, prices, masses, laplacian


def covariance_hessian(covariance):
    value, scores, prices, masses, laplacian = balanced_value(covariance)
    inverse = np.linalg.inv(np.linalg.cholesky(covariance))
    physical = np.array([inverse @ direction @ inverse.T for direction in BASIS])
    raw_hessian = np.zeros((5, 5))
    price_cross = np.zeros((4, 5))
    for i, j, edge, coefficient, probability, first, second in facets(scores, prices):
        transformed_edges = np.einsum('aij,j->ai', physical, edge)
        raw_hessian += coefficient * (
            transformed_edges @ second @ transformed_edges.T
            - probability * transformed_edges @ transformed_edges.T)
        contributions = coefficient * transformed_edges @ first
        price_cross[i] += contributions
        price_cross[j] -= contributions
    # The Moore-Penrose inverse implements the common-price quotient.
    hessian = (raw_hessian - price_cross.T @ np.linalg.pinv(laplacian)
               @ price_cross) / 4
    return value, (hessian + hessian.T) / 2, prices, masses


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cases', type=int, default=200)
    parser.add_argument('--seed', type=int, default=20261012)
    parser.add_argument('--log-eigenvalue-min', type=float, default=-8.)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.cases < 1 or args.log_eigenvalue_min >= 1:
        parser.error('Require cases >= 1 and log-eigenvalue-min < 1.')
    rng = np.random.default_rng(args.seed)
    report = {
        'discovery_only': True, 'proof_certificate': False,
        'covariance_concavity_proved': False,
        'numpy_version': np.__version__, 'scipy_version': scipy.__version__,
        'seed': args.seed, 'requested_cases': args.cases,
        'log_eigenvalue_range': [args.log_eigenvalue_min, 1.],
        'score_covariance_trace': 1., 'complete': False,
        'sources': {name: sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                    for name in ('covariance_probe.py', 'stationary_search.py')},
        'records': [], 'failures': [], 'warnings': []}
    with warnings.catch_warnings(record=True) as caught:
        warnings.simplefilter('always')
        for index in range(args.cases):
            orthogonal, _ = np.linalg.qr(rng.normal(size=(3, 3)))
            spectrum = np.exp(rng.uniform(args.log_eigenvalue_min, 1., 3))
            spectrum /= 4 * sum(spectrum)
            covariance = orthogonal @ np.diag(spectrum) @ orthogonal.T
            try:
                value, hessian, prices, masses = covariance_hessian(covariance)
                eigenvalues, eigenvectors = np.linalg.eigh(hessian)
                record = {'index': index, 'coordinate_covariance': covariance.tolist(),
                          'prices': prices.tolist(), 'masses': masses.tolist(),
                          'mass_error': float(np.max(np.abs(masses - .25))),
                          'balanced_value': value, 'hessian': hessian.tolist(),
                          'hessian_eigenvalues': eigenvalues.tolist()}
                if eigenvalues[-1] > 1e-5:
                    direction = np.einsum('i,ijk->jk', eigenvectors[:, -1], BASIS)
                    record['direction'] = direction.tolist()
                    record['directional_probes'] = []
                    for factor in (.1, .2, .4):
                        step = min(spectrum) * factor
                        plus = balanced_value(covariance + step * direction)[0]
                        minus = balanced_value(covariance - step * direction)[0]
                        record['directional_probes'].append({
                            'step': float(step), 'concavity_gap': value - (plus + minus) / 2})
                report['records'].append(record)
                if index % 25 == 0 or eigenvalues[-1] > 1e-5:
                    print(json.dumps({'index': index,
                                      'largest_eigenvalue': float(eigenvalues[-1]),
                                      'mass_error': record['mass_error']}), flush=True)
            except (RuntimeError, ValueError, OverflowError, ZeroDivisionError,
                    np.linalg.LinAlgError) as error:
                report['failures'].append({'index': index, 'error': str(error),
                                           'coordinate_covariance': covariance.tolist()})
            report['warnings'] = [{'category': item.category.__name__,
                                   'message': str(item.message)} for item in caught]
            report['complete'] = index + 1 == args.cases
            args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    maximum = max((row['hessian_eigenvalues'][-1] for row in report['records']),
                  default=None)
    print(json.dumps({'complete': report['complete'], 'cases': len(report['records']),
                      'failures': len(report['failures']), 'warnings': len(report['warnings']),
                      'largest_eigenvalue': maximum, 'proof_certificate': False}), flush=True)


if __name__ == '__main__':
    main()
