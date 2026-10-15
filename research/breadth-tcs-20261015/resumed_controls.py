"""Route controls for SC0; finite certificates do not prove the conjecture.

This file keeps each stronger/restricted assertion separate from the general
size-VC model. The Boolean arithmetic checker does not trust SAT model checks.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import importlib.util
import json
import time

HERE = Path(__file__).parent
spec = importlib.util.spec_from_file_location('finite_decoder', HERE/'finite_decoder.py')
fd = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fd)

WARMUTH = [3, 6, 12, 24, 17, 26, 22, 13, 21, 11]

def uniform_default_decoder(n, message):
    a, b = message
    # Empty message and >=2 negative literals use default 1. A mixed
    # message also uses default 1; positive-only and singleton-negative
    # messages use default 0. This is a fixed function of the message only.
    default_one = not a or (a != b and (b != 0 or a.bit_count() >= 2))
    return (((1 << n) - 1) & ~a if default_one else 0) | b

def check_decoder(n, C, d, decoder):
    samples = fd.samples(n, C)
    failures = []
    for a, b in samples:
        if not any((decoder(n, (u, b & u)) & a) == b
                   for u in fd.submasks(a) if u.bit_count() <= d):
            failures.append([a, b])
    return {'samples': len(samples), 'failures': failures,
            'plain_integer_verified': not failures}

def teaching_sizes(n, C):
    return {str(c): min(a.bit_count() for a in range(1 << n)
                       if [r for r in C if (r & a) == (c & a)] == [c])
            for c in C}

def clone_uniform_prior_obstruction(M=17):
    # Only five core coordinates are needed to specify the problematic S.
    # The other coordinates each carry a single private 1 for one clone.
    core_target = WARMUTH[0]
    core_other = [c for c in WARMUTH if c != core_target]
    C = [core_target]
    for c in core_other:
        for _ in range(M):
            C.append(c | (1 << (4+len(C))))
    n = 5 + M * len(core_other)
    a, b = 31, core_target
    eligible = [(u, b & u) for u in fd.submasks(a) if u.bit_count() <= 2]
    counts = [sum((c & u) == lab for c in C) for u, lab in eligible]
    matching = sum((c & a) == b for c in C)
    expectation = sum((Fraction(matching, count) for count in counts), Fraction())
    # Do not call vcdim over 2^n domains. The proof of VC=2 is structural:
    # private-coordinate 1 occurs in just one row; hence no shattered set
    # containing a private coordinate has cardinality >=2. Core VC=2 below.
    assert len(C) == 1 + 9*M and matching == 1
    assert fd.vcdim(5, WARMUTH) == 2
    assert all(sum((c >> j) & 1 for c in C) == 1 for j in range(5, n))
    assert min(counts) >= M + 1
    assert expectation < 1
    return {'M': M, 'n': n, 'concepts': len(C), 'VC_dimension': 2,
            'VC_check': 'Structural private-coordinate proof plus exact five-coordinate projection VC check; not exhaustive 2^n projection enumeration.',
            'sample_mask': a, 'sample_labels': b,
            'sample_version_space_size': matching,
            'eligible_messages': len(eligible),
            'message_version_space_sizes': counts,
            'uniform_conditional_expected_successful_messages': str(expectation),
            'expectation_lt_one': expectation < 1,
            'route_defeated': 'Uniform random proper h_T from each original version space; not arbitrary prior, fractional scheme, or SC0.'}

def uniform_majority_obstruction():
    target = WARMUTH[0]
    others = [c for c in WARMUTH if c != target]
    multiplicities = {c: 1 << (j+1) for j,c in enumerate(others)}
    weighted = [(target,1)] + list(multiplicities.items())
    records = []
    for a in range(32):
        if a.bit_count() > 2:
            continue
        eligible = [(c,w) for c,w in weighted if (c&a) == (target&a)]
        total = sum(w for c,w in eligible)
        majority = sum((1<<i) for i in range(5)
                       if 2*sum(w for c,w in eligible if (c>>i)&1) > total)
        dominant, weight = max(eligible,key=lambda p:p[1])
        assert dominant != target and weight > total-weight
        assert majority == dominant and majority != target
        records.append({'mask':a, 'labels':target&a, 'core_majority':majority,
                        'version_space_size':total,
                        'dominant_weight':weight, 'strict_margin':2*weight-total})
    return {'core_target':target,'core_multiplicities':weighted,
        'full_total_class_size':sum(w for c,w in weighted),
        'full_domain_size':5+sum(multiplicities.values()),
        'full_VC_dimension':2,
        'private_coordinate_construction':'Each copy has its own private 1, other private bits zero; proof in the notes.',
        'all_16_message_records':records,
        'route_defeated':'Coordinatewise uniform-version-space majority, with arbitrary tie breaking. All witnessed core disagreements have strict majorities. Not SC0.'}

def main():
    started = time.time()
    control = {'status': 'Finite route controls only. No SC0 resolution or new major result.',
               'solver': fd.z3.get_version_string(), 'warmuth_primary_rows': WARMUTH}
    control['warmuth_VC'] = fd.vcdim(5, WARMUTH)
    control['warmuth_teaching_sizes'] = teaching_sizes(5, WARMUTH)
    assert control['warmuth_VC'] == 2
    assert set(control['warmuth_teaching_sizes'].values()) == {3}
    control['warmuth_general_size_2'] = check_decoder(5, WARMUTH, 2, uniform_default_decoder)
    control['universal_decoder_controls'] = []
    for k in range(2, 6):
        n = 2*k + 1
        # All partial samples in {0,1,*}^n, not just concept rows.
        record = check_decoder(n, range(1 << n), k, uniform_default_decoder)
        record.update({'n': n, 'compression_size': k, 'class_VC': n,
                       'scope': 'Universal full binary cube on this n only; the accompanying written proof covers every n<=2k+1, k>=2.'})
        assert record['plain_integer_verified']
        control['universal_decoder_controls'].append(record)
    # Five samples in the VC-one singleton class induce exactly a C5 in
    # the incompatibility graph. This rejects a proposed perfectness shortcut.
    cycle_samples = [((1 << i) | (1 << ((i-1) % 5)), 1 << ((i-1) % 5))
                     for i in range(5)]
    edges = [[i,j] for i in range(5) for j in range(i+1,5)
             if ((cycle_samples[i][1] ^ cycle_samples[j][1]) &
                 cycle_samples[i][0] & cycle_samples[j][0])]
    assert edges == [[0,1], [0,4], [1,2], [2,3], [3,4]]
    control['incompatibility_C5'] = {'concepts': [1,2,4,8,16], 'VC': 1,
        'samples': cycle_samples, 'induced_edges': edges,
        'scope': 'Graph is not perfect even at VC one. This does not show that the actual legal-message lists lack a coloring.'}
    control['uniform_prior_obstruction'] = clone_uniform_prior_obstruction()
    control['uniform_majority_obstruction'] = uniform_majority_obstruction()
    control['singleton_h_polynomial'] = []
    for n in range(2,9):
        from math import comb
        C = [1<<i for i in range(n)]
        histogram = Counter(a.bit_count() for a,b in fd.samples(n,C))
        h = [sum(histogram[j]*comb(n-j,k-j)*(-1)**(k-j)
                 for j in range(k+1)) for k in range(n+1)]
        expected = [1,n] + [0]*(n-2) + [-1]
        assert h == expected
        control['singleton_h_polynomial'].append({'n':n,'face_counts_by_cardinality':dict(histogram),'h_coefficients':h})
    (HERE/'RESUMED_ROUTE_CONTROLS.json').write_text(json.dumps(control, indent=2)+'\n')
    print(json.dumps({k:v for k,v in control.items() if k not in ['warmuth_general_size_2']},indent=2),flush=True)
    print('elapsed', time.time()-started, flush=True)

if __name__ == '__main__':
    main()
