"""Reproduce the quotient search with compiled C++17 incidence and search binaries."""
import argparse
import itertools
import json
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_cores import EDGES, PAIRS, HERE, dot, graph, psd

# Total support histograms with fixed core labels, followed by their orbit count
# under Aut(C). The first count already identifies permutations of exterior labels.
COUNTS = {
    53: (103729799, 154087), 54: (302882, 6940), 55: (436, 65),
    58: (1, 1), 61: (6, 3), 66: (6, 5), 75: (4, 3), 77: (10752, 162),
    79: (1, 1), 80: (4, 4), 92: (96, 18), 93: (7, 5), 94: (10, 3),
    99: (2, 2), 104: (3, 2), 105: (1, 1), 117: (6, 3), 118: (5, 5),
    124: (1, 1), 125: (1, 1), 128: (1, 1), 148: (1, 1), 149: (2, 2),
    151: (3, 2), 174: (1, 1), 175: (1, 1),
}


def incidence_input(c):
    moment = [[6 * (i == j) + 6 - 5 * c[i][j] - dot(c[i], c[j])
               for j in range(6)] for i in range(6)]
    kernel = [[3 * (i == j) - 3 * c[i][j] + 1 for j in range(6)] for i in range(6)]
    flags = []
    for mask in range(64):
        v = [(mask >> i) & 1 for i in range(6)]
        z = [1 - 3 * a for a in v]
        valid = (psd([r + [a] for r, a in zip(kernel, z)] + [z + [10]])
                 and all(not v[i] or dot(c[i], v) <= 1 for i in range(6))
                 and all(v[i] * v[j] <= moment[i][j] for i, j in EDGES))
        flags.append(int(valid))
    return '\n'.join(' '.join(map(str, row)) for row in c + moment + [flags]) + '\n'


def golay_test(search):
    # Cayley graph on F_3^5 using +/- x^j, j=0,...,10, with
    # x^5 = x^3 - x^2 + x + 1. Verify the graph parameters directly.
    points = list(itertools.product(range(3), repeat=5))
    index = {v: i for i, v in enumerate(points)}
    s = (1, 0, 0, 0, 0)
    steps = set()
    for _ in range(11):
        steps.add(s)
        steps.add(tuple(-v % 3 for v in s))
        a, b, c, d, e = s
        s = e, (a + e) % 3, (b - e) % 3, (c + e) % 3, d
    nbr = [{index[tuple((a + b) % 3 for a, b in zip(v, delta))] for delta in steps}
           for v in points]
    assert all(len(a) == 22 for a in nbr)
    assert all(len(nbr[i] & nbr[j]) == 2 - int(j in nbr[i])
               for i, j in itertools.combinations(range(243), 2))

    # Translation by a non-neighbour has 81 independent three-point orbits.
    shift = next(v for v in points if v not in steps and any(v))
    perm = [index[tuple((a + b) % 3 for a, b in zip(v, shift))] for v in points]
    orbits = [(i, perm[i], perm[perm[i]]) for i in range(243)
              if i == min(i, perm[i], perm[perm[i]])]
    assert len(orbits) == 81
    orbits = [orbits[i] for i in sorted(range(81), key=lambda i: (17 * i) % 81)]
    q = [[len(nbr[orbit[0]].intersection(other)) for other in orbits] for orbit in orbits]
    assert all(q[i][i] == 0 and sum(q[i]) == 22 for i in range(81))
    # Leave two indistinguishable column prefixes whose hidden edges differ.
    base = [i for i in range(2, 81) if q[i][0] == q[i][1]][:40]
    hidden = [i for i in range(81) if i not in base]
    assert len(base) == 40 and any(q[i][0] != q[i][1] for i in hidden)
    fixture = '\n'.join(' '.join(str(q[i][j]) for j in base) for i in base + hidden)
    subprocess.run([search, '--243-test'], input=fixture, text=True, check=True)


def examine_batch(args):
    binary, core_text, profiles, histograms = args
    data = [str(len(histograms)) + '\n']
    for hist in histograms:
        data.append(core_text)
        order = sorted(range(64), key=lambda m: (hist[m], -m.bit_count(), m))
        data.extend(profiles[m] * hist[m] for m in order if hist[m])
    result = subprocess.run([binary], input=''.join(data), text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f'quotient search exited {result.returncode}\n{result.stdout}\n{result.stderr}')
    lines = [s.split() for s in result.stdout.splitlines()]
    if len(lines) != len(histograms) or any(len(s) != 3 or s[:2] != [str(i), 'exhausted']
                                            for i, s in enumerate(lines)):
        raise RuntimeError('incomplete quotient-search output')
    return len(lines), sum(int(s[2]) for s in lines)


def checked_histograms(stream, c):
    # Check the emitted objects independently of the row-prefix generator.
    required = [6 * (i == j) + 6 - 5 * c[i][j] - dot(c[i], c[j]) for i, j in PAIRS]
    contributors = [[m for m in range(64) if (m >> i) & (m >> j) & 1] for i, j in PAIRS]
    seen = set()
    for row in stream:
        hist = tuple(map(int, row.split()))
        assert len(hist) == 64 and min(hist) >= 0 and sum(hist) == 27
        key = bytes(hist)
        assert key not in seen
        seen.add(key)
        assert all(sum(hist[m] for m in indices) == n for indices, n in zip(contributors, required))
        yield hist


def batches(histograms, size, args):
    while group := list(itertools.islice(histograms, size)):
        yield (*args, group)


def run_core(atlas, c, incidence, search, workers):
    order = sorted(range(6), key=lambda i: -sum(c[i]))
    c = [[c[i][j] for j in order] for i in order]
    core_text = ''.join(' '.join(str(a + 2 * (i == j)) for j, a in enumerate(row)) + '\n'
                        for i, row in enumerate(c))
    profiles = [' '.join(str((m >> j) & 1) for j in range(6)) + '\n' for m in range(64)]
    with tempfile.TemporaryFile(mode='w+') as stream:
        census = subprocess.run([incidence], input=incidence_input(c), text=True,
                                stdout=stream, stderr=subprocess.PIPE, check=True)
        counts = tuple(map(int, census.stderr.split()))
        assert counts == COUNTS[atlas], (atlas, counts)
        stream.seek(0)
        # Small batches distribute the large individual cases across workers.
        batch_size = 50 if counts[1] > 500 else 1
        arguments = batches(checked_histograms(stream, c), batch_size, (search, core_text, profiles))
        done = nodes = 0
        with ThreadPoolExecutor(max_workers=workers) as pool:
            for n, visits in pool.map(examine_batch, arguments):
                done += n
                nodes += visits
        assert done == counts[1]
    print(f'{atlas}: {counts[0]} labelled-core histograms, {done} representatives, '
          f'{nodes} prefixes, 0 quotient matrices.', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('incidences', type=Path)
    parser.add_argument('search', type=Path)
    parser.add_argument('--jobs', type=int, default=1)
    parser.add_argument('--atlas', nargs='+', type=int, choices=sorted(COUNTS))
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be positive')
    incidence, search = args.incidences.resolve(), args.search.resolve()
    subprocess.run([search, '--grid-test'], check=True)
    golay_test(search)
    records = {r['atlas']: graph(r['mask']) for r in json.loads((HERE / 'cores.json').read_text())
               if 'outer' in r}
    assert set(records) == set(COUNTS)
    for atlas in args.atlas or sorted(set(records) - {53}):
        run_core(atlas, records[atlas], incidence, search, args.jobs)


if __name__ == '__main__':
    main()
