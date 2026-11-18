"""Build extension CNFs and verify independently checked UNSAT proofs."""
import argparse
import itertools
import json
import subprocess
import tempfile
from pathlib import Path

from check_cores import HERE, graph
from extensions import representatives


class Formula:
    def __init__(self):
        self.variables = 0
        self.clauses = []

    def new(self):
        self.variables += 1
        return self.variables

    def exactly(self, literals, count):
        literals = list(literals)
        if count > len(literals) // 2:
            literals = [-x for x in literals]
            count = len(literals) - count
        if count < 0:
            self.clauses.append([])
            return
        if count == 0:
            self.clauses.extend([[-x] for x in literals])
            return
        if count == 1:
            self.clauses.append(literals)
            self.clauses.extend([[-a, -b] for a, b in itertools.combinations(literals, 2)])
            return
        # prefix[j-1] means "at least j true literals in the preceding prefix".
        prefix = []
        for v in literals:
            current = []
            for j in range(1, min(count + 1, len(prefix) + 1) + 1):
                z = self.new()
                current.append(z)
                same = prefix[j - 1] if j <= len(prefix) else None
                prev = prefix[j - 2] if j > 1 else None
                if same is not None:
                    self.clauses.append([-same, z])
                self.clauses.append(([-prev] if prev is not None else []) + [-v, z])
                alternatives = [-z] + ([same] if same is not None else [])
                if prev is not None:
                    self.clauses.append(alternatives + [prev])
                self.clauses.append(alternatives + [v])
            prefix = current
        self.clauses.extend([[prefix[count - 1]], [-prefix[count]]])

    def write(self, path):
        with path.open('w') as f:
            print('p cnf', self.variables, len(self.clauses), file=f)
            for clause in self.clauses:
                print(*clause, 0, file=f)


def extension_formula(h, words):
    outer = [set() for _ in range(81)]
    for a, word in enumerate(words):
        for i, shift in enumerate(word):
            if shift >= 0:
                for t in range(3):
                    outer[3 * a + t].add(3 * i + (shift + t) % 3)
    stars = [{j for j in range(81) if k in outer[j]} for k in range(18)]
    assert all(len(h[i]) + len(stars[i]) == 14 for i in range(18))
    for i, j in itertools.combinations(range(18), 2):
        assert len(h[i] & h[j]) + len(stars[i] & stars[j]) == 2 - int(j in h[i])

    f, edges, doubles = Formula(), {}, {}
    for a, b in itertools.combinations(range(27), 2):
        values = []
        for shift in range(3):
            v = f.new()
            edges[a, b, shift] = edges[b, a, -shift % 3] = v
            values.append(v)
            shared = len(outer[3 * a] & outer[3 * b + shift])
            assert shared <= 2
            if shared == 2:
                f.clauses.append([-v])
        d = f.new()
        doubles[a, b] = doubles[b, a] = d
        f.clauses.append([-v for v in values])
        for x, y in itertools.combinations(values, 2):
            f.clauses.extend([[-x, -y, d], [-d, x, y]])

    def edge(i, j):
        return edges[i // 3, j // 3, (j - i) % 3]

    for a in range(27):
        i = 3 * a
        f.exactly((doubles[a, b] for b in range(27) if a != b), 2)
        f.exactly((edge(i, j) for j in range(81) if j // 3 != a), 14 - len(outer[i]))
        for k in range(18):
            rhs = 2 - int(k in outer[i]) - len(h[k] & outer[i])
            f.exactly((edge(i, j) for j in sorted(stars[k]) if j // 3 != a), rhs)

    for a, b in itertools.combinations(range(27), 2):
        i = 3 * a
        for j in range(3 * b, 3 * b + 3):
            shared = len(outer[i] & outer[j])
            if shared == 0:
                continue
            for k in range(81):
                if k // 3 in (a, b):
                    continue
                clause = [-edge(i, k), -edge(j, k)]
                if shared == 1:
                    clause.append(-edge(i, j))
                f.clauses.append(clause)
    return f


def run(directory, solver=None, checker=None, selected=(105, 124)):
    records = json.loads((HERE / 'cores.json').read_text())
    for atlas in selected:
        record = next(r for r in records if r['atlas'] == atlas)
        count, reps = representatives(graph(record['mask']))
        print(f'Atlas {atlas}: {count} incidences in {len(reps)} classes.', flush=True)
        assert (count, len(reps)) == {105: (14, 3), 124: (18, 6)}[atlas]
        for i, (h, cols) in enumerate(reps):
            stem = directory / f'core-{atlas}-{i}'
            cnf, proof = stem.with_suffix('.cnf'), stem.with_suffix('.drat')
            extension_formula(h, cols).write(cnf)
            if solver is None:
                continue
            with stem.with_suffix('.log').open('w') as log:
                result = subprocess.run([solver, cnf, proof], stdout=log, stderr=log)
            if result.returncode != 20:
                raise RuntimeError(f'{cnf.name}: solver exit {result.returncode}, expected UNSAT (20)')
            result = subprocess.run([checker, cnf, proof], stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True)
            if result.returncode or 's VERIFIED' not in result.stdout.splitlines():
                raise RuntimeError(f'{cnf.name}: proof verification failed\n{result.stdout[-1000:]}')
            print(f'{cnf.name}: DRAT verified', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--solver', type=Path, help='CaDiCaL executable')
    parser.add_argument('--checker', type=Path, help='drat-trim executable')
    parser.add_argument('--output', type=Path, help='keep the CNFs, proofs and solver logs here')
    args = parser.parse_args()
    if bool(args.solver) != bool(args.checker) or not (args.output or args.solver):
        parser.error('provide both --solver and --checker, or --output to emit CNFs')
    if args.output:
        args.output.mkdir(parents=True, exist_ok=True)
        run(args.output, args.solver, args.checker)
    else:
        with tempfile.TemporaryDirectory() as raw:
            run(Path(raw), args.solver, args.checker)
