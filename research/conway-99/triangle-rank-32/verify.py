"""Check the rank-32 extension obstruction, using two C++17 executables and NumPy."""
from argparse import ArgumentParser
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "triangle-rank"))
from check import TWIN, adjacency, axis_types, canonical, eliminate


def wing_components(adjacency_matrix):
    remaining = set(range(3, 39))
    while remaining:
        component = [min(remaining)]
        remaining.remove(component[0])
        for v in component:
            for site in np.flatnonzero(adjacency_matrix[v]):
                if site in remaining:
                    remaining.remove(site)
                    component.append(site)
        yield component


def possible_words(a):
    """Exact single-vertex restrictions, including the real component balance."""
    shortage = 2 - a - a @ a
    pairs = []
    for h in range(3):
        sites = range(3+12*h, 15+12*h)
        pairs.append(np.array([(i,j) for i,j in combinations(sites,2) if not a[i,j]]))
    choices = np.indices((60,60,60), dtype=np.int16).reshape(3,-1).T
    six = np.hstack([pairs[h][choices[:,h]] for h in range(3)])
    ok = np.ones(len(six), dtype=bool)
    for i,j in combinations(range(6),2):
        ok &= shortage[six[:,i], six[:,j]] >= 1
    for component in wing_components(a):
        ok &= 6*np.isin(six, component).sum(axis=1) == len(component)
    for v in range(3,39):
        neighbors = a[v,six].sum(axis=1)
        ok &= neighbors + (six == v).any(axis=1) <= 2
    return choices[ok], six[ok]


def direction_codes(vectors):
    """Normalize nonzero vectors and encode base eight to compare projective points."""
    vectors = vectors.copy() % 7
    rows = np.flatnonzero(vectors.any(axis=1))
    pivots = np.argmax(vectors[rows] != 0, axis=1)
    reciprocals = np.array([0,1,4,5,2,3,6])
    vectors[rows] = vectors[rows]*reciprocals[vectors[rows,pivots],None] % 7
    powers = np.uint64(8)**np.arange(vectors.shape[1], dtype=np.uint64)
    return vectors.astype(np.uint64) @ powers


def has_common_plane(choices, vectors):
    """Choose the first nonzero direction at a required pair, then work modulo it."""
    required = [np.flatnonzero(choices[:,h] == i) for h in range(3) for i in range(60)]
    if any(len(indices) == 0 for indices in required):
        return False
    codes = direction_codes(vectors)
    groups = [np.unique(codes[indices]) for indices in required]
    forced = [directions for directions in groups if 0 not in directions]
    if not forced:
        return True
    for first in min(forced, key=len):
        v = np.array([(int(first) >> (3*i)) & 7 for i in range(vectors.shape[1])])
        pivot = np.flatnonzero(v)[0]
        residual = direction_codes(vectors-vectors[:,pivot,None]*v)
        shared = None
        for indices in required:
            directions = np.unique(residual[indices])
            if 0 in directions:
                continue
            shared = directions if shared is None else np.intersect1d(
                shared, directions, assume_unique=True)
            if not len(shared):
                break
        else:
            return True
    return False


def obstruction(a, rank):
    shortage = 2-a-a@a
    if np.any(shortage[np.triu_indices(39,1)] < 0):
        return "too many common neighbors in the shell"
    s = 2*a-1+np.eye(39,dtype=int)
    transform, pivots, _ = eliminate(s)
    assert len(pivots) == rank
    choices, six = possible_words(a)
    v = np.full((len(six),39), -1, dtype=int)
    v[np.arange(len(six))[:,None],six] = 1
    pairings = v @ transform[rank:].T % 7
    if rank == 28 and not has_common_plane(choices, pairings):
        return "no common plane for the exterior columns"
    if rank == 31:
        eligible = v[np.all(pairings == 0, axis=1)][:,pivots]
        inverse = eliminate(s[np.ix_(pivots,pivots)])[0]
        norms = np.sum((eligible @ inverse % 7)*eligible, axis=1) % 7
        if np.all(norms == 0):
            return "a rank-one residual would have zero diagonal"
    raise AssertionError("This shell still needs an obstruction")


def main(args):
    charts = [(TWIN,p,q) for p,q in axis_types()]
    assert len(charts) == 3580
    records = [" ".join([str(i), *(str(int(x)) for p in c for x in p)])
               for i,c in enumerate(charts)]
    with TemporaryDirectory() as directory:
        chart_file = Path(directory) / "charts"
        chart_file.write_text("\n".join(records)+"\n")
        def run(start):
            chunk = "\n".join(records[start:start+32])+"\n"
            census = subprocess.run([args.census],input=chunk,text=True,
                                    capture_output=True,check=True).stdout
            result = subprocess.run([args.extend,chart_file],input=census,text=True,
                                    capture_output=True,check=True).stdout
            return census.splitlines(), result.splitlines()
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            chunks = list(pool.map(run, range(0,len(charts),32)))
    before = sorted(line for chunk,_ in chunks for line in chunk)
    after = sorted(line for _,chunk in chunks for line in chunk)
    expected = {
        "census": (33124, "f7b00acd43bf716b485f148e641457bee48923e936f2b6eeaeb182d8410b190e"),
        "extension": (72, "d8df755af3c521d71fa51fd7506de4f036da7cee17b6dcbbad0bfadf2dcf7cb4"),
    }
    for label, lines in [("census",before),("extension",after)]:
        digest = sha256(("\n".join(lines)+"\n").encode()).hexdigest()
        assert (len(lines),digest) == expected[label], label
        print(f"{label} {len(lines)} rows, SHA-256 {digest}",flush=True)
    representatives = {}
    for line in after:
        chart, rank, *p = map(int,line.split())
        key = (chart, canonical((*charts[chart],p)))
        representatives.setdefault(key,(chart,rank,p))
    counts = Counter()
    for chart,rank,p in representatives.values():
        counts[obstruction(adjacency(charts[chart],p),rank)] += 1
    assert sorted(counts.values()) == [1,1,6] and len(representatives) == 8
    print(f"{len(representatives)} representatives, all excluded",dict(counts))


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("census")
    parser.add_argument("extend")
    parser.add_argument("--jobs",type=int,default=1)
    args = parser.parse_args()
    if not __debug__ or args.jobs < 1:
        parser.error("enable Python assertions and use a positive number of jobs")
    main(args)
