"""Independently enumerate all five-subsets; no SAT or search-oracle import."""
import argparse
import itertools
import json
import math
from pathlib import Path


def check_edges(edges, width=6, forbidden_size=5):
    if type(width) is not int or width<6:
        raise ValueError('vertex bound must be an integer at least six')
    if type(forbidden_size) is not int or not 0<=forbidden_size<=5:
        raise ValueError('invalid cover budget')
    if not isinstance(edges, list) or not edges:
        raise ValueError('expected a nonempty list of edges')
    for e in edges:
        if not isinstance(e, (list, tuple)) or len(e) != 6:
            raise ValueError('each edge must contain six labels')
        if any(type(v) is not int or not 0 <= v < width for v in e):
            raise ValueError('vertex label outside the declared bound')
    edges = [tuple(e) for e in edges]
    if len(set(edges)) != len(edges):
        raise ValueError('duplicate edges')
    for e, f in itertools.combinations(edges, 2):
        if not any(a == b for a, b in zip(e, f)):
            raise ValueError('nonintersecting edges')
    # Each bit is a vertex, rather than an edge as in the search oracle.
    edge_masks = [sum(1 << (width*c+v) for c, v in enumerate(e)) for e in edges]
    checked = 0
    for cover in itertools.combinations(range(6*width), forbidden_size):
        cover_mask = sum(1 << v for v in cover)
        if all(cover_mask & e for e in edge_masks):
            raise ValueError(f'{forbidden_size}-cover exists: {cover}')
        checked += 1
    if checked != math.comb(6*width,forbidden_size):
        raise RuntimeError('unexpected enumeration count')
    return checked


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate', type=Path)
    args = ap.parse_args()
    data = json.loads(args.certificate.read_text())
    checked = check_edges(data['edges'],data.get('vertex_bound',6))
    print(f'Intersecting rank-six witness: {checked} five-subsets rejected; cover number six')


if __name__ == '__main__':
    main()
