"""Independent exact recount of the perturbation using all induced weighted walks.
Uses the shared frozen input but NOT the formula implementation in verify.py.
Requires a little-endian Linux system with GNU C++17 and GMP.
"""
from array import array
from fractions import Fraction
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

SOURCE = Path(__file__).resolve().parent
BASE = Fraction(27220838459434583306277336063848530765605851167,
                903180180540490237232196590042258640992206848000)
BOUND = Fraction(17013023763767619940673353171840153525115959621,
                 564487612837806398270122868776411650620129280000)


def require(test, reason):
    if not test:
        raise ValueError(reason)


def checked(path, digest):
    data = Path(path).read_bytes()
    require(hashlib.sha256(data).hexdigest() == digest, str(path) + ': SHA-256 mismatch')
    return gzip.decompress(data)


def main(path):
    require(sys.byteorder == 'little' and array('i').itemsize == 4,
            'This exporter requires little-endian 32-bit C int.')
    d = json.loads(checked(path, '82c28f7761f8392df6ed1728b5eefdc4ef388b266fc2beb1a2f0a54f7dd2631a'))
    n = 3840
    den = 2**20
    require(d['block_weights'] == [1]*n and d['edge_probability_denominator'] == den, 'unexpected base')
    rows = d['red_probability_numerators']
    require(len(rows) == n and all(len(row) == n for row in rows), 'wrong base dimensions')
    with tempfile.TemporaryDirectory() as work:
        wd = Path(work)
        with (wd/'matrix').open('wb') as f:
            for row in rows:
                array('i', row).tofile(f)
        (wd/'triangles').write_bytes(checked(SOURCE/'triangles.tsv.gz',
            'f5be0d010110b6ecaf2eb618efb1909197c2c6eea11fd64c6288f4f263072411'))
        subprocess.run(['g++', '-std=c++17', '-O2', str(SOURCE/'independent_walks.cpp'),
                        '-lgmpxx', '-lgmp', '-o', str(wd/'count')], check=True)
        out = subprocess.check_output([str(wd/'count'), str(wd/'matrix'), str(wd/'triangles')], text=True)
    ntri, nneg, ncolor, nedge, numerator = map(int, out.split())
    require((ntri, nneg, ncolor, nedge) == (8320, 8320, 23, 24960), 'packing/negativity mismatch')
    delta = Fraction(numerator, n**4*den**6)
    require(delta == BOUND-BASE, 'independent weighted-walk count disagrees')
    print('Triangles / negative / labels / support edges:', ntri, nneg, ncolor, nedge)
    print('Raw signed numerator:', numerator)
    print('Reduced change:', delta)
    print('Bound:', BASE+delta)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('usage: python3 check_walks.py c89_stepgraphon_D20.json.gz')
    main(sys.argv[1])
