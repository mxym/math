"""Independent GF(2) word enumeration and augmented stabilizer equations."""
import argparse
from collections import Counter
from hashlib import sha1, sha256
from itertools import combinations
from functools import reduce
from pathlib import Path
import re


def row_reduce(matrix, width):
    matrix = list(matrix)
    i = 0
    for bit in (1 << p for p in range(width)):
        at = next((k for k in range(i, len(matrix)) if matrix[k] & bit), None)
        if at is None:
            continue
        matrix[i], matrix[at] = matrix[at], matrix[i]
        for k in range(i+1, len(matrix)):
            if matrix[k] & bit:
                matrix[k] ^= matrix[i]
        i += 1
    return i


def generator_rows(columns, d):
    return [sum(((c >> j) & 1) << i for i, c in enumerate(columns))
            for j in range(d)]


def span(rows):
    words = [0]
    for row in rows:
        words += [word ^ row for word in words]
    return words


def augmented(lines, d):
    width = d*d + 4*len(lines)
    equations = []
    for i, (a, b) in enumerate(lines):
        for column, p in enumerate((a, b)):
            for coordinate in range(d):
                eq = sum(1 << (d*j+coordinate) for j in range(d) if p >> j & 1)
                eq |= ((a >> coordinate) & 1) << (d*d+4*i+2*column)
                eq |= ((b >> coordinate) & 1) << (d*d+4*i+2*column+1)
                equations.append(eq)
    return equations, width


def provenance(path, pts):
    raw = path.read_bytes()
    assert len(raw) == 23363
    assert sha256(raw).hexdigest() == '842b8cbc8f3c9f0c1ac284b8ee3d0f46d45049f26ce9415ca03cebbf645f4d82'
    obj = ('blob %d\0' % len(raw)).encode() + raw
    assert sha1(obj).hexdigest() == '8b546714bd25b3a71944995c5f823034293d3943'
    m = re.search(rb"'n'\s*:\s*198[\s\S]*?'source'\s*:", raw)
    assert m
    pieces = re.findall(rb'"([01]+)"', m.group())
    assert len(pieces) == 20
    rows = [pieces[j]+pieces[j+1] for j in range(0, 20, 2)]
    assert {len(row) for row in rows} == {198}
    assert sha256(b'\n'.join(rows)+b'\n').hexdigest() == '898853c72c714e715a2d1d67a57180f903648746738ae07a79746b52ce9510b5'
    columns = [int(bytes(reversed(t)), 2) for t in zip(*rows)]
    assert len(columns) == len(set(columns)) == 198 and set(columns) == pts
    print('optional upstream: tagged raw Git blob, canonical row digest, and all 198 labels match')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--sage-file', type=Path)
    args = parser.parse_args()
    path = Path(__file__).with_name('partition.tsv')
    lines = [tuple(map(int, line.split())) for line in path.read_text().splitlines()]
    assert len(lines) == 66 and all(len(L) == 3 and len(set(L)) == 3 for L in lines)
    assert all(max(L) < 1024 and min(L) > 0 and L[0] ^ L[1] ^ L[2] == 0 for L in lines)
    pairs = [(a, b) for a, b, _ in lines]
    columns = [p for line in lines for p in line]
    d = 10
    word_sq = span(generator_rows([p for pair in pairs for p in pair], d))
    word_sb = span(generator_rows(columns, d))
    assert len(set(word_sq)) == len(set(word_sb)) == 1024
    even = sum(1 << (2*i) for i in range(66))
    qweights = [((v | (v >> 1)) & even).bit_count() for v in word_sq]
    assert Counter(qweights) == {0: 1, 48: 825, 56: 198}
    assert all(2*q == b.bit_count() for q, b in zip(qweights, word_sb))
    assert len(set(columns)) == 198
    assert all(row_reduce(A+B, d) == 4 for A, B in combinations(pairs, 2))
    matrix, width = augmented(pairs, d)
    assert (len(matrix), width, row_reduce(matrix, width)) == (1320, 364, 363)
    common_I = sum(1 << (d*j+j) for j in range(d))
    local_I = sum(9 << (d*d+4*j) for j in range(66))  # column-major [[1,0],[0,1]]
    assert all((eq & (common_I | local_I)).bit_count() % 2 == 0 for eq in matrix)
    test, testwidth = augmented([(1, 2), (4, 8)], 4)  # ordinary F4^2 coordinate lines
    assert (len(test), testwidth, row_reduce(test, testwidth)) == (16, 24, 16)
    J = (2, 3, 8, 12)
    T = 14  # column-major [[0,1],[1,1]], representing multiplication by omega
    field_action = sum(col << (4*j) for j, col in enumerate(J)) | T << 16 | T << 20
    assert all((eq & field_action).bit_count() % 2 == 0 for eq in test)
    for j, p in enumerate(J):
        assert (p ^ (1 << j)) == reduce(int.__xor__, (J[k] for k in range(4) if (p >> k) & 1), 0)
    print('independent: 1024 distinct words; expanded binary weight equals twice quaternary word-by-word')
    print('independent: 2145 rank-four pairs; augmented system rank 363 of 364; ordinary F4^2 control PASS')
    if args.sage_file:
        provenance(args.sage_file, set(columns))


if __name__ == '__main__':
    main()
