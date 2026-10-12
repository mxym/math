#!/usr/bin/env python3
"""Adversarial controls for both exact dimension-55 proof certificates."""
import json
from pathlib import Path
import tempfile
from check_all_tree import check as check_C
from check_two_layer import check as check_B

ROOT=Path(__file__).resolve().parent.parent


def reject(label,source,mutate,verifier):
    data=json.loads(Path(source).read_text())
    mutate(data)
    with tempfile.TemporaryDirectory() as directory:
        damaged=Path(directory)/'corrupt.json'
        damaged.write_text(json.dumps(data,separators=(',',':'))+'\n')
        try:
            verifier(damaged,quiet=True)
        except RuntimeError as e:
            print(f'REJECTED {label}: {e}')
        else:
            raise RuntimeError('invalid exact certificate wrongly accepted: '+label)


if __name__=='__main__':
    c=ROOT/'certificates/all_tree49to55.json'
    b=ROOT/'certificates/two_layer56.json'
    reject('false product/join state',c,
           lambda x:x['frontiers'][0][0].__setitem__('Q','3'),check_C)
    reject('false point H coordinate',b,
           lambda x:x['frontiers'][1][0].__setitem__('H','2'),check_B)
    reject('false two-layer reported optimum',b,
           lambda x:x['summary'][0].__setitem__('sharp_ratio','3'),check_B)
    print('PASS: three hostile certificate mutations rejected')
