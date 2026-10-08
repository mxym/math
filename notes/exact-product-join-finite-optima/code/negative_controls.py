#!/usr/bin/env python3
"""Adversarial controls: verify the exact certificate checker rejects corrupt data."""
import copy
import json
import tempfile
from pathlib import Path
from check import check


ORIGINAL=Path(__file__).resolve().parent.parent/'certificates'/'frontiers48.json'


def rejected(name,mutation):
    payload=json.loads(ORIGINAL.read_text())
    mutation(payload)
    with tempfile.TemporaryDirectory() as tmp:
        corrupted=Path(tmp)/'corrupted.json'
        corrupted.write_text(json.dumps(payload))
        try:
            check(corrupted)
        except RuntimeError as err:
            print(f'REJECTED {name}: {str(err)}')
        else:
            raise RuntimeError(f'corrupted certificate accepted: {name}')


def false_state(d):
    d['states'][1][0]['Q']='2'


def missing_frontier(d):
    d['states'][4].pop(0)
    d['summary'][3]['frontier_size']-=1


def false_maximum(d):
    d['summary'][1]['ratio_num']='17'


if __name__=='__main__':
    rejected('invented positive-dimensional state',false_state)
    rejected('missing dominating frontier vertex',missing_frontier)
    rejected('incorrect reported optimum',false_maximum)
    print('PASS: three adversarial corruptions all rejected')
