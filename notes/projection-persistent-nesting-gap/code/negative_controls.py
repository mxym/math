#!/usr/bin/env python3
"""Deliberately corrupt exact certificate data; prove error checks stay active."""
import copy
import json
from pathlib import Path
import check

SOURCE=check.CERT


def reject(label,fn):
    try:
        fn()
    except RuntimeError as err:
        print('REJECTED '+label+': '+str(err)[:140])
    else:
        raise RuntimeError('malicious change incorrectly accepted: '+label)


def corrupt_attained_state():
    raw=json.loads(SOURCE.read_text())
    raw['frontiers'][0][0]['Q']='9'
    levels,_=check.replay_original_base()
    check.exact_B_extension(levels,raw)


def corrupt_frontier_coverage():
    raw=json.loads(SOURCE.read_text())
    raw['frontiers'][0].pop(0)
    levels,_=check.replay_original_base()
    check.exact_B_extension(levels,raw)


def corrupt_tail_potential():
    saved=check.Q5
    try:
        check.Q5=check.F(1,1)
        check.verify_infinite_tail()
    finally:
        check.Q5=saved


def corrupt_parent_hash():
    raw=json.loads(SOURCE.read_text())
    raw['parent_sha256']='0'*64
    levels,_=check.replay_original_base()
    check.exact_B_extension(levels,raw)


if __name__=='__main__':
    reject('nonattainable 57D frontier state',corrupt_attained_state)
    reject('missing dominating 57D frontier state',corrupt_frontier_coverage)
    reject('false infinite-tail potential',corrupt_tail_potential)
    reject('incorrect base-certificate provenance',corrupt_parent_hash)
    print('PASS: four adversarial corruptions all rejected')
