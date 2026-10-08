#!/usr/bin/env python3
"""Check that the exact proof replay rejects several corrupted hypotheses."""
import check


def reject(label, key, value):
    saved=getattr(check,key)
    try:
        setattr(check,key,value)
        try:
            check.check()
        except RuntimeError as exc:
            print(f'REJECTED {label}: {exc}')
        else:
            raise RuntimeError('incorrect certificate accepted: '+label)
    finally:
        setattr(check,key,saved)


if __name__=='__main__':
    reject('false pi lower bound','PI_LO',check.F(22,7))
    reject('false two-layer spectral winner','Q5',check.F(1))
    reject('false affine-defect winner','Q4',check.F(1))
    print('PASS: all three corruptions rejected')
