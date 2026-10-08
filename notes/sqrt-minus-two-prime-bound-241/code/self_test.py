#!/usr/bin/env python3
"""Negative controls for parent identity, exceptional handling and graph BFS."""
import check_exact as C


def expect_failure(name,call):
    try:call()
    except ValueError:print('REJECTED:',name)
    else:raise RuntimeError('invalid input accepted: '+name)

if __name__=='__main__':
    groups,closure=C.read_source()
    original=C.POS_SHA
    C.POS_SHA='0'*64
    try:expect_failure('wrong pinned positive partition',C.read_source)
    finally:C.POS_SHA=original
    expect_failure('missing exceptional 19-prime factor',
                   lambda:C.extra_exceptional_check([p for p in closure if p!=[1,3]]))
    expect_failure('duplicate local lattice vertex',
                   lambda:C.adjacency(((0,0),(0,0))))
    points=((0,0),(1,0),(5,0))
    edges=C.adjacency(points)
    sizes=sorted(len(part) for part in C.connected_parts(bytearray([1,1,1]),edges))
    C.require(sizes==[1,2],'incorrect component BFS')
    sizes=sorted(len(part) for part in C.connected_parts(bytearray([1,0,1]),edges))
    C.require(sizes==[1,1],'deleted vertex not handled by BFS')
    print('ALL NEGATIVE AND GRAPH CONTROLS PASSED')
