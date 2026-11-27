#!/usr/bin/env python3
"""Reproduce the complete reduced enumeration and audit the raw-to-reduced and flat witnesses."""
import argparse, base64, hashlib, io, lzma, pathlib, os, subprocess, tempfile, urllib.request
from audit import DATA, read, need, audit, affine_check, classify
from collections import Counter
from lift import check
ROOT=pathlib.Path(__file__).resolve().parent
URLS={'raw':'https://langevin.univ-tln.fr/project/indice/rd2-4-7.txt',
      'reduced':'https://langevin.univ-tln.fr/project/indice/representatives.txt'}
TRACE_SHA='5a958ec1101b847332ba3bcad0c29eb38c6d164f035bc329a6df06b92dd723ba'
LIFT_SHA='df2feefeb31417e4f43e656fe7166e89a91aeb1e6e8b004094a8d56965dc46ea'
def run(argv):subprocess.run(list(map(str,argv)),check=True)
def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('--download',action='store_true')
    p.add_argument('--raw',type=pathlib.Path);p.add_argument('--reduced',type=pathlib.Path)
    p.add_argument('--nauty',action='store_true',help='also verify transporter counts independently using pynauty 2.8.8.1')
    p.add_argument('--export-trace',type=pathlib.Path,help='optional: write decompressed plain witness text')
    a=p.parse_args()
    if a.download and (a.raw or a.reduced) or not a.download and not (a.raw and a.reduced):
        p.error('choose either --download or both --raw PATH and --reduced PATH')
    trace=lzma.decompress(base64.b64decode((ROOT/'alignments.xz.b64').read_bytes()))
    need(hashlib.sha256(trace).hexdigest()==TRACE_SHA,'wrong witness stream')
    lifts=(ROOT/'ea-lifts.txt').read_bytes()
    need(hashlib.sha256(lifts).hexdigest()==LIFT_SHA,'wrong lift stream')
    with tempfile.TemporaryDirectory() as temp:
        tmp=pathlib.Path(temp);paths={}
        for mode in URLS:
            path=getattr(a,mode)
            if a.download:
                path=tmp/(mode+'.dat')
                with urllib.request.urlopen(URLS[mode],timeout=90) as r:path.write_bytes(r.read())
            need(hashlib.sha256(path.read_bytes()).hexdigest()==DATA[mode][0], 'wrong '+mode+' source')
            paths[mode]=path
        raw=read(paths['raw'],'raw');reps=read(paths['reduced'],'reduced')
        check(raw,reps,io.BytesIO(lifts))
        exe=tmp/'enum';out=tmp/'calculated.txt'
        run([os.environ.get('CXX','c++'),'-O3','-std=c++17',ROOT/'enumerate.cpp','-o',exe])
        run([exe,paths['raw'],'count-raw'])
        run([exe,paths['reduced'],'reduced','--trace',out])
        need(out.read_bytes()==trace,'recomputed complete trace differs from supplied trace')
        multiplicity=Counter(int(row.split()[1]) for row in io.BytesIO(lifts))
        num=Counter(tuple(map(int,row.split(maxsplit=2)[:2])) for row in io.BytesIO(trace))
        counts=(sum(multiplicity[i]*multiplicity[j] for i,j in num),
                sum(k*multiplicity[i]*multiplicity[j] for (i,j),k in num.items()))
        need(counts==(4296389,77339359954),'raw multiplicity checksum failed')
        if a.nauty:
            audit(reps,io.BytesIO(trace))
            need(classify(raw,counts_only=True)==counts,'raw nauty counts disagree with EA lifts')
            print('PASS: raw graph audit agrees on',counts[0],'ordered pairs and',counts[1],'weighted maps.')
        else:
            pairs=set();n=0
            for row in io.BytesIO(trace):
                vals=list(map(int,row.split()));need(len(vals)==15,'bad witness row')
                i,j,_=affine_check(vals,reps);pairs.add((i,j));n+=1
            need((len(pairs),n)==(11568,37132),'unexpected enumeration totals')
            print('PASS: 37,132 direct sixteen-point witnesses and complete exhaustive enumeration.')
        if a.export_trace:a.export_trace.write_bytes(trace)
if __name__=='__main__':main()
