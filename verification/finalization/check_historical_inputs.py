#!/usr/bin/env python3
"""Positive/negative checks of immutable input recovery after parallel edits."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'manuscripts'))
import historical


def main():
    with tempfile.TemporaryDirectory(prefix='math-pinned-source-control-') as temp:
        root=Path(temp)
        subprocess.run(['git','init','-q'],cwd=root,check=True)
        source=root/'notes/example/proof.txt';source.parent.mkdir(parents=True)
        original=b'Exact old proof source.\n';source.write_bytes(original)
        subprocess.run(['git','add','.'],cwd=root,check=True)
        subprocess.run(['git','-c','user.name=Reproduction control',
                        '-c','user.email=control@example.invalid','commit','-qm',
                        'Create immutable test input'],cwd=root,check=True)
        commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
        (root/'manuscripts').mkdir()
        pins=root/'manuscripts/SOURCE_PINS.json'
        pins.write_text(json.dumps({'commit':commit,'files':{
            'notes/example/proof.txt':sha256(original).hexdigest()}}))
        historical.ROOT=root
        reader=historical.HistoricalInputs()
        if reader.read_bytes('notes/example/proof.txt')!=original or reader.restored:
            raise RuntimeError('Unchanged pinned file not read directly')
        source.write_text('Changed parallel result.\n')
        reader=historical.HistoricalInputs()
        if reader.read_bytes('notes/example/proof.txt')!=original or not reader.restored:
            raise RuntimeError('Exact historical blob not recovered')
        data=json.loads(pins.read_text())
        data['files']['notes/example/proof.txt']='0'*64
        pins.write_text(json.dumps(data))
        try:historical.HistoricalInputs().read_bytes('notes/example/proof.txt')
        except RuntimeError:pass
        else:raise RuntimeError('Incorrect historical hash accepted')
    print('PASS unchanged input, exact historical recovery, and wrong-hash rejection')


if __name__=='__main__':main()
