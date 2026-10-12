#!/usr/bin/env python3
"""Build the editable TeX, PDF and extracted text; no theorem verification."""
from datetime import datetime, timezone
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
env = os.environ.copy()
env['SOURCE_DATE_EPOCH'] = str(int(datetime(2026,10,8,tzinfo=timezone.utc).timestamp()))
env['FORCE_SOURCE_DATE'] = '1'
subprocess.run(['pandoc', 'paper.md', '--standalone', '-t', 'latex', '-o', 'paper.tex'], cwd=HERE, env=env, check=True)
subprocess.run(['pandoc', 'paper.md', '--standalone', '--pdf-engine=xelatex', '-o', 'paper.pdf'], cwd=HERE, env=env, check=True)
subprocess.run(['pdftotext', '-layout', 'paper.pdf', 'results/paper.txt'], cwd=HERE, env=env, check=True)
