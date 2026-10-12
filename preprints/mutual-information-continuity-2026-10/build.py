#!/usr/bin/env python3
"""Build the signed article without changing frozen v1 or Lean source."""
from pathlib import Path
import importlib.util
here=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('article_builder',here.parent/'article-revisions-2026-10/build.py')
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
module.build(here,['paper.tex'])
