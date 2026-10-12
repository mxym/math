# Rebuild the written-proof PDF

From this directory run:

```sh
python3 build.py
```

The script uses the installed `pdflatex` for two passes, disables shell escape, fixes the source date to 9 October 2026, and suppresses volatile PDF timestamps and trailer IDs. It downloads and installs nothing. The resulting file is `source/paper.pdf`.

The release build was repeated in separate temporary directories and gave identical PDF bytes. Exact byte reproduction requires the same TeX engine, packages and fonts; mathematical content is in both `../paper.md` and `source/paper.tex`.

This is written-proof v1. Lean formalization is incomplete. The counterexample changes both marginals; no fixed-one-marginal result or priority claim is certified.
