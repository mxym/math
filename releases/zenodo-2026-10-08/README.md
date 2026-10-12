# Public archive verification records

All deposited records are published and their DOIs were confirmed as `findable` in the public DataCite API. Every listed public file was downloaded anonymously and its SHA-256 and byte length checked, together with creator, ORCID, public access and custom rights metadata.

Run `python3 -B verify_downloads.py` to recheck records that do not already have a passing cached report. For a fresh full run, move `PUBLIC_DOWNLOAD_AUDIT.json` aside before running. Python 3 and its standard library suffice; no Zenodo token or login is needed. Remote access or temporary API failures can interrupt a run; they are not treated as passes.

`PUBLICATION_STATE.json` maps each GitHub version to its version DOI, concept DOI, fixed source commit, and exact uploaded-file inventory. `ARCHIVE_AUDIT.json` records the original source Git-object and release-asset byte checks. These checks concern archive integrity, not mathematical correctness or a new Lean execution.

Three large archives use lossless `.partNN` files. Download all their parts, `CHUNKS.json` and `reconstruct.py` into one directory and run `python3 reconstruct.py`. The program checks every part and the complete original archive before creating the restored tar.gz. The local reconstruction executions are recorded in `RECONSTRUCTION_AUDIT.json`; public individual part hashes are in the download audit.

Existing licenses remain in force. Previously unlicensed original materials retain all rights with their rights holders. DOI deposits are later archives of the GitHub disclosures, not retroactive Zenodo publication times or a certification of novelty, priority or peer review.
