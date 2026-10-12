# Exact quadratic-orders Main source archive

The frozen 14,635,994-byte source archive is stored in two ordered, unmodified byte ranges because the publication connector rejects request bodies above 16 MiB. Base64 encoding the single archive exceeds that transport limit. This is a storage-only split, not a new archive or a new source revision.

The reconstructed archive has 1,448 regular files under `formalizations/quadratic-orders-main`. Its SHA-256 is:

`8e16e2191c788738dbe3592578fb8c4a09082215ec373ff8d87201fbe6a15e6f`

From this directory, after downloading both parts and `SHA256SUMS`, run:

```sh
sha256sum --check SHA256SUMS
cat part-00 part-01 > ../quadratic-orders-main-source-20261008-v2-final.tar.gz
printf '%s  %s\n' 8e16e2191c788738dbe3592578fb8c4a09082215ec373ff8d87201fbe6a15e6f ../quadratic-orders-main-source-20261008-v2-final.tar.gz | sha256sum --check -
```

Do not decompress either part separately. Concatenation in the displayed order reproduces the exact reviewed `.tar.gz` bytes; no tar or gzip regeneration is needed. The complete expanded source is also [available in the repository](../../formalizations/quadratic-orders-main/README.md). The [publication manifest](../2026-10-08-quadratic-orders-main.json) binds this archive, both parts, the source package, completed public-run evidence and independent final review.
