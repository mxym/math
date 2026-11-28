# No additional positive \(5x+1\) cycles with at most 21 local minima

For the **shortcut map** \(T(x)=x/2\) on even positive integers and \(T(x)=(5x+1)/2\) on odd positive integers, a cycle with at most 21 local minima in its least period is one of the three already known cycles:

- \(1,3,8,4,2\): one local minimum.
- \(13,33,83,208,104,52,26\): one local minimum.
- \(17,43,108,54,27,68,34\): two local minima.

Thus an additional positive cycle, if one exists, has **at least 22 local minima**. This counts local minima, not the total period. It does not prove that these are all positive cycles, does not classify nonperiodic or negative trajectories, and is not an assertion on the ordinary \(3x+1\) map.

[The proof](FactorFiveXPlusOneTwentyOneCycles.md) combines new geometric chaining at local minima, exact comparison of 22 linear forms for large minima, and a bounded search of every positive odd starting integer below \(2^{29}\). [Simons (2008), §4, Lemma 16 and table (43)](https://www.impan.pl/shop/publication/transaction/download/product/82891?download.pdf=) gave the three known cycles and the prior exclusion through seven local minima. His two-logarithm estimate is an explicit input here.

## Reproduce

Use Node.js 18+ and ordinary Python 3.10+ (do not use `-O`). The eight scan shards are independent and can be run in parallel.

```sh
sha256sum -c MANIFEST.sha256
python3 verify_factor_five_x_plus_one_21_form_bounds.py
python3 -I -B independent_forms.py
node verify_factor_five_x_plus_one_21_cycle_scan.js --kernel-only
for s in 0 1 2 3 4 5 6 7; do
    node verify_factor_five_x_plus_one_21_cycle_scan.js "$s" || exit 1
done
for s in 0 1 2 3 4 5 6 7; do
    node independent_scan.js "$s" || exit 1
done
```

The independent direct-step scan is a separate implementation, not a wrapper around the compressed odd-block kernel. [The replay notes](RELEASE_NOTES.md) record exactly what each implementation checked. These artifacts are not Lean formalizations.
