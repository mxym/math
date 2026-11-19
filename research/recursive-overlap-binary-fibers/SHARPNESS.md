# Why no universal deterministic-map extension to fibers of size three is possible

This example concerns arbitrary deterministic observations of independent Bernoulli bits only, not positive weighted sums. It is **not** a counterexample to Neunhäuserer Conjecture 3.1.

Take n=24. On each successive block of two bits use the permutation cycling 00→01→11→00 and fixing 10. Apply it on all blocks simultaneously, giving a permutation T of the whole cube of order 3. It has one fixed word (all blocks 10); the other orbits are triples. In each such triple the three Hamming weights sum to 3n/2, since every block has average weight one. Map each orbit to its own label, **except** the triple of all blocks 00, all blocks 01, and all blocks 11, which is split into three distinct singleton labels. Thus both extremal words have singleton fibers, there are four singleton words altogether, and all other fibers have size three.

At p=1/2 each word has mass 2^{-n}, logarithmic derivative s=4(k−n/2) and negative logarithmic second derivative 4n. The output masses of each remaining triple have zero derivative, by their mean Hamming weight. Each triple has mass 3·2^{-n} and each singleton has mass 2^{-n}; using ∑W″=0 in −∑(W″log W+W′²/W) gives
$$2^n H''(1/2)=(\log3-1)\sum_{x\,{\rm singleton}}s_x^2-4n\log3\cdot 4
=8n[(n-2)\log3-n]>0.$$
For n=24 the sign is equivalent to log3>12/11; for instance the first three positive terms in log3=2(1/2+(1/2)³/3+(1/2)⁵/5+…) already exceed 12/11. The two nonextremal singletons have Hamming weight n/2. This is a rigorous finite witness to the sharpness of the universal two-point fiber cap. The construction merges comparable words (e.g. vary just the first block as 00,01,11 and fix the other blocks at 10); no strictly positive weighted sum can furnish this map.
