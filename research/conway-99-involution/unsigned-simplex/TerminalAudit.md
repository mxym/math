# Optional audit of the last two singleton charts

This is a supplement to the 262389-byte primary archive, SHA-256 f59122cc87e939d76782b7e9108e72af925391c779e4f931ec715a332549d05e. It adds no graph-level claim. The primary binary atlas and 3,580-chart replay remain necessary for complete coverage. The supplement instruments the same complete two-exception recomputation; it is **not** a separate full generation of all 3,580 charts. Its terminal checker is independently written.

Unzip the primary archive, then copy the contents of this supplement's unsigned15/ into the primary singleton-simplex-packet/unsigned15/ (including both files in expected/). From that latter directory:

    g++ -std=c++17 -O3 -mpopcnt casepair.cpp -o casepair -lgmpxx -lgmp
    { ./casepair 183 184; ./casepair 3377 3378; } >cases-run.txt 2>cases-new.tsv
    cmp cases-new.tsv expected/case-witnesses.tsv
    PYTHONDONTWRITEBYTECODE=1 python3 casecheck.py >literal-check.txt
    cmp literal-check.txt expected/case-literal-check.txt

Each case row gives chart, lift ID, six-positive sign mask g, signed local 16-label rank mod 7, four triples (outer ID, same-mask, opposite-mask), and the six pairs (unsigned T, signed L) on the heavy quartet in lower-triangular order. Domain rows give all 26 distinct outside labels and sizes after the necessary one-label tests. Small rows explicitly list every choice on the two smallest domains: outside ID, two signed star masks, four heavy pairs (T,L). The first lift in each chart also lists one candidate per outside label. Such necessary-test witnesses need not have true Euclidean rank or PSD; indeed the checker finds examples that do not.

There are two lifts in each of the two charts: sign mask 1621 at #183 and 3363 at #3377. In both #183 lifts the two smallest domains have sizes (2,2); in both #3377 lifts these are (1,1). For each of the 4 or 1 candidate pairs respectively, try exactly (T,L)=(0,0),(1,1),(1,-1),(2,0). Independently build all 51 physical vertices and the raw 18-label signed Gram from those literal edges. At each #183 lift, 6 of the 16 link choices violate the physical common-neighbor caps, and all other 10 have signed rank greater than 13 over F₇. At each #3377 lift all four choices violate the physical caps. Thus not even the two smallest domains admit a compatible choice, without relying on any rational-projection congruence at this last step. This last literal rejection is independent; the domain and four-lift enumeration is still the primary, necessary-constraint search with logging.
