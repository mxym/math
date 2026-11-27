/*
 * Canary harness for the header-only Dynamic SHA / Dynamic SHA2 reference code.
 * Compile with exactly one reference header pre-included, for example:
 *   gcc -O0 -std=c99 -include /path/to/dsha2_Ref.h canary_harness.c -o canary
 */
#include <stdio.h>
#include <string.h>

static void run_hash(int bits, size_t expected, unsigned char fill,
                     unsigned char region[160])
{
    unsigned char dummy = 0;
    memset(region, fill, 160);
    if (Hash(bits, &dummy, 0, region + 16) != SUCCESS) {
        fprintf(stderr, "Hash(%d) failed\n", bits);
    }
    (void)expected;
}

static void test_one(int bits)
{
    const size_t expected = (size_t)(bits + 7) / 8;
    unsigned char a[160], b[160];
    size_t i, last = expected, extra = 0;
    int prefix_ok = 1;

    run_hash(bits, expected, 0xA5, a);
    run_hash(bits, expected, 0x5A, b);

    for (i = 0; i < 16; ++i)
        if (a[i] != 0xA5 || b[i] != 0x5A)
            prefix_ok = 0;

    /*
     * The same deterministic output byte cannot equal both distinct canaries.
     * Thus the paired runs avoid a false negative if one output byte happens
     * to equal one chosen sentinel.
     */
    for (i = expected; i < expected + 32; ++i) {
        if (a[16 + i] != 0xA5 || b[16 + i] != 0x5A) {
            ++extra;
            last = i + 1;
        }
    }

    printf("%d: expected=%zu written=%zu extra=%zu prefix_ok=%s",
           bits, expected, last, extra, prefix_ok ? "yes" : "NO");
    if (extra) {
        printf(" suffix=");
        for (i = expected; i < last; ++i)
            printf("%02x", a[16 + i]);
    }
    putchar('\n');
}

int main(void)
{
    test_one(224);
    test_one(256);
    test_one(384);
    test_one(512);
    return 0;
}
