#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

#ifdef NDEBUG
#error Do not build this verifier with NDEBUG
#endif

using U = std::uint32_t;

int degree(U x) {
    int n = -1;
    for (; x; x >>= 1) ++n;
    return n;
}

U rem(U a, U b) {
    assert(b);
    while (a && degree(a) >= degree(b)) a ^= b << (degree(a) - degree(b));
    return a;
}

U gcd(U a, U b) {
    while (b) {
        U r = rem(a, b);
        a = b;
        b = r;
    }
    return a;
}

struct Field {
    int m, k;
    U size, modulus;

    Field(int mm, int kk, U p) : m(mm), k(kk), size(1U << m), modulus(p) {
        // Binary polynomial irreducibility: no factor of degree <= m/2,
        // and X^(2^m) == X mod modulus. Also handles m=2.
        assert(degree(p) == m && (p & 1U));
        U z = 2;
        for (int i = 1; i <= m; ++i) {
            z = mul(z, z);
            if (i <= m / 2) assert(gcd(p, z ^ 2U) == 1);
        }
        assert(z == 2);
    }

    U mul(U x, U y) const {
        U z = 0;
        while (y) {
            if (y & 1U) z ^= x;
            y >>= 1;
            x <<= 1;
            if (x & size) x ^= modulus;
        }
        return z;
    }

    U power(U x, U e) const {
        U t = 1;
        while (e) {
            if (e & 1U) t = mul(t, x);
            x = mul(x, x);
            e >>= 1;
        }
        return t;
    }

    U trace(U x) const {
        U t = 0;
        for (int i = 0; i < m; ++i) {
            t ^= x;
            x = mul(x, x);
        }
        assert(t <= 1);
        return t;
    }
};

void fwt(std::vector<int>& w) {
    for (std::size_t s = 1; s < w.size(); s <<= 1) {
        for (std::size_t i = 0; i < w.size(); i += s << 1) {
            for (std::size_t j = i; j < i + s; ++j) {
                const int a = w[j], b = w[j+s];
                w[j] = a + b;
                w[j+s] = a - b;
            }
        }
    }
}

void check(int k, U modulus, bool check_full_walsh) {
    const Field f(6*k, k, modulus);
    const U n = f.size;
    std::vector<U> q(n), q2(n), q3(n), q4(n), psi(n), p_inv(n, n), tr(n);
    for (U x = 0; x < n; ++x) {
        q[x] = f.power(x, 1U << k);
        tr[x] = f.trace(x);
    }
    for (U x = 0; x < n; ++x) {
        q2[x] = q[q[x]];
        q3[x] = q[q2[x]];
        q4[x] = q[q3[x]];
        // Use the original unreduced three terms.
        psi[x] = f.mul(x, q[x]) ^ f.mul(q3[x], q[x]) ^ f.mul(q3[x], q4[x]);
        assert(p_inv[psi[x]] == n);
        p_inv[psi[x]] = x;
    }

    // Independently check the rational map Phi_b on K=F_(q^3) for every b in F_q.
    std::vector<U> K;
    for (U t = 0; t < n; ++t) if (q3[t] == t) K.push_back(t);
    assert(K.size() == (1U << (3*k)));
    for (U b : K) if (q[b] == b) {
        std::vector<bool> seen(n, false);
        for (U t : K) {
            const U d = t ^ q[t] ^ 1U;
            assert(d);
            const U z = f.mul(f.mul(t, q[t]) ^ b, f.power(d, U(K.size())-2));
            assert(q3[z] == z && !seen[z]);
            seen[z] = true;
        }
    }
    assert((0U ^ q[0]) == 0); // Removing the +1 makes the denominator vanish at 0.
    std::cout << "k=" << k << ": " << n
              << " distinct psi images, all base-field constants in Phi_b PASS\n";

    auto raw = [&](U x, U y, bool mutant) {
        const U p3 = f.mul(y, f.mul(q[y], mutant ? q3[y] : q2[y]));
        return tr[f.mul(y, psi[x]) ^ p3];
    };
    auto reduced = [&](U x, U y) {
        return tr[f.mul(y, psi[x ^ q4[y]])];
    };

    if (!check_full_walsh) {
        // Deterministic large-field spot check; not used in the proof.
        U state = 0x91fe9f1bU;
        auto next = [&]() {
            state = 1664525U * state + 1013904223U;
            return state & (n-1);
        };
        for (int i = 0; i < 16384; ++i) {
            const U x = next(), y = next();
            assert(raw(x, y, false) == reduced(x, y));
        }
        std::cout << "k=" << k << ": 16384 direct shear checks PASS\n";
        return;
    }

    const std::size_t total = std::size_t(n) * n;
    std::vector<int> w(total);
    std::uint64_t direct_mutant_mismatches = 0;
    for (U y = 0; y < n; ++y)
        for (U x = 0; x < n; ++x) {
            const U f_val = raw(x, y, false);
            assert(f_val == reduced(x, y));
            if (k == 1) direct_mutant_mismatches += raw(x, y, true) != f_val;
            w[x + std::size_t(n) * y] = 1 - 2 * int(f_val);
        }
    if (k == 1) assert(direct_mutant_mismatches != 0);
    fwt(w);

    // Characters in polynomial coordinates are indexed by the trace-dual mask.
    std::vector<U> dual_mask(n, n);
    for (U a = 0; a < n; ++a) {
        U mask = 0;
        for (int i = 0; i < f.m; ++i) mask |= tr[f.mul(a, 1U << i)] << i;
        assert(dual_mask[mask] == n);
        dual_mask[mask] = a;
    }
    std::uint64_t pos = 0, neg = 0;
    for (U j = 0; j < n; ++j)
        for (U i = 0; i < n; ++i) {
            const U a = dual_mask[i], b = dual_mask[j];
            const U z = p_inv[b ^ q2[a]];
            const int predicted = int(n) * (1 - 2 * int(tr[f.mul(a,z)]));
            const int actual = w[i + std::size_t(n) * j];
            assert(actual == predicted);
            if (actual > 0) ++pos; else ++neg;
        }
    assert(pos + neg == total && pos - neg == n);
    std::cout << "k=" << k << ": all " << total << " original truth inputs and Walsh signs PASS; +"
              << pos << " / -" << neg;
    if (k == 1) std::cout << "; changed y exponent differs on " << direct_mutant_mismatches;
    std::cout << '\n';
}

int main() {
    check(1, 0x43U, true);       // X^6 + X + 1
    check(2, 0x1053U, true);     // X^12 + X^6 + X^4 + X + 1
    check(3, 0x40081U, false);   // X^18 + X^7 + 1
}
