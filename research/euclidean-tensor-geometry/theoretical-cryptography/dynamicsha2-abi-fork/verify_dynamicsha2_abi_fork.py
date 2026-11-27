#!/usr/bin/env python3
"""Executable certificate for the Dynamic SHA2-256 cross-ABI digest fork.

This is a clean-room model of the 256-bit compression path in the submitted
Dynamic SHA2 reference header.  It intentionally models only byte-aligned
messages of at most 55 bytes, which need exactly one padded block.  That is
enough for the empty-message certificate and avoids conflating this finding
with the reference Update()/Final() buffer-reuse behavior at block boundaries.

Models:
  fixed32 -- the proposal's intended 32-bit word semantics, with a safe rotate
             for count zero.
  lp64    -- the shipped C expressions when uint_32t/unsigned long are 64-bit;
             ROTR32 still uses the literal 32, exactly as in the source.
"""
from __future__ import annotations

import argparse

IV = (
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
    0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
)

EXPECTED_EMPTY = {
    2: {
        "fixed32": "e3491cc1781737fefd334b0e7e6bd7f40432706ac5716aab06d99cdab9f30ea9",
        "lp64":    "895f5512d4a8ad4cdc5204be5e3c652592f50e4877ba14c57c8a989d28e70e91",
    },
    4: {
        "fixed32": "a43c5d67f6435db7479e013e8f43ae3f06c5ea27c890866f304cb8f262da387e",
        "lp64":    "3f082668a6e5cb1cebc3444201f2291c5d60e3267c2b7cc0f12dd054d55fbe2a",
    },
    6: {
        "fixed32": "21e9768d735b1b5b35513a8848dede0aa6d915cddb9977f1d62b44bb24c9ad85",
        "lp64":    "4accf68006adeeb9d09ab5ebfce2e54105779909af11f8e924bde57f95f0cce2",
    },
    8: {
        "fixed32": "8a9510725f8bc37cc1c3cf7488c77d18e25cee2cb386cb55614a09d32c4d047b",
        "lp64":    "6de691d001c1dcb6b044a77251a8f8cd4612cb336222454a28ab1000c03b1516",
    },
}


class WordModel:
    def __init__(self, mode: str):
        if mode not in ("fixed32", "lp64"):
            raise ValueError(mode)
        self.mode = mode
        self.width = 32 if mode == "fixed32" else 64
        self.mask = (1 << self.width) - 1

    def n(self, x: int) -> int:
        return x & self.mask

    def add(self, a: int, b: int) -> int:
        return (a + b) & self.mask

    def xor(self, a: int, b: int) -> int:
        return (a ^ b) & self.mask

    def band(self, a: int, b: int) -> int:
        return (a & b) & self.mask

    def bor(self, a: int, b: int) -> int:
        return (a | b) & self.mask

    def bnot(self, a: int) -> int:
        return (~a) & self.mask

    def rotr32_source(self, x: int, count: int) -> int:
        """Evaluate ROTR32's source expression in this word model."""
        count &= 31
        x &= self.mask
        if self.mode == "fixed32":
            # The literal source expression shifts by 32 when count==0, which
            # is undefined for a 32-bit type.  fixed32 is the intended repair.
            if count == 0:
                return x
            return ((x >> count) | (x << (32 - count))) & self.mask
        # On LP64 both shift counts are <64, so the shipped expression is
        # defined and the high half is retained.
        return ((x >> count) | (x << (32 - count))) & self.mask


def _f3(m: WordModel, selector: int, x: int, y: int, z: int) -> int:
    if selector == 0:
        return m.xor(m.xor(x, y), z)
    if selector == 1:
        return m.xor(m.band(x, y), z)
    if selector == 2:
        return m.bor(m.bnot(m.bor(x, z)), m.band(x, m.xor(y, z)))
    if selector == 3:
        return m.bor(m.bnot(m.bor(x, m.xor(y, z))), m.band(x, m.bnot(z)))
    raise AssertionError(selector)


def _mix_sum(m: WordModel, ch: list[int]) -> int:
    t = m.xor(ch[0], ch[1])
    t = m.add(t, ch[2])
    t = m.xor(t, ch[3])
    t = m.add(t, ch[4])
    t = m.xor(t, ch[5])
    t = m.add(t, ch[6])
    return m.xor(t, ch[7])


def compress256(block: bytes, chaining: tuple[int, ...], rounds: int, mode: str) -> tuple[int, ...]:
    if len(block) != 64:
        raise ValueError("one 64-byte block required")
    if not 1 <= rounds <= 8:
        raise ValueError("rounds must be in 1..8")
    m = WordModel(mode)
    w = [int.from_bytes(block[4*i:4*i+4], "big") for i in range(16)]
    ch = [m.n(x) for x in chaining]
    original = ch.copy()

    for i in range(rounds):
        for i1 in (0, 8):
            wi = w[i + i1]

            temp = m.rotr32_source(_mix_sum(m, ch), wi & 31)
            old = ch.copy()
            ch[7] = old[6]
            ch[6] = m.rotr32_source(old[5], (wi >> 5) & 31)
            ch[5] = m.add(old[4], w[((i + 3) % 8) + i1])
            ch[4] = m.rotr32_source(old[3], (wi >> 10) & 31)
            ch[3] = m.add(
                w[((i + 2) % 8) + i1],
                _f3(m, wi >> 30, old[0], old[1], old[2]),
            )
            ch[2], ch[1] = old[1], old[0]
            ch[0] = m.add(temp, w[((i + 1) % 8) + i1])

            temp = m.rotr32_source(_mix_sum(m, ch), (wi >> 15) & 31)
            old = ch.copy()
            ch[7] = m.add(old[6], w[((i + 7) % 8) + i1])
            ch[6] = m.rotr32_source(old[5], (wi >> 20) & 31)
            ch[5] = m.add(old[4], w[((i + 6) % 8) + i1])
            ch[4] = m.rotr32_source(old[3], (wi >> 25) & 31)
            ch[3] = m.add(
                w[((i + 5) % 8) + i1],
                _f3(m, i % 4, old[0], old[1], old[2]),
            )
            ch[2], ch[1] = m.add(old[1], wi), old[0]
            ch[0] = m.add(temp, w[((i + 4) % 8) + i1])

        if i == 0:
            for _ in range(9):
                temp = m.xor(m.add(m.xor(m.add(m.xor(m.add(ch[0], ch[1]), ch[2]), ch[3]), ch[4]), ch[5]), ch[6])
                temp = ((temp >> 17) ^ temp) & 0x1FFFF
                temp = ((temp >> 10) ^ temp) & 0x3FF
                temp = ((temp >> 5) ^ temp) & 0x1F
                temp = m.rotr32_source(ch[7], temp)
                ch = [temp, ch[0], ch[1], ch[2], ch[3], ch[4], ch[5], ch[6]]

    return tuple(m.add(original[i], ch[i]) for i in range(8))


def hash256_short(message: bytes, rounds: int, mode: str) -> str:
    if len(message) > 55:
        raise ValueError("certificate model is deliberately limited to 0..55 bytes")
    block = bytearray(message)
    block.append(0x80)
    block.extend(b"\x00" * (56 - len(block)))
    block.extend((8 * len(message)).to_bytes(8, "big"))
    state = compress256(bytes(block), IV, rounds, mode)
    return "".join(f"{x & 0xFFFFFFFF:08x}" for x in state)


def self_test() -> None:
    for rounds, pair in EXPECTED_EMPTY.items():
        got32 = hash256_short(b"", rounds, "fixed32")
        got64 = hash256_short(b"", rounds, "lp64")
        assert got32 == pair["fixed32"], (rounds, "fixed32", got32)
        assert got64 == pair["lp64"], (rounds, "lp64", got64)
        assert got32 != got64, (rounds, "unexpected equality")
    print("PASS: all four empty-message ABI-fork certificates reproduced")
    for rounds in sorted(EXPECTED_EMPTY):
        print(f"r={rounds}: fixed32={EXPECTED_EMPTY[rounds]['fixed32']}")
        print(f"r={rounds}: lp64   ={EXPECTED_EMPTY[rounds]['lp64']}")


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--self-test", action="store_true")
    p.add_argument("--rounds", type=int, default=8)
    p.add_argument("--mode", choices=("fixed32", "lp64"), default="lp64")
    p.add_argument("--message-hex", default="")
    args = p.parse_args()
    if args.self_test:
        self_test()
    else:
        print(hash256_short(bytes.fromhex(args.message_hex), args.rounds, args.mode))


if __name__ == "__main__":
    main()
