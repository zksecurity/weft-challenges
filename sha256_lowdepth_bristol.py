#!/usr/bin/env python3
"""Generate a low-AND-depth SHA-256 Boolean circuit in Bristol Fashion.

Gate model:
  * XOR and INV have multiplicative depth 0.
  * AND has multiplicative depth 1.

The circuit expects already padded 512-bit SHA-256 blocks. Input bits are
ordered exactly as the bits of the block byte string: byte 0 bit 7 first,
then byte 0 bit 6, ..., byte 63 bit 0. Output bits use standard digest byte
order (most-significant bit first).

Modes:
  fixed-iv    SHA-256 over a fixed number of already padded blocks, starting
              from the standard IV. Inputs: 512 * blocks bits.
  compression One compression function. Inputs: 256 chaining-value bits in
              digest bit order, followed by one 512-bit block. Outputs: the
              updated 256-bit chaining value in digest bit order.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import heapq
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

MASK32 = (1 << 32) - 1

IV = [
    0x6A09E667,
    0xBB67AE85,
    0x3C6EF372,
    0xA54FF53A,
    0x510E527F,
    0x9B05688C,
    0x1F83D9AB,
    0x5BE0CD19,
]

K = [
    0x428A2F98, 0x71374491, 0xB5C0FBCF, 0xE9B5DBA5,
    0x3956C25B, 0x59F111F1, 0x923F82A4, 0xAB1C5ED5,
    0xD807AA98, 0x12835B01, 0x243185BE, 0x550C7DC3,
    0x72BE5D74, 0x80DEB1FE, 0x9BDC06A7, 0xC19BF174,
    0xE49B69C1, 0xEFBE4786, 0x0FC19DC6, 0x240CA1CC,
    0x2DE92C6F, 0x4A7484AA, 0x5CB0A9DC, 0x76F988DA,
    0x983E5152, 0xA831C66D, 0xB00327C8, 0xBF597FC7,
    0xC6E00BF3, 0xD5A79147, 0x06CA6351, 0x14292967,
    0x27B70A85, 0x2E1B2138, 0x4D2C6DFC, 0x53380D13,
    0x650A7354, 0x766A0ABB, 0x81C2C92E, 0x92722C85,
    0xA2BFE8A1, 0xA81A664B, 0xC24B8B70, 0xC76C51A3,
    0xD192E819, 0xD6990624, 0xF40E3585, 0x106AA070,
    0x19A4C116, 0x1E376C08, 0x2748774C, 0x34B0BCB5,
    0x391C0CB3, 0x4ED8AA4A, 0x5B9CCA4F, 0x682E6FF3,
    0x748F82EE, 0x78A5636F, 0x84C87814, 0x8CC70208,
    0x90BEFFFA, 0xA4506CEB, 0xBEF9A3F7, 0xC67178F2,
]


@dataclass(frozen=True)
class Gate:
    op: str
    ins: tuple[int, ...]
    out: int


class Circuit:
    def __init__(self, n_inputs: int) -> None:
        if n_inputs <= 0:
            raise ValueError("at least one input wire is required")
        self.n_inputs = n_inputs
        self.depth: list[int] = [0] * n_inputs
        self.gates: list[Gate] = []
        self.and_count = 0

        # Affine constants. Bristol Fashion has no native constant gates.
        self.zero = self.xor(0, 0)
        self.one = self.inv(self.zero)

    @property
    def n_wires(self) -> int:
        return len(self.depth)

    def _new(self, op: str, ins: tuple[int, ...], d: int) -> int:
        out = len(self.depth)
        self.depth.append(d)
        self.gates.append(Gate(op, ins, out))
        if op == "AND":
            self.and_count += 1
        return out

    def xor(self, x: int, y: int) -> int:
        return self._new("XOR", (x, y), max(self.depth[x], self.depth[y]))

    def and_(self, x: int, y: int) -> int:
        return self._new("AND", (x, y), 1 + max(self.depth[x], self.depth[y]))

    def inv(self, x: int) -> int:
        return self._new("INV", (x,), self.depth[x])

    def xor_many(self, xs: Sequence[int]) -> int:
        if not xs:
            return self.zero
        acc = xs[0]
        for x in xs[1:]:
            acc = self.xor(acc, x)
        return acc

    def const_word(self, value: int) -> list[int]:
        return [self.one if ((value >> i) & 1) else self.zero for i in range(32)]

    @staticmethod
    def word_depth(word: Sequence[int], depths: Sequence[int]) -> int:
        return max(depths[w] for w in word)

    def copy_for_output(self, x: int) -> int:
        # Keep all designated output wires contiguous at the end.
        return self.xor(x, self.zero)


def xor_words(c: Circuit, *words: Sequence[int]) -> list[int]:
    if not words:
        raise ValueError("xor_words needs at least one word")
    return [c.xor_many([w[i] for w in words]) for i in range(32)]


def rotr(word: Sequence[int], n: int) -> list[int]:
    # Internal word representation is little-endian by bit significance.
    n %= 32
    return [word[(i + n) % 32] for i in range(32)]


def shr(c: Circuit, word: Sequence[int], n: int) -> list[int]:
    return [word[i + n] if i + n < 32 else c.zero for i in range(32)]


def ch(c: Circuit, x: Sequence[int], y: Sequence[int], z: Sequence[int]) -> list[int]:
    # z XOR x AND (y XOR z): one AND per bit.
    out: list[int] = []
    for i in range(32):
        yz = c.xor(y[i], z[i])
        prod = c.and_(x[i], yz)
        out.append(c.xor(z[i], prod))
    return out


def maj(c: Circuit, x: Sequence[int], y: Sequence[int], z: Sequence[int]) -> list[int]:
    # x XOR (x XOR y) AND (x XOR z): one AND per bit.
    out: list[int] = []
    for i in range(32):
        xy = c.xor(x[i], y[i])
        xz = c.xor(x[i], z[i])
        prod = c.and_(xy, xz)
        out.append(c.xor(x[i], prod))
    return out


def csa3(c: Circuit, x: Sequence[int], y: Sequence[int], z: Sequence[int]) -> tuple[list[int], list[int]]:
    """3:2 carry-save compressor modulo 2^32.

    Returns s, shifted-carry with x+y+z == s+carry (mod 2^32).
    The discarded carry out means only 31 ANDs are needed.
    """
    s: list[int] = []
    carry: list[int] = [c.zero]
    for i in range(32):
        s.append(c.xor_many((x[i], y[i], z[i])))
        if i < 31:
            xy = c.xor(x[i], y[i])
            xz = c.xor(x[i], z[i])
            carry.append(c.xor(x[i], c.and_(xy, xz)))
    return s, carry


def add32_sklansky(c: Circuit, x: Sequence[int], y: Sequence[int]) -> list[int]:
    """Modulo-2^32 adder using a 5-stage Sklansky prefix network.

    It omits carry-out and therefore uses exactly 181 AND gates:
    31 initial generates plus 75 prefix nodes times two ANDs.
    """
    p_orig = [c.xor(x[i], y[i]) for i in range(32)]

    # Only bit positions 0..30 are needed to form carries into sums 1..31.
    P = p_orig[:31]
    G = [c.and_(x[i], y[i]) for i in range(31)]

    for stage in range(5):
        half = 1 << stage
        block = half << 1
        old_P = P[:]
        old_G = G[:]
        for base in range(0, 31, block):
            pivot = base + half - 1
            if pivot >= 31:
                continue
            stop = min(base + block, 31)
            for i in range(base + half, stop):
                # (G_hi,P_hi) o (G_lo,P_lo)
                G[i] = c.xor(old_G[i], c.and_(old_P[i], old_G[pivot]))
                P[i] = c.and_(old_P[i], old_P[pivot])

    out = [p_orig[0]]
    for i in range(1, 32):
        out.append(c.xor(p_orig[i], G[i - 1]))
    return out


def sum_words(c: Circuit, words: Iterable[Sequence[int]]) -> list[int]:
    """Arrival-time-aware carry-save reduction followed by a prefix adder."""
    heap: list[tuple[int, int, list[int]]] = []
    serial = 0
    for word in words:
        w = list(word)
        heapq.heappush(heap, (Circuit.word_depth(w, c.depth), serial, w))
        serial += 1
    if len(heap) < 2:
        raise ValueError("sum_words needs at least two operands")
    while len(heap) > 2:
        a = heapq.heappop(heap)[2]
        b = heapq.heappop(heap)[2]
        d = heapq.heappop(heap)[2]
        s, carry = csa3(c, a, b, d)
        for w in (s, carry):
            heapq.heappush(heap, (Circuit.word_depth(w, c.depth), serial, w))
            serial += 1
    a = heapq.heappop(heap)[2]
    b = heapq.heappop(heap)[2]
    return add32_sklansky(c, a, b)


def big_sigma0(c: Circuit, x: Sequence[int]) -> list[int]:
    return xor_words(c, rotr(x, 2), rotr(x, 13), rotr(x, 22))


def big_sigma1(c: Circuit, x: Sequence[int]) -> list[int]:
    return xor_words(c, rotr(x, 6), rotr(x, 11), rotr(x, 25))


def small_sigma0(c: Circuit, x: Sequence[int]) -> list[int]:
    return xor_words(c, rotr(x, 7), rotr(x, 18), shr(c, x, 3))


def small_sigma1(c: Circuit, x: Sequence[int]) -> list[int]:
    return xor_words(c, rotr(x, 17), rotr(x, 19), shr(c, x, 10))


def bits_msb_to_internal_words(bits: Sequence[int]) -> list[list[int]]:
    if len(bits) % 32:
        raise ValueError("bit count must be divisible by 32")
    words: list[list[int]] = []
    for off in range(0, len(bits), 32):
        external = bits[off:off + 32]   # word bit 31 down to bit 0
        words.append(list(reversed(external)))
    return words


def internal_words_to_bits_msb(words: Sequence[Sequence[int]]) -> list[int]:
    out: list[int] = []
    for w in words:
        out.extend(reversed(w))
    return out


def message_schedule(c: Circuit, block_bits: Sequence[int]) -> tuple[list[list[int]], int]:
    if len(block_bits) != 512:
        raise ValueError("a SHA-256 block must contain 512 bits")
    W = bits_msb_to_internal_words(block_bits)
    for t in range(16, 64):
        W.append(sum_words(c, (
            small_sigma1(c, W[t - 2]),
            W[t - 7],
            small_sigma0(c, W[t - 15]),
            W[t - 16],
        )))
    return W, max(Circuit.word_depth(w, c.depth) for w in W)


def compress(c: Circuit, H: Sequence[Sequence[int]], block_bits: Sequence[int]) -> tuple[list[list[int]], dict[str, int]]:
    W, schedule_depth = message_schedule(c, block_bits)
    a, b, cc, d, e, f, g, h = [list(w) for w in H]
    k_words = [c.const_word(v) for v in K]

    for t in range(64):
        s1 = big_sigma1(c, e)
        choose = ch(c, e, f, g)
        s0 = big_sigma0(c, a)
        majority = maj(c, a, b, cc)

        # Flatten the round rather than materializing T1 and then adding T2/d.
        new_a = sum_words(c, (h, s1, choose, k_words[t], W[t], s0, majority))
        new_e = sum_words(c, (d, h, s1, choose, k_words[t], W[t]))
        a, b, cc, d, e, f, g, h = new_a, a, b, cc, new_e, e, f, g

    state_depth = max(Circuit.word_depth(w, c.depth) for w in (a, b, cc, d, e, f, g, h))
    out = [sum_words(c, (H[i], w)) for i, w in enumerate((a, b, cc, d, e, f, g, h))]
    output_depth = max(Circuit.word_depth(w, c.depth) for w in out)
    return out, {
        "schedule_depth": schedule_depth,
        "state_depth_before_feedforward": state_depth,
        "output_depth": output_depth,
    }


def build_fixed_iv(blocks: int) -> tuple[Circuit, list[int], dict[str, int]]:
    if blocks < 1:
        raise ValueError("blocks must be positive")
    c = Circuit(512 * blocks)
    H = [c.const_word(v) for v in IV]
    max_schedule = 0
    last_stats: dict[str, int] = {}
    for j in range(blocks):
        block = list(range(512 * j, 512 * (j + 1)))
        H, stats = compress(c, H, block)
        max_schedule = max(max_schedule, stats["schedule_depth"])
        last_stats = stats
    output_bits = [c.copy_for_output(w) for w in internal_words_to_bits_msb(H)]
    stats = dict(last_stats)
    stats["max_schedule_depth"] = max_schedule
    stats["output_depth"] = max(c.depth[w] for w in output_bits)
    return c, output_bits, stats


def build_compression() -> tuple[Circuit, list[int], dict[str, int]]:
    c = Circuit(256 + 512)
    H = bits_msb_to_internal_words(list(range(256)))
    block = list(range(256, 768))
    out, stats = compress(c, H, block)
    output_bits = [c.copy_for_output(w) for w in internal_words_to_bits_msb(out)]
    stats["output_depth"] = max(c.depth[w] for w in output_bits)
    return c, output_bits, stats


def write_bristol(path: Path, c: Circuit, outputs: Sequence[int]) -> None:
    if len(outputs) != 256:
        raise ValueError("expected 256 output wires")
    expected = list(range(c.n_wires - len(outputs), c.n_wires))
    if list(outputs) != expected:
        raise ValueError("output wires must be the final contiguous wires")

    opener = gzip.open if path.suffix == ".gz" else open
    mode = "wt"
    with opener(path, mode, encoding="ascii", newline="\n") as f:
        f.write(f"{len(c.gates)} {c.n_wires}\n")
        f.write(f"1 {c.n_inputs}\n")
        f.write("1 256\n\n")
        for gate in c.gates:
            ins = " ".join(str(x) for x in gate.ins)
            f.write(f"{len(gate.ins)} 1 {ins} {gate.out} {gate.op}\n")


def eval_circuit(c: Circuit, input_bits: Sequence[int], outputs: Sequence[int]) -> list[int]:
    if len(input_bits) != c.n_inputs:
        raise ValueError(f"expected {c.n_inputs} input bits, got {len(input_bits)}")
    wires = [int(bool(x)) for x in input_bits] + [0] * (c.n_wires - c.n_inputs)
    for gate in c.gates:
        if gate.op == "XOR":
            wires[gate.out] = wires[gate.ins[0]] ^ wires[gate.ins[1]]
        elif gate.op == "AND":
            wires[gate.out] = wires[gate.ins[0]] & wires[gate.ins[1]]
        elif gate.op == "INV":
            wires[gate.out] = wires[gate.ins[0]] ^ 1
        else:
            raise ValueError(f"unknown gate: {gate.op}")
    return [wires[w] for w in outputs]


def bytes_to_bits_msb(data: bytes) -> list[int]:
    return [(byte >> bit) & 1 for byte in data for bit in range(7, -1, -1)]


def bits_to_bytes_msb(bits: Sequence[int]) -> bytes:
    if len(bits) % 8:
        raise ValueError("bit count must be divisible by 8")
    out = bytearray()
    for off in range(0, len(bits), 8):
        value = 0
        for bit in bits[off:off + 8]:
            value = (value << 1) | bit
        out.append(value)
    return bytes(out)


def pad_sha256(message: bytes) -> bytes:
    bit_len = len(message) * 8
    padded = bytearray(message)
    padded.append(0x80)
    while len(padded) % 64 != 56:
        padded.append(0)
    padded.extend(bit_len.to_bytes(8, "big"))
    return bytes(padded)


def self_test() -> None:
    c, outputs, stats = build_fixed_iv(1)
    padded = pad_sha256(b"abc")
    if len(padded) != 64:
        raise AssertionError("abc should use one padded block")
    got = bits_to_bytes_msb(eval_circuit(c, bytes_to_bits_msb(padded), outputs))
    expected = hashlib.sha256(b"abc").digest()
    if got != expected:
        raise AssertionError(f"self-test failed: got {got.hex()}, expected {expected.hex()}")
    if c.and_count != 58_232:
        raise AssertionError(f"unexpected AND count {c.and_count}")
    if stats["output_depth"] != 456:
        raise AssertionError(f"unexpected AND-depth {stats['output_depth']}")
    print("self-test: OK")
    print(f"sha256('abc') = {got.hex()}")
    print(f"AND gates       = {c.and_count}")
    print(f"AND-depth       = {stats['output_depth']}")
    print(f"schedule depth  = {stats['schedule_depth']}")
    print(f"round-state depth before feed-forward = {stats['state_depth_before_feedforward']}")
    print(f"all gates       = {len(c.gates)}")
    print(f"all wires       = {c.n_wires}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("fixed-iv", "compression"), default="fixed-iv")
    parser.add_argument("--blocks", type=int, default=1, help="number of already padded blocks in fixed-iv mode")
    parser.add_argument("--output", type=Path, help="Bristol output path; use .gz for gzip")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    if args.self_test:
        self_test()
        if args.output is None:
            return

    if args.mode == "fixed-iv":
        c, outputs, stats = build_fixed_iv(args.blocks)
    else:
        if args.blocks != 1:
            parser.error("--blocks applies only to fixed-iv mode")
        c, outputs, stats = build_compression()

    print(f"inputs={c.n_inputs}")
    print(f"outputs={len(outputs)}")
    print(f"AND gates={c.and_count}")
    print(f"AND-depth={stats['output_depth']}")
    print(f"all gates={len(c.gates)}")
    print(f"all wires={c.n_wires}")
    print(f"schedule depth={stats['schedule_depth']}")
    print(f"round-state depth before feed-forward={stats['state_depth_before_feedforward']}")

    if args.output is not None:
        write_bristol(args.output, c, outputs)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
