#!/usr/bin/env python3
"""Improved low-AND-depth SHA-256 Boolean circuit generator (Bristol Fashion).

Same gate model, bit ordering, modes and file format as sha256_lowdepth_bristol.py
(XOR/INV depth 0, AND depth 1), but with fewer AND gates at the same AND-depth:

  * Constant folding in the circuit builder (fixed-IV mode: the first rounds
    operate on a constant state and collapse; K constants fold into gates).
  * The three early-arriving words h, K[t], W[t] are compressed once and the
    result is shared by the a' and e' compressor trees (saves one 3:2 compressor
    per round).
  * Every 2-operand adder is synthesised by a timing-driven dynamic programme
    over carry-prefix networks: given the actual arrival depth of each input bit
    and the required depth of each output bit (from a backward pass over a
    reference build), it returns a minimum-AND prefix network from the family of
    recursive block splits (ripple, Sklansky, Brent-Kung, Ladner-Fischer and
    hybrids).  On the round-critical path this yields the Sklansky shape but
    drops the never-used group-propagate gates and uses the one-AND
    maj(x,y,c) form wherever a single bit is merged into a carry; adders with
    slack (message schedule) become much cheaper, deeper networks.
  * The 3:2-compressor trees are re-arranged: the early words h, K[t], W[t]
    are resolved once into a single word by a slack-tolerant adder (when this is
    provably off the critical path) and shared by the a' and e' trees.
  * For the two dominant round-adder timing profiles, exact_solutions.json holds
    prefix networks found by exact (z3 MaxSAT) search on 15-element halves,
    composed and validated (115 ANDs instead of the DP's 122 and the original
    181).  If the file is absent the DP result is used.
  * A final sweep removes gates that do not reach any output.

Verification is the same known-answer + random test set as the original.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import heapq
import random
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

from sha256_lowdepth_bristol import (
    IV, K, MASK32, bytes_to_bits_msb, bits_to_bytes_msb, pad_sha256,
)
from prefix_dp import Synth, INF


@dataclass(frozen=True)
class Gate:
    op: str
    ins: tuple[int, ...]
    out: int


class Circuit:
    """Bristol-style gate list with constant folding and depth tracking."""

    def __init__(self, n_inputs: int) -> None:
        self.n_inputs = n_inputs
        self.depth: list[int] = [0] * n_inputs
        self.const: list[int | None] = [None] * n_inputs
        self.gates: list[Gate] = []
        self.and_count = 0
        self.zero = self._new("XOR", (0, 0), 0, 0)
        self.one = self._new("INV", (self.zero,), 0, 1)

    @property
    def n_wires(self) -> int:
        return len(self.depth)

    def _new(self, op: str, ins: tuple[int, ...], d: int, cval: int | None) -> int:
        out = len(self.depth)
        self.depth.append(d)
        self.const.append(cval)
        self.gates.append(Gate(op, ins, out))
        if op == "AND":
            self.and_count += 1
        return out

    def is_const(self, w: int) -> bool:
        return self.const[w] is not None

    def xor(self, x: int, y: int) -> int:
        cx, cy = self.const[x], self.const[y]
        if cx is not None and cy is not None:
            return self.one if (cx ^ cy) else self.zero
        if cx == 0:
            return y
        if cy == 0:
            return x
        if x == y:
            return self.zero
        return self._new("XOR", (x, y), max(self.depth[x], self.depth[y]), None)

    def and_(self, x: int, y: int) -> int:
        cx, cy = self.const[x], self.const[y]
        if cx == 0 or cy == 0:
            return self.zero
        if cx == 1:
            return y
        if cy == 1:
            return x
        if x == y:
            return x
        return self._new("AND", (x, y), 1 + max(self.depth[x], self.depth[y]), None)

    def inv(self, x: int) -> int:
        return self.xor(x, self.one)

    def xor_many(self, xs: Sequence[int]) -> int:
        acc = self.zero
        for x in xs:
            acc = self.xor(acc, x)
        return acc

    def const_word(self, value: int) -> list[int]:
        return [self.one if ((value >> i) & 1) else self.zero for i in range(32)]

    def word_depth(self, word: Sequence[int]) -> int:
        return max(self.depth[w] for w in word)

    def copy_for_output(self, x: int) -> int:
        # Raw XOR with zero so output wires are fresh and contiguous.
        return self._new("XOR", (x, self.zero), self.depth[x], self.const[x])


# ---------------------------------------------------------------- word ops

def xor_words(c: Circuit, *words: Sequence[int]) -> list[int]:
    return [c.xor_many([w[i] for w in words]) for i in range(32)]


def rotr(word: Sequence[int], n: int) -> list[int]:
    n %= 32
    return [word[(i + n) % 32] for i in range(32)]


def shr(c: Circuit, word: Sequence[int], n: int) -> list[int]:
    return [word[i + n] if i + n < 32 else c.zero for i in range(32)]


def ch(c: Circuit, x, y, z) -> list[int]:
    return [c.xor(z[i], c.and_(x[i], c.xor(y[i], z[i]))) for i in range(32)]


def maj(c: Circuit, x, y, z) -> list[int]:
    return [c.xor(x[i], c.and_(c.xor(x[i], y[i]), c.xor(x[i], z[i]))) for i in range(32)]


def csa3(c: Circuit, x, y, z) -> tuple[list[int], list[int]]:
    s = [c.xor_many((x[i], y[i], z[i])) for i in range(32)]
    carry = [c.zero]
    for i in range(31):
        carry.append(c.xor(x[i], c.and_(c.xor(x[i], y[i]), c.xor(x[i], z[i]))))
    return s, carry


def big_sigma0(c, x): return xor_words(c, rotr(x, 2), rotr(x, 13), rotr(x, 22))
def big_sigma1(c, x): return xor_words(c, rotr(x, 6), rotr(x, 11), rotr(x, 25))
def small_sigma0(c, x): return xor_words(c, rotr(x, 7), rotr(x, 18), shr(c, x, 3))
def small_sigma1(c, x): return xor_words(c, rotr(x, 17), rotr(x, 19), shr(c, x, 10))


# ---------------------------------------------------------------- adders

def add32_sklansky(c: Circuit, x, y) -> list[int]:
    """Reference 5-stage Sklansky adder (pass 1 only)."""
    p_orig = [c.xor(x[i], y[i]) for i in range(32)]
    P = p_orig[:31]
    G = [c.and_(x[i], y[i]) for i in range(31)]
    for stage in range(5):
        half = 1 << stage
        block = half << 1
        old_P, old_G = P[:], G[:]
        for base in range(0, 31, block):
            pivot = base + half - 1
            if pivot >= 31:
                continue
            for i in range(base + half, min(base + block, 31)):
                G[i] = c.xor(old_G[i], c.and_(old_P[i], old_G[pivot]))
                P[i] = c.and_(old_P[i], old_P[pivot])
    return [p_orig[0]] + [c.xor(p_orig[i], G[i - 1]) for i in range(1, 32)]


class _Backend:
    """Maps prefix-DP plan operations onto circuit gates for elements 0..n-1
    (element k corresponds to bit position pos[k])."""

    def __init__(self, c: Circuit, x, y, pos):
        self.c, self.x, self.y, self.pos = c, x, y, pos
        self._p = {}
        self._g = {}

    def P(self, k):
        if k not in self._p:
            i = self.pos[k]
            self._p[k] = self.c.xor(self.x[i], self.y[i])
        return self._p[k]

    def g(self, k):
        if k not in self._g:
            i = self.pos[k]
            self._g[k] = self.c.and_(self.x[i], self.y[i])
        return self._g[k]

    def and_(self, u, v): return self.c.and_(u, v)
    def xor(self, u, v): return self.c.xor(u, v)

    def maj(self, k, G):
        i = self.pos[k]
        xi, yi = self.x[i], self.y[i]
        return self.c.xor(xi, self.c.and_(self.c.xor(xi, yi), self.c.xor(xi, G)))


_synth_cache: dict[tuple, Synth] = {}
_key_usage: dict[tuple, int] = {}

_EXACT_PATH = Path(__file__).resolve().parent / "exact_solutions.json"
_exact: dict[str, dict] = {}
if _EXACT_PATH.exists():
    import json as _json
    _exact = _json.loads(_EXACT_PATH.read_text())


def _key_str(key) -> str:
    import json as _json
    return _json.dumps([list(x) for x in key])


def build_from_exact(sol: dict, n: int, be: "_Backend") -> dict[int, int]:
    """Emit gates for a SAT-found prefix network (see exact_prefix_search.py).
    Returns carries: element index k -> wire of G[0..k]."""
    bestG: dict[tuple[int, int], tuple] = {}
    bestP: dict[tuple[int, int], tuple] = {}
    for typ, a, b, m, l in sol["prods"]:
        d = bestG if typ == "G" else bestP
        if (a, b) not in d or d[(a, b)][3] > l:
            d[(a, b)] = (typ, a, b, l, m)
    memoG: dict[tuple[int, int], int] = {}
    memoP: dict[tuple[int, int], int] = {}

    def P(a, b):
        if a == b:
            return be.P(a)
        if (a, b) not in memoP:
            m = bestP[(a, b)][4]
            memoP[(a, b)] = be.and_(P(m + 1, b), P(a, m))
        return memoP[(a, b)]

    def G(a, b):
        if a == b:
            return be.g(a)
        if (a, b) not in memoG:
            m = bestG[(a, b)][4]
            if m + 1 == b:
                memoG[(a, b)] = be.maj(b, G(a, m))
            else:
                memoG[(a, b)] = be.xor(G(m + 1, b), be.and_(P(m + 1, b), G(a, m)))
        return memoG[(a, b)]

    return {k: G(0, k) for k in range(n)}


def add32_dp(c: Circuit, x, y, deadlines: Sequence[int]) -> list[int]:
    """Timing-driven adder: output bit i must have depth <= deadlines[i]."""
    p = [c.xor(x[i], y[i]) for i in range(32)]
    # carry positions 0..30; drop leading positions whose generate is constant 0
    pos = []
    for i in range(31):
        gi_zero = c.const[x[i]] == 0 or c.const[y[i]] == 0
        if not pos and gi_zero:
            continue
        pos.append(i)
    out = list(p)
    if not pos:
        return out
    pl, gl, gc, dl = [], [], [], []
    for k, i in enumerate(pos):
        a = max(c.depth[x[i]], c.depth[y[i]])
        pl.append(a)
        cst = c.is_const(x[i]) or c.is_const(y[i])
        gl.append(a if cst else a + 1)
        gc.append(0 if cst else 1)
        # carry into bit i+1 must be ready for sum bit i+1
        dl.append(deadlines[i + 1])
    base = min(pl)
    key = (tuple(v - base for v in pl), tuple(v - base for v in gl), tuple(gc),
           tuple(v - base for v in dl))
    _key_usage[key] = _key_usage.get(key, 0) + 1
    syn = _synth_cache.get(key)
    if syn is None:
        syn = Synth(key[0], key[1], key[2])
        if syn.solve(key[3]) == INF:
            raise RuntimeError("adder synthesis infeasible for deadlines")
        _synth_cache[key] = syn
    be = _Backend(c, x, y, pos)
    ex = _exact.get(_key_str(key))
    if ex is not None and ex["prods"] and ex["cost"] < syn.solve(key[3]):
        try:
            carries = build_from_exact(ex, len(pos), be)
        except KeyError:
            carries = syn.build(key[3], be)
    else:
        carries = syn.build(key[3], be)
    for k, i in enumerate(pos):
        out[i + 1] = c.xor(p[i + 1], carries[k])
    return out


# ---------------------------------------------------------------- build plan

class Plan:
    """Records pass-1 decisions (CSA tree order, adder output deadlines) so pass 2
    reproduces the same structure outside the adders."""

    def __init__(self):
        self.csa_orders: list[list[tuple[int, int, int]]] = []
        self.adder_outputs: list[list[int]] = []
        self.adder_deadlines: list[list[int]] = []
        self.base_modes: list[bool] = []
        self.replay = False
        self._csa_i = 0
        self._add_i = 0
        self._base_i = 0

    def next_base_mode(self):
        b = self.base_modes[self._base_i]
        self._base_i += 1
        return b

    def next_csa_order(self):
        o = self.csa_orders[self._csa_i]
        self._csa_i += 1
        return o

    def next_deadlines(self):
        d = self.adder_deadlines[self._add_i]
        self._add_i += 1
        return d


def sum_words(c: Circuit, plan: Plan, words: Iterable[Sequence[int]]) -> list[int]:
    """Carry-save reduction to two words followed by a 2-operand adder.

    Pass 1 orders the 3:2 compressors by arrival depth and records the choices;
    pass 2 replays them and uses the deadline-driven adder."""
    ws = [list(w) for w in words]
    if plan.replay:
        order = plan.next_csa_order()
        for (i, j, k) in order[:-1]:
            s, cr = csa3(c, ws[i], ws[j], ws[k])
            ws.append(s)
            ws.append(cr)
        a_idx, b_idx, _ = order[-1]
        return add32_dp(c, ws[a_idx], ws[b_idx], plan.next_deadlines())
    heap = [(c.word_depth(w), i, i) for i, w in enumerate(ws)]
    heapq.heapify(heap)
    order = []
    while len(heap) > 2:
        i = heapq.heappop(heap)[2]
        j = heapq.heappop(heap)[2]
        k = heapq.heappop(heap)[2]
        s, cr = csa3(c, ws[i], ws[j], ws[k])
        for w in (s, cr):
            ws.append(w)
            heapq.heappush(heap, (c.word_depth(w), len(ws) - 1, len(ws) - 1))
        order.append((i, j, k))
    a_idx = heapq.heappop(heap)[2]
    b_idx = heapq.heappop(heap)[2]
    order.append((a_idx, b_idx, -1))
    plan.csa_orders.append(order)
    res = add32_sklansky(c, ws[a_idx], ws[b_idx])
    plan.adder_outputs.append(list(res))
    return res


def bits_msb_to_internal_words(bits: Sequence[int]) -> list[list[int]]:
    return [list(reversed(bits[off:off + 32])) for off in range(0, len(bits), 32)]


def internal_words_to_bits_msb(words) -> list[int]:
    out = []
    for w in words:
        out.extend(reversed(w))
    return out


def message_schedule(c: Circuit, plan: Plan, block_bits: Sequence[int]) -> list[list[int]]:
    W = bits_msb_to_internal_words(block_bits)
    for t in range(16, 64):
        W.append(sum_words(c, plan, (
            small_sigma1(c, W[t - 2]),
            W[t - 7],
            small_sigma0(c, W[t - 15]),
            W[t - 16],
        )))
    return W


def compress(c: Circuit, plan: Plan, H, block_bits) -> list[list[int]]:
    W = message_schedule(c, plan, block_bits)
    a, b, cc, d, e, f, g, h = [list(w) for w in H]
    k_words = [c.const_word(v) for v in K]
    for t in range(64):
        s1 = big_sigma1(c, e)
        choose = ch(c, e, f, g)
        s0 = big_sigma0(c, a)
        majority = maj(c, a, b, cc)
        # h, K[t], W[t] all arrive early: compress once, share between a' and e'.
        if plan.replay:
            word_mode = plan.next_base_mode()
        else:
            # A resolved base word is off the critical path if a 6-level reference
            # adder on (h + K + W) finishes no later than Sigma1(e) arrives.
            word_mode = max(c.word_depth(h), c.word_depth(W[t])) + 7 <= c.word_depth(s1)
            plan.base_modes.append(word_mode)
        if word_mode:
            base = sum_words(c, plan, (h, k_words[t], W[t]))
            new_a = sum_words(c, plan, (base, s1, choose, s0, majority))
            new_e = sum_words(c, plan, (base, d, s1, choose))
        else:
            base_s, base_c = csa3(c, h, k_words[t], W[t])
            new_a = sum_words(c, plan, (base_s, base_c, s1, choose, s0, majority))
            new_e = sum_words(c, plan, (base_s, base_c, d, s1, choose))
        a, b, cc, d, e, f, g, h = new_a, a, b, cc, new_e, e, f, g
    return [sum_words(c, plan, (H[i], w)) for i, w in enumerate((a, b, cc, d, e, f, g, h))]


def build_once(mode: str, blocks: int, plan: Plan):
    if mode == "fixed-iv":
        c = Circuit(512 * blocks)
        H = [c.const_word(v) for v in IV]
        for j in range(blocks):
            H = compress(c, plan, H, list(range(512 * j, 512 * (j + 1))))
    else:
        c = Circuit(256 + 512)
        H = bits_msb_to_internal_words(list(range(256)))
        H = compress(c, plan, H, list(range(256, 768)))
    outputs = [c.copy_for_output(w) for w in internal_words_to_bits_msb(H)]
    return c, outputs


def required_times(c: Circuit, outputs: Sequence[int], target: int) -> list[int]:
    req = [10 ** 9] * c.n_wires
    for w in outputs:
        req[w] = target
    for g in reversed(c.gates):
        r = req[g.out] - (1 if g.op == "AND" else 0)
        for w in g.ins:
            if r < req[w]:
                req[w] = r
    return req


def prune(c: Circuit, outputs: Sequence[int]) -> tuple[list[Gate], int, int, dict[int, int]]:
    """Remove gates not reaching outputs; return (gates, n_wires, and_count, remap)."""
    live = set(outputs)
    for g in reversed(c.gates):
        if g.out in live:
            live.update(g.ins)
    remap = {i: i for i in range(c.n_inputs)}
    gates = []
    nxt = c.n_inputs
    for g in c.gates:
        if g.out in live:
            remap[g.out] = nxt
            nxt += 1
            gates.append(Gate(g.op, tuple(remap[i] for i in g.ins), remap[g.out]))
    and_count = sum(1 for g in gates if g.op == "AND")
    return gates, nxt, and_count, remap


def build(mode: str, blocks: int, adder: str = "dp", verbose: bool = False):
    plan = Plan()
    c1, out1 = build_once(mode, blocks, plan)
    depth1 = max(c1.depth[w] for w in out1)
    if adder == "sklansky":
        c, outs = c1, out1
    else:
        req = required_times(c1, out1, depth1)
        plan.adder_deadlines = [[req[w] for w in ws] for ws in plan.adder_outputs]
        plan.replay = True
        c, outs = build_once(mode, blocks, plan)
    depth = max(c.depth[w] for w in outs)
    gates, n_wires, and_count, remap = prune(c, outs)
    stats = {
        "and_depth": depth,
        "reference_depth": depth1,
        "and_gates": and_count,
        "xor_gates": sum(1 for g in gates if g.op == "XOR"),
        "inv_gates": sum(1 for g in gates if g.op == "INV"),
        "all_gates": len(gates),
        "all_wires": n_wires,
        "reference_and_gates_unpruned": c1.and_count,
    }
    return c, outs, gates, n_wires, stats


# ---------------------------------------------------------------- I/O + eval

def write_bristol(path: Path, gates: Sequence[Gate], n_wires: int, n_inputs: int) -> None:
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "wt", encoding="ascii", newline="\n") as f:
        f.write(f"{len(gates)} {n_wires}\n")
        f.write(f"1 {n_inputs}\n")
        f.write("1 256\n\n")
        for g in gates:
            ins = " ".join(str(x) for x in g.ins)
            f.write(f"{len(g.ins)} 1 {ins} {g.out} {g.op}\n")


def eval_gates(gates: Sequence[Gate], n_wires: int, n_inputs: int, input_bits: Sequence[int]) -> list[int]:
    wires = [int(bool(x)) for x in input_bits] + [0] * (n_wires - n_inputs)
    for g in gates:
        if g.op == "XOR":
            wires[g.out] = wires[g.ins[0]] ^ wires[g.ins[1]]
        elif g.op == "AND":
            wires[g.out] = wires[g.ins[0]] & wires[g.ins[1]]
        else:
            wires[g.out] = wires[g.ins[0]] ^ 1
    return wires[n_wires - 256:]


def ref_compress(h: Sequence[int], block: bytes) -> list[int]:
    def rotr(x, n): return ((x >> n) | (x << (32 - n))) & MASK32
    w = [int.from_bytes(block[4 * i:4 * i + 4], "big") for i in range(16)]
    for t in range(16, 64):
        s0 = rotr(w[t - 15], 7) ^ rotr(w[t - 15], 18) ^ (w[t - 15] >> 3)
        s1 = rotr(w[t - 2], 17) ^ rotr(w[t - 2], 19) ^ (w[t - 2] >> 10)
        w.append((w[t - 16] + s0 + w[t - 7] + s1) & MASK32)
    a, b, c, d, e, f, g, hh = h
    for t in range(64):
        S1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)
        chv = (e & f) ^ (~e & g)
        t1 = (hh + S1 + chv + K[t] + w[t]) & MASK32
        S0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)
        mj = (a & b) ^ (a & c) ^ (b & c)
        t2 = (S0 + mj) & MASK32
        hh, g, f, e, d, c, b, a = g, f, e, (d + t1) & MASK32, c, b, a, (t1 + t2) & MASK32
    return [(x + y) & MASK32 for x, y in zip(h, (a, b, c, d, e, f, g, hh))]


def self_test(adder: str = "dp") -> dict:
    rng = random.Random(2024)
    # one block, fixed IV
    c, outs, gates, nw, st = build("fixed-iv", 1, adder)
    n_in = c.n_inputs
    msgs = [b"abc", b"", b"a" * 55, bytes(rng.getrandbits(8) for _ in range(rng.randrange(0, 56)))]
    for m in msgs:
        got = bits_to_bytes_msb(eval_gates(gates, nw, n_in, bytes_to_bits_msb(pad_sha256(m))))
        exp = hashlib.sha256(m).digest()
        assert got == exp, f"fixed-iv mismatch for {m!r}: {got.hex()} != {exp.hex()}"
    # random full blocks, no padding semantics needed: compare with reference compress
    for _ in range(3):
        blk = bytes(rng.getrandbits(8) for _ in range(64))
        got = bits_to_bytes_msb(eval_gates(gates, nw, n_in, bytes_to_bits_msb(blk)))
        exp = b"".join(x.to_bytes(4, "big") for x in ref_compress(IV, blk))
        assert got == exp, "fixed-iv random block mismatch"
    print(f"fixed-iv  : OK  AND={st['and_gates']} depth={st['and_depth']} gates={st['all_gates']}")
    # compression mode
    c2, outs2, gates2, nw2, st2 = build("compression", 1, adder)
    for _ in range(4):
        hv = [rng.getrandbits(32) for _ in range(8)]
        blk = bytes(rng.getrandbits(8) for _ in range(64))
        bits = bytes_to_bits_msb(b"".join(x.to_bytes(4, "big") for x in hv) + blk)
        got = bits_to_bytes_msb(eval_gates(gates2, nw2, c2.n_inputs, bits))
        exp = b"".join(x.to_bytes(4, "big") for x in ref_compress(hv, blk))
        assert got == exp, "compression mismatch"
    print(f"compression: OK  AND={st2['and_gates']} depth={st2['and_depth']} gates={st2['all_gates']}")
    # two blocks
    c3, outs3, gates3, nw3, st3 = build("fixed-iv", 2, adder)
    m = bytes(rng.getrandbits(8) for _ in range(100))
    got = bits_to_bytes_msb(eval_gates(gates3, nw3, c3.n_inputs, bytes_to_bits_msb(pad_sha256(m))))
    assert got == hashlib.sha256(m).digest(), "two-block mismatch"
    print(f"2 blocks   : OK  AND={st3['and_gates']} depth={st3['and_depth']} gates={st3['all_gates']}")
    return {"fixed-iv": st, "compression": st2, "2block": st3}


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--mode", choices=("fixed-iv", "compression"), default="fixed-iv")
    ap.add_argument("--blocks", type=int, default=1)
    ap.add_argument("--adder", choices=("dp", "sklansky"), default="dp")
    ap.add_argument("--output", type=Path)
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        self_test(args.adder)
        if args.output is None:
            return
    c, outs, gates, nw, st = build(args.mode, args.blocks, args.adder)
    for k, v in st.items():
        print(f"{k}={v}")
    if args.output is not None:
        write_bristol(args.output, gates, nw, c.n_inputs)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
