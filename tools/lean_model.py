#!/usr/bin/env python3
"""Simulate the Lean circuit on an exported plan.

Builds the compression circuit exactly as the Lean gadgets do (constant
folding inside a word gadget, shares across interfaces, the plan's
compression orders and prefix networks with the same fallbacks), counting
AND gates and AND depth, and evaluating the bits to check the values.
"""
from __future__ import annotations

import hashlib
import json
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import sha256_lowdepth_v2 as v2  # noqa: E402

MASK = (1 << 32) - 1


class Wire:
    __slots__ = ("const", "val", "depth")

    def __init__(self, const: bool, val: int, depth: int):
        self.const, self.val, self.depth = const, val, depth


def C(b: int) -> Wire:
    return Wire(True, b & 1, 0)


class Model:
    def __init__(self):
        self.ands = 0
        self.by_cat: dict[str, int] = {}
        self.cat = "?"
        self.errors: list[str] = []

    # ---- folding primitives (WeftChals/Circuit/BitM.lean)
    def xor(self, x: Wire, y: Wire) -> Wire:
        if x.const and y.const:
            return C(x.val ^ y.val)
        if x.const and x.val == 0:
            return y
        if y.const and y.val == 0:
            return x
        return Wire(False, x.val ^ y.val, max(x.depth, y.depth))

    def and_(self, x: Wire, y: Wire) -> Wire:
        if x.const and y.const:
            return C(x.val & y.val)
        if x.const:
            return C(0) if x.val == 0 else y
        if y.const:
            return C(0) if y.val == 0 else x
        self.ands += 1
        self.by_cat[self.cat] = self.by_cat.get(self.cat, 0) + 1
        return Wire(False, x.val & y.val, 1 + max(x.depth, y.depth))

    def ch3(self, x, y, z):
        t = self.xor(y, z)
        p = self.and_(x, t)
        return self.xor(z, p)

    def maj3(self, x, y, z):
        cs = [w.const for w in (x, y, z)]
        if sum(cs) >= 2:
            if x.const and y.const:
                return C(x.val) if x.val == y.val else z
            if x.const and z.const:
                return C(x.val) if x.val == z.val else y
            return C(y.val) if y.val == z.val else x
        t = self.xor(x, y)
        u = self.xor(x, z)
        p = self.and_(t, u)
        return self.xor(x, p)

    # ---- interfaces: shares in, shares out
    @staticmethod
    def share(w: list[Wire]) -> list[Wire]:
        return [Wire(False, b.val, b.depth) for b in w]

    # ---- word gadgets (Csa.lean, Adder.lean, Sum.lean)
    def csa3(self, x, y, z):
        s = [self.xor(self.xor(x[i], y[i]), z[i]) for i in range(32)]
        c = [C(0)] + [self.maj3(x[i], y[i], z[i]) for i in range(31)]
        return s, c

    def add(self, net: dict, x: list[Wire], y: list[Wire]) -> list[Wire]:
        pos = [i for i in range(31)]
        while pos and ((x[pos[0]].const and x[pos[0]].val == 0) or (y[pos[0]].const and y[pos[0]].val == 0)):
            pos.pop(0)
        n = len(pos)
        prods = net["prods"] if net["n"] == n else []
        if net["n"] != n:
            self.errors.append(f"net size {net['n']} != positions {n}")
        env: dict[tuple, Wire] = {}

        def leafG(k):
            key = (True, k, k)
            if key not in env:
                env[key] = self.and_(x[pos[k]], y[pos[k]])
            return env[key]

        def leafP(k):
            return self.xor(x[pos[k]], y[pos[k]])

        def getG(a, b):
            if a == b:
                return leafG(a)
            if (True, a, b) in env:
                return env[(True, a, b)]
            self.errors.append(f"missing G[{a}..{b}]")
            g = leafG(a)
            for k in range(a + 1, b + 1):
                g = self.maj3(x[pos[k]], y[pos[k]], g)
            return g

        def getP(a, b):
            if a == b:
                return leafP(a)
            if (False, a, b) in env:
                return env[(False, a, b)]
            self.errors.append(f"missing P[{a}..{b}]")
            p = leafP(a)
            for k in range(a + 1, b + 1):
                p = self.and_(p, leafP(k))
            return p

        for isG, a, b, m in prods:
            if not (a <= m < b < n):
                self.errors.append(f"bad production {(isG, a, b, m)}")
                continue
            if isG:
                if m + 1 == b:
                    env[(True, a, b)] = self.maj3(x[pos[b]], y[pos[b]], getG(a, m))
                else:
                    hi = getG(m + 1, b)
                    phi = getP(m + 1, b)
                    lo = getG(a, m)
                    env[(True, a, b)] = self.xor(hi, self.and_(phi, lo))
            else:
                env[(False, a, b)] = self.and_(getP(m + 1, b), getP(a, m))
        carries = [getG(0, k) for k in range(n)]
        p0 = pos[0] if pos else 31
        out = []
        for i in range(32):
            p = self.xor(x[i], y[i])
            if i == 0 or i - 1 < p0:
                carry = C(0)
            else:
                carry = carries[i - 1 - p0] if i - 1 - p0 < len(carries) else C(0)
            out.append(self.xor(p, carry))
        return out

    def sum32(self, plan: dict, nets: list[dict], ws: list[list[Wire]]) -> list[Wire]:
        ws = [list(w) for w in ws]
        for i, j, k in plan["csa"]:
            if not (i < len(ws) and j < len(ws) and k < len(ws) and len({i, j, k}) == 3):
                self.errors.append(f"bad csa step {(i, j, k)} on {len(ws)} words")
                continue
            x, y, z = ws[i], ws[j], ws[k]
            for idx in sorted([i, j, k], reverse=True):
                ws.pop(idx)
            s, c = self.csa3(x, y, z)
            ws += [s, c]
        while len(ws) > 2:
            self.errors.append("leftover operands")
            s, c = self.csa3(ws[0], ws[1], ws[2])
            ws = ws[3:] + [s, c]
        if len(ws) == 2:
            return self.add(nets[plan["net"]], ws[0], ws[1])
        return ws[0] if ws else [C(0)] * 32

    # ---- interface wrappers
    def Ch32(self, x, y, z):
        self.cat = "ch"
        x, y, z = map(self.share, (x, y, z))
        return self.share([self.ch3(x[i], y[i], z[i]) for i in range(32)])

    def Maj32(self, x, y, z):
        self.cat = "maj"
        x, y, z = map(self.share, (x, y, z))
        return self.share([self.maj3(x[i], y[i], z[i]) for i in range(32)])

    def Csa3(self, x, y, z):
        self.cat = "csa"
        s, c = self.csa3(*map(self.share, (x, y, z)))
        return self.share(s), self.share(c)

    def Add32(self, net, x, y):
        self.cat = "add"
        return self.share(self.add(net, self.share(x), self.share(y)))

    def Sum32(self, plan, nets, ws):
        self.cat = "sum"
        return self.share(self.sum32(plan, nets, [self.share(w) for w in ws]))


def xorw(m: Model, *ws):
    out = []
    for i in range(32):
        acc = ws[0][i]
        for w in ws[1:]:
            acc = m.xor(acc, w[i])
        out.append(acc)
    return out


def rotr(w, n):
    return [w[(i + n) % 32] for i in range(32)]


def shr(w, n):
    return [w[i + n] if i + n < 32 else C(0) for i in range(32)]


def const_word(v: int):
    return [C((v >> i) & 1) for i in range(32)]


def share_word(v: int):
    return [Wire(False, (v >> i) & 1, 0) for i in range(32)]


def val(w) -> int:
    return sum(b.val << i for i, b in enumerate(w))


def compress(m: Model, plan: dict, H: list[int], block: list[int]) -> list[int]:
    nets = plan["nets"]
    W = [share_word(v) for v in block]
    for t in range(16, 64):
        p = plan["schedule"][t - 16]
        s1 = xorw(m, rotr(W[t - 2], 17), rotr(W[t - 2], 19), shr(W[t - 2], 10))
        s0 = xorw(m, rotr(W[t - 15], 7), rotr(W[t - 15], 18), shr(W[t - 15], 3))
        W.append(m.Sum32(p, nets, [s1, W[t - 7], s0, W[t - 16]]))
    a, b, c, d, e, f, g, h = [share_word(v) for v in H]
    for t in range(64):
        rd = plan["rounds"][t]
        k = const_word(v2.K[t])
        s1 = xorw(m, rotr(e, 6), rotr(e, 11), rotr(e, 25))
        ch = m.Ch32(e, f, g)
        s0 = xorw(m, rotr(a, 2), rotr(a, 13), rotr(a, 22))
        mj = m.Maj32(a, b, c)
        if rd["base"]:
            base = m.Sum32(rd["base"], nets, [h, k, W[t]])
            na = m.Sum32(rd["newA"], nets, [base, s1, ch, s0, mj])
            ne = m.Sum32(rd["newE"], nets, [base, d, s1, ch])
        else:
            bs, bc = m.Csa3(h, k, W[t])
            na = m.Sum32(rd["newA"], nets, [bs, bc, s1, ch, s0, mj])
            ne = m.Sum32(rd["newE"], nets, [bs, bc, d, s1, ch])
        a, b, c, d, e, f, g, h = na, a, b, c, ne, e, f, g
    outs = [a, b, c, d, e, f, g, h]
    res = [m.Add32(nets[plan["final"][i]], share_word(H[i]), outs[i]) for i in range(8)]
    return res


def main() -> None:
    plan = json.loads(Path(sys.argv[1]).read_text())
    m = Model()
    abc = v2.pad_sha256(b"abc")
    block = [int.from_bytes(abc[4 * i:4 * i + 4], "big") for i in range(16)]
    out = compress(m, plan, v2.IV, block)
    depth = max(b.depth for w in out for b in w)
    digest = b"".join(val(w).to_bytes(4, "big") for w in out)
    ok = digest == hashlib.sha256(b"abc").digest()
    print(f"and_gates={m.ands} and_depth={depth} categories={m.by_cat} abc_ok={ok}")
    rng = random.Random(7)
    for _ in range(3):
        hv = [rng.getrandbits(32) for _ in range(8)]
        blk = bytes(rng.getrandbits(8) for _ in range(64))
        bw = [int.from_bytes(blk[4 * i:4 * i + 4], "big") for i in range(16)]
        got = [val(w) for w in compress(Model(), plan, hv, bw)]
        exp = v2.ref_compress(hv, blk)
        assert got == exp, "random compression mismatch"
    print("random compressions: OK")
    if m.errors:
        seen = {}
        for e in m.errors:
            seen[e] = seen.get(e, 0) + 1
        print(f"plan errors ({len(m.errors)}): {dict(list(seen.items())[:10])}")
    else:
        print("plan well-formed under the Lean rules")


if __name__ == "__main__":
    main()
