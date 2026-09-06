#!/usr/bin/env python3
"""Export the structure of the v2 compression circuit as a plan.

Runs sha256_lowdepth_v2's two-pass build in compression mode with the
second pass instrumented: every multi-operand sum records its carry-save
order (as positions in a shrinking operand list) and its carry-prefix
network (the DP's productions, restricted to those the carries need).
Writes tools/plan_compression.json and WeftChals/Plans/Compression.lean.
"""
from __future__ import annotations

import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import sha256_lowdepth_v2 as v2  # noqa: E402
import prefix_dp  # noqa: E402
from prefix_dp import INF  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent

records: list[dict] = []          # one per sum_words call of pass 2, in program order
nets: list[dict] = []             # distinct networks
net_index: dict[tuple, int] = {}
stats = {"maj_tree_conflicts": 0, "adders": 0}


def live_productions(n: int, prods: list[tuple]) -> list[tuple]:
    """Keep the productions the carries G[0..k] need, in emission order."""
    prods = list(dict.fromkeys(prods))          # dedupe, keep first
    have = {(t, a, b): (t, a, b, m) for (t, a, b, m) in prods}
    needed: set[tuple] = set()
    stack = [("G", 0, k) for k in range(n) if k > 0]
    while stack:
        key = stack.pop()
        if key in needed or key not in have:
            continue
        needed.add(key)
        t, a, b, m = have[key]
        if t == "G":
            if a < m:
                stack.append(("G", a, m))
            if m + 1 < b:
                stack.append(("G", m + 1, b))
                stack.append(("P", m + 1, b))
        else:
            if a < m:
                stack.append(("P", a, m))
            if m + 1 < b:
                stack.append(("P", m + 1, b))
    return [p for p in prods if (p[0], p[1], p[2]) in needed]


def record_net(syn: prefix_dp.Synth, dl) -> int:
    dl, ripple_ok = syn._prep(tuple(dl))
    n = syn.n
    if ripple_ok:
        prods = [("G", 0, j, j - 1) for j in range(1, n)]
    elif n == 1:
        prods = []
    else:
        be = prefix_dp._RecBE()
        syn._rec(0, n - 1, dl, (INF,) * n, be)
        prods = be.prods
    prods = [(t, a, b, m) for (t, a, b, m, _l) in prods] if prods and len(prods[0]) == 5 else prods
    for (t, a, b, m) in prods:
        if t == "G" and m + 1 == b:
            pass
    live = live_productions(n, prods)
    key = (n, tuple(live))
    if key not in net_index:
        net_index[key] = len(nets)
        nets.append({"n": n, "prods": [[1 if t == "G" else 0, a, b, m] for (t, a, b, m) in live]})
    return net_index[key]


def add32_rec(c, x, y, deadlines):
    """v2.add32_dp, recording the network it builds."""
    p = [c.xor(x[i], y[i]) for i in range(32)]
    pos = []
    for i in range(31):
        gi_zero = c.const[x[i]] == 0 or c.const[y[i]] == 0
        if not pos and gi_zero:
            continue
        pos.append(i)
    out = list(p)
    if not pos:
        return out, None
    pl, gl, gc, dl = [], [], [], []
    for k, i in enumerate(pos):
        a = max(c.depth[x[i]], c.depth[y[i]])
        pl.append(a)
        cst = c.is_const(x[i]) or c.is_const(y[i])
        gl.append(a if cst else a + 1)
        gc.append(0 if cst else 1)
        dl.append(deadlines[i + 1])
    base = min(pl)
    key = (tuple(v - base for v in pl), tuple(v - base for v in gl), tuple(gc), tuple(v - base for v in dl))
    syn = v2._synth_cache.get(key)
    if syn is None:
        syn = prefix_dp.Synth(key[0], key[1], key[2])
        if syn.solve(key[3]) == INF:
            raise RuntimeError("adder synthesis infeasible for deadlines")
        v2._synth_cache[key] = syn
    be = v2._Backend(c, x, y, pos)
    carries = syn.build(key[3], be)
    for k, i in enumerate(pos):
        out[i + 1] = c.xor(p[i + 1], carries[k])
    stats["adders"] += 1
    return out, record_net(syn, key[3])


def sum_words_rec(c, plan, words):
    ws = [list(w) for w in words]
    if not plan.replay:
        return v2_sum_words_orig(c, plan, words)
    order = plan.next_csa_order()
    cur = list(range(len(ws)))
    steps = []
    for (i, j, k) in order[:-1]:
        pi, pj, pk = cur.index(i), cur.index(j), cur.index(k)
        steps.append([pi, pj, pk])
        for idx in sorted([pi, pj, pk], reverse=True):
            cur.pop(idx)
        s, cr = v2.csa3(c, ws[i], ws[j], ws[k])
        ws.append(s)
        ws.append(cr)
        cur.append(len(ws) - 2)
        cur.append(len(ws) - 1)
    a_idx, b_idx, _ = order[-1]
    assert len(cur) == 2 and set(cur) == {a_idx, b_idx}, (cur, a_idx, b_idx)
    dl = plan.next_deadlines()
    res, net = add32_rec(c, ws[cur[0]], ws[cur[1]], dl)
    assert net is not None
    records.append({"csa": steps, "net": net})
    return res


v2_sum_words_orig = v2.sum_words


def export() -> dict:
    t0 = time.time()
    v2.sum_words = sum_words_rec
    c, outs, gates, n_wires, st = v2.build("compression", 1, "dp")
    v2.sum_words = v2_sum_words_orig
    # program order: 48 schedule sums, then per round base?/newA/newE, then 8 final
    it = iter(records)
    schedule = [next(it) for _ in range(48)]
    plan_obj = v2.Plan()  # just to count base modes we need from the build: recover from record count
    rounds = []
    # base modes are not visible here; infer from the record stream: a round has 3 sums if word_mode else 2.
    # Recover word modes by re-running the pass-1 decision: replay the same build to read plan.base_modes.
    plan2 = v2.Plan()
    c1, out1 = v2.build_once("compression", 1, plan2)
    base_modes = plan2.base_modes
    assert len(base_modes) == 64
    for t in range(64):
        if base_modes[t]:
            base = next(it)
        else:
            base = None
        newA = next(it)
        newE = next(it)
        rounds.append({"base": base, "newA": newA, "newE": newE})
    final = [next(it)["net"] for _ in range(8)]
    rest = list(it)
    assert not rest, len(rest)
    for r in schedule + [x for rd in rounds for x in (rd["base"], rd["newA"], rd["newE"]) if x]:
        assert all(all(0 <= v < 8 for v in s) for s in r["csa"])
    return {
        "mode": "compression",
        "v2_stats": st,
        "nets": nets,
        "schedule": schedule,
        "rounds": rounds,
        "final": final,
        "export_seconds": round(time.time() - t0, 1),
    }


def emit_lean(plan: dict, path: Path) -> None:
    def prod_code(p):
        isG, a, b, m = p
        return isG * 32768 + a * 1024 + b * 32 + m

    def step_code(s):
        i, j, k = s
        return i * 64 + j * 8 + k

    def fmt_list(xs, indent="    "):
        s = ", ".join(str(x) for x in xs)
        lines, cur = [], ""
        for tok in s.split(", "):
            if len(cur) + len(tok) + 2 > 110:
                lines.append(cur.rstrip())
                cur = ""
            cur += tok + ", "
        lines.append(cur.rstrip().rstrip(","))
        return ("\n" + indent).join(lines)

    out = ["import WeftChals.Circuit.Plan", "", "/-! Generated by tools/plan_export.py; do not edit. -/",
           "namespace WeftChals.Plans.Compression", "open WeftChals", ""]
    for idx, net in enumerate(plan["nets"]):
        out.append(f"def net{idx} : Net := ⟨{net['n']}, [{fmt_list(prod_code(p) for p in net['prods'])}]⟩")
    out.append("")
    sums = []

    def sum_def(rec):
        sums.append(rec)
        i = len(sums) - 1
        out.append(f"def s{i} : SumPlan := ⟨[{fmt_list(step_code(s) for s in rec['csa'])}], net{rec['net']}⟩")
        return f"s{i}"

    sched = [sum_def(r) for r in plan["schedule"]]
    rounds = []
    for rd in plan["rounds"]:
        base = f"some {sum_def(rd['base'])}" if rd["base"] else "none"
        a = sum_def(rd["newA"])
        e = sum_def(rd["newE"])
        rounds.append(f"⟨{base}, {a}, {e}⟩")
    out.append("")
    out.append("def plan : BlockPlan :=")
    out.append(f"  ⟨[{fmt_list(sched, '    ')}],")
    out.append(f"   [{fmt_list(rounds, '    ')}],")
    out.append(f"   [{fmt_list('net%d' % n for n in plan['final'])}]⟩")
    out.append("")
    out.append("end WeftChals.Plans.Compression")
    path.write_text("\n".join(out) + "\n")


def main() -> None:
    plan = export()
    json_path = ROOT / "tools" / "plan_compression.json"
    json_path.write_text(json.dumps(plan, indent=1))
    lean_path = ROOT / "WeftChals" / "Plans" / "Compression.lean"
    lean_path.parent.mkdir(parents=True, exist_ok=True)
    emit_lean(plan, lean_path)
    total_prods = sum(len(n["prods"]) for n in plan["nets"])
    print(f"v2: {plan['v2_stats']}")
    print(f"nets={len(plan['nets'])} productions={total_prods} adders={stats['adders']} "
          f"sums={len(records)} seconds={plan['export_seconds']}")
    print(f"wrote {json_path} and {lean_path}")


if __name__ == "__main__":
    main()
