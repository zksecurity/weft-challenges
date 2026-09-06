"""Timing-driven minimum-AND carry-prefix network synthesis.

Cost model: AND = 1 gate and +1 level, XOR free (level 0).

Elements i = 0..n-1 are bit positions whose carry-out is needed.  Each has
  pl[i]   level at which p_i = x_i ^ y_i is available
  gl[i]   level at which g_i = x_i & y_i is available
  gc[i]   AND cost of materialising g_i (1 normally, 0 if one operand is a
          known constant so that g_i is free)
We must produce C[j] = G[0..j] for all j with level(C[j]) <= dl[j].

Combine rules (all one AND):
  P[a..b] = P[m+1..b] & P[a..m]                      level 1+max
  G[a..b] = G[m+1..b] ^ (P[m+1..b] & G[a..m])        level max(lG_hi, 1+max(lP_hi, lG_lo))
  if the high part is a single bit b:  G[a..b] = maj(x_b, y_b, G[a..b-1])
     costs one AND, needs neither g_b nor p_b, level 1+max(pl[b], lG_lo).

Search space: recursive block splits of a range [s..e] at m.  The outputs of
the upper part are produced either as a *tree* (each G[s..j], P[s..j] for j>m
combines the upper child's range values G[m+1..j], P[m+1..j] with the pivot
G[s..m], P[s..m]) or, for the generate chain only, as a *ripple*
(G[s..j] = maj(x_j, y_j, G[s..j-1]) for consecutive j, needing no upper range
values), while the propagate outputs still use the tree.  This covers ripple,
Sklansky, Brent-Kung, Ladner-Fischer and the hybrids found by exact search.
"""
from __future__ import annotations
import sys

INF = float("inf")
sys.setrecursionlimit(10000)


def _fin(xs):
    return [x for x in xs if x < INF]


class Synth:
    def __init__(self, pl, gl, gc):
        self.pl = tuple(pl)
        self.gl = tuple(gl)
        self.gc = tuple(gc)
        self.n = len(pl)
        self._memo: dict = {}

    # ------------------------------------------------------------------ DP
    def pwp(self, s, e, LG, LP):
        """Min ANDs to provide G[s..j] (deadline LG[j-s]) and P[s..j] (LP[j-s])
        for all j in s..e; INF marks an unneeded value.  The single-element
        generate g_s is charged by the parent that uses it as a pivot."""
        key = (s, e, LG, LP)
        hit = self._memo.get(key)
        if hit is not None:
            return hit[0]
        best = (INF, None)
        if s == e:
            ok = (LP[0] == INF or self.pl[s] <= LP[0]) and (LG[0] == INF or self.pl[s] + 1 <= LG[0])
            if ok:
                best = (0, ("leaf",))
        else:
            for m in range(s, e):
                k = m - s
                hiG, hiP = LG[k + 1:], LP[k + 1:]
                finG, finP = _fin(hiG), _fin(hiP)
                nG, nP = len(finG), len(finP)
                lowLP = LP[:k] + (min(LP[k], min(finP) - 1) if nP else LP[k],)
                if lowLP[-1] < 0:
                    continue
                for mode in ("tree", "ripple"):
                    if mode == "ripple":
                        if nG == 0:
                            continue  # nothing to ripple; identical to tree with nG == 0
                        # chain G[s..j] = maj(x_j, y_j, G[s..j-1]) for j = m+1..jlast
                        jlast = max(j for j in range(m + 1, e + 1) if LG[j - s] < INF)
                        need_piv = min(LG[j - s] - (j - m) for j in range(m + 1, jlast + 1) if LG[j - s] < INF)
                        # arrival of p_k inside the chain
                        feasible = True
                        for j in range(m + 1, jlast + 1):
                            if LG[j - s] == INF:
                                continue
                            for kk in range(m + 1, j + 1):
                                if self.pl[kk] + 1 + (j - kk) > LG[j - s]:
                                    feasible = False
                                    break
                            if not feasible:
                                break
                        if not feasible:
                            continue
                        lowLG = LG[:k] + (min(LG[k], need_piv),)
                        upG = (INF,) * (e - m)
                        upP = tuple(p - 1 for p in hiP)
                        gcost = jlast - m
                    else:
                        lowLG = LG[:k] + (min(LG[k], min(finG) - 1) if nG else LG[k],)
                        upG = hiG
                        upP = tuple(min(g - 1, p - 1) for g, p in zip(hiG, hiP))
                        gcost = nG
                    if lowLG[-1] < 0:
                        continue
                    extra = 0
                    if m == s and nG:
                        if self.gl[s] > lowLG[-1]:
                            continue
                        extra = self.gc[s]
                    lo = self.pwp(s, m, lowLG, lowLP)
                    if lo == INF:
                        continue
                    hi = self.pwp(m + 1, e, upG, upP)
                    if hi == INF:
                        continue
                    cost = lo + hi + extra + gcost + nP
                    if cost < best[0]:
                        best = (cost, ("split", m, mode))
        self._memo[key] = best
        return best[0]

    def ripple_levels(self):
        """Output levels of the pure ripple chain G[0..j] = maj(x_j, y_j, G[0..j-1])."""
        lv = [self.gl[0]]
        for j in range(1, self.n):
            lv.append(1 + max(self.pl[j], lv[-1]))
        return lv

    def _prep(self, dl):
        """Return (deadlines, ripple_ok).  A pure ripple is the cheapest possible
        network (one AND per carry), so when it meets every deadline it is used
        directly.  Deadlines are otherwise left untouched: clamping individual
        outputs would restrict the search and can make it infeasible."""
        rl = self.ripple_levels()
        ok = all(r <= d for r, d in zip(rl, dl))
        return tuple(dl), ok

    def solve(self, dl):
        dl, ripple_ok = self._prep(tuple(dl))
        if ripple_ok:
            return self.gc[0] + (self.n - 1)
        if self.n == 1:
            return self.gc[0] if self.gl[0] <= dl[0] else INF
        return self.pwp(0, self.n - 1, dl, (INF,) * self.n)

    # ------------------------------------------------------- reconstruction
    def build(self, dl, be):
        """Emit gates through backend `be` (methods P(i), g(i), and_, xor,
        maj(i, G)); returns {k: wire of G[0..k]}."""
        dl, ripple_ok = self._prep(tuple(dl))
        if ripple_ok:
            out = {0: be.g(0)}
            for j in range(1, self.n):
                out[j] = be.maj(j, out[j - 1])
            return out
        if self.n == 1:
            return {0: be.g(0)}
        assert self.solve(dl) < INF, "infeasible"
        G, P = self._rec(0, self.n - 1, dl, (INF,) * self.n, be)
        if G.get(0) is None:
            G[0] = be.g(0)
        return {k: G[k] for k in range(self.n)}

    def _rec(self, s, e, LG, LP, be):
        plan = self._memo[(s, e, LG, LP)][1]
        if plan[0] == "leaf":
            return {s: None}, {s: be.P(s)}
        _, m, mode = plan
        k = m - s
        hiG, hiP = LG[k + 1:], LP[k + 1:]
        finG, finP = _fin(hiG), _fin(hiP)
        nG, nP = len(finG), len(finP)
        lowLP = LP[:k] + (min(LP[k], min(finP) - 1) if nP else LP[k],)
        if mode == "ripple":
            jlast = max(j for j in range(m + 1, e + 1) if LG[j - s] < INF)
            need_piv = min(LG[j - s] - (j - m) for j in range(m + 1, jlast + 1) if LG[j - s] < INF)
            lowLG = LG[:k] + (min(LG[k], need_piv),)
            upG = (INF,) * (e - m)
            upP = tuple(p - 1 for p in hiP)
        else:
            lowLG = LG[:k] + (min(LG[k], min(finG) - 1) if nG else LG[k],)
            upG = hiG
            upP = tuple(min(g - 1, p - 1) for g, p in zip(hiG, hiP))
        Glo, Plo = self._rec(s, m, lowLG, lowLP, be)
        if nG and Glo.get(m) is None:
            Glo[m] = be.g(m)  # single-element lower child used as pivot
        Ghi, Phi = self._rec(m + 1, e, upG, upP, be)
        G, P = dict(Glo), dict(Plo)
        if nG:
            piv = Glo[m]
            if mode == "ripple":
                prev = piv
                for j in range(m + 1, jlast + 1):
                    prev = be.maj(j, prev)
                    G[j] = prev
            else:
                for j in range(m + 1, e + 1):
                    if LG[j - s] == INF:
                        continue
                    if j == m + 1:
                        G[j] = be.maj(j, piv)
                    else:
                        if Ghi.get(j) is None:
                            Ghi[j] = be.g(j)
                        G[j] = be.xor(Ghi[j], be.and_(Phi[j], piv))
        if nP:
            pivP = Plo[m]
            for j in range(m + 1, e + 1):
                if LP[j - s] < INF:
                    P[j] = be.and_(Phi[j], pivP)
        return G, P


if __name__ == "__main__":
    for n, L in [(15, 4), (30, 5), (31, 5), (31, 6), (31, 8), (31, 12), (31, 31)]:
        s = Synth([0] * n, [1] * n, [1] * n)
        print(n, L, s.solve([L] * n))
    s = Synth([0] + [1] * 29, [1] + [2] * 29, [1] * 30)
    print("round profile:", s.solve([6] * 30))


class _RecBE:
    """Backend that records range productions instead of emitting gates."""

    def __init__(self):
        self.prods = []
        self.gs = set()

    def P(self, k): return ("P", k, k)
    def g(self, k): self.gs.add(k); return ("G", k, k)

    def and_(self, u, v):
        if u[0] == "P" and v[0] == "P":          # P[a..b] = P[m+1..b] & P[a..m]
            _, m1, b = u; _, a, m = v
            self.prods.append(("P", a, b, m, 0))
            return ("P", a, b)
        return ("PG", u, v)                       # P[m+1..b] & G[a..m], consumed by xor

    def xor(self, u, v):                          # G[m+1..b] ^ (P[m+1..b] & G[a..m])
        _, (tp, m1, b), (tg, a, m) = v
        self.prods.append(("G", a, b, m, 0))
        return ("G", a, b)

    def maj(self, k, G):
        _, a, m = G
        self.prods.append(("G", a, k, m, 0))
        return ("G", a, k)


def dp_productions(syn: "Synth", s, e, LG, LP):
    """Export the DP's plan for pwp(s, e, LG, LP) as exact-search style productions."""
    assert syn.pwp(s, e, LG, LP) < INF
    be = _RecBE()
    syn._rec(s, e, LG, LP, be)
    seen = set(); out = []
    for pr in be.prods:
        if pr[:4] not in seen:
            seen.add(pr[:4]); out.append(pr)
    return out, sorted(be.gs)
