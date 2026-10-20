"""Adaptive plan search with the exact integer tree (mirror of the Lean checker)."""
import sys
from dense import *
import dense

def total_deg(A):
    return max((j + k + len(f) - 1 for j, r in enumerate(A) for k, f in enumerate(r) if f), default=0)

def best_trunc(A, budget):
    """largest drop (smallest total degree cap) with dropped abs-sum <= budget; returns cap or None."""
    # dropped amount by degree level
    lvl = {}
    for j, r in enumerate(A):
        for k, f in enumerate(r):
            for m, x in enumerate(f):
                lvl[j+k+m] = lvl.get(j+k+m, 0) + abs(x)
    top = max(lvl) if lvl else 0
    cap = top; acc = 0
    while cap > 0 and acc + lvl.get(cap, 0) <= budget:
        acc += lvl.get(cap, 0); cap -= 1
    return (cap if cap < top else None), acc

class Searcher:
    def __init__(self, mode, weights, rem_frac=0.3, maxdepth=30, trunc=True, floor=None, dd=None):
        self.dd = dd
        self.floor = floor; self.depth_cost = {}
        self.mode = mode  # 'abs' (|A| <= D) or 'up' (A <= D)
        self.w = weights; self.rem_frac = rem_frac; self.maxdepth = maxdepth
        self.leaves = 0; self.nodes = 0; self.trunc = trunc
        self.fail = None
    def leaf_ok(self, A, D, rem):
        lo = lower(D, 0)
        if self.mode == 'abs': return absup(A, rem) <= lo
        return upper(A, rem) <= lo
    def search(self, A, D, rem, h, depth, scale_bits=0):
        self.scale_bits = scale_bits
        c0 = dense.COST[0]
        """returns plan string or None. h: relative half widths (for split heuristic)."""
        self.nodes += 1
        if self.leaf_ok(A, D, rem):
            self.leaves += 1; return 'L'
        if depth >= self.maxdepth:
            self.fail = (h, depth, absup(A, rem), rem, lower(D, 0), const(D)); return None
        plan = ''
        if self.trunc:
            Dl = lower(D, 0)
            if self.floor is not None: Dl = max(Dl, self.floor << self.scale_bits)
            if self.mode == 'abs': budget = int(max(0, self.rem_frac*max(Dl, 0) - rem) // 3)
            else: budget = int(max(0, self.rem_frac*(lower(D, 0) - const(A)) - rem) // 3)
            cap, acc = best_trunc(A, budget)
            if cap is not None:
                A, r2 = truncate_total(A, cap); assert r2 == acc
                rem += acc; plan += f'D{cap}'
                if self.leaf_ok(A, D, rem):
                    self.leaves += 1; return plan + 'L'
        wts = [h[i]/self.w[i] for i in range(3)]
        ax = max(range(3), key=lambda i: wts[i])
        if deg_ax(A, ax) <= 0 and deg_ax(D, ax) <= 0:
            # nothing depends on this axis; pick another
            order = sorted(range(3), key=lambda i: -wts[i])
            for i in order:
                if deg_ax(A, i) > 0 or deg_ax(D, i) > 0: ax = i; break
        d = max(deg_ax(A, ax), deg_ax(D, ax), 0) if self.dd is None else self.dd[ax]
        sub = []
        for sgn in (-1, 1):
            An = shift_ax(A, ax, sgn, d); Dn = shift_ax(D, ax, sgn, d)
            hn = list(h); hn[ax] /= 2
            self.depth_cost[depth] = self.depth_cost.get(depth, 0) + dense.COST[0] - c0; c0 = dense.COST[0]
            p = self.search(An, Dn, rem << d, hn, depth + 1, scale_bits + d)
            c0 = dense.COST[0]
            if p is None: return None
            sub.append(p)
        return plan + 'SZT'[ax] + sub[0] + sub[1]
