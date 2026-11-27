"""Wide-tube slab certificates for the label-0.474 forward trace (N-216 stage 3 pilot).

For every requested slab this script

1. computes, in exact integer arithmetic, Taylor models in normalized slab time of the three
   field polynomials and of their first and second formal derivatives, once on the reference
   line (zero spatial radius) and once on a coordinate rectangle containing the moving trial
   ball (the rectangle half-widths sit in the remainders of the two position models);
2. derives the rational numbers of ``DommaschkWideTubeStep.Numbers`` (central trace and disk
   bounds, and the bounds for the frame-conjugated second derivatives in both frame
   directions), the residual budget, and the ``PositionFrameSlabs.Step`` record;
3. checks every emitted inequality again with ``fractions.Fraction`` (``validate``);
4. writes Lean modules that prove, for that slab, the two-sided bound on the frame-reduced
   Jacobian on the whole trial ball (P1) and ``FieldBounds`` (P2), and for each group of
   consecutive slabs the chain over ``PositionFrameWide.valid``;
5. optionally compiles the modules with ``lean`` (at most ``--jobs`` processes) and records
   wall time, peak memory and the ``#print axioms`` output.

Trust: this script is an untrusted generator. The reference line and the frames are float
proposals (``wide_trace.py``); the starting radius of a group that does not start at slab 0
is an assumption of the pilot, stated in the emitted hand-off file. Only the compiled Lean
theorems are results.

    OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/qa2r_wide/wide_tube_pilot.py \
        --groups 0-3 268-271 --compile --jobs 8
"""
import argparse
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction as F
from math import ceil, floor, isqrt
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
KAM = ROOT / "scripts" / "dommaschk_kam"
sys.path.insert(0, str(KAM))
sys.path.insert(0, str(HERE))

from bounce_mirror_pilot import Model, R0M, SCALE, ZERO, angle_models  # noqa: E402
from bounce_phase_frame import FRAME_SCALE, affine_frame, shifted_jump  # noqa: E402
from emit_sparse_jacobian import derivative, matrix_certificate  # noqa: E402
from emit_sparse_taylor_slab import DATA, coefficients, field, model_literal, models  # noqa: E402
from emit_sparse_trace_defect_samples import emit_selected  # noqa: E402
from screen_sparse_reference_defects import enclosing_box, residual_models  # noqa: E402

import wide_trace  # noqa: E402

PACKAGE = "WideTube"
GRID = 10**8
SOURCES = (("dD", "D"), ("dnR", "R"), ("dnZ", "Z"))
VARIANTS = (("", ()), ("U", (0,)), ("Z", (1,)), ("UU", (0, 0)), ("UZ", (0, 1)), ("ZZ", (1, 1)))
DERIVED = {"U": "dU {}", "Z": "dZ {}", "UU": "dU (dU {})", "UZ": "dZ (dU {})", "ZZ": "dZ (dZ {})"}
OPTIONS = ("set_option linter.style.longLine false\nset_option Elab.async false\n"
           "set_option maxRecDepth 16000\n")
LICENSE = """/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

"""
RFL = ".dyadic (bits := 80) (Certificates.DyadicHornerStep.le_of_sub_toNat_zero rfl)"


def up(x, grid=GRID):
    return F(ceil(F(x) * grid), grid)


def down(x, grid=GRID):
    return F(floor(F(x) * grid), grid)


def sqrt_up(x, grid=GRID):
    """A grid rational r >= 0 with x <= r^2."""
    r = F(isqrt(ceil(F(x) * grid * grid)) + 1, grid)
    assert r >= 0 and x <= r * r
    return r


def magnitude(p):
    return sum(map(abs, p))


def fused(a, x, q=None):
    """A model of a*x+q whose radius is the least one accepted by DyadicHornerStep.Fits."""
    conv = [0] * (len(a.a) + len(x.a) - 1)
    for i, v in enumerate(a.a):
        for j, w in enumerate(x.a):
            conv[i + j] += v * w
    qa = q.a if q is not None else []
    qe = q.e if q is not None else 0
    exact = [(conv[k] if k < len(conv) else 0) + SCALE * (qa[k] if k < len(qa) else 0)
             for k in range(max(len(conv), len(qa)))]
    out = [(2 * v + SCALE) // (2 * SCALE) for v in exact[:8]]
    error = sum(abs(v - SCALE * (out[k] if k < len(out) else 0)) for k, v in enumerate(exact))
    total = a.e * (magnitude(x.a) + x.e) + x.e * magnitude(a.a) + SCALE * qe + error
    return Model(out, -(-total // SCALE))


def fits(a, x, q, out):
    """DyadicHornerStep.Fits 80, literally."""
    def plus(p, r):
        return [(p[k] if k < len(p) else 0) + (r[k] if k < len(r) else 0)
                for k in range(max(len(p), len(r)))]

    conv = [0] * (len(a.a) + len(x.a) - 1) if a.a and x.a else []
    for i, v in enumerate(a.a):
        for j, w in enumerate(x.a):
            conv[i + j] += v * w
    err = plus(conv, [SCALE * v for v in plus(q.a, [-v for v in out.a])])
    return (a.e * (magnitude(x.a) + x.e) + x.e * magnitude(a.a) + SCALE * q.e + magnitude(err)
            <= SCALE * out.e)


def const(c):
    return Model([SCALE * c], 0)


class Ops:
    """Records multiply-add steps as Lean definitions, checks and proof lines."""

    def __init__(self):
        self.defs, self.proof, self.table, self.count = [], [], {}, 0

    def leaf(self, key, lean_name, model, line):
        self.table[key] = (lean_name, model)
        self.proof.append(line)
        return key

    def _emit(self, name, model, operands, line):
        a, x, q = operands
        assert fits(a[1], x[1], q[1], model), name
        md = "model" + name
        self.defs.append(f"private def {md} : Model := {model_literal(model)}")
        self.defs.append(f"private theorem check{name} : Certificates.DyadicHornerStep.MulAdd "
                         f"{a[0]} {x[0]} {q[0]} {md} :=\n  {RFL}\n")
        self.proof.append(line)
        self.table[name] = (md, model)
        self.count += 1
        return name

    def mul(self, name, a, x):
        A, X = self.table[a], self.table[x]
        zero = ("(DommaschkDyadicFrameModel.constant 0)", const(0))
        return self._emit(name, fused(A[1], X[1]), (A, X, zero),
                          f"  have h{name} := DommaschkDyadicFrameModel.mul_mem check{name} ht h{a} h{x}")

    def muladd(self, name, a, x, q):
        A, X, Q = self.table[a], self.table[x], self.table[q]
        return self._emit(name, fused(A[1], X[1], Q[1]), (A, X, Q),
                          f"  have h{name} := check{name}.mem ht h{a} h{x} h{q}")

    def add(self, name, a, b):
        A, B = self.table[a], self.table[b]
        one = ("(DommaschkDyadicFrameModel.constant 1)", const(1))
        return self._emit(name, A[1] + B[1], (A, one, B),
                          f"  have h{name} := DommaschkDyadicFrameModel.add_mem check{name} ht h{a} h{b}")

    def sub(self, name, a, b):
        A, B = self.table[a], self.table[b]
        minus = ("(DommaschkDyadicFrameModel.constant (-1))", const(-1))
        return self._emit(name, A[1] - B[1], (B, minus, A),
                          f"  have h{name} := DommaschkDyadicFrameModel.sub_mem check{name} ht h{a} h{b}")

    def neg(self, name, a):
        A = self.table[a]
        minus = ("(DommaschkDyadicFrameModel.constant (-1))", const(-1))
        zero = ("(DommaschkDyadicFrameModel.constant 0)", const(0))
        return self._emit(name, -A[1], (A, minus, zero),
                          f"  have h{name} := DommaschkDyadicFrameModel.neg_mem check{name} ht h{a}")

    def range(self, key, mid, rad):
        """|y - mid| <= rad for every member y of the model, validated exactly."""
        md, model = self.table[key]
        assert (F(model.e, SCALE) + abs(F(model.a[0], SCALE) - mid)
                + F(magnitude(model.a[1:]), SCALE) <= rad), key
        self.defs.append(f"""private theorem range{key} {{t y : ℝ}} (ht : |t| ≤ 1) (h : {md}.Mem t y) :
    |y - {mid}| ≤ {rad} := by
  have hh := enclose (c := ⟨[{mid}], {rad}⟩) ht h (by kernel_fact)
  simpa [Model.Mem, PlasmaLean.Certificates.QPoly.eval_cons,
    PlasmaLean.Certificates.QPoly.eval_nil] using hh
""")
        self.proof.append(f"  have bound{key} := range{key} ht h{key}")


# ------------------------------------------------------------------ numerics of one slab
def jet_terms():
    text = DATA.read_text()
    out = {}
    for source, tag in SOURCES:
        base = coefficients(text, source)
        for suffix, axes in VARIANTS:
            terms = base
            for axis in axes:
                terms = derivative(terms, axis)
            out[tag + suffix] = terms
    return out


def lean_poly(source, suffix):
    return source if not suffix else DERIVED[suffix].format(source)


def poly_name(source, tag, suffix):
    return source if not suffix else "jet" + tag + suffix


def row_radius(a, b, trial):
    """Least natural p with (a^2+b^2) trial^2 <= (p 2^40)^2."""
    target = (a * a + b * b) * trial * trial
    p = isqrt(target) // FRAME_SCALE
    while (p * FRAME_SCALE) ** 2 < target:
        p += 1
    return p


def det_floor(l, r):
    """PositionFrameSlabs.detFloor."""
    (la, lb), (lc, ld) = l
    (ra, rb), (rc, rd) = r
    p = (la + ra, lb + rb, lc + rc, ld + rd)
    d = (ra - la, rb - lb, rc - lc, rd - ld)
    det = lambda m: m[0] * m[3] - m[1] * m[2]  # noqa: E731
    mixed = p[0] * d[3] + d[0] * p[3] - p[1] * d[2] - d[1] * p[2]
    return F(det(p) - abs(mixed) - abs(det(d)), 4 * 2**80)


def norm_product(l, r):
    (la, lb), (lc, ld) = l
    (ra, rb), (rc, rd) = r
    a, b, c, d = (max(abs(x), abs(y)) for x, y in ((la, ra), (lb, rb), (lc, rc), (ld, rd)))
    return max(a + c, b + d) * max(a + b, c + d)


class Slab:
    """All numbers of one slab certificate; `previous` is (point, radius) of the entry state."""

    def __init__(self, row, trial, terms):
        self.index = i = row["index"]
        self.trial = trial
        self.start, self.end = row["frame_start"], row["frame_end"]
        self.coeffs = row["coefficients"]
        self.stem = f"DommaschkWideTubeF{i:03}"
        self.res = f"DommaschkTraceResidualWideForward{i:03}"
        nominal = [Model(list(c)) for c in self.coeffs]
        self.nominal = nominal
        waves = angle_models(F(2 * i + 1, 128), F(1, 128), F(0))
        self.central_columns = (nominal[0] - R0M, nominal[1], waves[2], waves[1])
        self.radial = max(row_radius(*m[0], trial) for m in (self.start, self.end))
        self.vertical = max(row_radius(*m[1], trial) for m in (self.start, self.end))
        self.tube_columns = (Model(self.central_columns[0].a, self.radial),
                             Model(nominal[1].a, self.vertical), waves[2], waves[1])
        safe = F(self.radial, SCALE) + F(magnitude(self.tube_columns[0].a), SCALE)
        assert safe <= F(1, 2), "rectangle too close to the axis"
        self.terms = terms
        self.central_blocks = {k: models(terms[k], self.central_columns)
                               for k in ("D", "DU", "DZ", "R", "RU", "RZ", "Z", "ZU", "ZZ")}
        self.tube_blocks = {k: models(v, self.tube_columns) for k, v in terms.items()}
        self.numbers = {}
        self._central()
        self._tube()
        self._residual()

    # central line: the existing matrix certificate with integer multiply-add checks
    def _central(self):
        source_models = {}
        for source, tag in SOURCES:
            for suffix in ("", "U", "Z"):
                key = tag + suffix
                name = source if not suffix else "grad" + key
                source_models[key] = (name + "0", name, sum(self.central_blocks[key], ZERO))
        got = {}

        def numeric(table, step):
            lo, hi = table["den"][1].bound()
            mid = down((lo + hi) / 2)
            radius = up(max(mid - lo, hi - mid))
            dl = mid - radius
            tr, di, off = (up(max(map(abs, table[t][1].bound()))) for t in ("tr", "dif", "off"))
            disk = sqrt_up(di * di + off * off)
            mu0 = up((tr + disk) / (2 * dl))
            assert dl > 0
            got.update(dl=dl, tr=tr, di=di, off=off, disk=disk, mu0=mu0)
            return list(map(str, [mid, radius, dl, tr, di, off]))

        modules = [self.res + s for s in ("D", "DU", "DZ", "R", "RU", "RZ", "Z", "ZU", "ZZ")]
        text = matrix_certificate(source_models, dict(frame_end=self.end), namespace=self.res,
                                  start=self.start, dependencies=modules,
                                  context="DommaschkJacobian", numeric=numeric,
                                  integer_frame=True)
        for old, new in (("firstLeft", "leftFrame"), ("firstRight", "rightFrame"),
                         ("(hin : trial.Mem t u z c s)", "(hin : reference.Mem t u z c s)")):
            assert old in text
            text = text.replace(old, new)
        for old, new in ((f"A.a + A.d ≤ {got['tr']} ∧", f"|A.a + A.d| ≤ {got['tr']} ∧"),
                         ("  · exact (le_abs_self _).trans (by simpa only [sub_zero] using boundtr)",
                          "  · exact (by simpa only [sub_zero] using boundtr)")):
            assert text.count(old) == 1, old
            text = text.replace(old, new)
        self.central_text = text
        self.numbers.update(got)

    def _tube(self):
        ops = Ops()
        for source, tag in SOURCES:
            for suffix, _ in VARIANTS:
                key = tag + suffix
                name = poly_name(source, tag, suffix)
                ops.leaf(key, name + "0", sum(self.tube_blocks[key], ZERO),
                         f"  have h{key} := {name}_checked.mem ht hin")
        m = affine_frame(self.start, self.end, F(1, 64))[0]
        for k, model, (row, col) in zip("abcd", (m[0][0], m[0][1], m[1][0], m[1][1]),
                                        ((0, 0), (0, 1), (1, 0), (1, 1))):
            lit = (f"(ofDyadic 80 [2^39*(leftFrame.{k}+rightFrame.{k}),"
                   f"2^39*(rightFrame.{k}-leftFrame.{k})] 0)")
            ops.leaf("M" + k, lit, model,
                     f"  have hM{k} := DommaschkDyadicFrameModel.frame_mem leftFrame.{k} rightFrame.{k} t")
        for k in ("DU", "DZ", "DUU", "DUZ", "DZZ"):
            ops.neg("n" + k, k)
        for N in "RZ":
            fU = ops.muladd("fU" + N, N + "U", "D", ops.mul("fUt" + N, N, "nDU"))
            fZ = ops.muladd("fZ" + N, N + "Z", "D", ops.mul("fZt" + N, N, "nDZ"))
            pUU = ops.muladd("pUU" + N, N + "UU", "D", ops.mul("pUUt" + N, N, "nDUU"))
            mixed = ops.mul("pMt" + N, N, "nDUZ")
            pUZ = ops.muladd("pUZ" + N, N + "UZ", "D", ops.muladd(
                "pUZb" + N, N + "U", "DZ", ops.muladd("pUZa" + N, N + "Z", "nDU", mixed)))
            pZU = ops.muladd("pZU" + N, N + "UZ", "D", ops.muladd(
                "pZUb" + N, N + "Z", "DU", ops.muladd("pZUa" + N, N + "U", "nDZ", mixed)))
            pZZ = ops.muladd("pZZ" + N, N + "ZZ", "D", ops.mul("pZZt" + N, N, "nDZZ"))
            f2U, f2Z = ops.add("f2U" + N, fU, fU), ops.add("f2Z" + N, fZ, fZ)
            ops.muladd("sUU" + N, pUU, "D", ops.mul("sUUt" + N, f2U, "nDU"))
            ops.muladd("sUZ" + N, pUZ, "D", ops.mul("sUZt" + N, f2U, "nDZ"))
            ops.muladd("sZU" + N, pZU, "D", ops.mul("sZUt" + N, f2Z, "nDU"))
            ops.muladd("sZZ" + N, pZZ, "D", ops.mul("sZZt" + N, f2Z, "nDZ"))
        ops.neg("negB", "Mb")
        ops.neg("negC", "Mc")
        for l, (p, q) in enumerate((("Ma", "Mc"), ("Mb", "Md"))):
            t = f"L{l}"
            ja = ops.muladd(t + "ja", "sUUR", p, ops.mul(t + "jat", "sUZR", q))
            jb = ops.muladd(t + "jb", "sZUR", p, ops.mul(t + "jbt", "sZZR", q))
            jc = ops.muladd(t + "jc", "sUUZ", p, ops.mul(t + "jct", "sUZZ", q))
            jd = ops.muladd(t + "jd", "sZUZ", p, ops.mul(t + "jdt", "sZZZ", q))
            ca = ops.muladd(t + "ca", ja, "Ma", ops.mul(t + "cat", jb, "Mc"))
            cb = ops.muladd(t + "cb", ja, "Mb", ops.mul(t + "cbt", jb, "Md"))
            cc = ops.muladd(t + "cc", jc, "Ma", ops.mul(t + "cct", jd, "Mc"))
            cd = ops.muladd(t + "cd", jc, "Mb", ops.mul(t + "cdt", jd, "Md"))
            aa = ops.muladd(t + "aa", "Md", ca, ops.mul(t + "aat", "negB", cc))
            ab = ops.muladd(t + "ab", "Md", cb, ops.mul(t + "abt", "negB", cd))
            ac = ops.muladd(t + "ac", "negC", ca, ops.mul(t + "act", "Ma", cc))
            ad = ops.muladd(t + "ad", "negC", cb, ops.mul(t + "adt", "Ma", cd))
            ops.add(t + "tr", aa, ad)
            ops.sub(t + "dif", aa, ad)
            ops.add(t + "off", ab, ac)
        det = ops.sub("det", ops.mul("detAD", "Ma", "Md"), ops.mul("detBC", "Mb", "Mc"))
        den = ops.mul("den", det, ops.mul("cube", ops.mul("square", "D", "D"), "D"))
        lo, hi = ops.table[den][1].bound()
        mid = down((lo + hi) / 2)
        radius = up(max(mid - lo, hi - mid))
        n = dict(dlT=mid - radius)
        assert n["dlT"] > 0, "tube denominator not positive"
        ops.range(den, mid, radius)
        for l in (0, 1):
            for tag, key in (("tr", "tr"), ("dif", "di"), ("off", "off")):
                name = f"L{l}{tag}"
                n[f"{key}{l}"] = up(max(map(abs, ops.table[name][1].bound())))
                ops.range(name, 0, n[f"{key}{l}"])
            n[f"disk{l}"] = sqrt_up(n[f"di{l}"] ** 2 + n[f"off{l}"] ** 2)
            n[f"g{l}"] = up((n[f"tr{l}"] + n[f"disk{l}"]) / (2 * n["dlT"]))
        n["lip"] = sqrt_up(n["g0"] ** 2 + n["g1"] ** 2)
        n["mu"] = up(self.numbers["mu0"] + n["lip"] * F(self.trial, SCALE))
        self.numbers.update(n)
        self.tube_ops, self.tube_mid, self.tube_radius = ops, mid, radius

    def _residual(self):
        transformed, denominator = residual_models(0, 1, self.index, self.coeffs, self.start,
                                                   self.end)
        rb, zb, dl = enclosing_box(transformed, denominator, 8)
        assert dl > 0
        self.budget = F(-(-(isqrt(rb * rb + zb * zb) + 1) * SCALE // dl), SCALE)
        assert rb * rb + zb * zb <= (self.budget * dl) ** 2

    def validate(self):
        """Every closed rational side condition of Numbers.Valid, in exact arithmetic."""
        n, rho = self.numbers, F(self.trial, SCALE)
        assert n["dl"] > 0 and n["mu0"] >= 0 and n["disk"] >= 0
        assert n["di"] ** 2 + n["off"] ** 2 <= n["disk"] ** 2
        assert n["tr"] + n["disk"] <= 2 * n["dl"] * n["mu0"]
        assert n["dlT"] > 0 and n["lip"] >= 0
        for l in (0, 1):
            assert n[f"g{l}"] >= 0 and n[f"disk{l}"] >= 0
            assert n[f"di{l}"] ** 2 + n[f"off{l}"] ** 2 <= n[f"disk{l}"] ** 2
            assert n[f"tr{l}"] + n[f"disk{l}"] <= 2 * n["dlT"] * n[f"g{l}"]
        assert n["g0"] ** 2 + n["g1"] ** 2 <= n["lip"] ** 2
        assert n["mu0"] + n["lip"] * rho <= n["mu"]
        for frame in (self.start, self.end):
            for (a, b), p in zip(frame, (self.radial, self.vertical)):
                assert (a * a + b * b) * self.trial**2 <= (p * FRAME_SCALE) ** 2

    def step(self, point, radius):
        """The Step record entered from (point, radius), with the wide validity check."""
        nominal = self.nominal
        jump = tuple(x.endpoint(-1) - y for x, y in zip(nominal, point, strict=True))
        jump_bound = shifted_jump(self.start, jump)
        incoming = radius + jump_bound
        mu, defect = self.numbers["mu"], self.budget
        outgoing = ceil((64 * incoming + SCALE * defect) / (64 - mu))
        product = norm_product(self.start, self.end)
        op = F(isqrt(product) + 1, FRAME_SCALE)
        det_lower = det_floor(self.start, self.end)
        physical = [ceil(op * x) for x in (incoming, outgoing, self.trial)]
        (a, b), (c, d) = self.start
        det = a * d - b * c
        x, y = jump
        checks = dict(
            length=all(len(p) == 8 for p in self.coeffs), det=det >= 1,
            jump=SCALE * ((d * x - b * y) ** 2 + (a * y - c * x) ** 2) <= jump_bound**2 * det**2,
            det_lower=F(97, 100) < det_lower, op=0 <= op < F(31, 10),
            norm=product <= SCALE * op * op, defect=defect >= 0, rate=0 <= mu < 64,
            growth=64 * incoming + SCALE * defect <= outgoing * (64 - mu),
            trial=outgoing < self.trial, physical=op * outgoing <= physical[1])
        if not all(checks.values()):
            raise ArithmeticError(f"slab {self.index}: wide step check fails: {checks}")
        record = dict(px=self.coeffs[0], py=self.coeffs[1], frame=self.end, jump=jump,
                      jumpBound=jump_bound, incoming=incoming, outgoing=outgoing,
                      trial=self.trial, physicalIn=physical[0], physicalOut=physical[1],
                      physicalTrial=physical[2], detLower=det_lower, op=op, mu=mu, defect=defect)
        return record, ([x.endpoint(1) for x in nominal], outgoing)


# ------------------------------------------------------------------ Lean text
def localize(text, local):
    """Imports of modules of this package use the package root."""
    def swap(match):
        return f"public import {PACKAGE}.{match[1]}" if match[1] in local else match[0]
    return re.sub(r"^public import PlasmaLean\.Design\.(\w+)$", swap, text, flags=re.MULTILINE)


def poly_module(namespace, imports, source, name, lean, terms, columns, input_name):
    out = LICENSE + "".join(f"public import {x}\n" for x in imports)
    out += "public import PlasmaLean.Design.DommaschkJacobianFrames\n"
    out += f"""
/-! # Taylor enclosure of `{lean}` on a wide-tube slab

Generated by `scripts/qa2r_wide/wide_tube_pilot.py`. -/

@[expose] public section
namespace PlasmaLean.Design.{namespace}

open PlasmaLean.Certificates.TrajectoryTaylorModel DommaschkKam DommaschkKam.DkPoly
open DommaschkBounceTaylor DommaschkJacobian

{OPTIONS}
"""
    if name != source:
        out += f"/-- The formal derivative enclosed in this module. -/\nabbrev {name} : SP := {lean}\n\n"
    out += field(name, columns, input_name, terms=terms)
    return out + f"\nend PlasmaLean.Design.{namespace}\n"


def frame_literal(frame):
    return "⟨" + ", ".join(str(x) for row in frame for x in row) + "⟩"


def lean_int(x):
    return f"({x})" if x < 0 else str(x)


def step_literal(r):
    ints = lambda p: "[" + ", ".join(map(lean_int, p)) + "]"  # noqa: E731
    return (f"⟨{ints(r['px'])}, {ints(r['py'])},\n   {frame_literal(r['frame'])}, "
            f"⟨{lean_int(r['jump'][0])}, {lean_int(r['jump'][1])}⟩,\n   {r['jumpBound']}, "
            f"{r['incoming']}, {r['outgoing']}, {r['trial']}, {r['physicalIn']}, "
            f"{r['physicalOut']}, {r['physicalTrial']},\n   ({r['detLower']}), ({r['op']}), "
            f"({r['mu']}), ({r['defect']})⟩")


def tube_modules(slab):
    """Inputs, eighteen polynomial enclosures and the directional bounds on the rectangle."""
    stem, files = slab.stem, {}
    files[stem + "Inputs"] = LICENSE + f"""public import PlasmaLean.Design.DommaschkJacobianFrames

/-! # Coordinate rectangle of forward slab {slab.index}, label 0.474

Generated by `scripts/qa2r_wide/wide_tube_pilot.py`. -/

@[expose] public section
namespace PlasmaLean.Design.{stem}

open PlasmaLean.Certificates.TrajectoryTaylorModel DommaschkKam DommaschkBounceTaylor
open PlasmaLean.Certificates.PositionFrameSlabs

{OPTIONS}
/-- Reference polynomials with the rectangle half-widths, and the two harmonic models. -/
def tube : Inputs := ⟨{(',' + chr(10) + '  ').join(map(model_literal, slab.tube_columns))}⟩

/-- Frame at the start of the slab. -/
def leftFrame : Frame := {frame_literal(slab.start)}

/-- Frame at the end of the slab. -/
def rightFrame : Frame := {frame_literal(slab.end)}

end PlasmaLean.Design.{stem}
"""
    polys = []
    for source, tag in SOURCES:
        for suffix, _ in VARIANTS:
            module = stem + "T" + tag + suffix
            polys.append(module)
            files[module] = poly_module(stem, [f"{PACKAGE}.{stem}Inputs"], source,
                                        poly_name(source, tag, suffix), lean_poly(source, suffix),
                                        slab.terms[tag + suffix], slab.tube_columns, "tube")
    n, ops = slab.numbers, slab.tube_ops
    out = LICENSE + "".join(f"public import {PACKAGE}.{m}\n" for m in polys)
    out += f"""public import PlasmaLean.Design.DommaschkDyadicFrameModel
public import PlasmaLean.Design.DommaschkWideTubeHessian

/-! # Frame-conjugated second derivatives on the rectangle of forward slab {slab.index}

Generated by `scripts/qa2r_wide/wide_tube_pilot.py`: {ops.count} certified multiply-adds. -/

@[expose] public section
namespace PlasmaLean.Design.{stem}

open PlasmaLean.Certificates.TrajectoryTaylorModel DommaschkKam DommaschkKam.DkPoly
open DommaschkBounceTaylor DommaschkJacobian DommaschkWideTubeHessian
open PlasmaLean.Certificates.PositionFrameSlabs

{OPTIONS}
"""
    out += "\n".join(ops.defs)
    out += f"""
/-- Joint bounds on the rectangle: the common denominator `det M · D³` and, for both frame
directions, the trace, diagonal difference and off-diagonal sum of the conjugated numerator
of the derivative of the spatial Jacobian. -/
theorem tube_bounds {{t u z c s : ℝ}} (ht : |t| ≤ 1) (hin : tube.Mem t u z c s) :
    TubeBounds (frameEntries leftFrame rightFrame t) (jet dnR u z c s) (jet dnZ u z c s)
      (jet dD u z c s) ({n['dlT']}) ({n['tr0']}) ({n['di0']}) ({n['off0']})
      ({n['tr1']}) ({n['di1']}) ({n['off1']}) := by
"""
    out += "\n".join(ops.proof)
    out += f"""
  have lower (v : ℝ) (h : |v - {slab.tube_mid}| ≤ {slab.tube_radius}) : ({n['dlT']}) ≤ v := by
    linarith only [(abs_le.mp h).1]
  dsimp only [TubeBounds, DirectionBounds, conjugated, direction, secUU, secUZ, secZU, secZZ,
    partUU, partUZ, partZU, partZZ, firstU, firstZ, jet, Entries.product, Entries.adj,
    Entries.det, frameEntries]
  refine ⟨lower _ boundden, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact (by simpa only [sub_zero] using boundL0tr)
  · exact (by simpa only [sub_zero] using boundL0dif)
  · exact (by simpa only [sub_zero] using boundL0off)
  · exact (by simpa only [sub_zero] using boundL1tr)
  · exact (by simpa only [sub_zero] using boundL1dif)
  · exact (by simpa only [sub_zero] using boundL1off)

end PlasmaLean.Design.{stem}
"""
    files[stem + "Tube"] = out
    return files


def central_modules(slab):
    """Residual packet (existing emitter), six gradient enclosures and the central bounds."""
    res, files = slab.res, {}
    job = (0, 1, slab.index, slab.coeffs, slab.start, slab.end, str(slab.budget), 8)
    raw = dict(emit_selected([job], label="Wide", launch=F(474, 1000)))
    assert list(raw)[-1] == res
    for source, tag in SOURCES:
        for axis, variable in enumerate("UZ"):
            key = tag + variable
            raw[res + key] = poly_module(res, [f"{PACKAGE}.{res}Inputs"], source, "grad" + key,
                                         lean_poly(source, variable), slab.terms[key],
                                         slab.central_columns, "reference")
    raw[res + "Jacobian"] = slab.central_text
    for name, text in raw.items():
        files[name] = localize(text, set(raw))
    return files


def slab_module(slab, group, position, record):
    i, stem, res, n = slab.index, slab.stem, slab.res, slab.numbers
    block, j = divmod(i, 8)
    previous = f"{group}.start" if position == 0 else f"next {group}.row{position - 1}"
    order = ("dl", "tr", "di", "off", "disk", "mu0", "dlT", "tr0", "di0", "off0", "disk0", "g0",
             "tr1", "di1", "off1", "disk1", "g1", "lip", "mu")
    fields = ", ".join(f"({n[k]})" for k in order)
    casts = "\n".join(
        f"private theorem cast_{k} : ((numbers.{lean} : ℚ) : ℝ) = ({n[k]}) := by norm_num [numbers]"
        for k, lean in (("dl", "dl"), ("tr", "tr"), ("di", "di"), ("off", "off"), ("dlT", "dlT"),
                        ("tr0", "tr₀"), ("di0", "di₀"), ("off0", "off₀"), ("tr1", "tr₁"),
                        ("di1", "di₁"), ("off1", "off₁")))

    def harmonic(name, inputs):
        return f"""private theorem {name} {{t : ℝ}} (ht : t ∈ Icc ({i} / 64 : ℝ) ({i + 1} / 64)) :
    {inputs}.cos.Mem (128 * t - {2 * i + 1}) (Real.cos (2 * t)) ∧
      {inputs}.sin.Mem (128 * t - {2 * i + 1}) (Real.sin (2 * t)) := by
  let packet := DommaschkHarmonicBlock{block:02}.packet ({j} : Fin 8)
  have ht' : t ∈ Set.Icc ((↑({8 * block}+({j} : Fin 8).val : ℕ) : ℝ)/64)
      (((↑({8 * block}+({j} : Fin 8).val : ℕ) : ℝ)+1)/64) := by norm_num at ht ⊢; exact ht
  have cos := Certificates.TrajectoryHarmonicPacket.physical packet false 0 false ht'
  have sin := Certificates.TrajectoryHarmonicPacket.physical packet false 0 true ht'
  constructor
  · change ((packet false 0).model false).Mem _ _
    norm_num [Certificates.TrajectoryTrig.wave] at cos ⊢
    exact cos
  · change ((packet false 0).model true).Mem _ _
    norm_num [Certificates.TrajectoryTrig.wave] at sin ⊢
    exact sin
"""
    return LICENSE + f"""public import PlasmaLean.Certificates.PositionFrameWideChain
public import PlasmaLean.Design.DommaschkWideTubeStep
public import PlasmaLean.Design.DommaschkHarmonicBlock{block:02}
public import {PACKAGE}.{group}
public import {PACKAGE}.{stem}Tube
public import {PACKAGE}.{res}Jacobian
public import {PACKAGE}.{res}

/-! # Wide-tube certificate of forward slab {i}, label 0.474, phase 0

Generated by `scripts/qa2r_wide/wide_tube_pilot.py`. The two-sided bound on the
frame-reduced Jacobian holds on the whole trial ball of frame radius
`{slab.trial} / 2^80` for all times of the slab. -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{stem}

open Certificates PositionFrameSlabs TrajectoryTaylorModel DommaschkKam DommaschkBounceField
open DommaschkBounceTaylor DommaschkJacobian DommaschkPhysicalTraceStep Set
open DommaschkWideTubeHessian DommaschkWideTubeStep
open scoped RealInnerProductSpace

{OPTIONS}
/-- Entrance state inherited from the preceding record of the group. -/
abbrev previous : PositionFrameSlabs.State := {previous}

/-- The record of this slab. -/
abbrev row : Step := {group}.row{position}

/-- The record passes the wide step check from the inherited state. -/
theorem checked : PositionFrameWide.valid previous row = true := by with_unfolding_all rfl

private theorem geo : geometry allLimits previous row = true :=
  (Bool.and_eq_true_iff.mp checked).1

private theorem clock (t : ℝ) : coord ({i} / 64) t = 128 * t - {2 * i + 1} := by
  unfold coord; ring

private theorem stop : ({i} / 64 : ℝ) + 1 / 64 = {i + 1} / 64 := by norm_num

private theorem tubeMatches : CenterMatches row tube := by
  constructor <;> with_unfolding_all rfl

private theorem centralMatches : CenterMatches row {res}.reference := by
  constructor <;> with_unfolding_all rfl

private theorem box : PositionFrameProjection.Rectangle previous.frame row.frame row.trial
    {slab.radial} {slab.vertical} := by
  constructor <;> unfold PositionFrameProjection.rowFits <;>
    apply (Int.ble'_eq_true _ _).mp <;> with_unfolding_all rfl

private theorem ru : (tube.u.radius : ℝ) = ({slab.radial} : ℝ) / 2 ^ 80 := by
  change (({slab.radial} / 2 ^ 80 : ℚ) : ℝ) = _
  norm_num

private theorem rz : (tube.z.radius : ℝ) = ({slab.vertical} : ℝ) / 2 ^ 80 := by
  change (({slab.vertical} / 2 ^ 80 : ℚ) : ℝ) = _
  norm_num

/-- The rational numbers of the certificate; `mu` is the certified two-sided bound. -/
def numbers : Numbers := ⟨{fields}⟩

/-- The closed rational side conditions, with the trial radius of the record. -/
theorem numbers_valid : numbers.Valid (row.trial / 2 ^ 80) := by
  have trial : (row.trial : ℚ) = {slab.trial} := rfl
  rw [trial]
  constructor <;> norm_num [numbers]

{casts}

{harmonic('harmonicTube', 'tube')}
{harmonic('harmonicCentral', res + '.reference')}
private theorem central_bounds : ∀ t ∈ Icc ({i} / 64 : ℝ) ({i} / 64 + 1 / 64), ∀ u z,
    {res}.reference.u.Mem (coord ({i} / 64) t) u →
    {res}.reference.z.Mem (coord ({i} / 64) t) z →
    CentralBounds previous.frame row.frame (coord ({i} / 64) t) u z
      (Real.cos (2 * (0 + 1 * t))) (Real.sin (2 * (0 + 1 * t)))
      numbers.dl numbers.tr numbers.di numbers.off := by
  intro t ht u z hu hz
  have ht2 : t ∈ Icc ({i} / 64 : ℝ) ({i + 1} / 64) := stop ▸ ht
  have hs : |128 * t - {2 * i + 1}| ≤ 1 :=
    abs_le.mpr ⟨by linarith [ht2.1], by linarith [ht2.2]⟩
  rw [clock] at hu hz ⊢
  obtain ⟨hc, hsn⟩ := harmonicCentral ht2
  have h := {res}.symmetric_bounds hs ⟨hu, hz, hc, hsn⟩
  unfold CentralBounds
  rw [cast_dl, cast_tr, cast_di, cast_off, show (0 : ℝ) + 1 * t = t by ring]
  exact h

private theorem directional_bounds : ∀ t ∈ Icc ({i} / 64 : ℝ) ({i} / 64 + 1 / 64), ∀ u z,
    tube.u.Mem (coord ({i} / 64) t) u → tube.z.Mem (coord ({i} / 64) t) z →
    let c := Real.cos (2 * (0 + 1 * t))
    let s' := Real.sin (2 * (0 + 1 * t))
    TubeBounds (frameEntries previous.frame row.frame (coord ({i} / 64) t)) (jet dnR u z c s')
      (jet dnZ u z c s') (jet dD u z c s') numbers.dlT numbers.tr₀ numbers.di₀ numbers.off₀
      numbers.tr₁ numbers.di₁ numbers.off₁ := by
  intro t ht u z hu hz
  have ht2 : t ∈ Icc ({i} / 64 : ℝ) ({i + 1} / 64) := stop ▸ ht
  have hs : |128 * t - {2 * i + 1}| ≤ 1 :=
    abs_le.mpr ⟨by linarith [ht2.1], by linarith [ht2.2]⟩
  rw [clock] at hu hz ⊢
  obtain ⟨hc, hsn⟩ := harmonicTube ht2
  have h := tube_bounds hs ⟨hu, hz, hc, hsn⟩
  dsimp only
  rw [cast_dlT, cast_tr0, cast_di0, cast_off0, cast_tr1, cast_di1, cast_off1,
    show (0 : ℝ) + 1 * t = t by ring]
  exact h

/-- **P1.** Two-sided bound on the frame-reduced Jacobian of the forward field line flow
on the whole trial ball, for all times of the slab. -/
theorem abs_quadratic : ∀ t ∈ Icc ({i} / 64 : ℝ) ({i} / 64 + 1 / 64),
    ∀ v ∈ Metric.closedBall (0 : Plane) (row.trial / (2 : ℝ) ^ 80), ∀ w : Plane,
    |⟪w, Fields.LogNormTrajectory.MovingFrame.jacobian
      (velocityJacobian 0 1 t (reference ({i} / 64) row t + moving previous row ({i} / 64) t v))
      (moving previous row ({i} / 64) t) (frameVelocity previous.frame row.frame) w⟫| ≤
      (({n['mu']} : ℚ) : ℝ) * ‖w‖ ^ 2 :=
  DommaschkWideTubeStep.abs_quadratic (n := numbers) geo centralMatches
    (eq_of_beq (by kernel_fact)) (eq_of_beq (by kernel_fact)) tubeMatches box ru rz
    numbers_valid central_bounds directional_bounds

/-- The lower half of **P1**, as used by the backward distance estimate. -/
theorem neg_le_quadratic : ∀ t ∈ Icc ({i} / 64 : ℝ) ({i} / 64 + 1 / 64),
    ∀ v ∈ Metric.closedBall (0 : Plane) (row.trial / (2 : ℝ) ^ 80), ∀ w : Plane,
    -((({n['mu']} : ℚ) : ℝ) * ‖w‖ ^ 2) ≤ ⟪w, Fields.LogNormTrajectory.MovingFrame.jacobian
      (velocityJacobian 0 1 t (reference ({i} / 64) row t + moving previous row ({i} / 64) t v))
      (moving previous row ({i} / 64) t) (frameVelocity previous.frame row.frame) w⟫ :=
  fun t ht v hv w => (abs_le.mp (abs_quadratic t ht v hv w)).1

/-- **P2.** All field hypotheses of the wide position-frame step on the trial ball:
regularity, the upper logarithmic-norm bound and the residual of the reference line. -/
theorem field_bounds : FieldBounds previous row ({i} / 64) (euclideanFlow 0 1)
    (velocityJacobian 0 1) ballDomain := by
  apply DommaschkWideTubeStep.field_bounds (n := numbers) (central := {res}.reference)
    (tube := tube) geo centralMatches (eq_of_beq (by kernel_fact)) (eq_of_beq (by kernel_fact))
    tubeMatches box ru rz (by kernel_fact) numbers_valid (by norm_num [numbers, {group}.row{position}])
    central_bounds directional_bounds
  intro t ht
  have h := Ico_subset_Icc_self ht
  apply residual_of_pulled geo centralMatches h
  have fm : residualFrame previous row = {res}.frame := by with_unfolding_all rfl
  have b : row.defect = {res}.budget := rfl
  simpa only [clock, fm, b] using {res}.physical_defect (stop ▸ h)

/-- The field line flow carries the entrance ellipsoid through this slab. -/
theorem physical_step : Fields.TrajectorySlabs.Step (euclideanFlow 0 1)
    (physicalSlab previous row ({i} / 64)) (stateSet previous) (stateSet (next row)) :=
  PositionFrameWide.physical_step_on checked field_bounds

end PlasmaLean.Design.{stem}
"""


def rows_module(group, slabs, records, start, note):
    point, frame, radius = start
    rows = "\n\n".join(f"/-- Record of forward slab {s.index}. -/\ndef row{k} : Step :=\n  "
                       + step_literal(r) for k, (s, r) in enumerate(zip(slabs, records)))
    return LICENSE + f"""public import PlasmaLean.Certificates.PositionFrameWide

/-! # Position-frame records of forward slabs {slabs[0].index}–{slabs[-1].index}, label 0.474

Generated by `scripts/qa2r_wide/wide_tube_pilot.py`. {note} -/

@[expose] public section
namespace PlasmaLean.Design.{group}

open PlasmaLean.Certificates.PositionFrameSlabs

{OPTIONS}
/-- Entrance state of the group: reference point, frame and frame radius. -/
def start : State := ⟨⟨{lean_int(point[0])}, {lean_int(point[1])}⟩, {frame_literal(frame)}, {radius}⟩

{rows}

end PlasmaLean.Design.{group}
"""


def chain_module(group, slabs):
    first, count = slabs[0].index, len(slabs)
    name = group + "Chain"
    stems = [s.stem for s in slabs]
    imports = "".join(f"public import {PACKAGE}.{s}\n" for s in stems)
    rows = ", ".join(f"{group}.row{k}" for k in range(count))
    steps = "⟨" + ", ".join(f"{s}.checked" for s in stems) + ", rfl⟩"
    bounds = []
    for k, s in enumerate(stems):
        clock = f"({first} / 64 : ℝ)" + " + 1 / 64" * k
        bounds.append(f"  · rw [show {clock} = {first + k} / 64 by norm_num]\n    exact {s}.field_bounds"
                      if k else f"  · exact {s}.field_bounds")
    return name, LICENSE + imports + f"""
/-! # Wide-tube chain over forward slabs {first}–{first + count - 1}, label 0.474

Generated by `scripts/qa2r_wide/wide_tube_pilot.py`. -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}

open Certificates PositionFrameSlabs PositionFrameWideChain DommaschkJacobian Set

{OPTIONS}
/-- The records of the group in order of increasing angle. -/
def rows : List Step := [{rows}]

/-- State left by the last record. -/
abbrev exitState : State := next {group}.row{count - 1}

/-- Every record is a valid wide step from the state left by its predecessor. -/
theorem steps : Steps {group}.start rows exitState := {steps}

/-- The field hypotheses of all records of the group. -/
theorem field_bounds : FieldBoundsOn (euclideanFlow 0 1) (velocityJacobian 0 1) {group}.start
    ({first} / 64) rows ballDomain := by
  refine ⟨{', '.join(['?_'] * count)}, trivial⟩
{chr(10).join(bounds)}

/-- Every point of the entrance ellipsoid launches one field line through the {count} slabs,
ending in the exit ellipsoid and lying in every recorded tube. -/
theorem trajectory {{x : Plane}} (entry : x ∈ stateSet {group}.start) :
    ∃ v : ℝ → Plane, v ({first} / 64) = x ∧ v ({first} / 64 + {count} / 64) ∈ stateSet exitState ∧
      (∀ t ∈ Icc ({first} / 64 : ℝ) ({first} / 64 + {count} / 64),
        HasDerivWithinAt v (euclideanFlow 0 1 t (v t))
          (Icc ({first} / 64 : ℝ) ({first} / 64 + {count} / 64)) t) ∧
      ∀ slab ∈ physicalSlabs {group}.start ({first} / 64) rows,
        ∀ t ∈ Icc slab.start slab.stop, v t ∈ slab.tube t := by
  have h := steps.trajectory_of_length (n := {count}) rfl field_bounds entry
  exact_mod_cast h

end PlasmaLean.Design.{name}
"""


# ------------------------------------------------------------------ compilation
def compile_all(root, files, claims, jobs, limit_seconds=1800):
    tree = root / PACKAGE
    tree.mkdir(parents=True, exist_ok=True)
    lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT, check=True,
                               capture_output=True, text=True).stdout.strip()
    env = {**os.environ, "LEAN_NUM_THREADS": "1", "LEAN_PATH": os.pathsep.join([str(root), lean_path])}
    deps = {name: set(re.findall(rf"^public import {PACKAGE}\.(\w+)$", text, re.MULTILINE))
            for name, text in files.items()}
    receipts = {}

    def build(name):
        src, obj = tree / (name + ".lean"), tree / (name + ".olean")
        stamp = tree / (name + ".receipt.json")
        text = files[name]
        if stamp.exists() and src.exists() and src.read_text() == text and obj.exists():
            old = json.loads(stamp.read_text())
            if all(old["deps"].get(d) == receipts[d]["finished"] for d in deps[name]):
                return old
        src.write_text(text)
        stats, log = tree / (name + ".time"), tree / (name + ".log")
        begin = time.monotonic()
        with log.open("w") as out:
            p = subprocess.run(["/usr/bin/time", "-f", "%M", "-o", str(stats), "lean", "-j1",
                                "-DwarningAsError=true", "-R", str(root), "-o", str(obj), str(src)],
                               cwd=ROOT, env=env, stdout=out, stderr=subprocess.STDOUT,
                               timeout=limit_seconds)
        seconds = time.monotonic() - begin
        if p.returncode:
            raise RuntimeError(f"{name} failed\n" + log.read_text()[-4000:])
        record = dict(module=name, wall_seconds=round(seconds, 2),
                      peak_rss_kib=int(stats.read_text().split()[-1]), finished=time.time(),
                      deps={d: receipts[d]["finished"] for d in deps[name]})
        stamp.write_text(json.dumps(record))
        return record

    pending, running = dict(deps), {}
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while pending or running:
            for name in [n for n, d in pending.items() if d <= set(receipts)]:
                del pending[name]
                running[name] = pool.submit(build, name)
            done = [n for n, f in running.items() if f.done()]
            if not done:
                time.sleep(0.2)
                continue
            for name in done:
                receipts[name] = running.pop(name).result()
                print(f"  {name}: {receipts[name]['wall_seconds']} s, "
                      f"{receipts[name]['peak_rss_kib'] // 1024} MiB", flush=True)
    audit = root / "Audit.lean"
    tops = sorted({c.rsplit(".", 1)[0] for c in claims})
    audit.write_text("".join(f"import {PACKAGE}.{t}\n" for t in tops)
                     + "".join(f"#print axioms PlasmaLean.Design.{c}\n" for c in claims))
    out = subprocess.run(["lean", "-j1", "-R", str(root), str(audit)], cwd=ROOT, env=env,
                         capture_output=True, text=True)
    (root / "audit.log").write_text(out.stdout + out.stderr)
    axioms = {}
    for c in claims:
        match = re.search(re.escape(f"'PlasmaLean.Design.{c}'") + r" depends on axioms:\s*\[([^]]*)\]",
                          out.stdout)
        axioms[c] = sorted(map(str.strip, match[1].split(","))) if match else None
    return receipts, axioms


def parse_groups(specs):
    out = []
    for spec in specs:
        lo, hi = map(int, spec.split("-"))
        out.append(list(range(lo, hi + 1)))
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--trace", type=Path, default=wide_trace.DEFAULT)
    parser.add_argument("--groups", nargs="+", default=["0-3", "268-271"])
    parser.add_argument("--trial", type=F, default=F(3, 10**4), help="frame trial radius")
    parser.add_argument("--start-radius", type=F, default=F(245, 10**6),
                        help="frame radius of the entrance ellipsoid at slab 0")
    parser.add_argument("--later-radius", type=F, nargs="*", default=[],
                        help="assumed entrance radii of the groups that do not start at slab 0")
    parser.add_argument("--root", type=Path, default=ROOT / ".lake" / "qa2r-wide" / "pilot")
    parser.add_argument("--output", type=Path, default=HERE / "results" / "wide_tube_pilot.json")
    parser.add_argument("--compile", action="store_true")
    parser.add_argument("--jobs", type=int, default=8)
    args = parser.parse_args()
    if not 1 <= args.jobs <= 8:
        parser.error("at most 8 Lean processes")
    trace = wide_trace.load(args.trace)["slabs"]
    trial = round(args.trial * SCALE)
    terms = jet_terms()
    files, claims, report = {}, [], dict(trial=trial, groups=[])
    later = list(args.later_radius)
    for indices in parse_groups(args.groups):
        first = indices[0]
        group = f"DommaschkWideTubeRows{first:03}"
        slabs = []
        for i in indices:
            clock = time.time()
            slab = Slab(trace[i], trial, terms)
            slab.validate()
            slab.python_seconds = time.time() - clock
            slabs.append(slab)
        if first == 0:
            radius = round(args.start_radius * SCALE)
            point = [x.endpoint(-1) for x in slabs[0].nominal]
            note = "The group starts at the launch point of the trace."
        else:
            radius = round(later.pop(0) * SCALE)
            point = [Model(list(c)).endpoint(1) for c in trace[first - 1]["coefficients"]]
            note = ("The entrance radius of this group is an assumption of the pilot: the "
                    "preceding slabs have no compiled certificate.")
        start = (point, slabs[0].start, radius)
        records, state = [], (point, radius)
        for slab in slabs:
            record, state = slab.step(*state)
            records.append(record)
        files[group] = rows_module(group, slabs, records, start, note)
        for k, (slab, record) in enumerate(zip(slabs, records)):
            files.update(tube_modules(slab))
            files.update(central_modules(slab))
            files[slab.stem] = slab_module(slab, group, k, record)
            claims += [f"{slab.stem}.{t}" for t in
                       ("checked", "abs_quadratic", "neg_le_quadratic", "field_bounds",
                        "physical_step")]
        name, text = chain_module(group, slabs)
        files[name] = text
        claims += [f"{name}.{t}" for t in ("steps", "field_bounds", "trajectory")]
        report["groups"].append(dict(
            first=first, count=len(slabs), entrance_radius=radius, entrance_note=note,
            exit_radius=state[1],
            slabs=[dict(index=s.index, radial=s.radial, vertical=s.vertical,
                        numbers={k: str(v) for k, v in s.numbers.items()},
                        mu=float(s.numbers["mu"]), mu_central=float(s.numbers["mu0"]),
                        lipschitz=float(s.numbers["lip"]), defect=str(s.budget),
                        multiply_adds=s.tube_ops.count, python_seconds=round(s.python_seconds, 2),
                        step={k: (str(v) if isinstance(v, F) else v) for k, v in r.items()})
                   for s, r in zip(slabs, records)]))
    args.root.mkdir(parents=True, exist_ok=True)
    tree = args.root / PACKAGE
    tree.mkdir(exist_ok=True)
    if args.compile:
        receipts, axioms = compile_all(args.root, files, claims, args.jobs)
        report["modules"] = list(receipts.values())
        report["axioms"] = axioms
    else:
        for name, text in files.items():
            (tree / (name + ".lean")).write_text(text)
    report["module_count"] = len(files)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=1))
    for g in report["groups"]:
        for s in g["slabs"]:
            print(s["index"], "mu", s["mu"], "central", s["mu_central"], "K", s["lipschitz"],
                  "box", s["radial"] / SCALE, s["vertical"] / SCALE)


if __name__ == "__main__":
    main()
