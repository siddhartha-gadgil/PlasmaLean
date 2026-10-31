/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.CylAlgebra
public import PlasmaLean.Certificates.KernelFact

/-!
# Data of the Dommaschk QA candidate (NFP 3, nmax 2, lmax 4): generated file

**Generated** by `scripts/dommaschk_qa/emit_lean.py` from
`scripts/dommaschk_qa/results/20261031T044845Z/candidate.json` (do not edit by hand).

The 24 Dommaschk basis potentials `V_k = trig(m φ) Σ c R^p (ln R)^q z^j` (`basis.py`), rewritten in
Cartesian coordinates as integer cylindrical potentials `P k : CylPoly` with
`V_k = scale k · eval (P k)` (`scale k = 1 / D_k`, `D_k` the lcm of the rational monomial
coefficients), and the exact fitted coefficient vector `candidate`. The generator checks
in sympy, before writing, that `P k / D_k` equals the cylindrical potential and that its
Laplacian vanishes, and that a Python mirror of `nf (lap (P k))` is empty. In Lean,
`nf_lap_P{k}` re-checks the harmonicity of each `P k` by kernel evaluation of the normal form
(`kernel_fact`: the proof is `Eq.refl`, checked only by the kernel), and `parity_P{k}` checks that
each `P k` is odd under the stellarator symmetry `(x, y, z) ↦ (x, −y, −z)`.
-/

public section
namespace PlasmaLean.Design.DommaschkQA3
open PlasmaLean.Fields.CylAlgebra

/-- Basis potential 0: `cos(0phi)*D_0,1` times `1` (1 monomials). -/
@[expose] def P0 : CylPoly :=
  [⟨1, 0, 0, 1, 0, 0⟩]

/-- Basis potential 1: `cos(0phi)*N_0,1` times `2` (1 monomials). -/
@[expose] def P1 : CylPoly :=
  [⟨1, 0, 0, 1, 0, 1⟩]

/-- Basis potential 2: `cos(0phi)*D_0,3` times `12` (4 monomials). -/
@[expose] def P2 : CylPoly :=
  [⟨3, 0, 0, 1, 0, 0⟩, ⟨3, 0, 0, 1, 0, 1⟩, ⟨(-3), 0, 0, 1, 1, 0⟩, ⟨2, 0, 0, 3, 0, 0⟩]

/-- Basis potential 3: `cos(0phi)*N_0,3` times `24` (5 monomials). -/
@[expose] def P3 : CylPoly :=
  [⟨(-6), 0, 0, 1, 0, 0⟩, ⟨(-3), 0, 0, 1, 0, 1⟩, ⟨6, 0, 0, 1, 1, 0⟩, ⟨(-3), 0, 0, 1, 1, 1⟩,
    ⟨2, 0, 0, 3, 0, 1⟩]

/-- Basis potential 4: `sin(3phi)*D_3,0` times `2` (4 monomials). -/
@[expose] def P4 : CylPoly :=
  [⟨(-1), 0, 3, 0, (-3), 0⟩, ⟨(-1), 0, 3, 0, 0, 0⟩, ⟨3, 2, 1, 0, (-3), 0⟩, ⟨3, 2, 1, 0, 0, 0⟩]

/-- Basis potential 5: `sin(3phi)*N_3,0` times `6` (4 monomials). -/
@[expose] def P5 : CylPoly :=
  [⟨1, 0, 3, 0, (-3), 0⟩, ⟨(-1), 0, 3, 0, 0, 0⟩, ⟨(-3), 2, 1, 0, (-3), 0⟩, ⟨3, 2, 1, 0, 0, 0⟩]

/-- Basis potential 6: `cos(3phi)*D_3,1` times `2` (4 monomials). -/
@[expose] def P6 : CylPoly :=
  [⟨(-3), 1, 2, 1, (-3), 0⟩, ⟨(-3), 1, 2, 1, 0, 0⟩, ⟨1, 3, 0, 1, (-3), 0⟩, ⟨1, 3, 0, 1, 0, 0⟩]

/-- Basis potential 7: `cos(3phi)*N_3,1` times `6` (4 monomials). -/
@[expose] def P7 : CylPoly :=
  [⟨3, 1, 2, 1, (-3), 0⟩, ⟨(-3), 1, 2, 1, 0, 0⟩, ⟨(-1), 3, 0, 1, (-3), 0⟩, ⟨1, 3, 0, 1, 0, 0⟩]

/-- Basis potential 8: `sin(3phi)*D_3,2` times `96` (12 monomials). -/
@[expose] def P8 : CylPoly :=
  [⟨5, 0, 3, 0, (-3), 0⟩, ⟨(-6), 0, 3, 0, (-2), 0⟩, ⟨(-2), 0, 3, 0, 0, 0⟩, ⟨3, 0, 3, 0, 1, 0⟩,
    ⟨(-24), 0, 3, 2, (-3), 0⟩, ⟨(-24), 0, 3, 2, 0, 0⟩, ⟨(-15), 2, 1, 0, (-3), 0⟩,
    ⟨18, 2, 1, 0, (-2), 0⟩, ⟨6, 2, 1, 0, 0, 0⟩, ⟨(-9), 2, 1, 0, 1, 0⟩, ⟨72, 2, 1, 2, (-3), 0⟩,
    ⟨72, 2, 1, 2, 0, 0⟩]

/-- Basis potential 9: `sin(3phi)*N_3,2` times `96` (12 monomials). -/
@[expose] def P9 : CylPoly :=
  [⟨(-1), 0, 3, 0, (-3), 0⟩, ⟨2, 0, 3, 0, (-2), 0⟩, ⟨(-2), 0, 3, 0, 0, 0⟩, ⟨1, 0, 3, 0, 1, 0⟩,
    ⟨8, 0, 3, 2, (-3), 0⟩, ⟨(-8), 0, 3, 2, 0, 0⟩, ⟨3, 2, 1, 0, (-3), 0⟩,
    ⟨(-6), 2, 1, 0, (-2), 0⟩, ⟨6, 2, 1, 0, 0, 0⟩, ⟨(-3), 2, 1, 0, 1, 0⟩,
    ⟨(-24), 2, 1, 2, (-3), 0⟩, ⟨24, 2, 1, 2, 0, 0⟩]

/-- Basis potential 10: `cos(3phi)*D_3,3` times `96` (12 monomials). -/
@[expose] def P10 : CylPoly :=
  [⟨15, 1, 2, 1, (-3), 0⟩, ⟨(-18), 1, 2, 1, (-2), 0⟩, ⟨(-6), 1, 2, 1, 0, 0⟩, ⟨9, 1, 2, 1, 1, 0⟩,
    ⟨(-24), 1, 2, 3, (-3), 0⟩, ⟨(-24), 1, 2, 3, 0, 0⟩, ⟨(-5), 3, 0, 1, (-3), 0⟩,
    ⟨6, 3, 0, 1, (-2), 0⟩, ⟨2, 3, 0, 1, 0, 0⟩, ⟨(-3), 3, 0, 1, 1, 0⟩, ⟨8, 3, 0, 3, (-3), 0⟩,
    ⟨8, 3, 0, 3, 0, 0⟩]

/-- Basis potential 11: `cos(3phi)*N_3,3` times `288` (12 monomials). -/
@[expose] def P11 : CylPoly :=
  [⟨(-9), 1, 2, 1, (-3), 0⟩, ⟨18, 1, 2, 1, (-2), 0⟩, ⟨(-18), 1, 2, 1, 0, 0⟩, ⟨9, 1, 2, 1, 1, 0⟩,
    ⟨24, 1, 2, 3, (-3), 0⟩, ⟨(-24), 1, 2, 3, 0, 0⟩, ⟨3, 3, 0, 1, (-3), 0⟩,
    ⟨(-6), 3, 0, 1, (-2), 0⟩, ⟨6, 3, 0, 1, 0, 0⟩, ⟨(-3), 3, 0, 1, 1, 0⟩,
    ⟨(-8), 3, 0, 3, (-3), 0⟩, ⟨8, 3, 0, 3, 0, 0⟩]

/-- Basis potential 12: `sin(3phi)*D_3,4` times `3840` (24 monomials). -/
@[expose] def P12 : CylPoly :=
  [⟨(-7), 0, 3, 0, (-3), 0⟩, ⟨25, 0, 3, 0, (-2), 0⟩, ⟨(-30), 0, 3, 0, (-1), 0⟩,
    ⟨10, 0, 3, 0, 0, 0⟩, ⟨5, 0, 3, 0, 1, 0⟩, ⟨(-3), 0, 3, 0, 2, 0⟩, ⟨100, 0, 3, 2, (-3), 0⟩,
    ⟨(-120), 0, 3, 2, (-2), 0⟩, ⟨(-40), 0, 3, 2, 0, 0⟩, ⟨60, 0, 3, 2, 1, 0⟩,
    ⟨(-80), 0, 3, 4, (-3), 0⟩, ⟨(-80), 0, 3, 4, 0, 0⟩, ⟨21, 2, 1, 0, (-3), 0⟩,
    ⟨(-75), 2, 1, 0, (-2), 0⟩, ⟨90, 2, 1, 0, (-1), 0⟩, ⟨(-30), 2, 1, 0, 0, 0⟩,
    ⟨(-15), 2, 1, 0, 1, 0⟩, ⟨9, 2, 1, 0, 2, 0⟩, ⟨(-300), 2, 1, 2, (-3), 0⟩,
    ⟨360, 2, 1, 2, (-2), 0⟩, ⟨120, 2, 1, 2, 0, 0⟩, ⟨(-180), 2, 1, 2, 1, 0⟩,
    ⟨240, 2, 1, 4, (-3), 0⟩, ⟨240, 2, 1, 4, 0, 0⟩]

/-- Basis potential 13: `sin(3phi)*N_3,4` times `11520` (24 monomials). -/
@[expose] def P13 : CylPoly :=
  [⟨3, 0, 3, 0, (-3), 0⟩, ⟨(-15), 0, 3, 0, (-2), 0⟩, ⟨30, 0, 3, 0, (-1), 0⟩,
    ⟨(-30), 0, 3, 0, 0, 0⟩, ⟨15, 0, 3, 0, 1, 0⟩, ⟨(-3), 0, 3, 0, 2, 0⟩,
    ⟨(-60), 0, 3, 2, (-3), 0⟩, ⟨120, 0, 3, 2, (-2), 0⟩, ⟨(-120), 0, 3, 2, 0, 0⟩,
    ⟨60, 0, 3, 2, 1, 0⟩, ⟨80, 0, 3, 4, (-3), 0⟩, ⟨(-80), 0, 3, 4, 0, 0⟩,
    ⟨(-9), 2, 1, 0, (-3), 0⟩, ⟨45, 2, 1, 0, (-2), 0⟩, ⟨(-90), 2, 1, 0, (-1), 0⟩,
    ⟨90, 2, 1, 0, 0, 0⟩, ⟨(-45), 2, 1, 0, 1, 0⟩, ⟨9, 2, 1, 0, 2, 0⟩, ⟨180, 2, 1, 2, (-3), 0⟩,
    ⟨(-360), 2, 1, 2, (-2), 0⟩, ⟨360, 2, 1, 2, 0, 0⟩, ⟨(-180), 2, 1, 2, 1, 0⟩,
    ⟨(-240), 2, 1, 4, (-3), 0⟩, ⟨240, 2, 1, 4, 0, 0⟩]

/-- Basis potential 14: `sin(6phi)*D_6,0` times `1` (6 monomials). -/
@[expose] def P14 : CylPoly :=
  [⟨3, 1, 5, 0, (-6), 0⟩, ⟨3, 1, 5, 0, 0, 0⟩, ⟨(-10), 3, 3, 0, (-6), 0⟩, ⟨(-10), 3, 3, 0, 0, 0⟩,
    ⟨3, 5, 1, 0, (-6), 0⟩, ⟨3, 5, 1, 0, 0, 0⟩]

/-- Basis potential 15: `sin(6phi)*N_6,0` times `6` (6 monomials). -/
@[expose] def P15 : CylPoly :=
  [⟨(-3), 1, 5, 0, (-6), 0⟩, ⟨3, 1, 5, 0, 0, 0⟩, ⟨10, 3, 3, 0, (-6), 0⟩, ⟨(-10), 3, 3, 0, 0, 0⟩,
    ⟨(-3), 5, 1, 0, (-6), 0⟩, ⟨3, 5, 1, 0, 0, 0⟩]

/-- Basis potential 16: `cos(6phi)*D_6,1` times `2` (8 monomials). -/
@[expose] def P16 : CylPoly :=
  [⟨(-1), 0, 6, 1, (-6), 0⟩, ⟨(-1), 0, 6, 1, 0, 0⟩, ⟨15, 2, 4, 1, (-6), 0⟩, ⟨15, 2, 4, 1, 0, 0⟩,
    ⟨(-15), 4, 2, 1, (-6), 0⟩, ⟨(-15), 4, 2, 1, 0, 0⟩, ⟨1, 6, 0, 1, (-6), 0⟩, ⟨1, 6, 0, 1, 0, 0⟩]

/-- Basis potential 17: `cos(6phi)*N_6,1` times `12` (8 monomials). -/
@[expose] def P17 : CylPoly :=
  [⟨1, 0, 6, 1, (-6), 0⟩, ⟨(-1), 0, 6, 1, 0, 0⟩, ⟨(-15), 2, 4, 1, (-6), 0⟩, ⟨15, 2, 4, 1, 0, 0⟩,
    ⟨15, 4, 2, 1, (-6), 0⟩, ⟨(-15), 4, 2, 1, 0, 0⟩, ⟨(-1), 6, 0, 1, (-6), 0⟩, ⟨1, 6, 0, 1, 0, 0⟩]

/-- Basis potential 18: `sin(6phi)*D_6,2` times `420` (18 monomials). -/
@[expose] def P18 : CylPoly :=
  [⟨(-60), 1, 5, 0, (-6), 0⟩, ⟨63, 1, 5, 0, (-5), 0⟩, ⟨42, 1, 5, 0, 0, 0⟩,
    ⟨(-45), 1, 5, 0, 1, 0⟩, ⟨630, 1, 5, 2, (-6), 0⟩, ⟨630, 1, 5, 2, 0, 0⟩,
    ⟨200, 3, 3, 0, (-6), 0⟩, ⟨(-210), 3, 3, 0, (-5), 0⟩, ⟨(-140), 3, 3, 0, 0, 0⟩,
    ⟨150, 3, 3, 0, 1, 0⟩, ⟨(-2100), 3, 3, 2, (-6), 0⟩, ⟨(-2100), 3, 3, 2, 0, 0⟩,
    ⟨(-60), 5, 1, 0, (-6), 0⟩, ⟨63, 5, 1, 0, (-5), 0⟩, ⟨42, 5, 1, 0, 0, 0⟩,
    ⟨(-45), 5, 1, 0, 1, 0⟩, ⟨630, 5, 1, 2, (-6), 0⟩, ⟨630, 5, 1, 2, 0, 0⟩]

/-- Basis potential 19: `sin(6phi)*N_6,2` times `840` (18 monomials). -/
@[expose] def P19 : CylPoly :=
  [⟨15, 1, 5, 0, (-6), 0⟩, ⟨(-21), 1, 5, 0, (-5), 0⟩, ⟨21, 1, 5, 0, 0, 0⟩,
    ⟨(-15), 1, 5, 0, 1, 0⟩, ⟨(-210), 1, 5, 2, (-6), 0⟩, ⟨210, 1, 5, 2, 0, 0⟩,
    ⟨(-50), 3, 3, 0, (-6), 0⟩, ⟨70, 3, 3, 0, (-5), 0⟩, ⟨(-70), 3, 3, 0, 0, 0⟩,
    ⟨50, 3, 3, 0, 1, 0⟩, ⟨700, 3, 3, 2, (-6), 0⟩, ⟨(-700), 3, 3, 2, 0, 0⟩,
    ⟨15, 5, 1, 0, (-6), 0⟩, ⟨(-21), 5, 1, 0, (-5), 0⟩, ⟨21, 5, 1, 0, 0, 0⟩,
    ⟨(-15), 5, 1, 0, 1, 0⟩, ⟨(-210), 5, 1, 2, (-6), 0⟩, ⟨210, 5, 1, 2, 0, 0⟩]

/-- Basis potential 20: `cos(6phi)*D_6,3` times `840` (24 monomials). -/
@[expose] def P20 : CylPoly :=
  [⟨20, 0, 6, 1, (-6), 0⟩, ⟨(-21), 0, 6, 1, (-5), 0⟩, ⟨(-14), 0, 6, 1, 0, 0⟩,
    ⟨15, 0, 6, 1, 1, 0⟩, ⟨(-70), 0, 6, 3, (-6), 0⟩, ⟨(-70), 0, 6, 3, 0, 0⟩,
    ⟨(-300), 2, 4, 1, (-6), 0⟩, ⟨315, 2, 4, 1, (-5), 0⟩, ⟨210, 2, 4, 1, 0, 0⟩,
    ⟨(-225), 2, 4, 1, 1, 0⟩, ⟨1050, 2, 4, 3, (-6), 0⟩, ⟨1050, 2, 4, 3, 0, 0⟩,
    ⟨300, 4, 2, 1, (-6), 0⟩, ⟨(-315), 4, 2, 1, (-5), 0⟩, ⟨(-210), 4, 2, 1, 0, 0⟩,
    ⟨225, 4, 2, 1, 1, 0⟩, ⟨(-1050), 4, 2, 3, (-6), 0⟩, ⟨(-1050), 4, 2, 3, 0, 0⟩,
    ⟨(-20), 6, 0, 1, (-6), 0⟩, ⟨21, 6, 0, 1, (-5), 0⟩, ⟨14, 6, 0, 1, 0, 0⟩,
    ⟨(-15), 6, 0, 1, 1, 0⟩, ⟨70, 6, 0, 3, (-6), 0⟩, ⟨70, 6, 0, 3, 0, 0⟩]

/-- Basis potential 21: `cos(6phi)*N_6,3` times `5040` (24 monomials). -/
@[expose] def P21 : CylPoly :=
  [⟨(-15), 0, 6, 1, (-6), 0⟩, ⟨21, 0, 6, 1, (-5), 0⟩, ⟨(-21), 0, 6, 1, 0, 0⟩,
    ⟨15, 0, 6, 1, 1, 0⟩, ⟨70, 0, 6, 3, (-6), 0⟩, ⟨(-70), 0, 6, 3, 0, 0⟩, ⟨225, 2, 4, 1, (-6), 0⟩,
    ⟨(-315), 2, 4, 1, (-5), 0⟩, ⟨315, 2, 4, 1, 0, 0⟩, ⟨(-225), 2, 4, 1, 1, 0⟩,
    ⟨(-1050), 2, 4, 3, (-6), 0⟩, ⟨1050, 2, 4, 3, 0, 0⟩, ⟨(-225), 4, 2, 1, (-6), 0⟩,
    ⟨315, 4, 2, 1, (-5), 0⟩, ⟨(-315), 4, 2, 1, 0, 0⟩, ⟨225, 4, 2, 1, 1, 0⟩,
    ⟨1050, 4, 2, 3, (-6), 0⟩, ⟨(-1050), 4, 2, 3, 0, 0⟩, ⟨15, 6, 0, 1, (-6), 0⟩,
    ⟨(-21), 6, 0, 1, (-5), 0⟩, ⟨21, 6, 0, 1, 0, 0⟩, ⟨(-15), 6, 0, 1, 1, 0⟩,
    ⟨(-70), 6, 0, 3, (-6), 0⟩, ⟨70, 6, 0, 3, 0, 0⟩]

/-- Basis potential 22: `sin(6phi)*D_6,4` times `26880` (36 monomials). -/
@[expose] def P22 : CylPoly :=
  [⟨75, 1, 5, 0, (-6), 0⟩, ⟨(-192), 1, 5, 0, (-5), 0⟩, ⟨126, 1, 5, 0, (-4), 0⟩,
    ⟨42, 1, 5, 0, 0, 0⟩, ⟨(-96), 1, 5, 0, 1, 0⟩, ⟨45, 1, 5, 0, 2, 0⟩,
    ⟨(-1920), 1, 5, 2, (-6), 0⟩, ⟨2016, 1, 5, 2, (-5), 0⟩, ⟨1344, 1, 5, 2, 0, 0⟩,
    ⟨(-1440), 1, 5, 2, 1, 0⟩, ⟨3360, 1, 5, 4, (-6), 0⟩, ⟨3360, 1, 5, 4, 0, 0⟩,
    ⟨(-250), 3, 3, 0, (-6), 0⟩, ⟨640, 3, 3, 0, (-5), 0⟩, ⟨(-420), 3, 3, 0, (-4), 0⟩,
    ⟨(-140), 3, 3, 0, 0, 0⟩, ⟨320, 3, 3, 0, 1, 0⟩, ⟨(-150), 3, 3, 0, 2, 0⟩,
    ⟨6400, 3, 3, 2, (-6), 0⟩, ⟨(-6720), 3, 3, 2, (-5), 0⟩, ⟨(-4480), 3, 3, 2, 0, 0⟩,
    ⟨4800, 3, 3, 2, 1, 0⟩, ⟨(-11200), 3, 3, 4, (-6), 0⟩, ⟨(-11200), 3, 3, 4, 0, 0⟩,
    ⟨75, 5, 1, 0, (-6), 0⟩, ⟨(-192), 5, 1, 0, (-5), 0⟩, ⟨126, 5, 1, 0, (-4), 0⟩,
    ⟨42, 5, 1, 0, 0, 0⟩, ⟨(-96), 5, 1, 0, 1, 0⟩, ⟨45, 5, 1, 0, 2, 0⟩,
    ⟨(-1920), 5, 1, 2, (-6), 0⟩, ⟨2016, 5, 1, 2, (-5), 0⟩, ⟨1344, 5, 1, 2, 0, 0⟩,
    ⟨(-1440), 5, 1, 2, 1, 0⟩, ⟨3360, 5, 1, 4, (-6), 0⟩, ⟨3360, 5, 1, 4, 0, 0⟩]

/-- Basis potential 23: `sin(6phi)*N_6,4` times `161280` (36 monomials). -/
@[expose] def P23 : CylPoly :=
  [⟨(-45), 1, 5, 0, (-6), 0⟩, ⟨144, 1, 5, 0, (-5), 0⟩, ⟨(-126), 1, 5, 0, (-4), 0⟩,
    ⟨126, 1, 5, 0, 0, 0⟩, ⟨(-144), 1, 5, 0, 1, 0⟩, ⟨45, 1, 5, 0, 2, 0⟩, ⟨1440, 1, 5, 2, (-6), 0⟩,
    ⟨(-2016), 1, 5, 2, (-5), 0⟩, ⟨2016, 1, 5, 2, 0, 0⟩, ⟨(-1440), 1, 5, 2, 1, 0⟩,
    ⟨(-3360), 1, 5, 4, (-6), 0⟩, ⟨3360, 1, 5, 4, 0, 0⟩, ⟨150, 3, 3, 0, (-6), 0⟩,
    ⟨(-480), 3, 3, 0, (-5), 0⟩, ⟨420, 3, 3, 0, (-4), 0⟩, ⟨(-420), 3, 3, 0, 0, 0⟩,
    ⟨480, 3, 3, 0, 1, 0⟩, ⟨(-150), 3, 3, 0, 2, 0⟩, ⟨(-4800), 3, 3, 2, (-6), 0⟩,
    ⟨6720, 3, 3, 2, (-5), 0⟩, ⟨(-6720), 3, 3, 2, 0, 0⟩, ⟨4800, 3, 3, 2, 1, 0⟩,
    ⟨11200, 3, 3, 4, (-6), 0⟩, ⟨(-11200), 3, 3, 4, 0, 0⟩, ⟨(-45), 5, 1, 0, (-6), 0⟩,
    ⟨144, 5, 1, 0, (-5), 0⟩, ⟨(-126), 5, 1, 0, (-4), 0⟩, ⟨126, 5, 1, 0, 0, 0⟩,
    ⟨(-144), 5, 1, 0, 1, 0⟩, ⟨45, 5, 1, 0, 2, 0⟩, ⟨1440, 5, 1, 2, (-6), 0⟩,
    ⟨(-2016), 5, 1, 2, (-5), 0⟩, ⟨2016, 5, 1, 2, 0, 0⟩, ⟨(-1440), 5, 1, 2, 1, 0⟩,
    ⟨(-3360), 5, 1, 4, (-6), 0⟩, ⟨3360, 5, 1, 4, 0, 0⟩]

/-- The 24 basis potentials (integer forms `D_k V_k`). -/
@[expose] def P : Fin 24 → CylPoly :=
  ![P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11,
    P12, P13, P14, P15, P16, P17, P18, P19, P20, P21, P22, P23]

/-- Harmonicity check for `P0` (`cos(0phi)*D_0,1`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P0 : nf (lap P0) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P0`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P0 : parityCheck 1 P0 = true := by kernel_fact

/-- Harmonicity check for `P1` (`cos(0phi)*N_0,1`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P1 : nf (lap P1) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P1`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P1 : parityCheck 1 P1 = true := by kernel_fact

/-- Harmonicity check for `P2` (`cos(0phi)*D_0,3`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P2 : nf (lap P2) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P2`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P2 : parityCheck 1 P2 = true := by kernel_fact

/-- Harmonicity check for `P3` (`cos(0phi)*N_0,3`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P3 : nf (lap P3) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P3`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P3 : parityCheck 1 P3 = true := by kernel_fact

/-- Harmonicity check for `P4` (`sin(3phi)*D_3,0`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P4 : nf (lap P4) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P4`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P4 : parityCheck 1 P4 = true := by kernel_fact

/-- Harmonicity check for `P5` (`sin(3phi)*N_3,0`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P5 : nf (lap P5) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P5`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P5 : parityCheck 1 P5 = true := by kernel_fact

/-- Harmonicity check for `P6` (`cos(3phi)*D_3,1`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P6 : nf (lap P6) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P6`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P6 : parityCheck 1 P6 = true := by kernel_fact

/-- Harmonicity check for `P7` (`cos(3phi)*N_3,1`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P7 : nf (lap P7) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P7`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P7 : parityCheck 1 P7 = true := by kernel_fact

/-- Harmonicity check for `P8` (`sin(3phi)*D_3,2`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P8 : nf (lap P8) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P8`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P8 : parityCheck 1 P8 = true := by kernel_fact

/-- Harmonicity check for `P9` (`sin(3phi)*N_3,2`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P9 : nf (lap P9) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P9`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P9 : parityCheck 1 P9 = true := by kernel_fact

/-- Harmonicity check for `P10` (`cos(3phi)*D_3,3`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P10 : nf (lap P10) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P10`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P10 : parityCheck 1 P10 = true := by kernel_fact

/-- Harmonicity check for `P11` (`cos(3phi)*N_3,3`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P11 : nf (lap P11) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P11`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P11 : parityCheck 1 P11 = true := by kernel_fact

/-- Harmonicity check for `P12` (`sin(3phi)*D_3,4`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P12 : nf (lap P12) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P12`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P12 : parityCheck 1 P12 = true := by kernel_fact

/-- Harmonicity check for `P13` (`sin(3phi)*N_3,4`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P13 : nf (lap P13) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P13`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P13 : parityCheck 1 P13 = true := by kernel_fact

/-- Harmonicity check for `P14` (`sin(6phi)*D_6,0`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P14 : nf (lap P14) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P14`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P14 : parityCheck 1 P14 = true := by kernel_fact

/-- Harmonicity check for `P15` (`sin(6phi)*N_6,0`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P15 : nf (lap P15) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P15`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P15 : parityCheck 1 P15 = true := by kernel_fact

/-- Harmonicity check for `P16` (`cos(6phi)*D_6,1`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P16 : nf (lap P16) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P16`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P16 : parityCheck 1 P16 = true := by kernel_fact

/-- Harmonicity check for `P17` (`cos(6phi)*N_6,1`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P17 : nf (lap P17) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P17`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P17 : parityCheck 1 P17 = true := by kernel_fact

/-- Harmonicity check for `P18` (`sin(6phi)*D_6,2`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P18 : nf (lap P18) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P18`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P18 : parityCheck 1 P18 = true := by kernel_fact

/-- Harmonicity check for `P19` (`sin(6phi)*N_6,2`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P19 : nf (lap P19) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P19`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P19 : parityCheck 1 P19 = true := by kernel_fact

/-- Harmonicity check for `P20` (`cos(6phi)*D_6,3`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P20 : nf (lap P20) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P20`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P20 : parityCheck 1 P20 = true := by kernel_fact

/-- Harmonicity check for `P21` (`cos(6phi)*N_6,3`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P21 : nf (lap P21) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P21`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P21 : parityCheck 1 P21 = true := by kernel_fact

/-- Harmonicity check for `P22` (`sin(6phi)*D_6,4`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P22 : nf (lap P22) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P22`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P22 : parityCheck 1 P22 = true := by kernel_fact

/-- Harmonicity check for `P23` (`sin(6phi)*N_6,4`): the formal Laplacian
normalises to zero (kernel evaluation). -/
theorem nf_lap_P23 : nf (lap P23) = [] := by kernel_fact

/-- Stellarator-symmetry check for `P23`: every monomial is odd under
`(x, y, z) ↦ (x, −y, −z)`. -/
theorem parity_P23 : parityCheck 1 P23 = true := by kernel_fact

/-- `scale k = 1 / D_k`: `V_k = scale k · eval (P k)`. -/
@[expose] def scale : Fin 24 → ℚ :=
  ![1 / 1, 1 / 2, 1 / 12, 1 / 24, 1 / 2, 1 / 6, 1 / 2, 1 / 6,
    1 / 96, 1 / 96, 1 / 96, 1 / 288, 1 / 3840, 1 / 11520, 1 / 1, 1 / 6,
    1 / 2, 1 / 12, 1 / 420, 1 / 840, 1 / 840, 1 / 5040, 1 / 26880, 1 / 161280]

/-- The exact fitted coefficients `a_k` of the candidate (`candidate.json`). -/
@[expose] def candidate : Fin 24 → ℚ :=
  ![27841411 / 5000000000,
    -322072681 / 2500000000,
    32229714833 / 10000000000,
    -1527422224167 / 10000000000,
    3383243 / 10000000000,
    5171963 / 312500000,
    -95569451 / 10000000000,
    -2400803779 / 10000000000,
    1328861329 / 10000000000,
    31261827547 / 5000000000,
    3773371719 / 2000000000,
    -26187123289 / 1000000000,
    366534297871 / 2000000000,
    4315312216509 / 2500000000,
    -43537577 / 10000000000,
    32846089 / 400000000,
    769502311 / 10000000000,
    -7333682537 / 10000000000,
    2530175663 / 5000000000,
    8049968461 / 1250000000,
    60515263269 / 10000000000,
    -36755522307 / 5000000000,
    -758615954127 / 10000000000,
    1756104898817 / 2500000000]

end PlasmaLean.Design.DommaschkQA3
