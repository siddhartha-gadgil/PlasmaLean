/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamCTorus

/-!
# Rational second-order jets of the Dommaschk residual majorants (N-33 plan item 9)

The Taylor constant `C₂` of the generalised KAM step (`FlowFieldG.GlobalHG.hC2R`, `hC2Z`,
`Design/KamFlowIterationG`) is `½ P̂''(a)[b, b]` (`PolyExpr.majD2`) of the residual polynomials
`resRp = D w_R − n_R`, `resZp = D w_z − n_z` of `dkFieldTC` (`Design/DommaschkKamCTorus`). The
three majorants `P̂(a)`, `P̂'(a)·b`, `P̂''(a)[b, b]` of a polynomial expression together form a
**second-order jet** `(f, f', f'')`: sums add componentwise and products obey the Leibniz rule
`(fg)'' = f''g + 2f'g' + fg''` (`jmul`), exactly the recursion of `PolyExpr.maj`, `majD`, `majD2`
(`rj_mul`, `rj_add`, `rj_sub`).

For the sparse polynomials of the Dommaschk field (`DkPoly.SP`, `toPE`) the jet is mirrored in
kernel-computable rational arithmetic (`jTm`, `jSP`, like the Lipschitz majorant `lipQ` of
`Design/DommaschkKamCAdmFrame`), at a point `a = (A₀, A₁, C, C, A₄, A₅)` with direction
`b = (B₀, B₁, 0, 0, B₄, B₅)` (the profile `SCG.avec + Tq • mvec`, `SCG.mvec`). The bridge
`rj_toPE` identifies the rational jet with the real majorants, and `majD2_resRp`, `majD2_resZp`
give `½ majD2` of the two residual polynomials as the casts of the rational numbers `c2RQ`,
`c2ZQ`, which `kernel_fact` then bounds (`Design/DommaschkKamCConsts`).

**Sanity.** `jSP_nil` (degenerate), `jpow_fixture` (concrete: the jet of `x²` at `x = 3` in
direction `1` is `(9, 6, 2)`), `jmul_comm`, and `jpow_fixture_ne` (rejected fixture).
-/

@[expose] public section

namespace PlasmaLean.Design.DommaschkKamC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Design.DommaschkKam PolyExpr

/-! ## Jets over a commutative ring -/

/-- A second-order jet `(f, f', f'')`. -/
abbrev Jet (K : Type) := K × K × K

section Ring

variable {K : Type} [CommRing K]

/-- The sum of jets. -/
def jadd (x y : Jet K) : Jet K := (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2)

/-- The product of jets (Leibniz rule up to second order, in the order of `PolyExpr.majD2`). -/
def jmul (x y : Jet K) : Jet K :=
  (x.1 * y.1, x.2.1 * y.1 + x.1 * y.2.1, x.2.2 * y.1 + 2 * (x.2.1 * y.2.1) + x.1 * y.2.2)

/-- Powers of a jet, `x⁰ = 1`, `x^{k+1} = x^k x` (the recursion of `PolyExpr.npow`). -/
def jpow (x : Jet K) : ℕ → Jet K
  | 0 => (1, 0, 0)
  | k + 1 => jmul (jpow x k) x

/-- **Sanity**: the product of jets is commutative. -/
theorem jmul_comm (x y : Jet K) : jmul x y = jmul y x := by
  simp only [jmul, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

end Ring

/-! ## The real majorant jet of a polynomial expression -/

section Real

variable (a b : Fin 6 → ℝ)

/-- The majorant jet `(P̂(a), P̂'(a)·b, P̂''(a)[b, b])`. -/
noncomputable def rj (e : PolyExpr ℂ (Fin 6)) : Jet ℝ := (maj a e, majD a b e, majD2 a b e)

/-- Jet of a constant. -/
theorem rj_const (c : ℂ) : rj a b (const c) = (‖c‖, 0, 0) := rfl

/-- Jet of a variable. -/
theorem rj_var (i : Fin 6) : rj a b (var i) = (a i, b i, 0) := rfl

/-- Jet of a sum. -/
theorem rj_add (p q : PolyExpr ℂ (Fin 6)) : rj a b (add p q) = jadd (rj a b p) (rj a b q) := rfl

/-- Jet of a difference (majorants add). -/
theorem rj_sub (p q : PolyExpr ℂ (Fin 6)) : rj a b (sub p q) = jadd (rj a b p) (rj a b q) := rfl

/-- Jet of a product. -/
theorem rj_mul (p q : PolyExpr ℂ (Fin 6)) : rj a b (mul p q) = jmul (rj a b p) (rj a b q) := rfl

/-- Jet of a power of a variable. -/
theorem rj_npow_var (i : Fin 6) : ∀ k : ℕ, rj a b (npow (var i) k) = jpow (a i, b i, 0) k
  | 0 => by simp [npow, rj_const, jpow]
  | k + 1 => by rw [npow, rj_mul, rj_npow_var i k, rj_var, jpow]

end Real

/-! ## The rational mirror for sparse polynomials -/

/-- The cast of a rational jet. -/
def c3 (x : Jet ℚ) : Jet ℝ := ((x.1 : ℝ), (x.2.1 : ℝ), (x.2.2 : ℝ))

/-- The cast commutes with sums. -/
theorem c3_jadd (x y : Jet ℚ) : c3 (jadd x y) = jadd (c3 x) (c3 y) := by
  simp only [c3, jadd, Rat.cast_add]

/-- The cast commutes with products. -/
theorem c3_jmul (x y : Jet ℚ) : c3 (jmul x y) = jmul (c3 x) (c3 y) := by
  simp only [c3, jmul]; push_cast; rfl

/-- The cast commutes with powers. -/
theorem c3_jpow (x : Jet ℚ) : ∀ k : ℕ, c3 (jpow x k) = jpow (c3 x) k
  | 0 => by simp [c3, jpow]
  | k + 1 => by rw [jpow, c3_jmul, c3_jpow x k, jpow]

/-- The rational jet of a term `q u^a z^b c^c s^d` at `(A₀, A₁, C, C)`, direction `(B₀, B₁, 0, 0)`
(the factor order of `monoE`). -/
def jTm (A0 A1 C B0 B1 : ℚ) (t : DkPoly.Tm) : Jet ℚ :=
  jmul (jmul (jmul (jmul (|t.q|, 0, 0) (jpow (C, 0, 0) t.d)) (jpow (C, 0, 0) t.c))
    (jpow (A1, B1, 0) t.b)) (jpow (A0, B0, 0) t.a)

/-- The rational jet of a sparse polynomial (the order of `sumE`). -/
def jSP (A0 A1 C B0 B1 : ℚ) (p : DkPoly.SP) : Jet ℚ :=
  p.foldr (fun t acc => jadd (jTm A0 A1 C B0 B1 t) acc) (0, 0, 0)

/-- **Sanity (degenerate)**: the empty polynomial has the zero jet. -/
theorem jSP_nil (A0 A1 C B0 B1 : ℚ) : jSP A0 A1 C B0 B1 [] = (0, 0, 0) := rfl

/-- **Sanity (concrete)**: the jet of `x²` at `x = 3` in direction `1` is `(9, 6, 2)`. -/
theorem jpow_fixture : jpow ((3, 1, 0) : Jet ℚ) 2 = (9, 6, 2) := by
  simp only [jpow, jmul]; norm_num

/-- **Sanity (rejected fixture)**: the second derivative of `x²` is not `1`. -/
theorem jpow_fixture_ne : (jpow ((3, 1, 0) : Jet ℚ) 2).2.2 ≠ 1 := by
  rw [jpow_fixture]; norm_num

section Bridge

variable {a b : Fin 6 → ℝ} {A0 A1 C B0 B1 : ℚ}

/-- **The rational jet of a term is its real majorant jet.** -/
theorem rj_toE (h0 : a 0 = A0) (h1 : a 1 = A1) (h2 : a 2 = C) (h3 : a 3 = C) (hb0 : b 0 = B0)
    (hb1 : b 1 = B1) (hb2 : b 2 = 0) (hb3 : b 3 = 0) (t : DkPoly.Tm) :
    rj a b t.toE = c3 (jTm A0 A1 C B0 B1 t) := by
  simp only [DkPoly.Tm.toE, monoE, rj_mul, rj_const, rj_npow_var, jTm, c3_jmul, c3_jpow]
  rw [h0, h1, h2, h3, hb0, hb1, hb2, hb3]
  simp only [c3, Rat.cast_zero, Rat.cast_abs, Complex.norm_ratCast]

/-- **The rational jet of a sparse polynomial is its real majorant jet.** -/
theorem rj_toPE (h0 : a 0 = A0) (h1 : a 1 = A1) (h2 : a 2 = C) (h3 : a 3 = C) (hb0 : b 0 = B0)
    (hb1 : b 1 = B1) (hb2 : b 2 = 0) (hb3 : b 3 = 0) (p : DkPoly.SP) :
    rj a b (DkPoly.toPE p) = c3 (jSP A0 A1 C B0 B1 p) := by
  induction p with
  | nil => simp [DkPoly.toPE, sumE, rj_const, jSP, c3]
  | cons t p ih =>
    simp only [DkPoly.toPE, List.map_cons, sumE] at ih ⊢
    rw [rj_add, ih, rj_toE h0 h1 h2 h3 hb0 hb1 hb2 hb3, ← c3_jadd]
    rfl

end Bridge

/-! ## The residual polynomials of `dkFieldTC` -/

/-- `½ P̂''(a)[b, b]` of `D w − n`, rational: `((J_D · (A_w, B_w, 0))'' + J_n'')/2`. -/
def c2Q (A0 A1 C B0 B1 Aw Bw : ℚ) (n : DkPoly.SP) : ℚ :=
  ((jmul (jSP A0 A1 C B0 B1 DommaschkKam.dD) (Aw, Bw, 0)).2.2 + (jSP A0 A1 C B0 B1 n).2.2) / 2

/-- **The Taylor majorant of the `R`-residual** of `dkFieldTC` as a rational number. -/
theorem majD2_resRp {a b : Fin 6 → ℝ} {A0 A1 C A4 B0 B1 B4 : ℚ} (h0 : a 0 = A0) (h1 : a 1 = A1)
    (h2 : a 2 = C) (h3 : a 3 = C) (h4 : a 4 = A4) (hb0 : b 0 = B0) (hb1 : b 1 = B1)
    (hb2 : b 2 = 0) (hb3 : b 3 = 0) (hb4 : b 4 = B4) :
    PolyExpr.majD2 a b dkFieldTC.resRp / 2 =
      ((c2Q A0 A1 C B0 B1 A4 B4 DommaschkKam.dnR : ℚ) : ℝ) := by
  have e : PolyExpr.majD2 a b dkFieldTC.resRp = (rj a b dkFieldTC.resRp).2.2 := rfl
  have hD : rj a b dkFieldTC.Dp = c3 (jSP A0 A1 C B0 B1 DommaschkKam.dD) :=
    rj_toPE h0 h1 h2 h3 hb0 hb1 hb2 hb3 _
  have hn : rj a b dkFieldTC.nRp = c3 (jSP A0 A1 C B0 B1 DommaschkKam.dnR) :=
    rj_toPE h0 h1 h2 h3 hb0 hb1 hb2 hb3 _
  rw [e, FlowFieldG.resRp, rj_sub, rj_mul, hD, hn, rj_var, h4, hb4,
    show ((A4 : ℝ), (B4 : ℝ), (0 : ℝ)) = c3 (A4, B4, 0) by simp [c3], ← c3_jmul, ← c3_jadd]
  simp only [c3, jadd, c2Q]; push_cast; ring

/-- **The Taylor majorant of the `z`-residual** of `dkFieldTC` as a rational number. -/
theorem majD2_resZp {a b : Fin 6 → ℝ} {A0 A1 C A5 B0 B1 B5 : ℚ} (h0 : a 0 = A0) (h1 : a 1 = A1)
    (h2 : a 2 = C) (h3 : a 3 = C) (h5 : a 5 = A5) (hb0 : b 0 = B0) (hb1 : b 1 = B1)
    (hb2 : b 2 = 0) (hb3 : b 3 = 0) (hb5 : b 5 = B5) :
    PolyExpr.majD2 a b dkFieldTC.resZp / 2 =
      ((c2Q A0 A1 C B0 B1 A5 B5 DommaschkKam.dnZ : ℚ) : ℝ) := by
  have e : PolyExpr.majD2 a b dkFieldTC.resZp = (rj a b dkFieldTC.resZp).2.2 := rfl
  have hD : rj a b dkFieldTC.Dp = c3 (jSP A0 A1 C B0 B1 DommaschkKam.dD) :=
    rj_toPE h0 h1 h2 h3 hb0 hb1 hb2 hb3 _
  have hn : rj a b dkFieldTC.nZp = c3 (jSP A0 A1 C B0 B1 DommaschkKam.dnZ) :=
    rj_toPE h0 h1 h2 h3 hb0 hb1 hb2 hb3 _
  rw [e, FlowFieldG.resZp, rj_sub, rj_mul, hD, hn, rj_var, h5, hb5,
    show ((A5 : ℝ), (B5 : ℝ), (0 : ℝ)) = c3 (A5, B5, 0) by simp [c3], ← c3_jmul, ← c3_jadd]
  simp only [c3, jadd, c2Q]; push_cast; ring

end PlasmaLean.Design.DommaschkKamC
