/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2Rotated
public import PlasmaLean.Design.LandremanFamily2Labels
public import PlasmaLean.Certificates.ValidatedTrigFast
public import PlasmaLean.Certificates.ValidatedQuadratureArcs
public import PlasmaLean.Design.SolovevMercierQuadrature

/-!
# Validated quadrature of the family-2 Mercier data: interval evaluation and checker

Fixed-point interval (`FIv`) evaluation of every quantity entering the Mercier index of
Landreman's family 2 (`ε = 1/4`, `S = 4`, integer `λ`) on a cell `k ∈ [k_a, k_b]` of flux
surfaces, with soundness lemmas: each evaluation encloses the exact real value of the closed
forms of `LandremanFamily2Surface`, `LandremanFamily2Rotated`, `LandremanFamily2Labels`,
uniformly for all `k` in the cell.

* `zEval`: the `ζ`-dependent quantities `ν, cosh ν, sinh ν, T` and the ridge rotation
  `sin φ, cos φ, C`;
* `coreEval`: at a point of the ridge-aligned poloidal angle `χ'`, the (scaled) numerators
  `λ² HB, λ² HX, λ² HZ`, the kernel data `a²/λ²`, `P/λ²`, the ridge factor `g` (`f = sin χ' g`),
  and `gp2/λ²`; the scaling by powers of `λ` keeps all fixed-point quantities of order one;
* tip cells (`tipCell`, arcs `χ' = arctan t`, `arctan t + π`): **product integration** — the
  numerator is enclosed on the cell, the sharp factor `1/(a² + P g² sin²χ')` (width `O(1/λ)`)
  is integrated exactly with the Lorentzian kernel `∫ dt/(α + γ t²)` (`lorentzIv`,
  `mem_prodB`); side cells (`sideCell`, arcs `χ' = ±π/2 - arctan u`): plain interval cells;
* `innerSum`/`mem_inner` (poloidal integral, via `integral_periodic_shift` and
  `integral_eq_quarter_arcs`), `outerSum`/`mem_outer` (toroidal integral, via
  `integral_comp_two_mul_periodic` and quarter arcs in `2ζ`): enclosures of the surface
  integrals `IntR`;
* `quad1`/`mem_quad1`: the one-dimensional integrals `F₁, F₁', Z, Z', E, E'`;
* `cellCheck`/`cellCheck_sound`: the per-cell checker and its soundness,
  `(2π)⁶ D_Merc = D6R > 0` for both signs `s_G = ±1` on the whole cell; `cellCheck_of_pieces`
  lets large cells be certified in separately kernel-checked pieces.

All evaluations are total; an operation that cannot be bounded (division by an enclosure
containing `0`, `arcsin` outside `(-1,1)`, ...) returns an invalid enclosure, which the
checker rejects.
-/

public section
noncomputable section

namespace PlasmaLean.Design.LandremanFamily2Quad

open Real PlasmaLean.Certificates.ValidatedQuadrature PlasmaLean.Design.LandremanFamily2Surface
open PlasmaLean.Design.LandremanFamily2Rotated
open FIv (Mem mem_add mem_sub mem_mul mem_sq mem_inv mem_sqrt mem_neg mem_ofInt mem_ofFrac
  mem_meet mem_asinFast mem_coshSmall mem_sinhSmall mem_atanFast mem_divInt)

/-! ## Helpers -/

/-- Signed reciprocal: valid for enclosures not containing `0`. -/
@[expose] def invS (I : FIv) : FIv :=
  if 0 < I.lo then I.inv else if I.hi < 0 then I.neg.inv.neg else ⟨0, 0, false⟩

/-- Soundness of the signed reciprocal. -/
theorem mem_invS {I : FIv} {x : ℝ} (h : I.Mem x) : (invS I).Mem x⁻¹ := by
  unfold invS
  split_ifs
  · exact mem_inv h
  · have := mem_neg (mem_inv (mem_neg h))
    rwa [inv_neg, neg_neg] at this
  · intro h'; exact absurd h' (by simp)

/-- Transport of a membership along an equality of reals. -/
theorem memOfEq {I : FIv} {x y : ℝ} (h : I.Mem x) (e : x = y) : I.Mem y := e ▸ h

/-- The constant `1`. -/
@[expose] def c1I : FIv := FIv.ofInt 1
/-- The constant `2`. -/
@[expose] def c2I : FIv := FIv.ofInt 2
/-- The constant `4`. -/
@[expose] def c4I : FIv := FIv.ofInt 4
/-- The constant `6`. -/
@[expose] def c6I : FIv := FIv.ofInt 6
/-- The constant `1/2`. -/
@[expose] def halfI : FIv := FIv.ofFrac 1 2
/-- The constant `1/4 = ε`. -/
@[expose] def quarterI : FIv := FIv.ofFrac 1 4
/-- The constant `1/8 = ε/2`. -/
@[expose] def eighthI : FIv := FIv.ofFrac 1 8
/-- The constant `1/16 = ε²`. -/
@[expose] def sixteenthI : FIv := FIv.ofFrac 1 16
/-- The constant `4/5`. -/
@[expose] def fourFifthI : FIv := FIv.ofFrac 4 5
/-- The constant `6/5`. -/
@[expose] def sixFifthI : FIv := FIv.ofFrac 6 5

/-- Soundness of the constant `1`. -/
theorem mem_c1 : c1I.Mem 1 := by unfold c1I; simpa using mem_ofInt 1
/-- Soundness of the constant `2`. -/
theorem mem_c2 : c2I.Mem 2 := by unfold c2I; simpa using mem_ofInt 2
/-- Soundness of the constant `4`. -/
theorem mem_c4 : c4I.Mem 4 := by unfold c4I; simpa using mem_ofInt 4
/-- Soundness of the constant `6`. -/
theorem mem_c6 : c6I.Mem 6 := by unfold c6I; simpa using mem_ofInt 6
/-- Soundness of the constant `1/2`. -/
theorem mem_half : halfI.Mem (1 / 2) := by unfold halfI; simpa using mem_ofFrac 1 2
/-- Soundness of the constant `1/4`. -/
theorem mem_quarter : quarterI.Mem (1 / 4) := by unfold quarterI; simpa using mem_ofFrac 1 4
/-- Soundness of the constant `1/8`. -/
theorem mem_eighth : eighthI.Mem (1 / 8) := by unfold eighthI; simpa using mem_ofFrac 1 8
/-- Soundness of the constant `1/16`. -/
theorem mem_sixteenth : sixteenthI.Mem (1 / 16) := by
  unfold sixteenthI; simpa using mem_ofFrac 1 16
/-- Soundness of the constant `4/5`. -/
theorem mem_fourFifth : fourFifthI.Mem (4 / 5) := by
  unfold fourFifthI; simpa using mem_ofFrac 4 5
/-- Soundness of the constant `6/5`. -/
theorem mem_sixFifth : sixFifthI.Mem (6 / 5) := by
  unfold sixFifthI; simpa using mem_ofFrac 6 5

/-! ## `ζ`-dependent quantities -/

/-- Enclosures of the `ζ`-dependent quantities. -/
structure ZIv where
  /-- `sin 2ζ`. -/
  s2 : FIv
  /-- `cos 2ζ`. -/
  c2 : FIv
  /-- `ν`. -/
  nu : FIv
  /-- `cosh ν`. -/
  ch : FIv
  /-- `sinh ν`. -/
  sh : FIv
  /-- `T² = cosh² ν - k²`. -/
  T2 : FIv
  /-- `T`. -/
  T : FIv
  /-- `sin φ`. -/
  sph : FIv
  /-- `cos φ`. -/
  cph : FIv
  /-- `C = √(1 - k² sin² φ)`. -/
  Cph : FIv

/-- Evaluation of the `ζ`-dependent quantities from enclosures of `k²`, `sin 2ζ`, `cos 2ζ`. -/
@[expose] def zEval (K2 S2 C2 : FIv) : ZIv :=
  let nu := eighthI.mul S2
  let ch := FIv.coshSmall nu
  let sh := FIv.sinhSmall nu
  let T2 := ch.sq.sub K2
  let T := T2.sqrt
  let rho := (ch.mul sh).mul T.inv
  let u := c1I.add rho.sq
  let D := (u.sq.sub ((c4I.mul K2).mul rho.sq)).sqrt
  let sph := rho.mul (c2I.mul (u.add D).inv).sqrt
  ⟨S2, C2, nu, ch, sh, T2, T, sph, (c1I.sub sph.sq).sqrt, (c1I.sub (K2.mul sph.sq)).sqrt⟩

/-- Membership of all `ζ`-quantities. -/
structure ZMem (z : ZIv) (k s2 c2 : ℝ) : Prop where
  hs2 : z.s2.Mem s2
  hc2 : z.c2.Mem c2
  hnu : z.nu.Mem (nuc (1 / 4) s2)
  hch : z.ch.Mem (chc (1 / 4) s2)
  hsh : z.sh.Mem (shc (1 / 4) s2)
  hT2 : z.T2.Mem (Tc (1 / 4) k s2 ^ 2)
  hT : z.T.Mem (Tc (1 / 4) k s2)
  hsph : z.sph.Mem (sphr k s2)
  hcph : z.cph.Mem (cphr k s2)
  hCph : z.Cph.Mem (Cphr k s2)

/-- **Soundness of `zEval`.** -/
theorem mem_zEval {K2 S2 C2 : FIv} {k s2 c2 : ℝ} (hK2 : K2.Mem (k ^ 2)) (hS2 : S2.Mem s2)
    (hC2 : C2.Mem c2) (hk : k ^ 2 < 1) : ZMem (zEval K2 S2 C2) k s2 c2 := by
  have hnu : (eighthI.mul S2).Mem (nuc (1 / 4) s2) := by
    have := mem_mul mem_eighth hS2
    unfold nuc; convert this using 1; ring
  have hch : (FIv.coshSmall (eighthI.mul S2)).Mem (chc (1 / 4) s2) := mem_coshSmall hnu
  have hsh : (FIv.sinhSmall (eighthI.mul S2)).Mem (shc (1 / 4) s2) := mem_sinhSmall hnu
  have hT2' := mem_sub (mem_sq hch) hK2
  have hT2 := memOfEq hT2' (Tc_sq hk).symm
  have hT := mem_sqrt hT2'
  have hrho := memOfEq (mem_mul (mem_mul hch hsh) (mem_inv hT))
    (by rw [← div_eq_mul_inv]; rfl : _ = rhoR k s2)
  have hu := mem_add mem_c1 (mem_sq hrho)
  have hD := memOfEq (mem_sqrt (mem_sub (mem_sq hu) (mem_mul (mem_mul mem_c4 hK2) (mem_sq hrho))))
    (rfl : _ = DR k s2)
  have hw := memOfEq (mem_sqrt (mem_mul mem_c2 (mem_inv (mem_add hu hD))))
    (by rw [← div_eq_mul_inv]; rfl : _ = wR k s2)
  have hsph := memOfEq (mem_mul hrho hw) (rfl : _ = sphr k s2)
  exact ⟨hS2, hC2, hnu, hch, hsh, hT2, hT, hsph, mem_sqrt (mem_sub mem_c1 (mem_sq hsph)),
    mem_sqrt (mem_sub mem_c1 (mem_mul hK2 (mem_sq hsph)))⟩

/-! ## Core evaluation in the rotated frame -/

/-- Enclosures produced at one point (cell) of the rotated poloidal angle. -/
structure CoreIv where
  /-- `λ² HB`. -/
  hB : FIv
  /-- `λ² HX`. -/
  hX : FIv
  /-- `λ² HZ`. -/
  hZ : FIv
  /-- `a²/λ² = X² gX2/λ²`. -/
  a2 : FIv
  /-- `P/λ² = T² k²/T₀²`. -/
  P : FIv
  /-- The ridge factor `g` (tip modes) or `f` (side mode). -/
  g : FIv
  /-- `gp2/λ² = |∇ψ|²/λ²`. -/
  gp2 : FIv

/-- The symmetric clip interval `[-k_hi, k_hi]`. -/
@[expose] def clipI (K : FIv) : FIv := ⟨-K.hi, K.hi, K.ok⟩

/-- Soundness of the clip interval: any `x` with `|x| ≤ k` lies in it. -/
theorem mem_clipI {K : FIv} {k x : ℝ} (hK : K.Mem k) (hx : |x| ≤ k) : (clipI K).Mem x := by
  intro hok
  obtain ⟨_, h2⟩ := hK hok
  have := abs_le.mp (hx.trans h2)
  refine ⟨?_, this.2⟩
  have e : fxVal (-K.hi) = -fxVal K.hi := by unfold fxVal; push_cast; ring
  simp only [clipI, e]
  exact this.1

/-- The real ridge factor for the three modes: `g_A` (tip arc through `χ' = 0`), `g_B` (tip arc
through `χ' = π`) and `f` itself (side arcs). -/
@[expose] def gsel (mode : ℕ) (k sp cp s2 : ℝ) : ℝ :=
  if mode = 0 then gAR k sp cp s2 else if mode = 1 then gBR k sp cp s2 else fR k sp cp s2

/-- The multiplier `sin χ'` (tip modes) or `1` (side mode) with `f = spf · g`. -/
@[expose] def spf (mode : ℕ) (sp : ℝ) : ℝ := if mode < 2 then sp else 1

/-- `f = spf · g` in each mode (under the half-circle conditions of the tip modes). -/
theorem fR_eq_sel {mode : ℕ} {k sp cp s2 : ℝ} (hk : k ^ 2 < 1) (h : sp ^ 2 + cp ^ 2 = 1)
    (hA : mode = 0 → 1 + cp ≠ 0) (hB : mode = 1 → 1 - cp ≠ 0) :
    fR k sp cp s2 = spf mode sp * gsel mode k sp cp s2 := by
  by_cases h0 : mode = 0
  · subst h0; simp only [spf, gsel, ite_true, Nat.ofNat_pos]; exact fR_eq_A hk h (hA rfl)
  by_cases h1 : mode = 1
  · subst h1; simp only [spf, gsel, one_ne_zero, ite_false, ite_true, Nat.one_lt_ofNat]
    exact fR_eq_B hk h (hB rfl)
  · have h2 : ¬ mode < 2 := by omega
    simp only [spf, gsel, h0, h1, h2, ite_false, one_mul]

/-- **Core evaluation** at a cell of the rotated angle, from enclosures of `λ`, `1/λ²`,
`1/(2λ)`, `k`, `k²`, `dI = λ - I'`, the `ζ`-data, `sin χ'` and `cos χ'`; `mode` selects the
ridge factorization (`0`, `1`: tip arcs; `2`: side arcs). -/
@[expose] def coreEval (mode : ℕ) (lamI ilam2I ihlamI K K2 DI : FIv) (z : ZIv) (SP CP : FIv) :
    CoreIv :=
  let s1 := (SP.mul z.cph).add (CP.mul z.sph)
  let c1 := (CP.mul z.cph).sub (SP.mul z.sph)
  let Y := K.mul s1
  let X := K.mul c1
  let Y2 := Y.sq
  let cc := (c1I.sub Y2).sqrt
  let T0 := z.ch.sq.sub Y2
  let sAc := ((((cc.mul z.ch).mul X).add ((Y.mul z.sh).mul z.T)).mul T0.inv).meet (clipI K)
  let sig := c4I.add (FIv.asinFast sAc)
  let h := ((c4I.mul sig.sq).add sixteenthI).sqrt
  let m := (h.sub (quarterI.mul z.c2)).mul halfI
  let G := (h.add (quarterI.mul z.c2)).mul halfI
  let q := sig.sq.add z.nu.sq
  let r := m.sq.mul q.inv
  let base := (z.cph.sq.mul cc).add (z.sph.sq.mul z.Cph)
  let coef := ((CP.mul z.sph).mul z.cph).mul K2
  let g := if mode = 0 then (z.T.mul z.cph.inv).mul (base.add (((coef.mul
      (((z.sph.mul SP).mul (c1I.add CP).inv).sub z.cph)).mul (z.sph.add s1)).mul
      (cc.add z.Cph).inv))
    else if mode = 1 then (z.T.mul z.cph.inv).mul (base.add (((coef.mul (z.sph.sub s1)).mul
      (((z.sph.mul SP).mul (c1I.sub CP).inv).add z.cph)).mul (cc.add z.Cph).inv))
    else ((s1.mul cc).mul z.T).sub ((c1.mul z.ch).mul z.sh)
  let fg := (if mode < 2 then SP else c1I).mul g
  let uI := (K.mul fg).mul T0.inv
  let uI2 := uI.sq
  let Bsq := (((z.T2.add uI2).mul (m.mul q.inv)).mul quarterI).add (X.sq.mul ilam2I)
  let gX2 := (q.mul m.inv).mul ((z.T2.mul (c1I.add r).sq).add (uI2.mul (c1I.sub r).sq))
  let BD := ((z.T2.mul (c1I.add r)).sub (uI2.mul (c1I.sub r))).mul ihlamI
  let Jac := (G.mul ((h.mul z.T).mul cc).inv).mul lamI
  let a2 := (X.sq.mul gX2).mul ilam2I
  let P := (z.T2.mul K2).mul T0.sq.inv
  ⟨Bsq.mul Jac, ((DI.mul Bsq).add BD).mul Jac,
    ((DI.mul ((DI.mul Bsq).add (c2I.mul BD))).add (gX2.mul ilam2I)).mul Jac, a2, P, g,
    a2.add (P.mul fg.sq)⟩

/-- Membership of the core outputs. -/
structure CoreMem (c : CoreIv) (mode : ℕ) (lam dI k sp cp s2 c2 : ℝ) : Prop where
  hB : c.hB.Mem (lam ^ 2 * HB lam k (s1r k sp cp s2) (c1r k sp cp s2) s2 c2)
  hX : c.hX.Mem (lam ^ 2 * HX lam dI k (s1r k sp cp s2) (c1r k sp cp s2) s2 c2)
  hZ : c.hZ.Mem (lam ^ 2 * HZ lam dI k (s1r k sp cp s2) (c1r k sp cp s2) s2 c2)
  a2 : c.a2.Mem (aSq k (s1r k sp cp s2) (c1r k sp cp s2) s2 c2 / lam ^ 2)
  P : c.P.Mem (PR lam k (s1r k sp cp s2) s2 / lam ^ 2)
  g : c.g.Mem (gsel mode k sp cp s2)
  gp2 : c.gp2.Mem (gp2 (1 / 4) 4 lam k (s1r k sp cp s2) (c1r k sp cp s2) s2 c2 / lam ^ 2)

/-- **Soundness of `coreEval`.** -/
theorem mem_coreEval {mode : ℕ} {lamI ilam2I ihlamI K K2 DI SP CP : FIv} {z : ZIv}
    {lam dI k sp cp s2 c2 : ℝ} (hl : lamI.Mem lam) (hl0 : lam ≠ 0)
    (hil2 : ilam2I.Mem (1 / lam ^ 2)) (hihl : ihlamI.Mem (1 / (2 * lam))) (hK : K.Mem k)
    (hK2 : K2.Mem (k ^ 2)) (hDI : DI.Mem dI) (hz : ZMem z k s2 c2) (hSP : SP.Mem sp)
    (hCP : CP.Mem cp) (hk0 : 0 ≤ k) (hk : k ^ 2 < 1) (hsc : sp ^ 2 + cp ^ 2 = 1)
    (hmA : mode = 0 → 1 + cp ≠ 0) (hmB : mode = 1 → 1 - cp ≠ 0) :
    CoreMem (coreEval mode lamI ilam2I ihlamI K K2 DI z SP CP) mode lam dI k sp cp s2 c2 := by
  have h1 : s1r k sp cp s2 ^ 2 + c1r k sp cp s2 ^ 2 = 1 := s1r_sq_add_c1r_sq hk hsc
  have hs1 := mem_add (mem_mul hSP hz.hcph) (mem_mul hCP hz.hsph)
  have hc1 := mem_sub (mem_mul hCP hz.hcph) (mem_mul hSP hz.hsph)
  have hY := mem_mul hK hs1
  have hX := mem_mul hK hc1
  have hY2 := mem_sq hY
  have hcc := mem_sqrt (mem_sub mem_c1 hY2)
  have hT0 := mem_sub (mem_sq hz.hch) hY2
  have hsA0 := memOfEq (mem_mul (mem_add (mem_mul (mem_mul hcc hz.hch) hX)
    (mem_mul (mem_mul hY hz.hsh) hz.hT)) (mem_inv hT0))
    (by rw [← div_eq_mul_inv]; rfl : _ = sA (1 / 4) k (s1r k sp cp s2) (c1r k sp cp s2) s2)
  have hsA := mem_meet hsA0 (mem_clipI hK (abs_sA_le h1 hk0 hk))
  have hsig := mem_add mem_c4 (mem_asinFast hsA)
  have hh := memOfEq (mem_sqrt (mem_add (mem_mul mem_c4 (mem_sq hsig)) mem_sixteenth))
    (by unfold hc sigc; norm_num : _ = hc (1 / 4) 4 k (s1r k sp cp s2) (c1r k sp cp s2) s2)
  have hm := memOfEq (mem_mul (mem_sub hh (mem_mul mem_quarter hz.hc2)) mem_half)
    (by unfold mc; ring : _ = mc (1 / 4) 4 k (s1r k sp cp s2) (c1r k sp cp s2) s2 c2)
  have hG := memOfEq (mem_mul (mem_add hh (mem_mul mem_quarter hz.hc2)) mem_half)
    (by unfold Gc; ring : _ = Gc (1 / 4) 4 k (s1r k sp cp s2) (c1r k sp cp s2) s2 c2)
  have hq := memOfEq (mem_add (mem_sq hsig) (mem_sq hz.hnu))
    (by unfold qc sigc; rfl : _ = qc (1 / 4) 4 k (s1r k sp cp s2) (c1r k sp cp s2) s2)
  have hr := memOfEq (mem_mul (mem_sq hm) (mem_inv hq))
    (by rw [← div_eq_mul_inv]; rfl : _ = rc (1 / 4) 4 k (s1r k sp cp s2) (c1r k sp cp s2) s2 c2)
  have hbase := mem_add (mem_mul (mem_sq hz.hcph) hcc) (mem_mul (mem_sq hz.hsph) hz.hCph)
  have hcoef := mem_mul (mem_mul (mem_mul hCP hz.hsph) hz.hcph) hK2
  have hg : (coreEval mode lamI ilam2I ihlamI K K2 DI z SP CP).g.Mem (gsel mode k sp cp s2) := by
    unfold coreEval gsel
    dsimp only
    split_ifs
    · exact memOfEq (mem_mul (mem_mul hz.hT (mem_inv hz.hcph)) (mem_add hbase (mem_mul (mem_mul
        (mem_mul hcoef (mem_sub (mem_mul (mem_mul hz.hsph hSP) (mem_inv (mem_add mem_c1 hCP)))
          hz.hcph)) (mem_add hz.hsph hs1)) (mem_inv (mem_add hcc hz.hCph))))) (by unfold gAR; rfl)
    · exact memOfEq (mem_mul (mem_mul hz.hT (mem_inv hz.hcph)) (mem_add hbase (mem_mul (mem_mul
        (mem_mul hcoef (mem_sub hz.hsph hs1)) (mem_add (mem_mul (mem_mul hz.hsph hSP)
          (mem_inv (mem_sub mem_c1 hCP))) hz.hcph)) (mem_inv (mem_add hcc hz.hCph)))))
        (by unfold gBR; rfl)
    · exact memOfEq (mem_sub (mem_mul (mem_mul hs1 hcc) hz.hT) (mem_mul (mem_mul hc1 hz.hch)
        hz.hsh)) (by unfold fR; rfl)
  have hspf : (if mode < 2 then SP else c1I).Mem (spf mode sp) := by
    unfold spf; split_ifs
    · exact hSP
    · exact mem_c1
  have hfg := memOfEq (mem_mul hspf hg) (fR_eq_sel hk hsc hmA hmB).symm
  have huI := memOfEq (mem_mul (mem_mul hK hfg) (mem_inv hT0))
    (by rw [uIc_rot, ← div_eq_mul_inv]; rfl :
      _ = uIc (1 / 4) k (s1r k sp cp s2) (c1r k sp cp s2) s2)
  have huI2 := mem_sq huI
  have hBsq := memOfEq (mem_add (mem_mul (mem_mul (mem_add hz.hT2 huI2) (mem_mul hm (mem_inv hq)))
    mem_quarter) (mem_mul (mem_sq hX) hil2))
    (by unfold Bsq Xc c1r; ring : _ = Bsq (1 / 4) 4 lam k (s1r k sp cp s2) (c1r k sp cp s2) s2 c2)
  have hgX2 := memOfEq (mem_mul (mem_mul hq (mem_inv hm)) (mem_add (mem_mul hz.hT2
    (mem_sq (mem_add mem_c1 hr))) (mem_mul huI2 (mem_sq (mem_sub mem_c1 hr)))))
    (by unfold gX2; rw [← div_eq_mul_inv] :
      _ = gX2 (1 / 4) 4 k (s1r k sp cp s2) (c1r k sp cp s2) s2 c2)
  have hBD := memOfEq (mem_mul (mem_sub (mem_mul hz.hT2 (mem_add mem_c1 hr))
    (mem_mul huI2 (mem_sub mem_c1 hr))) hihl)
    (by unfold BD; ring : _ = BD (1 / 4) 4 lam k (s1r k sp cp s2) (c1r k sp cp s2) s2 c2)
  have hJ := memOfEq (mem_mul (mem_mul hG (mem_inv (mem_mul (mem_mul hh hz.hT) hcc))) hl)
    (by
      rw [show √(1 - (k * (sp * cphr k s2 + cp * sphr k s2)) ^ 2) = cc k (s1r k sp cp s2) from rfl]
      unfold JacR; field_simp :
      _ = lam ^ 2 * JacR lam k (s1r k sp cp s2) (c1r k sp cp s2) s2 c2)
  have ha2 := memOfEq (mem_mul (mem_mul (mem_sq hX) hgX2) hil2)
    (by unfold aSq; rw [mul_one_div]; rfl :
      _ = aSq k (s1r k sp cp s2) (c1r k sp cp s2) s2 c2 / lam ^ 2)
  have hP := memOfEq (mem_mul (mem_mul hz.hT2 hK2) (mem_inv (mem_sq hT0)))
    (by
      rw [show chc (1 / 4) s2 ^ 2 - (k * (sp * cphr k s2 + cp * sphr k s2)) ^ 2 =
        T0c (1 / 4) k (s1r k sp cp s2) s2 from rfl]
      unfold PR; field_simp : _ = PR lam k (s1r k sp cp s2) s2 / lam ^ 2)
  refine ⟨memOfEq (mem_mul hBsq hJ) (by unfold HB; ring),
    memOfEq (mem_mul (mem_add (mem_mul hDI hBsq) hBD) hJ) (by unfold HX; ring), ?_, ha2, hP,
    hg, ?_⟩
  · exact memOfEq (mem_mul (mem_add (mem_mul hDI (mem_add (mem_mul hDI hBsq) (mem_mul mem_c2 hBD)))
      (mem_mul hgX2 hil2)) hJ) (by unfold HZ; ring)
  · refine memOfEq (mem_add ha2 (mem_mul hP (mem_sq hfg))) ?_
    rw [gp2_rot lam hk hsc c2]; ring

/-! ## Arc variables -/

/-- `sin(arctan t) = t/√(1+t²)`. -/
@[expose] def spA (t : ℝ) : ℝ := t / √(1 + t ^ 2)
/-- `cos(arctan t) = 1/√(1+t²)`. -/
@[expose] def cpA (t : ℝ) : ℝ := 1 / √(1 + t ^ 2)
/-- The arc weight `1/(1+t²)`. -/
@[expose] def wA (t : ℝ) : ℝ := 1 / (1 + t ^ 2)

/-- `(sin, cos)(arctan t)` lies on the unit circle. -/
theorem spA_sq_add_cpA_sq (t : ℝ) : spA t ^ 2 + cpA t ^ 2 = 1 := by
  have h : 0 < 1 + t ^ 2 := by positivity
  have hs := Real.sq_sqrt h.le
  have hs0 := (Real.sqrt_pos.2 h).ne'
  unfold spA cpA
  field_simp
  linarith

/-- `t ↦ t/√(1+t²)` is increasing. -/
theorem spA_mono : Monotone spA := by
  intro a b hab
  have := sin_arctan_strictMono.monotone hab
  simpa [spA, sin_arctan] using this

/-- `1/√(1+t²)` is decreasing on `t ≥ 0`. -/
theorem cpA_anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : cpA b ≤ cpA a := by
  unfold cpA
  apply one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity))
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- `1/√(1+t²)` is increasing on `t ≤ 0`. -/
theorem cpA_mono_neg {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) : cpA a ≤ cpA b := by
  unfold cpA
  apply one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity))
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- `1/(1+t²)` is decreasing on `t ≥ 0`. -/
theorem wA_anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : wA b ≤ wA a := by
  unfold wA
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

/-- `1/(1+t²)` is increasing on `t ≤ 0`. -/
theorem wA_mono_neg {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) : wA a ≤ wA b := by
  unfold wA
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

/-- Enclosure of `spA (p/N) = p/√(N² + p²)`. -/
@[expose] def spPt (N : ℕ) (p : ℤ) : FIv :=
  (FIv.ofInt p).mul (FIv.ofInt ((N : ℤ) ^ 2 + p ^ 2)).sqrt.inv
/-- Enclosure of `cpA (p/N) = N/√(N² + p²)`. -/
@[expose] def cpPt (N : ℕ) (p : ℤ) : FIv :=
  (FIv.ofInt N).mul (FIv.ofInt ((N : ℤ) ^ 2 + p ^ 2)).sqrt.inv
/-- Enclosure of `wA (p/N) = N²/(N² + p²)`. -/
@[expose] def wPt (N : ℕ) (p : ℤ) : FIv := FIv.ofFrac ((N : ℤ) ^ 2) ((N : ℤ) ^ 2 + p ^ 2)

/-- `√(1 + (p/N)²) = √(N² + p²)/N`. -/
theorem sqrt_one_add_frac {N : ℕ} (hN : 0 < N) (p : ℤ) :
    √(1 + ((p : ℝ) / N) ^ 2) = √((N : ℝ) ^ 2 + p ^ 2) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [show 1 + ((p : ℝ) / N) ^ 2 = ((N : ℝ) ^ 2 + p ^ 2) / (N : ℝ) ^ 2 by field_simp,
    Real.sqrt_div' _ (by positivity), Real.sqrt_sq hN'.le]

/-- Soundness of the point enclosure of `spA (p/N)`. -/
theorem mem_spPt {N : ℕ} (hN : 0 < N) (p : ℤ) : (spPt N p).Mem (spA ((p : ℝ) / N)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := mem_mul (mem_ofInt p) (mem_inv (mem_sqrt (mem_ofInt ((N : ℤ) ^ 2 + p ^ 2))))
  refine memOfEq h ?_
  have hs : 0 < √((N : ℝ) ^ 2 + p ^ 2) := Real.sqrt_pos.2 (by positivity)
  unfold spA
  rw [sqrt_one_add_frac hN]
  push_cast
  field_simp

/-- Soundness of the point enclosure of `cpA (p/N)`. -/
theorem mem_cpPt {N : ℕ} (hN : 0 < N) (p : ℤ) : (cpPt N p).Mem (cpA ((p : ℝ) / N)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := mem_mul (mem_ofInt (N : ℤ)) (mem_inv (mem_sqrt (mem_ofInt ((N : ℤ) ^ 2 + p ^ 2))))
  refine memOfEq h ?_
  have hs : 0 < √((N : ℝ) ^ 2 + p ^ 2) := Real.sqrt_pos.2 (by positivity)
  unfold cpA
  rw [sqrt_one_add_frac hN]
  push_cast
  field_simp

/-- Soundness of the point enclosure of `wA (p/N)`. -/
theorem mem_wPt {N : ℕ} (hN : 0 < N) (p : ℤ) : (wPt N p).Mem (wA ((p : ℝ) / N)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine memOfEq (mem_ofFrac _ _) ?_
  unfold wA
  push_cast
  field_simp

/-- Hull of two enclosures `[lo of I, hi of J]`. -/
@[expose] def span (I J : FIv) : FIv := ⟨I.lo, J.hi, I.ok && J.ok⟩

/-- Soundness of the hull of two point enclosures bracketing `x`. -/
theorem mem_span {I J : FIv} {a b x : ℝ} (hI : I.Mem a) (hJ : J.Mem b) (h1 : a ≤ x)
    (h2 : x ≤ b) : (span I J).Mem x := by
  intro hok
  simp only [span, Bool.and_eq_true] at hok
  exact ⟨(hI hok.1).1.trans h1, h2.trans (hJ hok.2).2⟩

/-- Cell enclosure of `spA` on `[pa/N, pb/N]` (increasing). -/
@[expose] def spCell (N : ℕ) (pa pb : ℤ) : FIv := span (spPt N pa) (spPt N pb)

/-- Cell enclosure of a function that is increasing on `t ≤ 0` and decreasing on `t ≥ 0`
(valid for cells not straddling `0`). -/
@[expose] def evenCell (f : ℕ → ℤ → FIv) (N : ℕ) (pa pb : ℤ) : FIv :=
  if 0 ≤ pa then span (f N pb) (f N pa) else if pb ≤ 0 then span (f N pa) (f N pb)
  else ⟨0, 0, false⟩

/-- Soundness of the cell enclosure of `spA`. -/
theorem mem_spCell {N : ℕ} (hN : 0 < N) {pa pb : ℤ} {t : ℝ}
    (ht : t ∈ Set.Icc ((pa : ℝ) / N) ((pb : ℝ) / N)) : (spCell N pa pb).Mem (spA t) :=
  mem_span (mem_spPt hN pa) (mem_spPt hN pb) (spA_mono ht.1) (spA_mono ht.2)

/-- Soundness of the cell enclosure of an even unimodal function (cells not straddling `0`). -/
theorem mem_evenCell {f : ℕ → ℤ → FIv} {g : ℝ → ℝ} {N : ℕ} (hN : 0 < N)
    (hf : ∀ p, (f N p).Mem (g ((p : ℝ) / N)))
    (hanti : ∀ a b : ℝ, 0 ≤ a → a ≤ b → g b ≤ g a)
    (hmono : ∀ a b : ℝ, a ≤ b → b ≤ 0 → g a ≤ g b) {pa pb : ℤ} {t : ℝ}
    (ht : t ∈ Set.Icc ((pa : ℝ) / N) ((pb : ℝ) / N)) : (evenCell f N pa pb).Mem (g t) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold evenCell
  split_ifs with h1 h2
  · have : (0 : ℝ) ≤ (pa : ℝ) / N := by
      have : (0 : ℝ) ≤ pa := by exact_mod_cast h1
      positivity
    exact mem_span (hf pb) (hf pa) (hanti _ _ (this.trans ht.1) ht.2) (hanti _ _ this ht.1)
  · have : (pb : ℝ) / N ≤ 0 := by
      have : (pb : ℝ) ≤ 0 := by exact_mod_cast h2
      exact div_nonpos_of_nonpos_of_nonneg this hN'.le
    exact mem_span (hf pa) (hf pb) (hmono _ _ ht.1 (ht.2.trans this)) (hmono _ _ ht.2 this)
  · intro h; exact absurd h (by simp)

/-- Soundness of the cell enclosure of `cpA`. -/
theorem mem_cpCell {N : ℕ} (hN : 0 < N) {pa pb : ℤ} {t : ℝ}
    (ht : t ∈ Set.Icc ((pa : ℝ) / N) ((pb : ℝ) / N)) : (evenCell cpPt N pa pb).Mem (cpA t) :=
  mem_evenCell hN (mem_cpPt hN) (fun _ _ h1 h2 => cpA_anti h1 h2)
    (fun _ _ h1 h2 => cpA_mono_neg h1 h2) ht

/-- Soundness of the cell enclosure of the arc weight `wA`. -/
theorem mem_wCell {N : ℕ} (hN : 0 < N) {pa pb : ℤ} {t : ℝ}
    (ht : t ∈ Set.Icc ((pa : ℝ) / N) ((pb : ℝ) / N)) : (evenCell wPt N pa pb).Mem (wA t) :=
  mem_evenCell hN (mem_wPt hN) (fun _ _ h1 h2 => wA_anti h1 h2)
    (fun _ _ h1 h2 => wA_mono_neg h1 h2) ht

/-! ## Lorentzian kernel and product-integration cells -/

open PlasmaLean.Certificates.ValidatedQuadrature (lorentzK integral_lorentzian
  integral_div_le_lorentz lorentz_le_integral_div)

/-- Enclosure of `lorentzK (pa/N) (pb/N) (A/2³²) (G/2³²)` (valid only for `A, G > 0` and
`pa pb ≥ 0`): `arctan((b - a)s/(1 + ab s²))/(α s)` with `s = √(γ/α)`. -/
@[expose] def lorentzIv (N : ℕ) (pa pb A G : ℤ) : FIv :=
  let Ai := FIv.thin A
  let s := ((FIv.thin G).mul Ai.inv).sqrt
  let r := (FIv.atanFast (((FIv.ofFrac (pb - pa) N).mul s).mul
    (c1I.add ((FIv.ofFrac (pa * pb) ((N : ℤ) ^ 2)).mul s.sq)).inv)).mul (Ai.mul s).inv
  ⟨r.lo, r.hi, r.ok && decide (0 < A) && decide (0 < G) && decide (0 ≤ pa * pb)⟩

/-- A positive fixed-point integer has positive value. -/
theorem fxVal_pos {n : ℤ} (h : 0 < n) : 0 < fxVal n := by
  unfold fxVal
  exact div_pos (by exact_mod_cast h) fxScale_pos

/-- The arctangent difference formula `arctan x - arctan y = arctan((x-y)/(1+xy))` for
`xy ≥ 0`. -/
theorem arctan_sub_of_mul_nonneg {x y : ℝ} (h : 0 ≤ x * y) :
    arctan x - arctan y = arctan ((x - y) / (1 + x * y)) := by
  have := arctan_add (x := x) (y := -y) (by nlinarith)
  rw [arctan_neg] at this
  rw [sub_eq_add_neg, this]
  congr 1; ring

/-- **Soundness of the Lorentzian kernel enclosure.** -/
theorem mem_lorentzIv (N : ℕ) (pa pb A G : ℤ) :
    (lorentzIv N pa pb A G).Mem (lorentzK ((pa : ℝ) / N) ((pb : ℝ) / N) (fxVal A) (fxVal G)) := by
  intro hok
  simp only [lorentzIv, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hr, hA⟩, hG⟩, hab⟩ := hok
  have hA' := fxVal_pos hA
  have hG' := fxVal_pos hG
  have hs0 : 0 < √(fxVal G / fxVal A) := Real.sqrt_pos.2 (div_pos hG' hA')
  have hab' : (0 : ℝ) ≤ (pa : ℝ) / N * ((pb : ℝ) / N) := by
    have : (0 : ℝ) ≤ (pa : ℝ) * pb := by exact_mod_cast hab
    rw [div_mul_div_comm]; positivity
  have hαγ : √(fxVal A * fxVal G) = fxVal A * √(fxVal G / fxVal A) := by
    rw [show fxVal A * fxVal G = fxVal A ^ 2 * (fxVal G / fxVal A) by field_simp,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA'.le]
  rw [lorentzK, integral_lorentzian hA' hG', arctan_sub_of_mul_nonneg (by
    have := mul_nonneg hab' (sq_nonneg (√(fxVal G / fxVal A)))
    nlinarith), hαγ]
  have hs := mem_sqrt (mem_mul (FIv.mem_thin G) (mem_inv (FIv.mem_thin A)))
  have h := mem_mul (mem_atanFast (mem_mul (mem_mul (mem_ofFrac (pb - pa) N) hs)
    (mem_inv (mem_add mem_c1 (mem_mul (mem_ofFrac (pa * pb) ((N : ℤ) ^ 2)) (mem_sq hs))))))
    (mem_inv (mem_mul (FIv.mem_thin A) hs))
  refine (memOfEq h ?_) hr
  rw [← div_eq_mul_inv (fxVal G) (fxVal A),
    div_eq_mul_inv _ (fxVal A * √(fxVal G / fxVal A))]
  push_cast
  congr 2
  by_cases hN : (N : ℝ) = 0
  · simp [hN]
  · field_simp

/-- Product-integration bound for one cell: `[Hl K(αh,γh), Hh K(αl,γl)]` with the sign cases
(`H` encloses the numerator on the cell, `Kup`/`Klo` the kernel integrals). -/
@[expose] def prodB (H Kup Klo : FIv) : FIv :=
  ⟨if 0 ≤ H.lo then ((FIv.thin H.lo).mul Klo).lo else ((FIv.thin H.lo).mul Kup).lo,
    if 0 ≤ H.hi then ((FIv.thin H.hi).mul Kup).hi else ((FIv.thin H.hi).mul Klo).hi,
    H.ok && Kup.ok && Klo.ok⟩

/-- **Soundness of a product-integration cell.** -/
theorem mem_prodB {Hf D : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hH : ContinuousOn Hf (Set.Icc a b))
    (hD : ContinuousOn D (Set.Icc a b)) {H Kup Klo : FIv} {αl γl αh γh : ℝ} (hαl : 0 < αl)
    (hγl : 0 < γl) (hDl : ∀ t ∈ Set.Icc a b, αl + γl * t ^ 2 ≤ D t)
    (hDh : ∀ t ∈ Set.Icc a b, D t ≤ αh + γh * t ^ 2) (hHm : ∀ t ∈ Set.Icc a b, H.Mem (Hf t))
    (hKup : Kup.Mem (lorentzK a b αl γl)) (hKlo : Klo.Mem (lorentzK a b αh γh)) :
    (prodB H Kup Klo).Mem (∫ t in a..b, Hf t / D t) := by
  intro hok
  simp only [prodB, Bool.and_eq_true] at hok
  obtain ⟨⟨hHok, hUok⟩, hLok⟩ := hok
  have hS := fxScale_pos
  have hHh : ∀ t ∈ Set.Icc a b, Hf t ≤ fxVal H.hi := fun t ht => ((hHm t ht) hHok).2
  have hHl : ∀ t ∈ Set.Icc a b, fxVal H.lo ≤ Hf t := fun t ht => ((hHm t ht) hHok).1
  have up := integral_div_le_lorentz hab hH hD hαl hγl hDl hDh hHh
  have lo := lorentz_le_integral_div hab hH hD hαl hγl hDl hDh hHl
  have pos_iff : ∀ n : ℤ, (0 ≤ n ↔ 0 ≤ fxVal n) := fun n => by
    unfold fxVal; constructor
    · intro h; exact div_nonneg (by exact_mod_cast h) hS.le
    · intro h; have := (div_nonneg_iff.mp h); rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact_mod_cast h1
      · linarith
  constructor
  · dsimp only [prodB]
    split_ifs with h0
    · have hp := (mem_mul (FIv.mem_thin H.lo) hKlo) (by simp [FIv.mul, FIv.thin, hLok])
      rw [ite_eq_left_of_eq_true _ _ (eq_true ((pos_iff _).mp h0))] at lo
      exact hp.1.trans lo
    · have hp := (mem_mul (FIv.mem_thin H.lo) hKup) (by simp [FIv.mul, FIv.thin, hUok])
      rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => h0 ((pos_iff _).mpr h)))] at lo
      exact hp.1.trans lo
  · dsimp only [prodB]
    split_ifs with h0
    · have hp := (mem_mul (FIv.mem_thin H.hi) hKup) (by simp [FIv.mul, FIv.thin, hUok])
      rw [ite_eq_left_of_eq_true _ _ (eq_true ((pos_iff _).mp h0))] at up
      exact up.trans hp.2
    · have hp := (mem_mul (FIv.mem_thin H.hi) hKlo) (by simp [FIv.mul, FIv.thin, hLok])
      rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => h0 ((pos_iff _).mpr h)))] at up
      exact up.trans hp.2

/-! ## Tip cells (product integration across the ridge) -/

/-- Enclosures of `λ`, `λ²`, `1/λ²`, `1/(2λ)` for an integer `λ`. -/
structure LamC where
  /-- `λ`. -/
  lamI : FIv
  /-- `λ²`. -/
  lam2I : FIv
  /-- `1/λ²`. -/
  ilam2I : FIv
  /-- `1/(2λ)`. -/
  ihlamI : FIv

/-- The constants for `λ ∈ ℕ`. -/
@[expose] def lamC (lam : ℕ) : LamC :=
  ⟨FIv.ofInt lam, FIv.ofInt ((lam : ℤ) ^ 2), FIv.ofFrac 1 ((lam : ℤ) ^ 2), FIv.ofFrac 1 (2 * lam)⟩

/-- Membership of the `λ` constants. -/
structure LamMem (L : LamC) (lam : ℝ) : Prop where
  hl : L.lamI.Mem lam
  hl2 : L.lam2I.Mem (lam ^ 2)
  hil2 : L.ilam2I.Mem (1 / lam ^ 2)
  hihl : L.ihlamI.Mem (1 / (2 * lam))

/-- Soundness of the `λ` constants. -/
theorem mem_lamC (lam : ℕ) : LamMem (lamC lam) lam := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [lamC] using mem_ofInt (lam : ℤ)
  · exact memOfEq (mem_ofInt ((lam : ℤ) ^ 2)) (by push_cast; ring)
  · exact memOfEq (mem_ofFrac 1 ((lam : ℤ) ^ 2)) (by push_cast; ring)
  · simpa [lamC] using mem_ofFrac 1 (2 * (lam : ℤ))

/-- Validity gate: keep the bounds, require the extra flag. -/
@[expose] def gate (b : Bool) (I : FIv) : FIv := ⟨I.lo, I.hi, b && I.ok⟩

/-- Gating preserves membership. -/
theorem mem_gate {b : Bool} {I : FIv} {x : ℝ} (h : I.Mem x) : (gate b I).Mem x := by
  intro hok
  simp only [gate, Bool.and_eq_true] at hok
  exact h hok.2

/-- `±` choice of the arc orientation. -/
@[expose] def sgn (neg : Bool) (x : ℝ) : ℝ := if neg then -x else x

/-- `±` choice on enclosures. -/
@[expose] def sgnI (neg : Bool) (I : FIv) : FIv := if neg then I.neg else I

/-- Soundness of the orientation sign on enclosures. -/
theorem mem_sgnI {neg : Bool} {I : FIv} {x : ℝ} (h : I.Mem x) : (sgnI neg I).Mem (sgn neg x) := by
  unfold sgnI sgn; cases neg
  · exact h
  · exact mem_neg h

/-- The orientation sign does not change squares. -/
theorem sgn_sq (neg : Bool) (x : ℝ) : sgn neg x ^ 2 = x ^ 2 := by
  unfold sgn; cases neg <;> simp

/-- The orientation sign is continuous. -/
theorem continuous_sgn (neg : Bool) : Continuous (sgn neg) := by
  unfold sgn; cases neg <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

/-- Endpoint numerators `pa = 2i - N`, `pb = 2i + 2 - N` of the `i`-th cell of `[-1, 1]`. -/
@[expose] def pA (N i : ℕ) : ℤ := 2 * i - N
/-- Upper endpoint numerator. -/
@[expose] def pB (N i : ℕ) : ℤ := 2 * i + 2 - N

/-- The core enclosures on a tip cell (rotated angle `χ' = ±arctan t`). -/
@[expose] def tipCore (L : LamC) (K K2 DI : FIv) (z : ZIv) (N i : ℕ) (neg : Bool) : CoreIv :=
  coreEval (if neg then 1 else 0) L.lamI L.ilam2I L.ihlamI K K2 DI z
    (sgnI neg (spCell N (pA N i) (pB N i))) (sgnI neg (evenCell cpPt N (pA N i) (pB N i)))

/-- The kernel data of a tip cell: validity flag and the two Lorentzian kernel enclosures
(`D = α + γ t²` with `α = a²/λ²`, `γ = α + (P/λ²) g²`). -/
@[expose] def tipKer (c : CoreIv) (N i : ℕ) : Bool × FIv × FIv :=
  let G := c.a2.add (c.P.mul c.g.sq)
  (c.a2.ok && G.ok, lorentzIv N (pA N i) (pB N i) c.a2.lo G.lo,
    lorentzIv N (pA N i) (pB N i) c.a2.hi G.hi)

/-- **A tip cell**: product-integration bounds for `∫_{pa/N}^{pb/N} H/(gp2 (1+t²)/λ²)`. -/
@[expose] def tipCell (L : LamC) (K K2 DI : FIv) (z : ZIv) (N i : ℕ) (neg : Bool) :
    FIv × FIv × FIv :=
  let c := tipCore L K K2 DI z N i neg
  let kr := tipKer c N i
  (gate kr.1 (prodB c.hB kr.2.1 kr.2.2), gate kr.1 (prodB c.hX kr.2.1 kr.2.2),
    gate kr.1 (prodB c.hZ kr.2.1 kr.2.2))

/-! ### Real side of a tip cell -/

/-- `sin χ` on a tip arc. -/
@[expose] def tipS (k s2 : ℝ) (neg : Bool) (t : ℝ) : ℝ :=
  s1r k (sgn neg (spA t)) (sgn neg (cpA t)) s2
/-- `cos χ` on a tip arc. -/
@[expose] def tipC (k s2 : ℝ) (neg : Bool) (t : ℝ) : ℝ :=
  c1r k (sgn neg (spA t)) (sgn neg (cpA t)) s2
/-- The scaled denominator `gp2 · (1 + t²)/λ²` on a tip arc. -/
@[expose] def tipD (lam k s2 c2 : ℝ) (neg : Bool) (t : ℝ) : ℝ :=
  gp2 (1 / 4) 4 lam k (tipS k s2 neg t) (tipC k s2 neg t) s2 c2 / lam ^ 2 * (1 + t ^ 2)

/-- `sin²(arctan t)(1+t²) = t²`. -/
theorem spA_sq_mul (t : ℝ) : spA t ^ 2 * (1 + t ^ 2) = t ^ 2 := by
  have h : 0 < 1 + t ^ 2 := by positivity
  unfold spA
  rw [div_pow, Real.sq_sqrt h.le]
  field_simp

/-- `sin²χ'(1+t²) = t²` on both tip arcs. -/
theorem sgn_spA_sq_mul (neg : Bool) (t : ℝ) :
    sgn neg (spA t) ^ 2 * (1 + t ^ 2) = t ^ 2 := by rw [sgn_sq]; exact spA_sq_mul t

/-- Continuity of `spA`. -/
theorem continuous_spA : Continuous spA := by
  unfold spA
  exact continuous_id.div (by fun_prop) (fun t => (Real.sqrt_pos.2 (by positivity)).ne')

/-- Continuity of `cpA`. -/
theorem continuous_cpA : Continuous cpA := by
  unfold cpA
  exact continuous_const.div (by fun_prop) (fun t => (Real.sqrt_pos.2 (by positivity)).ne')

/-- `cpA > 0`. -/
theorem cpA_pos (t : ℝ) : 0 < cpA t := by
  unfold cpA; exact div_pos one_pos (Real.sqrt_pos.2 (by positivity))

/-- **Exact Lorentzian form of the tip denominator**: `D = α + (α + (P/λ²) g²) t²`. -/
theorem tipD_eq (lam k s2 c2 : ℝ) (neg : Bool) (t : ℝ) (hk : k ^ 2 < 1) :
    tipD lam k s2 c2 neg t =
      aSq k (tipS k s2 neg t) (tipC k s2 neg t) s2 c2 / lam ^ 2 +
        (aSq k (tipS k s2 neg t) (tipC k s2 neg t) s2 c2 / lam ^ 2 +
          PR lam k (tipS k s2 neg t) s2 / lam ^ 2 *
            gsel (if neg then 1 else 0) k (sgn neg (spA t)) (sgn neg (cpA t)) s2 ^ 2) * t ^ 2 := by
  have hsc : sgn neg (spA t) ^ 2 + sgn neg (cpA t) ^ 2 = 1 := by
    rw [sgn_sq, sgn_sq]; exact spA_sq_add_cpA_sq t
  have hf := fR_eq_sel (mode := if neg then 1 else 0) (s2 := s2) hk hsc
    (fun h => by cases neg <;> simp at h; simp [sgn]; linarith [cpA_pos t])
    (fun h => by cases neg <;> simp at h; simp [sgn]; linarith [cpA_pos t])
  have hspf : spf (if neg then 1 else 0) (sgn neg (spA t)) = sgn neg (spA t) := by
    unfold spf; cases neg <;> simp
  have hsq := sgn_spA_sq_mul neg t
  unfold tipD tipS tipC
  rw [gp2_rot lam hk hsc c2, hf, hspf]
  linear_combination (PR lam k (s1r k (sgn neg (spA t)) (sgn neg (cpA t)) s2) s2 / lam ^ 2 *
    gsel (if neg then 1 else 0) k (sgn neg (spA t)) (sgn neg (cpA t)) s2 ^ 2) * hsq

/-- The tip-arc parametrization satisfies the hypotheses of `continuous_closed`. -/
theorem tip_paramOK {k s2 c2 : ℝ} (neg : Bool) (hk0 : 0 < k) (hk : k ^ 2 < 1)
    (hc2 : |c2| ≤ 1) :
    ParamOK (fun t => tipS k s2 neg t) (fun t => tipC k s2 neg t) (fun _ => s2) (fun _ => c2)
      k := by
  have hs : Continuous (fun t => sgn neg (spA t)) := (continuous_sgn neg).comp continuous_spA
  have hc : Continuous (fun t => sgn neg (cpA t)) := (continuous_sgn neg).comp continuous_cpA
  refine ⟨?_, ?_, continuous_const, continuous_const, fun t => ?_, fun _ => hc2, hk0, hk⟩
  · unfold tipS s1r; fun_prop
  · unfold tipC c1r; fun_prop
  · unfold tipS tipC
    refine s1r_sq_add_c1r_sq hk ?_
    rw [sgn_sq, sgn_sq]; exact spA_sq_add_cpA_sq t

/-- Pointwise core membership on a tip cell. -/
theorem tipCore_mem {L : LamC} {K K2 DI : FIv} {z : ZIv} {N i : ℕ} {neg : Bool}
    {lam dI k s2 c2 : ℝ} (hL : LamMem L lam) (hl : lam ≠ 0) (hK : K.Mem k) (hK2 : K2.Mem (k ^ 2))
    (hDI : DI.Mem dI) (hz : ZMem z k s2 c2) (hk0 : 0 < k) (hk : k ^ 2 < 1) (hN : 0 < N)
    {t : ℝ} (ht : t ∈ Set.Icc ((pA N i : ℝ) / N) ((pB N i : ℝ) / N)) :
    CoreMem (tipCore L K K2 DI z N i neg) (if neg then 1 else 0) lam dI k (sgn neg (spA t))
      (sgn neg (cpA t)) s2 c2 :=
  mem_coreEval hL.hl hl hL.hil2 hL.hihl hK hK2 hDI hz (mem_sgnI (mem_spCell hN ht))
    (mem_sgnI (mem_cpCell hN ht)) hk0.le hk (by rw [sgn_sq, sgn_sq]; exact spA_sq_add_cpA_sq t)
    (fun h => by cases neg <;> simp at h; simp [sgn]; linarith [cpA_pos t])
    (fun h => by cases neg <;> simp at h; simp [sgn]; linarith [cpA_pos t])

/-- **Kernel facts of a tip cell**: when the kernel enclosures are valid, they enclose
Lorentzian kernels whose quadratic forms squeeze the tip denominator on the whole cell. -/
theorem tipKer_facts {L : LamC} {K K2 DI : FIv} {z : ZIv} {N i : ℕ} {neg : Bool}
    {lam dI k s2 c2 : ℝ} (hL : LamMem L lam) (hl : lam ≠ 0) (hK : K.Mem k)
    (hK2 : K2.Mem (k ^ 2))
    (hDI : DI.Mem dI) (hz : ZMem z k s2 c2) (hk0 : 0 < k) (hk : k ^ 2 < 1) (hN : 0 < N)
    (hok : (tipKer (tipCore L K K2 DI z N i neg) N i).1 = true)
    (hok1 : (tipKer (tipCore L K K2 DI z N i neg) N i).2.1.ok = true) :
    ∃ αl γl αh γh : ℝ, 0 < αl ∧ 0 < γl ∧
      (∀ t ∈ Set.Icc ((pA N i : ℝ) / N) ((pB N i : ℝ) / N),
        αl + γl * t ^ 2 ≤ tipD lam k s2 c2 neg t ∧ tipD lam k s2 c2 neg t ≤ αh + γh * t ^ 2) ∧
      (tipKer (tipCore L K K2 DI z N i neg) N i).2.1.Mem
        (lorentzK ((pA N i : ℝ) / N) ((pB N i : ℝ) / N) αl γl) ∧
      (tipKer (tipCore L K K2 DI z N i neg) N i).2.2.Mem
        (lorentzK ((pA N i : ℝ) / N) ((pB N i : ℝ) / N) αh γh) := by
  have hcm := fun t (ht : t ∈ Set.Icc ((pA N i : ℝ) / N) ((pB N i : ℝ) / N)) =>
    tipCore_mem (neg := neg) hL hl hK hK2 hDI hz hk0 hk hN ht
  unfold tipKer at hok hok1 ⊢
  dsimp only at hok hok1 ⊢
  simp only [Bool.and_eq_true] at hok
  obtain ⟨okA, okG⟩ := hok
  simp only [lorentzIv, Bool.and_eq_true] at hok1
  refine ⟨_, _, _, _, fxVal_pos (of_decide_eq_true hok1.1.1.2),
    fxVal_pos (of_decide_eq_true hok1.1.2), fun t ht => ?_, mem_lorentzIv _ _ _ _ _,
    mem_lorentzIv _ _ _ _ _⟩
  obtain ⟨-, -, -, ha2, hP, hg, -⟩ := hcm t ht
  have mA := ha2 okA
  have mG := (mem_add ha2 (mem_mul hP (mem_sq hg))) okG
  rw [tipD_eq lam k s2 c2 neg t hk]
  have ht2 := sq_nonneg t
  simp only [tipS, tipC] at ⊢
  constructor
  · nlinarith [mA.1, mG.1, mul_le_mul_of_nonneg_right mG.1 ht2]
  · nlinarith [mA.2, mG.2, mul_le_mul_of_nonneg_right mG.2 ht2]

/-- Cell endpoints are ordered. -/
theorem pA_le_pB (N i : ℕ) : (pA N i : ℝ) / N ≤ (pB N i : ℝ) / N := by
  unfold pA pB
  push_cast
  exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg N)

/-- One component of a tip cell (generic numerator). -/
theorem tip_component {L : LamC} {K K2 DI : FIv} {z : ZIv} {N i : ℕ} {neg : Bool}
    {lam dI k s2 c2 : ℝ} (hL : LamMem L lam) (hK : K.Mem k) (hK2 : K2.Mem (k ^ 2))
    (hDI : DI.Mem dI) (hz : ZMem z k s2 c2) (hk0 : 0 < k) (hk : k ^ 2 < 1) (hN : 0 < N)
    (hc2 : |c2| ≤ 1) (hl : lam ≠ 0) (sel : CoreIv → FIv) (Hf : ℝ → ℝ)
    (hHm : ∀ t ∈ Set.Icc ((pA N i : ℝ) / N) ((pB N i : ℝ) / N),
      (sel (tipCore L K K2 DI z N i neg)).Mem (Hf t))
    (hHc : Continuous Hf) :
    (gate (tipKer (tipCore L K K2 DI z N i neg) N i).1
      (prodB (sel (tipCore L K K2 DI z N i neg))
        (tipKer (tipCore L K K2 DI z N i neg) N i).2.1
        (tipKer (tipCore L K K2 DI z N i neg) N i).2.2)).Mem
      (∫ t in ((pA N i : ℝ) / N)..((pB N i : ℝ) / N), Hf t / tipD lam k s2 c2 neg t) := by
  intro hok
  simp only [gate, Bool.and_eq_true] at hok
  obtain ⟨hk1, hp⟩ := hok
  have hp' := hp
  simp only [prodB, Bool.and_eq_true] at hp'
  obtain ⟨αl, γl, αh, γh, hαl, hγl, hD, hKu, hKl⟩ :=
    tipKer_facts hL hl hK hK2 hDI hz hk0 hk hN hk1 hp'.1.2
  have hPO := tip_paramOK (s2 := s2) neg hk0 hk hc2
  have hDc : Continuous (fun t => tipD lam k s2 c2 neg t) := by
    unfold tipD
    exact ((continuous_closed (dI := 0) hPO hl).2.2.2.div_const (lam ^ 2)).mul (by fun_prop)
  exact (mem_prodB (pA_le_pB N i) hHc.continuousOn hDc.continuousOn hαl hγl
    (fun t ht => (hD t ht).1) (fun t ht => (hD t ht).2) hHm hKu hKl) hp

/-- **Soundness of a tip cell** (all three numerators). -/
theorem mem_tipCell {L : LamC} {K K2 DI : FIv} {z : ZIv} {N i : ℕ} {neg : Bool}
    {lam dI k s2 c2 : ℝ} (hL : LamMem L lam) (hK : K.Mem k) (hK2 : K2.Mem (k ^ 2))
    (hDI : DI.Mem dI) (hz : ZMem z k s2 c2) (hk0 : 0 < k) (hk : k ^ 2 < 1) (hN : 0 < N)
    (hc2 : |c2| ≤ 1) (hl : lam ≠ 0) :
    (tipCell L K K2 DI z N i neg).1.Mem (∫ t in ((pA N i : ℝ) / N)..((pB N i : ℝ) / N),
      lam ^ 2 * HB lam k (tipS k s2 neg t) (tipC k s2 neg t) s2 c2 / tipD lam k s2 c2 neg t) ∧
    (tipCell L K K2 DI z N i neg).2.1.Mem (∫ t in ((pA N i : ℝ) / N)..((pB N i : ℝ) / N),
      lam ^ 2 * HX lam dI k (tipS k s2 neg t) (tipC k s2 neg t) s2 c2 / tipD lam k s2 c2 neg t) ∧
    (tipCell L K K2 DI z N i neg).2.2.Mem (∫ t in ((pA N i : ℝ) / N)..((pB N i : ℝ) / N),
      lam ^ 2 * HZ lam dI k (tipS k s2 neg t) (tipC k s2 neg t) s2 c2 /
        tipD lam k s2 c2 neg t) := by
  have hPO := tip_paramOK (s2 := s2) neg hk0 hk hc2
  have hcont := continuous_closed (lam := lam) (dI := dI) hPO hl
  have hcm := fun t (ht : t ∈ Set.Icc ((pA N i : ℝ) / N) ((pB N i : ℝ) / N)) =>
    tipCore_mem (neg := neg) hL hl hK hK2 hDI hz hk0 hk hN ht
  refine ⟨?_, ?_, ?_⟩
  · exact tip_component hL hK hK2 hDI hz hk0 hk hN hc2 hl CoreIv.hB _
      (fun t ht => (hcm t ht).hB) (continuous_const.mul hcont.1)
  · exact tip_component hL hK hK2 hDI hz hk0 hk hN hc2 hl CoreIv.hX _
      (fun t ht => (hcm t ht).hX) (continuous_const.mul hcont.2.1)
  · exact tip_component hL hK hK2 hDI hz hk0 hk hN hc2 hl CoreIv.hZ _
      (fun t ht => (hcm t ht).hZ) (continuous_const.mul hcont.2.2.1)

/-! ## Side cells (no peak: plain interval quadrature) -/

/-- `sin χ` on a side arc (`χ' = ±π/2 - arctan u`). -/
@[expose] def sideS (k s2 : ℝ) (neg : Bool) (u : ℝ) : ℝ :=
  s1r k (sgn neg (cpA u)) (sgn neg (spA u)) s2
/-- `cos χ` on a side arc. -/
@[expose] def sideC (k s2 : ℝ) (neg : Bool) (u : ℝ) : ℝ :=
  c1r k (sgn neg (cpA u)) (sgn neg (spA u)) s2

/-- The core enclosures on a side cell. -/
@[expose] def sideCore (L : LamC) (K K2 DI : FIv) (z : ZIv) (N i : ℕ) (neg : Bool) : CoreIv :=
  coreEval 2 L.lamI L.ilam2I L.ihlamI K K2 DI z
    (sgnI neg (evenCell cpPt N (pA N i) (pB N i))) (sgnI neg (spCell N (pA N i) (pB N i)))

/-- Plain cell bound `width · H · gp2⁻¹ · w` on a side cell. -/
@[expose] def sideB (H G W : FIv) (N : ℕ) : FIv := ((H.mul G.inv).mul W).mul (FIv.ofFrac 2 N)

/-- **A side cell**: plain interval bounds for `∫_{pa/N}^{pb/N} H/(gp2 (1+u²))`. -/
@[expose] def sideCell (L : LamC) (K K2 DI : FIv) (z : ZIv) (N i : ℕ) (neg : Bool) :
    FIv × FIv × FIv :=
  let c := sideCore L K K2 DI z N i neg
  let W := evenCell wPt N (pA N i) (pB N i)
  (sideB c.hB c.gp2 W N, sideB c.hX c.gp2 W N, sideB c.hZ c.gp2 W N)

/-- The side-arc parametrization satisfies the hypotheses of `continuous_closed`. -/
theorem side_paramOK {k s2 c2 : ℝ} (neg : Bool) (hk0 : 0 < k) (hk : k ^ 2 < 1)
    (hc2 : |c2| ≤ 1) :
    ParamOK (fun u => sideS k s2 neg u) (fun u => sideC k s2 neg u) (fun _ => s2) (fun _ => c2)
      k := by
  have hs : Continuous (fun t => sgn neg (spA t)) := (continuous_sgn neg).comp continuous_spA
  have hc : Continuous (fun t => sgn neg (cpA t)) := (continuous_sgn neg).comp continuous_cpA
  refine ⟨?_, ?_, continuous_const, continuous_const, fun t => ?_, fun _ => hc2, hk0, hk⟩
  · unfold sideS s1r; fun_prop
  · unfold sideC c1r; fun_prop
  · unfold sideS sideC
    refine s1r_sq_add_c1r_sq hk ?_
    rw [sgn_sq, sgn_sq, add_comm]; exact spA_sq_add_cpA_sq t

/-- Integral of a function enclosed by a constant interval on `[a, b]`. -/
theorem mem_integral_const {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    {I Wd : FIv} (hI : ∀ t ∈ Set.Icc a b, I.Mem (f t)) (hW : Wd.Mem (b - a)) :
    (I.mul Wd).Mem (∫ t in a..b, f t) := by
  have hba : 0 < b - a := by linarith
  have hint := hf.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab.le
  have key : I.Mem ((∫ t in a..b, f t) / (b - a)) := by
    intro hok
    have lo : (b - a) * fxVal I.lo ≤ ∫ t in a..b, f t := by
      have := intervalIntegral.integral_mono_on hab.le intervalIntegrable_const hint
        (fun t ht => ((hI t ht) hok).1)
      simpa [intervalIntegral.integral_const, smul_eq_mul] using this
    have hi : ∫ t in a..b, f t ≤ (b - a) * fxVal I.hi := by
      have := intervalIntegral.integral_mono_on hab.le hint intervalIntegrable_const
        (fun t ht => ((hI t ht) hok).2)
      simpa [intervalIntegral.integral_const, smul_eq_mul] using this
    constructor
    · rw [le_div_iff₀ hba]; linarith
    · rw [div_le_iff₀ hba]; linarith
  exact memOfEq (mem_mul key hW) (by field_simp)

/-- Cell width `2/N`. -/
theorem width_eq (N i : ℕ) (hN : 0 < N) :
    (pB N i : ℝ) / N - (pA N i : ℝ) / N = ((2 : ℤ) : ℝ) / ((N : ℤ) : ℝ) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold pA pB; push_cast; field_simp; ring

/-- Cell endpoints are strictly ordered. -/
theorem pA_lt_pB (N i : ℕ) (hN : 0 < N) : (pA N i : ℝ) / N < (pB N i : ℝ) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold pA pB; push_cast
  exact div_lt_div_of_pos_right (by linarith) hN'

/-- **Soundness of a side cell.** -/
theorem mem_sideCell {L : LamC} {K K2 DI : FIv} {z : ZIv} {N i : ℕ} {neg : Bool}
    {lam dI k s2 c2 : ℝ} (hL : LamMem L lam) (hK : K.Mem k) (hK2 : K2.Mem (k ^ 2))
    (hDI : DI.Mem dI) (hz : ZMem z k s2 c2) (hk0 : 0 < k) (hk : k ^ 2 < 1) (hN : 0 < N)
    (hc2 : |c2| ≤ 1) (hl : lam ≠ 0) :
    (sideCell L K K2 DI z N i neg).1.Mem (∫ u in ((pA N i : ℝ) / N)..((pB N i : ℝ) / N),
      lam ^ 2 * HB lam k (sideS k s2 neg u) (sideC k s2 neg u) s2 c2 /
        (gp2 (1 / 4) 4 lam k (sideS k s2 neg u) (sideC k s2 neg u) s2 c2 / lam ^ 2) * wA u) ∧
    (sideCell L K K2 DI z N i neg).2.1.Mem (∫ u in ((pA N i : ℝ) / N)..((pB N i : ℝ) / N),
      lam ^ 2 * HX lam dI k (sideS k s2 neg u) (sideC k s2 neg u) s2 c2 /
        (gp2 (1 / 4) 4 lam k (sideS k s2 neg u) (sideC k s2 neg u) s2 c2 / lam ^ 2) * wA u) ∧
    (sideCell L K K2 DI z N i neg).2.2.Mem (∫ u in ((pA N i : ℝ) / N)..((pB N i : ℝ) / N),
      lam ^ 2 * HZ lam dI k (sideS k s2 neg u) (sideC k s2 neg u) s2 c2 /
        (gp2 (1 / 4) 4 lam k (sideS k s2 neg u) (sideC k s2 neg u) s2 c2 / lam ^ 2) * wA u) := by
  have hPO := side_paramOK (s2 := s2) neg hk0 hk hc2
  have hcont := continuous_closed (lam := lam) (dI := dI) hPO hl
  have hgpos := fun u => gp2_pos_param (lam := lam) hPO hl u
  have hwc : Continuous wA := by
    unfold wA; exact continuous_const.div (by fun_prop) (fun t => by positivity)
  have hcm : ∀ u ∈ Set.Icc ((pA N i : ℝ) / N) ((pB N i : ℝ) / N),
      CoreMem (sideCore L K K2 DI z N i neg) 2 lam dI k (sgn neg (cpA u)) (sgn neg (spA u)) s2
        c2 :=
    fun u hu => mem_coreEval hL.hl hl hL.hil2 hL.hihl hK hK2 hDI hz
      (mem_sgnI (mem_cpCell hN hu)) (mem_sgnI (mem_spCell hN hu)) hk0.le hk
      (by rw [sgn_sq, sgn_sq, add_comm]; exact spA_sq_add_cpA_sq u) (by omega) (by omega)
  have hW : (FIv.ofFrac 2 N).Mem ((pB N i : ℝ) / N - (pA N i : ℝ) / N) := by
    rw [width_eq N i hN]; exact mem_ofFrac 2 N
  have gen : ∀ (sel : CoreIv → FIv) (Hf : ℝ → ℝ), Continuous Hf →
      (∀ u ∈ Set.Icc ((pA N i : ℝ) / N) ((pB N i : ℝ) / N),
        (sel (sideCore L K K2 DI z N i neg)).Mem (Hf u)) →
      (sideB (sel (sideCore L K K2 DI z N i neg)) (sideCore L K K2 DI z N i neg).gp2
        (evenCell wPt N (pA N i) (pB N i)) N).Mem
        (∫ u in ((pA N i : ℝ) / N)..((pB N i : ℝ) / N),
          Hf u / (gp2 (1 / 4) 4 lam k (sideS k s2 neg u) (sideC k s2 neg u) s2 c2 / lam ^ 2) *
            wA u) := by
    intro sel Hf hHc hHm
    refine mem_integral_const (pA_lt_pB N i hN) ?_ (fun u hu => ?_) hW
    · exact ((hHc.div (hcont.2.2.2.div_const (lam ^ 2)) (fun u => (div_pos (hgpos u)
        (by positivity)).ne')).mul hwc).continuousOn
    · exact memOfEq (mem_mul (mem_mul (hHm u hu) (mem_inv (hcm u hu).gp2)) (mem_wCell hN hu))
        (by rw [div_eq_mul_inv]; rfl)
  exact ⟨gen CoreIv.hB _ (continuous_const.mul hcont.1) (fun u hu => (hcm u hu).hB),
    gen CoreIv.hX _ (continuous_const.mul hcont.2.1) (fun u hu => (hcm u hu).hX),
    gen CoreIv.hZ _ (continuous_const.mul hcont.2.2.1) (fun u hu => (hcm u hu).hZ)⟩

/-! ## Sums over cells -/

/-- Sums of enclosures enclose sums. -/
theorem mem_sumIv {c : ℕ → FIv} {x : ℕ → ℝ} (N : ℕ) (h : ∀ i < N, (c i).Mem (x i)) :
    (sumIv c N).Mem (∑ i ∈ Finset.range N, x i) := by
  induction N with
  | zero => intro _; simp [sumIv, fxVal]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact mem_add (ih (fun i hi => h i (by omega))) (h n (by omega))

/-- Consecutive cells share endpoints. -/
theorem cell_endpoints (N : ℕ) (i : ℕ) : (pB N i : ℝ) / N = (pA N (i + 1) : ℝ) / N := by
  unfold pA pB; push_cast; ring_nf

/-- **Uniform-cell sum on `[-1, 1]`**: cell enclosures of the cell integrals give an enclosure
of the whole integral. -/
theorem mem_sum_cells {g : ℝ → ℝ} {c : ℕ → FIv} {N : ℕ} (hN : 0 < N) (hg : Continuous g)
    (hc : ∀ i < N, (c i).Mem (∫ x in ((pA N i : ℝ) / N)..((pB N i : ℝ) / N), g x)) :
    (sumIv c N).Mem (∫ x in (-1 : ℝ)..1, g x) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have e := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := MeasureTheory.volume)
    (a := fun i => (pA N i : ℝ) / N) (n := N) (fun i _ => hg.intervalIntegrable _ _)
  have a0 : (pA N 0 : ℝ) / N = -1 := by unfold pA; push_cast; field_simp; ring
  have aN : (pA N N : ℝ) / N = 1 := by unfold pA; push_cast; field_simp; ring
  rw [a0, aN] at e
  rw [← e]
  refine mem_sumIv N (fun i hi => ?_)
  rw [← cell_endpoints]
  exact hc i hi

/-- Componentwise sum of triples of enclosures. -/
@[expose] def sum3 (f : ℕ → FIv × FIv × FIv) : ℕ → FIv × FIv × FIv
  | 0 => (⟨0, 0, true⟩, ⟨0, 0, true⟩, ⟨0, 0, true⟩)
  | n + 1 => ((sum3 f n).1.add (f n).1, (sum3 f n).2.1.add (f n).2.1,
      (sum3 f n).2.2.add (f n).2.2)

/-- Componentwise addition of triples. -/
@[expose] def add3 (a b : FIv × FIv × FIv) : FIv × FIv × FIv :=
  (a.1.add b.1, a.2.1.add b.2.1, a.2.2.add b.2.2)

/-- Selection of a component of a triple. -/
@[expose] def pick (j : Fin 3) (r : FIv × FIv × FIv) : FIv :=
  if j = 0 then r.1 else if j = 1 then r.2.1 else r.2.2

/-- Component of a triple sum. -/
theorem pick_sum3 (j : Fin 3) (f : ℕ → FIv × FIv × FIv) (N : ℕ) :
    pick j (sum3 f N) = sumIv (fun i => pick j (f i)) N := by
  induction N with
  | zero => unfold pick sum3 sumIv; split_ifs <;> rfl
  | succ n ih =>
    rw [show sumIv (fun i => pick j (f i)) (n + 1) =
      (sumIv (fun i => pick j (f i)) n).add (pick j (f n)) from rfl, ← ih,
      show sum3 f (n + 1) = ((sum3 f n).1.add (f n).1, (sum3 f n).2.1.add (f n).2.1,
        (sum3 f n).2.2.add (f n).2.2) from rfl]
    unfold pick; split_ifs <;> rfl

/-- Component of a triple addition. -/
theorem pick_add3 (j : Fin 3) (a b : FIv × FIv × FIv) :
    pick j (add3 a b) = (pick j a).add (pick j b) := by
  unfold pick add3; split_ifs <;> rfl

/-! ## The inner (poloidal) integral over the four arcs -/

/-- Numerator selector: `HB`, `HX`, `HZ`. -/
@[expose] def Hsel (j : Fin 3) (lam dI k s1 c1 s2 c2 : ℝ) : ℝ :=
  if j = 0 then lam ^ 2 * HB lam k s1 c1 s2 c2 else if j = 1 then lam ^ 2 * HX lam dI k s1 c1 s2 c2
  else lam ^ 2 * HZ lam dI k s1 c1 s2 c2

/-- Continuity of the selected numerator along a parametrization. -/
theorem cont_Hsel {X : Type*} [TopologicalSpace X] {s1 c1 s2 c2 : X → ℝ} {k lam dI : ℝ}
    (j : Fin 3) (P : ParamOK s1 c1 s2 c2 k) (hl : lam ≠ 0) :
    Continuous (fun x => Hsel j lam dI k (s1 x) (c1 x) (s2 x) (c2 x)) := by
  have h := continuous_closed (lam := lam) (dI := dI) P hl
  unfold Hsel
  split_ifs
  · exact continuous_const.mul h.1
  · exact continuous_const.mul h.2.1
  · exact continuous_const.mul h.2.2.1

/-- Selected component of a tip cell. -/
theorem mem_tipCell_pick (j : Fin 3) {L : LamC} {K K2 DI : FIv} {z : ZIv} {N i : ℕ}
    {neg : Bool} {lam dI k s2 c2 : ℝ} (hL : LamMem L lam) (hK : K.Mem k)
    (hK2 : K2.Mem (k ^ 2)) (hDI : DI.Mem dI) (hz : ZMem z k s2 c2) (hk0 : 0 < k)
    (hk : k ^ 2 < 1) (hN : 0 < N) (hc2 : |c2| ≤ 1) (hl : lam ≠ 0) :
    (pick j (tipCell L K K2 DI z N i neg)).Mem
      (∫ t in ((pA N i : ℝ) / N)..((pB N i : ℝ) / N),
        Hsel j lam dI k (tipS k s2 neg t) (tipC k s2 neg t) s2 c2 / tipD lam k s2 c2 neg t) := by
  have h := mem_tipCell (neg := neg) (i := i) hL hK hK2 hDI hz hk0 hk hN hc2 hl
  unfold pick Hsel
  split_ifs
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- Selected component of a side cell. -/
theorem mem_sideCell_pick (j : Fin 3) {L : LamC} {K K2 DI : FIv} {z : ZIv} {N i : ℕ}
    {neg : Bool} {lam dI k s2 c2 : ℝ} (hL : LamMem L lam) (hK : K.Mem k)
    (hK2 : K2.Mem (k ^ 2)) (hDI : DI.Mem dI) (hz : ZMem z k s2 c2) (hk0 : 0 < k)
    (hk : k ^ 2 < 1) (hN : 0 < N) (hc2 : |c2| ≤ 1) (hl : lam ≠ 0) :
    (pick j (sideCell L K K2 DI z N i neg)).Mem
      (∫ u in ((pA N i : ℝ) / N)..((pB N i : ℝ) / N),
        Hsel j lam dI k (sideS k s2 neg u) (sideC k s2 neg u) s2 c2 /
          (gp2 (1 / 4) 4 lam k (sideS k s2 neg u) (sideC k s2 neg u) s2 c2 / lam ^ 2) * wA u) := by
  have h := mem_sideCell (neg := neg) (i := i) hL hK hK2 hDI hz hk0 hk hN hc2 hl
  unfold pick Hsel
  split_ifs
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- **The inner integral enclosure**: four arcs of the rotated angle, tip arcs by product
integration (`ntip` cells each), side arcs by plain cells (`nside` cells each). -/
@[expose] def innerSum (L : LamC) (K K2 DI : FIv) (z : ZIv) (ntip nside : ℕ) :
    FIv × FIv × FIv :=
  add3 (add3 (sum3 (fun i => tipCell L K K2 DI z ntip i false) ntip)
      (sum3 (fun i => tipCell L K K2 DI z ntip i true) ntip))
    (add3 (sum3 (fun i => sideCell L K K2 DI z nside i false) nside)
      (sum3 (fun i => sideCell L K K2 DI z nside i true) nside))

/-- The angle `φ = arcsin(sin φ)` of the ridge rotation. -/
@[expose] def phiR (k s2 : ℝ) : ℝ := arcsin (sphr k s2)

/-- `sin φ` of the ridge rotation. -/
theorem sin_phiR {k s2 : ℝ} (hk : k ^ 2 < 1) : sin (phiR k s2) = sphr k s2 := by
  have h := sphr_sq_add_cphr_sq (s2 := s2) hk
  have hc := cphr_pos (s2 := s2) hk
  unfold phiR
  exact sin_arcsin (by nlinarith [sq_nonneg (sphr k s2 + 1)])
    (by nlinarith [sq_nonneg (sphr k s2 - 1)])

/-- `cos φ` of the ridge rotation. -/
theorem cos_phiR {k s2 : ℝ} (hk : k ^ 2 < 1) : cos (phiR k s2) = cphr k s2 := by
  have h := sphr_sq_add_cphr_sq (s2 := s2) hk
  have hc := cphr_pos (s2 := s2) hk
  unfold phiR
  rw [cos_arcsin, show 1 - sphr k s2 ^ 2 = cphr k s2 ^ 2 by linarith, Real.sqrt_sq hc.le]

open PlasmaLean.Certificates.ValidatedQuadrature (integral_periodic_shift
  integral_eq_quarter_arcs sin_arctan_add_pi cos_arctan_add_pi sin_pi_div_two_sub_arctan
  cos_pi_div_two_sub_arctan sin_neg_pi_div_two_sub_arctan cos_neg_pi_div_two_sub_arctan)

/-- The rotated-circle parametrization satisfies the hypotheses of `continuous_closed`. -/
theorem rot_paramOK {k s2 c2 : ℝ} (hk0 : 0 < k) (hk : k ^ 2 < 1) (hc2 : |c2| ≤ 1) :
    ParamOK (fun x => s1r k (sin x) (cos x) s2) (fun x => c1r k (sin x) (cos x) s2)
      (fun _ => s2) (fun _ => c2) k := by
  refine ⟨?_, ?_, continuous_const, continuous_const, fun x => ?_, fun _ => hc2, hk0, hk⟩
  · unfold s1r; fun_prop
  · unfold c1r; fun_prop
  · exact s1r_sq_add_c1r_sq hk (sin_sq_add_cos_sq x)

/-- **Soundness of the inner integral enclosure.** For every `s2`, `c2` with `|c2| ≤ 1`
enclosed by the `ζ`-data, the integral over a full period of the poloidal angle of
`Hsel j / gp2` lies in the `j`-th component of `innerSum`. -/
theorem mem_inner (j : Fin 3) {L : LamC} {K K2 DI : FIv} {z : ZIv} {ntip nside : ℕ}
    {lam dI k s2 c2 : ℝ} (hL : LamMem L lam) (hK : K.Mem k) (hK2 : K2.Mem (k ^ 2))
    (hDI : DI.Mem dI) (hz : ZMem z k s2 c2) (hk0 : 0 < k) (hk : k ^ 2 < 1)
    (hnt : 0 < ntip) (hns : 0 < nside) (hc2 : |c2| ≤ 1) (hl : lam ≠ 0) :
    (pick j (innerSum L K K2 DI z ntip nside)).Mem
      (∫ χ in (-π)..π, Hsel j lam dI k (sin χ) (cos χ) s2 c2 /
        (gp2 (1 / 4) 4 lam k (sin χ) (cos χ) s2 c2 / lam ^ 2)) := by
  set G : ℝ → ℝ := fun x => Hsel j lam dI k (s1r k (sin x) (cos x) s2) (c1r k (sin x) (cos x) s2)
    s2 c2 / (gp2 (1 / 4) 4 lam k (s1r k (sin x) (cos x) s2) (c1r k (sin x) (cos x) s2) s2 c2 /
      lam ^ 2) with hGdef
  have hPO := rot_paramOK (s2 := s2) hk0 hk hc2
  have hG : Continuous G := (cont_Hsel j hPO hl).div ((cont_gp2 hPO).div_const (lam ^ 2))
    (fun x => (div_pos (gp2_pos_param hPO hl x) (by positivity)).ne')
  have hGp : Function.Periodic G (2 * π) := by
    intro x; simp only [hGdef, sin_add_two_pi, cos_add_two_pi]
  have hshift : ∫ χ in (-π)..π, Hsel j lam dI k (sin χ) (cos χ) s2 c2 /
      (gp2 (1 / 4) 4 lam k (sin χ) (cos χ) s2 c2 / lam ^ 2) = ∫ x in (-π)..π, G x := by
    rw [← integral_periodic_shift (f := fun χ => Hsel j lam dI k (sin χ) (cos χ) s2 c2 /
      (gp2 (1 / 4) 4 lam k (sin χ) (cos χ) s2 c2 / lam ^ 2)) (fun x => by
        simp only [sin_add_two_pi, cos_add_two_pi]) (phiR k s2)]
    congr 1; funext x
    simp only [hGdef, sin_add, cos_add, sin_phiR hk, cos_phiR hk, s1r, c1r]
  rw [hshift, integral_eq_quarter_arcs hG hGp]
  -- arc integrands
  have hsq : ∀ t : ℝ, 0 < 1 + t ^ 2 := fun t => by positivity
  have eT : ∀ (neg : Bool) (t : ℝ),
      G (if neg then arctan t + π else arctan t) / (1 + t ^ 2) =
        Hsel j lam dI k (tipS k s2 neg t) (tipC k s2 neg t) s2 c2 / tipD lam k s2 c2 neg t := by
    intro neg t
    have hs : sin (if neg then arctan t + π else arctan t) = sgn neg (spA t) := by
      cases neg
      · simp [sgn, spA, sin_arctan]
      · simp only [ite_true, sgn, spA]; rw [sin_arctan_add_pi]
    have hc : cos (if neg then arctan t + π else arctan t) = sgn neg (cpA t) := by
      cases neg
      · simp [sgn, cpA, cos_arctan]
      · simp only [ite_true, sgn, cpA]; rw [cos_arctan_add_pi]
    simp only [hGdef, hs, hc, tipD, tipS, tipC]
    rw [div_div]
  have eS : ∀ (neg : Bool) (u : ℝ),
      G (if neg then -(π / 2) - arctan u else π / 2 - arctan u) / (1 + u ^ 2) =
        Hsel j lam dI k (sideS k s2 neg u) (sideC k s2 neg u) s2 c2 /
          (gp2 (1 / 4) 4 lam k (sideS k s2 neg u) (sideC k s2 neg u) s2 c2 / lam ^ 2) * wA u := by
    intro neg u
    have hs : sin (if neg then -(π / 2) - arctan u else π / 2 - arctan u) = sgn neg (cpA u) := by
      cases neg
      · simp only [Bool.false_eq_true, ite_false, sgn, cpA]; rw [sin_pi_div_two_sub_arctan]
      · simp only [ite_true, sgn, cpA]; rw [sin_neg_pi_div_two_sub_arctan]
    have hc : cos (if neg then -(π / 2) - arctan u else π / 2 - arctan u) = sgn neg (spA u) := by
      cases neg
      · simp only [Bool.false_eq_true, ite_false, sgn, spA]; rw [cos_pi_div_two_sub_arctan]
      · simp only [ite_true, sgn, spA]; rw [cos_neg_pi_div_two_sub_arctan]
    simp only [hGdef, hs, hc, sideS, sideC, wA]
    rw [mul_one_div, div_div]
  -- split the arc integrals
  have cT : ∀ neg : Bool, Continuous (fun t => G (if neg then arctan t + π else arctan t) /
      (1 + t ^ 2)) := by
    intro neg
    cases neg <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
      exact (hG.comp (by fun_prop)).div (by fun_prop) (fun t => (hsq t).ne')
  have cS : ∀ neg : Bool, Continuous (fun u => G (if neg then -(π / 2) - arctan u
      else π / 2 - arctan u) / (1 + u ^ 2)) := by
    intro neg
    cases neg <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
      exact (hG.comp (by fun_prop)).div (by fun_prop) (fun t => (hsq t).ne')
  have split1 : ∫ t in (-1 : ℝ)..1, (G (arctan t) + G (arctan t + π)) / (1 + t ^ 2) =
      (∫ t in (-1 : ℝ)..1, G (if false then arctan t + π else arctan t) / (1 + t ^ 2)) +
        ∫ t in (-1 : ℝ)..1, G (if true then arctan t + π else arctan t) / (1 + t ^ 2) := by
    rw [← intervalIntegral.integral_add ((cT false).intervalIntegrable _ _)
      ((cT true).intervalIntegrable _ _)]
    congr 1; funext t; simp only [Bool.false_eq_true, ite_false, ite_true]; ring
  have split2 : ∫ u in (-1 : ℝ)..1, (G (π / 2 - arctan u) + G (-(π / 2) - arctan u)) /
      (1 + u ^ 2) =
      (∫ u in (-1 : ℝ)..1, G (if false then -(π / 2) - arctan u else π / 2 - arctan u) /
        (1 + u ^ 2)) +
        ∫ u in (-1 : ℝ)..1, G (if true then -(π / 2) - arctan u else π / 2 - arctan u) /
          (1 + u ^ 2) := by
    rw [← intervalIntegral.integral_add ((cS false).intervalIntegrable _ _)
      ((cS true).intervalIntegrable _ _)]
    congr 1; funext t; simp only [Bool.false_eq_true, ite_false, ite_true]; ring
  rw [split1, split2]
  unfold innerSum
  rw [pick_add3, pick_add3, pick_add3, pick_sum3, pick_sum3, pick_sum3, pick_sum3]
  have arcT : ∀ neg : Bool, (sumIv (fun i => pick j (tipCell L K K2 DI z ntip i neg)) ntip).Mem
      (∫ t in (-1 : ℝ)..1, G (if neg then arctan t + π else arctan t) / (1 + t ^ 2)) := by
    intro neg
    refine mem_sum_cells hnt (cT neg) (fun i _ => ?_)
    have := mem_tipCell_pick j (neg := neg) (i := i) hL hK hK2 hDI hz hk0 hk hnt hc2 hl
    simpa only [eT] using this
  have arcS : ∀ neg : Bool, (sumIv (fun i => pick j (sideCell L K K2 DI z nside i neg)) nside).Mem
      (∫ u in (-1 : ℝ)..1, G (if neg then -(π / 2) - arctan u else π / 2 - arctan u) /
        (1 + u ^ 2)) := by
    intro neg
    refine mem_sum_cells hns (cS neg) (fun i _ => ?_)
    have := mem_sideCell_pick j (neg := neg) (i := i) hL hK hK2 hDI hz hk0 hk hns hc2 hl
    simpa only [eS] using this
  exact mem_add (mem_add (arcT false) (arcT true)) (mem_add (arcS false) (arcS true))

/-! ## The outer (toroidal) integral -/

open PlasmaLean.Certificates.ValidatedQuadrature (integral_comp_two_mul_periodic
  continuous_parametric_integral)

/-- `(sin 2ζ, cos 2ζ)` on the four outer arcs, as functions of the arc variable. -/
@[expose] def arcS2 (a : Fin 4) (v : ℝ) : ℝ :=
  if a = 0 then spA v else if a = 1 then -spA v else if a = 2 then cpA v else -cpA v
/-- `cos 2ζ` on the four outer arcs. -/
@[expose] def arcC2 (a : Fin 4) (v : ℝ) : ℝ :=
  if a = 0 then cpA v else if a = 1 then -cpA v else if a = 2 then spA v else -spA v

/-- Enclosures of `(sin 2ζ, cos 2ζ)` on outer cell `i` of arc `a`. -/
@[expose] def arcSC (a : Fin 4) (N i : ℕ) : FIv × FIv :=
  let S := spCell N (pA N i) (pB N i)
  let C := evenCell cpPt N (pA N i) (pB N i)
  if a = 0 then (S, C) else if a = 1 then (S.neg, C.neg) else if a = 2 then (C, S)
  else (C.neg, S.neg)

/-- Soundness of the outer-arc enclosures of `(sin 2ζ, cos 2ζ)`. -/
theorem mem_arcSC (a : Fin 4) {N i : ℕ} (hN : 0 < N) {v : ℝ}
    (hv : v ∈ Set.Icc ((pA N i : ℝ) / N) ((pB N i : ℝ) / N)) :
    (arcSC a N i).1.Mem (arcS2 a v) ∧ (arcSC a N i).2.Mem (arcC2 a v) := by
  have hS := mem_spCell hN hv
  have hC := mem_cpCell hN hv
  unfold arcSC arcS2 arcC2
  split_ifs
  · exact ⟨hS, hC⟩
  · exact ⟨mem_neg hS, mem_neg hC⟩
  · exact ⟨hC, hS⟩
  · exact ⟨mem_neg hC, mem_neg hS⟩

/-- `|cos 2ζ| ≤ 1` on the outer arcs. -/
theorem arcC2_abs_le (a : Fin 4) (v : ℝ) : |arcC2 a v| ≤ 1 := by
  have h := spA_sq_add_cpA_sq v
  have hs : |spA v| ≤ 1 := abs_le_one_iff_mul_self_le_one.mpr (by nlinarith [sq_nonneg (cpA v)])
  have hc : |cpA v| ≤ 1 := abs_le_one_iff_mul_self_le_one.mpr (by nlinarith [sq_nonneg (spA v)])
  unfold arcC2
  split_ifs <;> (try rw [abs_neg]) <;> assumption

/-- Scaling of a triple by an enclosure. -/
@[expose] def mul3 (r : FIv × FIv × FIv) (W : FIv) : FIv × FIv × FIv :=
  (r.1.mul W, r.2.1.mul W, r.2.2.mul W)

/-- Component of a scaled triple. -/
theorem pick_mul3 (j : Fin 3) (r : FIv × FIv × FIv) (W : FIv) :
    pick j (mul3 r W) = (pick j r).mul W := by
  unfold pick mul3; split_ifs <;> rfl

/-- Contribution of one outer arc (`N2` cells). -/
@[expose] def outerArc (L : LamC) (K K2 DI : FIv) (ntip nside N2 : ℕ) (a : Fin 4) :
    FIv × FIv × FIv :=
  sum3 (fun i => mul3 (mul3 (innerSum L K K2 DI (zEval K2 (arcSC a N2 i).1 (arcSC a N2 i).2)
    ntip nside) (evenCell wPt N2 (pA N2 i) (pB N2 i))) (FIv.ofFrac 2 N2)) N2

/-- **The two-dimensional enclosure**: four outer arcs of `t = 2ζ`. -/
@[expose] def outerSum (L : LamC) (K K2 DI : FIv) (ntip nside N2 : ℕ) : FIv × FIv × FIv :=
  add3 (add3 (outerArc L K K2 DI ntip nside N2 0) (outerArc L K K2 DI ntip nside N2 1))
    (add3 (outerArc L K K2 DI ntip nside N2 2) (outerArc L K K2 DI ntip nside N2 3))

/-- The surface integral `∫∫ Hsel_j / gp2 dχ dζ` over `[-π, π]²`. -/
@[expose] def IntR (j : Fin 3) (lam dI k : ℝ) : ℝ :=
  ∫ ζ in (-π)..π, ∫ χ in (-π)..π, Hsel j lam dI k (sin χ) (cos χ) (sin (2 * ζ)) (cos (2 * ζ)) /
    (gp2 (1 / 4) 4 lam k (sin χ) (cos χ) (sin (2 * ζ)) (cos (2 * ζ)) / lam ^ 2)

/-- The inner integral as a function of `(sin t, cos t) = (s2, c2)`. -/
@[expose] def gIn (j : Fin 3) (lam dI k s2 c2 : ℝ) : ℝ :=
  ∫ χ in (-π)..π, Hsel j lam dI k (sin χ) (cos χ) s2 c2 /
    (gp2 (1 / 4) 4 lam k (sin χ) (cos χ) s2 c2 / lam ^ 2)

/-- Continuity of the inner integral along a continuous circle parametrization. -/
theorem continuous_gIn_circle (j : Fin 3) {lam dI k : ℝ} (hk0 : 0 < k) (hk : k ^ 2 < 1)
    (hl : lam ≠ 0) {s c : ℝ → ℝ} (hs : Continuous s) (hc : Continuous c)
    (hb : ∀ t, |c t| ≤ 1) : Continuous (fun t => gIn j lam dI k (s t) (c t)) := by
  have hPO : ParamOK (fun p : ℝ × ℝ => sin p.1) (fun p => cos p.1) (fun p => s p.2)
      (fun p => c p.2) k :=
    ⟨by fun_prop, by fun_prop, hs.comp continuous_snd, hc.comp continuous_snd,
      fun p => sin_sq_add_cos_sq p.1, fun p => hb p.2, hk0, hk⟩
  have hF := (cont_Hsel j (dI := dI) hPO hl).div ((cont_gp2 hPO).div_const (lam ^ 2))
    (fun p => (div_pos (gp2_pos_param hPO hl p) (by positivity)).ne')
  refine continuous_parametric_integral (F := fun χ t =>
    Hsel j lam dI k (sin χ) (cos χ) (s t) (c t) /
      (gp2 (1 / 4) 4 lam k (sin χ) (cos χ) (s t) (c t) / lam ^ 2)) ?_ (-π) π
  exact hF

/-- **Soundness of one outer arc.** -/
theorem mem_outerArc (j : Fin 3) (a : Fin 4) {L : LamC} {K K2 DI : FIv} {ntip nside N2 : ℕ}
    {lam dI k : ℝ} (hL : LamMem L lam) (hK : K.Mem k) (hK2 : K2.Mem (k ^ 2)) (hDI : DI.Mem dI)
    (hk0 : 0 < k) (hk : k ^ 2 < 1) (hnt : 0 < ntip) (hns : 0 < nside) (hN2 : 0 < N2)
    (hl : lam ≠ 0) :
    (pick j (outerArc L K K2 DI ntip nside N2 a)).Mem
      (∫ v in (-1 : ℝ)..1, gIn j lam dI k (arcS2 a v) (arcC2 a v) * wA v) := by
  have hsc : Continuous (arcS2 a) := by
    unfold arcS2; split_ifs
    · exact continuous_spA
    · exact continuous_spA.neg
    · exact continuous_cpA
    · exact continuous_cpA.neg
  have hcc : Continuous (arcC2 a) := by
    unfold arcC2; split_ifs
    · exact continuous_cpA
    · exact continuous_cpA.neg
    · exact continuous_spA
    · exact continuous_spA.neg
  have hwc : Continuous wA := by
    unfold wA; exact continuous_const.div (by fun_prop) (fun t => by positivity)
  have hg := continuous_gIn_circle j (dI := dI) hk0 hk hl hsc hcc (arcC2_abs_le a)
  unfold outerArc
  rw [pick_sum3]
  refine mem_sum_cells hN2 (hg.mul hwc) (fun i _ => ?_)
  rw [pick_mul3, pick_mul3]
  have hW : (FIv.ofFrac 2 N2).Mem ((pB N2 i : ℝ) / N2 - (pA N2 i : ℝ) / N2) := by
    rw [width_eq N2 i hN2]; exact mem_ofFrac 2 N2
  refine mem_integral_const (pA_lt_pB N2 i hN2) (hg.mul hwc).continuousOn (fun v hv => ?_) hW
  obtain ⟨hS, hC⟩ := mem_arcSC a hN2 hv
  have hz := mem_zEval hK2 hS hC hk
  exact mem_mul (mem_inner j hL hK hK2 hDI hz hk0 hk hnt hns (arcC2_abs_le a v) hl)
    (mem_wCell hN2 hv)

/-- **Soundness of the two-dimensional enclosure**: the surface integral `IntR j` lies in the
`j`-th component of `outerSum`. -/
theorem mem_outer (j : Fin 3) {L : LamC} {K K2 DI : FIv} {ntip nside N2 : ℕ} {lam dI k : ℝ}
    (hL : LamMem L lam) (hK : K.Mem k) (hK2 : K2.Mem (k ^ 2)) (hDI : DI.Mem dI)
    (hk0 : 0 < k) (hk : k ^ 2 < 1) (hnt : 0 < ntip) (hns : 0 < nside) (hN2 : 0 < N2)
    (hl : lam ≠ 0) : (pick j (outerSum L K K2 DI ntip nside N2)).Mem (IntR j lam dI k) := by
  set g : ℝ → ℝ := fun t => gIn j lam dI k (sin t) (cos t) with hgdef
  have hg : Continuous g := continuous_gIn_circle j hk0 hk hl continuous_sin continuous_cos
    (fun t => abs_cos_le_one t)
  have hgp : Function.Periodic g (2 * π) := by
    intro t; simp only [hgdef, sin_add_two_pi, cos_add_two_pi]
  have e1 : IntR j lam dI k = ∫ t in (-π)..π, g t := by
    rw [← integral_comp_two_mul_periodic hg hgp]; rfl
  rw [e1, integral_eq_quarter_arcs hg hgp]
  have hsq : ∀ t : ℝ, 0 < 1 + t ^ 2 := fun t => by positivity
  have ea : ∀ (a : Fin 4) (v : ℝ), gIn j lam dI k (arcS2 a v) (arcC2 a v) * wA v =
      g (if a = 0 then arctan v else if a = 1 then arctan v + π else
        if a = 2 then π / 2 - arctan v else -(π / 2) - arctan v) / (1 + v ^ 2) := by
    intro a v
    simp only [hgdef, wA, mul_one_div]
    congr 2
    · unfold arcS2; split_ifs
      · rw [sin_arctan]; rfl
      · rw [sin_arctan_add_pi]; rfl
      · rw [sin_pi_div_two_sub_arctan]; rfl
      · rw [sin_neg_pi_div_two_sub_arctan]; rfl
    · unfold arcC2; split_ifs
      · rw [cos_arctan]; rfl
      · rw [cos_arctan_add_pi]; rfl
      · rw [cos_pi_div_two_sub_arctan]; rfl
      · rw [cos_neg_pi_div_two_sub_arctan]; rfl
  have arc : ∀ a : Fin 4, (pick j (outerArc L K K2 DI ntip nside N2 a)).Mem
      (∫ v in (-1 : ℝ)..1, g (if a = 0 then arctan v else if a = 1 then arctan v + π else
        if a = 2 then π / 2 - arctan v else -(π / 2) - arctan v) / (1 + v ^ 2)) := by
    intro a
    have := mem_outerArc j a hL hK hK2 hDI hk0 hk hnt hns hN2 hl
    simpa only [ea] using this
  have ci : ∀ f : ℝ → ℝ, Continuous f →
      IntervalIntegrable (fun v => g (f v) / (1 + v ^ 2)) MeasureTheory.volume (-1) 1 :=
    fun f hf => ((hg.comp hf).div (by fun_prop) (fun v => (hsq v).ne')).intervalIntegrable _ _
  have s1 : ∫ t in (-1 : ℝ)..1, (g (arctan t) + g (arctan t + π)) / (1 + t ^ 2) =
      (∫ t in (-1 : ℝ)..1, g (arctan t) / (1 + t ^ 2)) +
        ∫ t in (-1 : ℝ)..1, g (arctan t + π) / (1 + t ^ 2) := by
    rw [← intervalIntegral.integral_add (ci _ (by fun_prop)) (ci _ (by fun_prop))]
    congr 1; funext t; ring
  have s2 : ∫ u in (-1 : ℝ)..1, (g (π / 2 - arctan u) + g (-(π / 2) - arctan u)) / (1 + u ^ 2) =
      (∫ t in (-1 : ℝ)..1, g (π / 2 - arctan t) / (1 + t ^ 2)) +
        ∫ t in (-1 : ℝ)..1, g (-(π / 2) - arctan t) / (1 + t ^ 2) := by
    rw [← intervalIntegral.integral_add (ci _ (by fun_prop)) (ci _ (by fun_prop))]
    congr 1; funext t; ring
  rw [s1, s2]
  unfold outerSum
  rw [pick_add3, pick_add3, pick_add3]
  have a0 := arc 0
  have a1 := arc 1
  have a2 := arc 2
  have a3 := arc 3
  simp only [Fin.isValue, ite_true, show (1 : Fin 4) ≠ 0 by simp, show (2 : Fin 4) ≠ 0 by simp,
    show (3 : Fin 4) ≠ 0 by simp, show (2 : Fin 4) ≠ 1 by simp,
    show (3 : Fin 4) ≠ 1 by simp, show (3 : Fin 4) ≠ 2 by simp, ite_false] at a0 a1 a2 a3
  exact mem_add (mem_add a0 a1) (mem_add a2 a3)

/-! ## One-dimensional integrals -/

open PlasmaLean.Design.LandremanFamily2Labels
open PlasmaLean.Design.SolovevMercierQuadrature (Ycell Wcell mem_cells wt rep_sin)

/-- Enclosure of `c = √(1 - k² + k² y²)`. -/
@[expose] def evc (K2 Y : FIv) : FIv := ((c1I.sub K2).add (K2.mul Y.sq)).sqrt
/-- Enclosure of `σ = 4 - arcsin(k y/c)`. -/
@[expose] def evsig (K K2 Y : FIv) : FIv := c4I.sub (FIv.asinFast ((K.mul Y).mul (evc K2 Y).inv))
/-- Enclosure of `h(σ) = √(4σ² + 1/16)`. -/
@[expose] def evh (K K2 Y : FIv) : FIv := ((c4I.mul (evsig K K2 Y).sq).add sixteenthI).sqrt

/-- Enclosure of the `F₁` integrand. -/
@[expose] def evF1 (K K2 Y : FIv) : FIv := ((evh K K2 Y).mul (evc K2 Y)).inv
/-- Enclosure of the `F₁'` integrand. -/
@[expose] def evF1k (K K2 Y : FIv) : FIv :=
  ((((c4I.mul (evsig K K2 Y)).mul Y).mul (((evh K K2 Y).sq.mul (c1I.sub K2).sqrt).inv)).add
    (K.mul (c1I.sub Y.sq))).mul ((evh K K2 Y).mul ((evc K2 Y).sq.mul (evc K2 Y))).inv
/-- Enclosure of `√(cosh²(y/8) - k²)`. -/
@[expose] def evtz (K2 Y : FIv) : FIv := ((FIv.coshSmall (eighthI.mul Y)).sq.sub K2).sqrt
/-- Enclosure of the `Z` integrand. -/
@[expose] def evZ (K2 Y : FIv) : FIv := (evtz K2 Y).inv
/-- Enclosure of the `Z'` integrand. -/
@[expose] def evZk (K K2 Y : FIv) : FIv := K.mul ((evtz K2 Y).sq.mul (evtz K2 Y)).inv
/-- Enclosure of `√(1 - k² y²)`. -/
@[expose] def evte (K2 Y : FIv) : FIv := (c1I.sub (K2.mul Y.sq)).sqrt
/-- Enclosure of the `E` integrand. -/
@[expose] def evE (K2 Y : FIv) : FIv := (evte K2 Y).inv
/-- Enclosure of the `E'` integrand. -/
@[expose] def evEk (K K2 Y : FIv) : FIv := (K.mul Y.sq).mul ((evte K2 Y).sq.mul (evte K2 Y)).inv

section OneDMem
variable {K K2 Y : FIv} {k y : ℝ} (hK : K.Mem k) (hK2 : K2.Mem (k ^ 2)) (hY : Y.Mem y)
include hK2 hY

/-- Soundness of the enclosure of `c`. -/
theorem mem_evc : (evc K2 Y).Mem (cK k y) :=
  mem_sqrt (mem_add (mem_sub mem_c1 hK2) (mem_mul hK2 (mem_sq hY)))

include hK in
/-- Soundness of the enclosure of `σ`. -/
theorem mem_evsig : (evsig K K2 Y).Mem (sigF 4 k y) :=
  mem_sub mem_c4 (mem_asinFast (memOfEq (mem_mul (mem_mul hK hY) (mem_inv (mem_evc hK2 hY)))
    (by rw [← div_eq_mul_inv])))

include hK in
/-- Soundness of the enclosure of `h(σ)`. -/
theorem mem_evh : (evh K K2 Y).Mem (hfun (1 / 4) (sigF 4 k y)) :=
  memOfEq (mem_sqrt (mem_add (mem_mul mem_c4 (mem_sq (mem_evsig hK hK2 hY))) mem_sixteenth))
    (by unfold hfun; norm_num)

include hK in
/-- Soundness of the `F₁` integrand enclosure. -/
theorem mem_evF1 : (evF1 K K2 Y).Mem (fF1 (1 / 4) 4 k y) :=
  mem_inv (mem_mul (mem_evh hK hK2 hY) (mem_evc hK2 hY))

include hK in
/-- Soundness of the `F₁'` integrand enclosure. -/
theorem mem_evF1k : (evF1k K K2 Y).Mem (fF1k (1 / 4) 4 k y) := by
  have hc := mem_evc hK2 hY
  have hs := mem_evsig hK hK2 hY
  have hh := mem_evh hK hK2 hY
  refine memOfEq (mem_mul (mem_add (mem_mul (mem_mul (mem_mul mem_c4 hs) hY)
    (mem_inv (mem_mul (mem_sq hh) (mem_sqrt (mem_sub mem_c1 hK2)))))
    (mem_mul hK (mem_sub mem_c1 (mem_sq hY)))) (mem_inv (mem_mul hh (mem_mul (mem_sq hc) hc))))
    ?_
  unfold fF1k
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, ← pow_succ]

/-- Soundness of the enclosure of `√(cosh² - k²)`. -/
theorem mem_evtz : (evtz K2 Y).Mem (√(tZ (1 / 4) k y)) := by
  have h := mem_coshSmall (mem_mul mem_eighth hY)
  refine memOfEq (mem_sqrt (mem_sub (mem_sq h) hK2)) ?_
  unfold tZ
  rw [show (1 : ℝ) / 4 * y / 2 = 1 / 8 * y by ring]

/-- Soundness of the `Z` integrand enclosure. -/
theorem mem_evZ : (evZ K2 Y).Mem (fZ (1 / 4) k y) := mem_inv (mem_evtz hK2 hY)

include hK in
/-- Soundness of the `Z'` integrand enclosure. -/
theorem mem_evZk : (evZk K K2 Y).Mem (fZk (1 / 4) k y) := by
  have h := mem_evtz hK2 hY
  refine memOfEq (mem_mul hK (mem_inv (mem_mul (mem_sq h) h))) ?_
  unfold fZk; rw [← div_eq_mul_inv, ← pow_succ]

/-- Soundness of the enclosure of `√(1 - k² y²)`. -/
theorem mem_evte : (evte K2 Y).Mem (√(1 - k ^ 2 * y ^ 2)) :=
  mem_sqrt (mem_sub mem_c1 (mem_mul hK2 (mem_sq hY)))

/-- Soundness of the `E` integrand enclosure. -/
theorem mem_evE : (evE K2 Y).Mem (fE k y) := mem_inv (mem_evte hK2 hY)

include hK in
/-- Soundness of the `E'` integrand enclosure. -/
theorem mem_evEk : (evEk K K2 Y).Mem (fEk k y) := by
  have h := mem_evte hK2 hY
  refine memOfEq (mem_mul (mem_mul hK (mem_sq hY)) (mem_inv (mem_mul (mem_sq h) h))) ?_
  unfold fEk; rw [← div_eq_mul_inv, ← pow_succ]

end OneDMem

/-- One-dimensional quadrature of `∫_{-π}^{π} f(sin t) dt` from a cell evaluation `ev`
(`N` cells of `[0, 1]` in `τ = tan(t/2)`, symmetrized in `y ↦ -y`). -/
@[expose] def quad1 (ev : FIv → FIv) (N : ℕ) : FIv :=
  (sumIv (fun i => ((ev (Ycell N i)).add (ev (Ycell N i).neg)).mul (Wcell N i)) N).divInt N

/-- **Soundness of the one-dimensional quadrature.** -/
theorem mem_quad1 {ev : FIv → FIv} {f : ℝ → ℝ} {N : ℕ} (hN : 0 < N)
    (hf : ContinuousOn f (Set.Icc (-1) 1)) (hev : ∀ {Y : FIv} {y : ℝ}, Y.Mem y → (ev Y).Mem (f y)) :
    (quad1 ev N).Mem (∫ t in (-π)..π, f (sin t)) := by
  obtain ⟨hrep, hint⟩ := rep_sin (g := fun y => f y + f (-y)) hf (fun y _ => rfl)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hS := fxScale_pos
  unfold quad1
  refine memOfEq (mem_divInt (x := (N : ℝ) * ∫ t in (-π)..π, f (sin t)) ?_ N) ?_
  · intro hok
    obtain ⟨b1, b2⟩ := integral_mem_sumIv hN _ hint (fun i hi τ hτ => by
      obtain ⟨hy, hw⟩ := mem_cells hN hi hτ
      exact mem_mul (mem_add (hev hy) (hev (mem_neg hy))) hw) hok
    rw [← hrep] at b1 b2
    unfold fxVal
    constructor
    · rw [div_le_iff₀ hS]
      rw [div_le_iff₀ (by positivity)] at b1
      linarith
    · rw [le_div_iff₀ hS]
      rw [le_div_iff₀ (by positivity)] at b2
      linarith
  · push_cast; field_simp

/-! ## The per-cell Mercier checker -/

open PlasmaLean.Design.SolovevMercierQuadrature (Ecell mem_Ecell)

/-- The certified real quantities on the surface `k` (closed forms in terms of `F₁, Z, E` and
their `k`-derivatives, and the surface integrals `IntR`): `ψ_t'(ψ)`. -/
@[expose] def tpR (lam k : ℝ) : ℝ := F1 (1 / 4) 4 k * ((4 * π) * lam)⁻¹
/-- `ι'` (toroidal-flux label). -/
@[expose] def iotapR (lam k : ℝ) : ℝ :=
  ((Zd (1 / 4) k * F1 (1 / 4) 4 k - Zint (1 / 4) k * F1d (1 / 4) 4 k) * (F1 (1 / 4) 4 k ^ 2)⁻¹) *
    (k * tpR lam k)⁻¹
/-- `s_ψ μ₀ p' V''`. -/
@[expose] def wellR (lam k : ℝ) : ℝ :=
  (-((4 * π) * (lam * F1 (1 / 4) 4 k)⁻¹)) *
    ((((2 * π) * ((Zd (1 / 4) k * Eint k * F1 (1 / 4) 4 k +
      Zint (1 / 4) k * Ed k * F1 (1 / 4) 4 k) - Zint (1 / 4) k * Eint k * F1d (1 / 4) 4 k)) *
      (F1 (1 / 4) 4 k ^ 2)⁻¹) * (k * tpR lam k)⁻¹)
/-- `dI = λ - I' = -2E/(λF₁)`. -/
@[expose] def dIR (lam k : ℝ) : ℝ := -((2 * Eint k) * (lam * F1 (1 / 4) 4 k)⁻¹)
/-- `1/ψ_t'`. -/
@[expose] def itpR (lam k : ℝ) : ℝ := ((4 * π) * lam) * (F1 (1 / 4) 4 k)⁻¹
/-- `1/ψ_t'³`. -/
@[expose] def c3R (lam k : ℝ) : ℝ := itpR lam k ^ 2 * itpR lam k
/-- `∫ B² dS/|∇ψ_t|³`. -/
@[expose] def B2R (lam k : ℝ) : ℝ := IntR 0 lam (dIR lam k) k * c3R lam k / lam ^ 4
/-- `∫ B·Ξ dS/|∇ψ_t|³`. -/
@[expose] def BXiR (lam k : ℝ) : ℝ := IntR 1 lam (dIR lam k) k * c3R lam k / lam ^ 4
/-- `∫ |Ξ|² dS/|∇ψ_t|³`. -/
@[expose] def Xi2R (lam k : ℝ) : ℝ := IntR 2 lam (dIR lam k) k * c3R lam k / lam ^ 4
/-- `(2π)⁶ D_Merc` for the sign `s_G`. -/
@[expose] def D6R (lam k sG : ℝ) : ℝ :=
  (sG * ((2 * π ^ 2) * iotapR lam k) - BXiR lam k) ^ 2 +
    (wellR lam k - Xi2R lam k) * B2R lam k

/-- The interval data computed by the checker for a `k`-cell. -/
structure CheckData where
  /-- `(2π)⁶ D` for `s_G = +1`. -/
  Dp : FIv
  /-- `(2π)⁶ D` for `s_G = -1`. -/
  Dm : FIv

/-- The six one-dimensional quadratures `F₁, F₁', Z, Z', E, E'` on a `k`-cell. -/
@[expose] def oneD (N1 : ℕ) (K : FIv) : FIv × FIv × FIv × FIv × FIv × FIv :=
  let K2 := K.sq
  (quad1 (evF1 K K2) N1, quad1 (evF1k K K2) N1, quad1 (evZ K2) N1, quad1 (evZk K K2) N1,
    quad1 (evE K2) N1, quad1 (evEk K K2) N1)

/-- Enclosure of `dI = λ - I' = -2E/(λF₁)`. -/
@[expose] def dIof (lam : ℕ) (F1 E : FIv) : FIv :=
  ((c2I.mul E).mul ((lamC lam).lamI.mul F1).inv).neg

/-- **The final combination** of the one-dimensional data `D` and the surface integrals `O`. -/
@[expose] def finalOf (lam : ℕ) (K : FIv) (D : FIv × FIv × FIv × FIv × FIv × FIv)
    (O : FIv × FIv × FIv) : CheckData :=
  let F1 := D.1
  let F1d := D.2.1
  let Z := D.2.2.1
  let Zd := D.2.2.2.1
  let E := D.2.2.2.2.1
  let Ed := D.2.2.2.2.2
  let lI := (lamC lam).lamI
  let itp := ((c4I.mul FIv.pi).mul lI).mul F1.inv
  let ktp := itp.mul K.inv
  let iotap := (((Zd.mul F1).sub (Z.mul F1d)).mul F1.sq.inv).mul ktp
  let well := (((c4I.mul FIv.pi).mul (lI.mul F1).inv).neg).mul
    ((((c2I.mul FIv.pi).mul ((((Zd.mul E).mul F1).add ((Z.mul Ed).mul F1)).sub
      ((Z.mul E).mul F1d))).mul F1.sq.inv).mul ktp)
  let c3 := itp.sq.mul itp
  let B2 := (O.1.mul c3).divInt ((lam : ℤ) ^ 4)
  let BXi := (O.2.1.mul c3).divInt ((lam : ℤ) ^ 4)
  let Xi2 := (O.2.2.mul c3).divInt ((lam : ℤ) ^ 4)
  let sh := (c2I.mul FIv.pi.sq).mul iotap
  let W := (well.sub Xi2).mul B2
  ⟨((c1I.mul sh).sub BXi).sq.add W, (((c1I.neg).mul sh).sub BXi).sq.add W⟩

/-- The checker on given data (positivity of both enclosures of `(2π)⁶ D`). -/
@[expose] def cellCheckOf (lam N1 ntip nside N2 : ℕ) (ka kb : ℚ)
    (D : FIv × FIv × FIv × FIv × FIv × FIv) (O : FIv × FIv × FIv) : Bool :=
  let d := finalOf lam (Ecell ka kb) D O
  decide (0 < ka) && decide (ka ≤ kb) && decide (kb ≤ 19 / 20) && decide (0 < lam) &&
    decide (0 < N1) && decide (0 < ntip) && decide (0 < nside) && decide (0 < N2) &&
    d.Dp.ok && d.Dm.ok && decide (0 < d.Dp.lo) && decide (0 < d.Dm.lo)

/-- **The per-cell checker** (integer `λ`, grids `N1` (1-D), `ntip`, `nside`, `N2`). -/
@[expose] def cellCheck (lam N1 ntip nside N2 : ℕ) (ka kb : ℚ) : Bool :=
  let D := oneD N1 (Ecell ka kb)
  cellCheckOf lam N1 ntip nside N2 ka kb D
    (outerSum (lamC lam) (Ecell ka kb) (Ecell ka kb).sq (dIof lam D.1 D.2.2.2.2.1) ntip nside N2)

/-- Field-wise equality test of enclosures. -/
@[expose] def eqF (I J : FIv) : Bool :=
  decide (I.lo = J.lo) && decide (I.hi = J.hi) && (I.ok == J.ok)

/-- Soundness of the field-wise equality test. -/
theorem eqF_sound {I J : FIv} (h : eqF I J = true) : I = J := by
  unfold eqF at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  cases I; cases J
  simp_all

/-- Equality test of triples of enclosures. -/
@[expose] def eq3 (a b : FIv × FIv × FIv) : Bool :=
  eqF a.1 b.1 && eqF a.2.1 b.2.1 && eqF a.2.2 b.2.2

/-- Soundness of the triple equality test. -/
theorem eq3_sound {a b : FIv × FIv × FIv} (h : eq3 a b = true) : a = b := by
  unfold eq3 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rcases a with ⟨a1, a2, a3⟩; rcases b with ⟨b1, b2, b3⟩
  simp only at h1 h2 h3
  rw [eqF_sound h1, eqF_sound h2, eqF_sound h3]

/-- Equality test of sextuples of enclosures. -/
@[expose] def eq6 (a b : FIv × FIv × FIv × FIv × FIv × FIv) : Bool :=
  eqF a.1 b.1 && eqF a.2.1 b.2.1 && eqF a.2.2.1 b.2.2.1 && eqF a.2.2.2.1 b.2.2.2.1 &&
    eqF a.2.2.2.2.1 b.2.2.2.2.1 && eqF a.2.2.2.2.2 b.2.2.2.2.2

/-- Soundness of the sextuple equality test. -/
theorem eq6_sound {a b : FIv × FIv × FIv × FIv × FIv × FIv} (h : eq6 a b = true) : a = b := by
  unfold eq6 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  rcases a with ⟨a1, a2, a3, a4, a5, a6⟩; rcases b with ⟨b1, b2, b3, b4, b5, b6⟩
  simp only at h1 h2 h3 h4 h5 h6
  rw [eqF_sound h1, eqF_sound h2, eqF_sound h3, eqF_sound h4, eqF_sound h5, eqF_sound h6]

/-- **Assembly from pieces**: if the one-dimensional data and the four outer-arc contributions
are known (each certified separately, e.g. by `decide +kernel` on `eq6`/`eq3`), the checker
reduces to the cheap final combination. -/
theorem cellCheck_of_pieces {lam N1 ntip nside N2 : ℕ} {ka kb : ℚ}
    {D : FIv × FIv × FIv × FIv × FIv × FIv} {O0 O1 O2 O3 : FIv × FIv × FIv}
    (hD : oneD N1 (Ecell ka kb) = D)
    (h0 : outerArc (lamC lam) (Ecell ka kb) (Ecell ka kb).sq (dIof lam D.1 D.2.2.2.2.1) ntip
      nside N2 0 = O0)
    (h1 : outerArc (lamC lam) (Ecell ka kb) (Ecell ka kb).sq (dIof lam D.1 D.2.2.2.2.1) ntip
      nside N2 1 = O1)
    (h2 : outerArc (lamC lam) (Ecell ka kb) (Ecell ka kb).sq (dIof lam D.1 D.2.2.2.2.1) ntip
      nside N2 2 = O2)
    (h3 : outerArc (lamC lam) (Ecell ka kb) (Ecell ka kb).sq (dIof lam D.1 D.2.2.2.2.1) ntip
      nside N2 3 = O3)
    (hF : cellCheckOf lam N1 ntip nside N2 ka kb D (add3 (add3 O0 O1) (add3 O2 O3)) = true) :
    cellCheck lam N1 ntip nside N2 ka kb = true := by
  unfold cellCheck outerSum
  simp only [hD]
  rw [h0, h1, h2, h3]
  exact hF

/-- Continuity in `y` of a jointly continuous integrand at fixed `k`. -/
theorem contOn_fix {f : ℝ → ℝ → ℝ} {S : Set (ℝ × ℝ)}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) S)
    {k : ℝ} (hS : ∀ y ∈ Set.Icc (-1 : ℝ) 1, (k, y) ∈ S) :
    ContinuousOn (fun y => f k y) (Set.Icc (-1) 1) :=
  hf.comp (by fun_prop : Continuous (fun y : ℝ => (k, y))).continuousOn (fun y hy => hS y hy)

/-- **Soundness of the per-cell checker**: acceptance proves `(2π)⁶ D_Merc > 0` for both
signs `s_G = ±1`, for every real `k` in the cell. -/
theorem cellCheck_sound {lam N1 ntip nside N2 : ℕ} {ka kb : ℚ}
    (h : cellCheck lam N1 ntip nside N2 ka kb = true) {k : ℝ} (hk1 : (ka : ℝ) ≤ k)
    (hk2 : k ≤ kb) : 0 < D6R lam k 1 ∧ 0 < D6R lam k (-1) := by
  unfold cellCheck cellCheckOf at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hka, hkab⟩, hkb⟩, hlam⟩, hN1⟩, hnt⟩, hns⟩, hN2⟩, okP⟩, okM⟩, posP⟩, posM⟩ := h
  have hk0 : 0 < k := lt_of_lt_of_le (by exact_mod_cast hka) hk1
  have hkb'' : (kb : ℝ) ≤ 19 / 20 := by
    rw [show (19 / 20 : ℝ) = ((19 / 20 : ℚ) : ℝ) by norm_num]; exact_mod_cast hkb
  have hkb' : k ≤ 19 / 20 := le_trans hk2 hkb''
  have hk : k ^ 2 < 1 := by nlinarith
  have hl : (lam : ℝ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hK : (Ecell ka kb).Mem k := mem_Ecell hk1 hk2
  have hK2 := mem_sq hK
  have hreg : ∀ y ∈ Set.Icc (-1 : ℝ) 1, (k, y) ∈ Kreg := fun _ _ => hk
  have hereg : ∀ y ∈ Set.Icc (-1 : ℝ) 1, (k, y) ∈ Ereg := fun y hy => ⟨hk, hy⟩
  have hF1 := mem_quad1 (f := fun y => fF1 (1 / 4) 4 k y) hN1
    (contOn_fix (continuousOn_fF1 (by norm_num)) hreg) (fun hY => mem_evF1 hK hK2 hY)
  have hF1d := mem_quad1 (f := fun y => fF1k (1 / 4) 4 k y) hN1
    (contOn_fix (continuousOn_fF1k (by norm_num)) hreg) (fun hY => mem_evF1k hK hK2 hY)
  have hZ := mem_quad1 (f := fun y => fZ (1 / 4) k y) hN1 (contOn_fix continuousOn_fZ hreg)
    (fun hY => mem_evZ hK2 hY)
  have hZd := mem_quad1 (f := fun y => fZk (1 / 4) k y) hN1 (contOn_fix continuousOn_fZk hreg)
    (fun hY => mem_evZk hK hK2 hY)
  have hE := mem_quad1 (f := fun y => fE k y) hN1 (contOn_fix continuousOn_fE hereg)
    (fun hY => mem_evE hK2 hY)
  have hEd := mem_quad1 (f := fun y => fEk k y) hN1 (contOn_fix continuousOn_fEk hereg)
    (fun hY => mem_evEk hK hK2 hY)
  have hL := mem_lamC lam
  have hDI := mem_neg (mem_mul (mem_mul mem_c2 hE) (mem_inv (mem_mul hL.hl hF1)))
  have hO := fun j => mem_outer j (ntip := ntip) (nside := nside) (N2 := N2) hL hK hK2 hDI hk0 hk
    hnt hns hN2 hl
  have hpi := FIv.mem_pi
  have hitp := mem_mul (mem_mul (mem_mul mem_c4 hpi) hL.hl) (mem_inv hF1)
  have hktp := mem_mul hitp (mem_inv hK)
  have hio := mem_mul (mem_mul (mem_sub (mem_mul hZd hF1) (mem_mul hZ hF1d)) (mem_inv (mem_sq hF1)))
    hktp
  have hwell := mem_mul (mem_neg (mem_mul (mem_mul mem_c4 hpi) (mem_inv (mem_mul hL.hl hF1))))
    (mem_mul (mem_mul (mem_mul (mem_mul mem_c2 hpi) (mem_sub (mem_add (mem_mul (mem_mul hZd hE) hF1)
      (mem_mul (mem_mul hZ hEd) hF1)) (mem_mul (mem_mul hZ hE) hF1d))) (mem_inv (mem_sq hF1))) hktp)
  have hc3 := mem_mul (mem_sq hitp) hitp
  have hB2 := mem_divInt (mem_mul (hO 0) hc3) ((lam : ℤ) ^ 4)
  have hBX := mem_divInt (mem_mul (hO 1) hc3) ((lam : ℤ) ^ 4)
  have hX2 := mem_divInt (mem_mul (hO 2) hc3) ((lam : ℤ) ^ 4)
  have hsh := mem_mul (mem_mul mem_c2 (mem_sq hpi)) hio
  have hW := mem_mul (mem_sub hwell hX2) hB2
  have hDp := mem_add (mem_sq (mem_sub (mem_mul mem_c1 hsh) hBX)) hW
  have hDm := mem_add (mem_sq (mem_sub (mem_mul (mem_neg mem_c1) hsh) hBX)) hW
  have hS := fxScale_pos
  constructor
  · have := (hDp okP).1
    refine lt_of_lt_of_le (fxVal_pos posP) (le_of_le_of_eq this ?_)
    unfold D6R B2R BXiR Xi2R c3R itpR wellR iotapR tpR dIR
    have hF := (F1_pos (S := 4) (by norm_num : (1 / 4 : ℝ) ≠ 0)
      (⟨by linarith, by nlinarith⟩ : k ∈ Set.Ioo (-1 : ℝ) 1)).ne'
    unfold F1 F1d Zint Zd Eint Ed at *
    push_cast
    field_simp
  · have := (hDm okM).1
    refine lt_of_lt_of_le (fxVal_pos posM) (le_of_le_of_eq this ?_)
    unfold D6R B2R BXiR Xi2R c3R itpR wellR iotapR tpR dIR
    have hF := (F1_pos (S := 4) (by norm_num : (1 / 4 : ℝ) ≠ 0)
      (⟨by linarith, by nlinarith⟩ : k ∈ Set.Ioo (-1 : ℝ) 1)).ne'
    unfold F1 F1d Zint Zd Eint Ed at *
    push_cast
    field_simp

end PlasmaLean.Design.LandremanFamily2Quad
