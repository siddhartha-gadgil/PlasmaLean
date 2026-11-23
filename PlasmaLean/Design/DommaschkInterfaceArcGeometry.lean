/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.EvalCertFIv
public import PlasmaLean.Design.DommaschkKamDio
public import PlasmaLean.Theory.Stability.InterfacePrincipalDirection

/-!
# A conditional principal-direction obstruction on the torus A interface arc

Use the cylindrical parametrization `X=(R cos φ,R sin φ,z)` along `θ=0`.
The field direction in the angular basis is `v=(dkIotaA,1)`. The chosen
normal is the unnormalized `Xφ × Xθ`. The curvature row uses
`Hᵢⱼ = - (Xφ × Xθ) · Xᵢⱼ`. Its sign depends on this convention.

The three input tables are the degree-four, one-cell proposal from
`scripts/dommaschk_kam/interface_arc.py`. Reproduce the dyadic endpoints with
`python3 scripts/dommaschk_kam/interface_geometry_boxes.py --check`.
The theorem takes real jet membership in those tables as hypotheses.
-/

@[expose] public section

namespace PlasmaLean.Design.DommaschkInterfaceArcGeometry

open PlasmaLean.Certificates.ValidatedQuadrature
open PlasmaLean.Stability.InterfacePrincipalDirection

/-- Physical-angle jet coordinates needed by the fundamental forms. -/
inductive Jet where
  | radius | rθ | rφ | zθ | zφ | rθθ | rθφ | rφφ | zθθ | zθφ | zφφ

/-- Height flag, poloidal derivative order, toroidal derivative order. -/
def Jet.source : Jet → Bool × ℕ × ℕ
  | .radius => (false, 0, 0)
  | .rθ => (false, 1, 0)
  | .rφ => (false, 0, 1)
  | .zθ => (true, 1, 0)
  | .zφ => (true, 0, 1)
  | .rθθ => (false, 2, 0)
  | .rθφ => (false, 1, 1)
  | .rφφ => (false, 0, 2)
  | .zθθ => (true, 2, 0)
  | .zθφ => (true, 1, 1)
  | .zφφ => (true, 0, 2)

/-- The endpoints are integer multiples of 2⁻¹⁶, embedded exactly in FIv's 2⁻³² grid. -/
def gridBox (lo hi : ℤ) : FIv := ⟨lo * 65536, hi * 65536, true⟩

/-- Both inequalities defining each input box use exact real endpoints. -/
theorem mem_gridBox_iff {lo hi : ℤ} {x : ℝ} :
    (gridBox lo hi).Mem x ↔ (lo : ℝ) / 65536 ≤ x ∧ x ≤ (hi : ℝ) / 65536 := by
  simp only [FIv.Mem, gridBox, fxVal, fxScale, forall_const, Int.cast_mul, Int.cast_ofNat]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

def leftBox : Jet → FIv
  | .radius => gridBox (65593) (65614)
  | .rθ => gridBox (-8) (8)
  | .rφ => gridBox (-120) (120)
  | .zθ => gridBox (1427) (1443)
  | .zφ => gridBox (-4816) (-4591)
  | .rθθ => gridBox (-1472) (-1458)
  | .rθφ => gridBox (-487) (-316)
  | .rφφ => gridBox (-6690) (-3054)
  | .zθθ => gridBox (-9) (9)
  | .zθφ => gridBox (-82) (82)
  | .zφφ => gridBox (-1659) (1659)

def rightBox : Jet → FIv
  | .radius => gridBox (65487) (65508)
  | .rθ => gridBox (-62) (-46)
  | .rφ => gridBox (-1265) (-1025)
  | .zθ => gridBox (1482) (1498)
  | .zφ => gridBox (-5019) (-4794)
  | .rθθ => gridBox (-1460) (-1446)
  | .rθφ => gridBox (-128) (43)
  | .rφφ => gridBox (-8899) (-5262)
  | .zθθ => gridBox (-46) (-29)
  | .zθφ => gridBox (427) (590)
  | .zφφ => gridBox (-3270) (49)

def arcBox : Jet → FIv
  | .radius => gridBox (65487) (65614)
  | .rθ => gridBox (-88) (8)
  | .rφ => gridBox (-1265) (120)
  | .zθ => gridBox (1427) (1502)
  | .zφ => gridBox (-5062) (-4591)
  | .rθθ => gridBox (-1472) (-1446)
  | .rθφ => gridBox (-487) (85)
  | .rφφ => gridBox (-9250) (-3054)
  | .zθθ => gridBox (-46) (9)
  | .zθφ => gridBox (-82) (679)
  | .zφφ => gridBox (-4120) (1659)

/-- All eleven components of a cylindrical jet lie in their specified intervals. -/
def InBox (box : Jet → FIv) (j : Jet → ℝ) : Prop := ∀ k, (box k).Mem (j k)

/-- First fundamental form evaluated on the angular vector (ι,1) in its first slot. -/
def metricRow {K : Type*} [Add K] [Mul K] (ι : K) (j : Jet → K) : K × K :=
  let g11 := j .rθ * j .rθ + j .zθ * j .zθ
  let g12 := j .rθ * j .rφ + j .zθ * j .zφ
  let g22 := j .rφ * j .rφ + j .radius * j .radius + j .zφ * j .zφ
  (ι * g11 + g12, ι * g12 + g22)

/-- Curvature form evaluated in the same direction with the orientation specified above. -/
def curvatureRow {K : Type*} [Add K] [Mul K] [Neg K] [Sub K] (ι : K) (j : Jet → K) : K × K :=
  let nr := j .radius * j .zθ
  let nφ := j .zφ * j .rθ - j .rφ * j .zθ
  let nz := -(j .radius * j .rθ)
  let h11 := -(nr * j .rθθ + nz * j .zθθ)
  let h12 := -(nr * j .rθφ + nφ * j .rθ + nz * j .zθφ)
  let h22 := -(nr * (j .rφφ - j .radius) + nφ * (j .rφ + j .rφ) + nz * j .zφφ)
  (ι * h11 + h12, ι * h12 + h22)

private local instance : Add FIv := ⟨FIv.add⟩
private local instance : Neg FIv := ⟨FIv.neg⟩
private local instance : Sub FIv := ⟨FIv.sub⟩
private local instance : Mul FIv := ⟨FIv.mul⟩

private def iotaBox := gridBox (-15638) (-15637)

private theorem iota_mem : iotaBox.Mem DommaschkKamDio.dkIotaA := by
  rw [iotaBox, mem_gridBox_iff, DommaschkKamDio.dkIotaA]
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg 5
  have hl : (22360 / 10000 : ℝ) ≤ Real.sqrt 5 := by nlinarith
  have hu : Real.sqrt 5 ≤ (22361 / 10000 : ℝ) := by nlinarith
  norm_num
  constructor <;> linarith

private theorem metric_mem {j : Jet → ℝ} {b : Jet → FIv} (h : InBox b j) :
    ((metricRow iotaBox b).1.Mem (metricRow DommaschkKamDio.dkIotaA j).1) ∧
    ((metricRow iotaBox b).2.Mem (metricRow DommaschkKamDio.dkIotaA j).2) := by
  unfold metricRow
  constructor <;> repeat first | exact iota_mem | exact h _ | apply FIv.mem_add | apply FIv.mem_mul

private theorem curvature_mem {j : Jet → ℝ} {b : Jet → FIv} (h : InBox b j) :
    ((curvatureRow iotaBox b).1.Mem (curvatureRow DommaschkKamDio.dkIotaA j).1) ∧
    ((curvatureRow iotaBox b).2.Mem (curvatureRow DommaschkKamDio.dkIotaA j).2) := by
  unfold curvatureRow
  constructor <;> repeat first | exact iota_mem | exact h _ | apply FIv.mem_add | apply FIv.mem_mul
                               | apply FIv.mem_sub | apply FIv.mem_neg

private def detBox (b : Jet → FIv) : FIv :=
  let g := metricRow iotaBox b
  let h := curvatureRow iotaBox b
  g.1 * h.2 - g.2 * h.1

private def directionBox (row : FIv × FIv) : FIv := iotaBox * row.1 + row.2

private theorem det_mem {j : Jet → ℝ} {b : Jet → FIv} (hj : InBox b j) :
    (detBox b).Mem (det (metricRow DommaschkKamDio.dkIotaA j)
      (curvatureRow DommaschkKamDio.dkIotaA j)) := by
  have hg := metric_mem hj
  have hh := curvature_mem hj
  exact FIv.mem_sub (FIv.mem_mul hg.1 hh.2) (FIv.mem_mul hg.2 hh.1)

private theorem direction_mem {i : FIv × FIv} {row : ℝ × ℝ}
    (hr : i.1.Mem row.1 ∧ i.2.Mem row.2) :
    (directionBox i).Mem (pair row (DommaschkKamDio.dkIotaA, 1)) := by
  rw [pair, mul_one, mul_comm row.1]
  exact FIv.mem_add (FIv.mem_mul iota_mem hr.1) hr.2

private def checkPositive (i : FIv) : Bool := i.ok && (0 < i.lo)
private def checkNegative (i : FIv) : Bool := i.ok && (i.hi < 0)

private theorem positive {i : FIv} {x : ℝ} (hm : i.Mem x) (hc : checkPositive i = true) :
    0 < x := by
  obtain ⟨hok, hlo⟩ : i.ok = true ∧ 0 < i.lo := by simpa [checkPositive] using hc
  exact lt_of_lt_of_le (div_pos (by exact_mod_cast hlo) fxScale_pos) (hm hok).1

private theorem negative {i : FIv} {x : ℝ} (hm : i.Mem x) (hc : checkNegative i = true) :
    x < 0 := by
  obtain ⟨hok, hhi⟩ : i.ok = true ∧ i.hi < 0 := by simpa [checkNegative] using hc
  exact lt_of_le_of_lt (hm hok).2 (div_neg_of_neg_of_pos (by exact_mod_cast hhi) fxScale_pos)

private theorem left_check : checkNegative (detBox leftBox) = true := by fiv_cert
private theorem right_check : checkPositive (detBox rightBox) = true := by fiv_cert
private theorem metric_check : checkPositive (directionBox (metricRow iotaBox arcBox)) = true := by
  fiv_cert
private theorem curvature_check :
    checkPositive (directionBox (curvatureRow iotaBox arcBox)) = true := by fiv_cert

/-- The determinant is strictly negative at the left endpoint. -/
theorem det_left_negative {j : Jet → ℝ} (hj : InBox leftBox j) :
    det (metricRow DommaschkKamDio.dkIotaA j) (curvatureRow DommaschkKamDio.dkIotaA j) < 0 :=
  negative (det_mem hj) left_check

/-- The determinant is strictly positive at the right endpoint. -/
theorem det_right_positive {j : Jet → ℝ} (hj : InBox rightBox j) :
    0 < det (metricRow DommaschkKamDio.dkIotaA j) (curvatureRow DommaschkKamDio.dkIotaA j) :=
  positive (det_mem hj) right_check

/-- Both fundamental forms evaluate strictly positively on the field direction on the arc. -/
theorem direction_positive {j : Jet → ℝ} (hj : InBox arcBox j) :
    0 < pair (metricRow DommaschkKamDio.dkIotaA j) (DommaschkKamDio.dkIotaA, 1) ∧
    0 < pair (curvatureRow DommaschkKamDio.dkIotaA j) (DommaschkKamDio.dkIotaA, 1) :=
  ⟨positive (direction_mem (metric_mem hj)) metric_check,
   positive (direction_mem (curvature_mem hj)) curvature_check⟩

/-- A continuous family of jets in the three boxes has a point excluding every
positive-pressure, negative-mixed-curvature variation for these rows. -/
theorem exists_obstruction {j : ℝ → Jet → ℝ}
    (hc : ∀ k, ContinuousOn (fun t => j t k) (Set.Icc 0 (1 / 5)))
    (hl : InBox leftBox (j 0)) (hr : InBox rightBox (j (1 / 5)))
    (ha : ∀ t ∈ Set.Icc 0 (1 / 5), InBox arcBox (j t)) :
    ∃ t ∈ Set.Icc 0 (1 / 5), ∀ z, 0 < pair (metricRow DommaschkKamDio.dkIotaA (j t)) z →
      0 < pair (curvatureRow DommaschkKamDio.dkIotaA (j t)) z := by
  apply exists_obstruction_of_sign_change (v := fun _ => (DommaschkKamDio.dkIotaA, 1)) (by norm_num)
  · dsimp only [det, metricRow, curvatureRow]
    fun_prop (disch := exact hc _)
  · exact (det_left_negative hl).le
  · exact (det_right_positive hr).le
  · exact fun t ht => (direction_positive (ha t ht)).1
  · exact fun t ht => (direction_positive (ha t ht)).2

end PlasmaLean.Design.DommaschkInterfaceArcGeometry
