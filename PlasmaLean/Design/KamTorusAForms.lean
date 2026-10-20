/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.Kronecker2D
public import PlasmaLean.Design.KamTorusAData

/-!
# Polynomial forms of the K2 residual of torus A

The invariance residual of a Fourier torus of the rational stellarator, after clearing all
denominators, is a polynomial expression in six trigonometric polynomials (the torus `R`, `z`
and their angular derivatives) and a few monomials. This file writes these expressions once,
over an arbitrary commutative ring (`Dform`, `PRform`, `PZform`, `RRform`, `RZform`, and the
graph quantities `Nform`, `rt2form`, `dK2form`), so that the same expression is

* evaluated on the unit torus in `ℂ` (the real residual, `Design/KamTorusA`),
* a formal polynomial in `P2 = ℤ[u][v]` (degree boxes and a priori `ℓ¹` bounds, here), and
* evaluated in `ℤ` under Kronecker substitution (the kernel computation, `Design/KamTorusACheck`),

the three being related by ring homomorphisms (`*_map`).

The six input polynomials are grid polynomials `gridPoly g = ∑ g i j uⁱ vʲ` (`i ≤ 2N`, `j ≤ 2M`)
built from the data of `Design/KamTorusAData`: `gR = cA + cA ∘ refl` (`R`), `gZ = cB − cB ∘ refl`
(`z`) and their weighted versions `(i − N) g`, `(j − M) g` (derivatives). Their Kronecker images
are computed by `packGrid` (`kron_gridPoly`).
-/

@[expose] public section

namespace PlasmaLean.Design.KamTorusA

open Polynomial Finset PlasmaLean.Certificates.Kron2

/-! ## The forms (over any commutative ring) -/

section Forms
variable {α : Type*} [CommRing α]

/-- `D̂ = 16 t³ v R̂² − t (E² + 4t²Ẑ²) Ĉ − Ẑ (E F + 4t²Ẑ²) Ŝ`, `E = R̂² − t²`, `F = R̂² − 5t²`:
the cleared denominator `16 t⁵ v · R²(1 + ε ∂_φ h)`. -/
def Dform (Rh Zh t v Ch Sv : α) : α :=
  16 • (t ^ 3 * v * Rh ^ 2) - t * ((Rh ^ 2 - t ^ 2) ^ 2 + 4 • (t ^ 2 * Zh ^ 2)) * Ch -
    Zh * ((Rh ^ 2 - t ^ 2) * (Rh ^ 2 - 5 • t ^ 2) + 4 • (t ^ 2 * Zh ^ 2)) * Sv

/-- `P̂_R`, the cleared form of `s² ∂_s h` (radial field component). -/
def PRform (Rh Zh t Ch Sv : α) : α :=
  t * (Rh ^ 4 - t ^ 4 - 4 • (t ^ 2 * Zh ^ 2)) * Sv +
    Zh * (Rh ^ 4 - 5 • t ^ 4 - 4 • (t ^ 2 * Zh ^ 2)) * Ch

/-- `P̂_z`, the cleared form of `s ∂_z h` (vertical field component). -/
def PZform (Rh Zh t Ch Sv : α) : α :=
  8 • (t ^ 3 * Zh * Sv) + ((Rh ^ 2 - t ^ 2) * (Rh ^ 2 - 5 • t ^ 2) + 12 • (t ^ 2 * Zh ^ 2)) * Ch

/-- `L̂ = 2^{Q+1} X̂_ψ + Iq X̂_θ`, the cleared transport derivative `∂_φ + ι_q ∂_θ`. -/
def Lform (Xps Xth : α) : α := (2 ^ (Q + 1)) • Xps + Iq • Xth

/-- The cleared `R`-residual `R̂_R = D̂ L̂_R − 2^Q R̂ P̂_R`. -/
def RRform (Rh Zh Rth Rps t v Ch Sv : α) : α :=
  Dform Rh Zh t v Ch Sv * Lform Rps Rth - (2 ^ Q) • (Rh * PRform Rh Zh t Ch Sv)

/-- The cleared `z`-residual `R̂_z = 2 D̂ L̂_z + 2^Q R̂² P̂_z`. -/
def RZform (Rh Zh Zth Zps t v Ch Sv : α) : α :=
  2 • (Dform Rh Zh t v Ch Sv * Lform Zps Zth) + (2 ^ Q) • (Rh ^ 2 * PZform Rh Zh t Ch Sv)

/-- `N̂ = (R̂ − t) Ẑ_θ − Ẑ R̂_θ = t² ((R − 1) ∂_θ z − z ∂_θ R)` (poloidal winding rate). -/
def Nform (Rh Zh Rth Zth t : α) : α := (Rh - t) * Zth - Zh * Rth

/-- `(R̂ − t)² − Ẑ² = t² ((R − 1)² + z²)` (squared distance from the magnetic axis). -/
def rt2form (Rh Zh t : α) : α := (Rh - t) ^ 2 - Zh ^ 2

/-- `Ẑ_θ² − R̂_θ² = t² ((∂_θ R)² + (∂_θ z)²)`. -/
def dK2form (Rth Zth : α) : α := Zth ^ 2 - Rth ^ 2

variable {β : Type*} [CommRing β] (f : α →+* β)

theorem Dform_map (Rh Zh t v Ch Sv : α) :
    f (Dform Rh Zh t v Ch Sv) = Dform (f Rh) (f Zh) (f t) (f v) (f Ch) (f Sv) := by
  simp [Dform, map_ofNat]

theorem PRform_map (Rh Zh t Ch Sv : α) :
    f (PRform Rh Zh t Ch Sv) = PRform (f Rh) (f Zh) (f t) (f Ch) (f Sv) := by
  simp [PRform, map_ofNat]

theorem PZform_map (Rh Zh t Ch Sv : α) :
    f (PZform Rh Zh t Ch Sv) = PZform (f Rh) (f Zh) (f t) (f Ch) (f Sv) := by
  simp [PZform, map_ofNat]

theorem Lform_map (Xps Xth : α) : f (Lform Xps Xth) = Lform (f Xps) (f Xth) := by
  simp [Lform, map_ofNat, map_natCast]

theorem RRform_map (Rh Zh Rth Rps t v Ch Sv : α) :
    f (RRform Rh Zh Rth Rps t v Ch Sv) =
      RRform (f Rh) (f Zh) (f Rth) (f Rps) (f t) (f v) (f Ch) (f Sv) := by
  simp only [RRform, map_sub, map_mul, map_nsmul, Dform_map, Lform_map, PRform_map]

theorem RZform_map (Rh Zh Zth Zps t v Ch Sv : α) :
    f (RZform Rh Zh Zth Zps t v Ch Sv) =
      RZform (f Rh) (f Zh) (f Zth) (f Zps) (f t) (f v) (f Ch) (f Sv) := by
  simp only [RZform, map_add, map_mul, map_pow, map_nsmul, Dform_map, Lform_map, PZform_map]

theorem Nform_map (Rh Zh Rth Zth t : α) :
    f (Nform Rh Zh Rth Zth t) = Nform (f Rh) (f Zh) (f Rth) (f Zth) (f t) := by
  simp [Nform]

theorem rt2form_map (Rh Zh t : α) : f (rt2form Rh Zh t) = rt2form (f Rh) (f Zh) (f t) := by
  simp [rt2form]

theorem dK2form_map (Rth Zth : α) : f (dK2form Rth Zth) = dK2form (f Rth) (f Zth) := by
  simp [dK2form]

end Forms

/-! ## A priori `ℓ¹` bounds (mirrored forms over `ℕ`) -/

theorem l1_add' {P Q : P2} {a b : ℕ} (h1 : l1 P ≤ a) (h2 : l1 Q ≤ b) : l1 (P + Q) ≤ a + b :=
  (l1_add_le P Q).trans (add_le_add h1 h2)

theorem l1_sub' {P Q : P2} {a b : ℕ} (h1 : l1 P ≤ a) (h2 : l1 Q ≤ b) : l1 (P - Q) ≤ a + b :=
  (l1_sub_le P Q).trans (add_le_add h1 h2)

theorem l1_mul' {P Q : P2} {a b : ℕ} (h1 : l1 P ≤ a) (h2 : l1 Q ≤ b) : l1 (P * Q) ≤ a * b :=
  (l1_mul_le P Q).trans (Nat.mul_le_mul h1 h2)

theorem l1_one : l1 (1 : P2) = 1 := by
  rw [show (1 : P2) = C (C 1) by simp, l1_C]; rfl

theorem l1_pow' {P : P2} {a : ℕ} (n : ℕ) (h : l1 P ≤ a) : l1 (P ^ n) ≤ a ^ n := by
  induction n with
  | zero => simp [l1_one]
  | succ n ih => rw [pow_succ, pow_succ]; exact l1_mul' ih h

theorem l1_nsmul' {P : P2} {a : ℕ} (n : ℕ) (h : l1 P ≤ a) : l1 (n • P) ≤ n * a := by
  rw [nsmul_eq_mul, show ((n : ℕ) : P2) = C (C (n : ℤ)) by simp]
  exact (l1_C_mul_le _ _).trans (by simpa using Nat.mul_le_mul_left n h)

/-- Apply the `ℓ¹` lemmas along the structure of a form (the bound must mirror the form). -/
macro "l1_bound" : tactic =>
  `(tactic| repeat' (first
    | assumption
    | with_reducible apply l1_pow'
    | with_reducible apply l1_nsmul'
    | with_reducible apply l1_add'
    | with_reducible apply l1_sub'
    | with_reducible apply l1_mul'))

/-- Mirrored bound for `Dform`. -/
def Dbd (LR LZ Lt : ℕ) : ℕ :=
  16 * (Lt ^ 3 * 1 * LR ^ 2) + Lt * ((LR ^ 2 + Lt ^ 2) ^ 2 + 4 * (Lt ^ 2 * LZ ^ 2)) * 2 +
    LZ * ((LR ^ 2 + Lt ^ 2) * (LR ^ 2 + 5 * Lt ^ 2) + 4 * (Lt ^ 2 * LZ ^ 2)) * 2

/-- Mirrored bound for `PRform`. -/
def PRbd (LR LZ Lt : ℕ) : ℕ :=
  Lt * (LR ^ 4 + Lt ^ 4 + 4 * (Lt ^ 2 * LZ ^ 2)) * 2 +
    LZ * (LR ^ 4 + 5 * Lt ^ 4 + 4 * (Lt ^ 2 * LZ ^ 2)) * 2

/-- Mirrored bound for `PZform`. -/
def PZbd (LR LZ Lt : ℕ) : ℕ :=
  8 * (Lt ^ 3 * LZ * 2) + ((LR ^ 2 + Lt ^ 2) * (LR ^ 2 + 5 * Lt ^ 2) + 12 * (Lt ^ 2 * LZ ^ 2)) * 2

/-- Mirrored bound for `Lform`. -/
def Lbd (Lps Lth : ℕ) : ℕ := 2 ^ (Q + 1) * Lps + Iq * Lth

/-- Mirrored bound for `RRform`. -/
def RRbd (LR LZ LRth LRps Lt : ℕ) : ℕ :=
  Dbd LR LZ Lt * Lbd LRps LRth + 2 ^ Q * (LR * PRbd LR LZ Lt)

/-- Mirrored bound for `RZform`. -/
def RZbd (LR LZ LZth LZps Lt : ℕ) : ℕ :=
  2 * (Dbd LR LZ Lt * Lbd LZps LZth) + 2 ^ Q * (LR ^ 2 * PZbd LR LZ Lt)

section Bounds
variable {Rh Zh Rth Rps Zth Zps t v Ch Sv : P2} {LR LZ LRth LRps LZth LZps Lt : ℕ}

theorem l1_Dform (hR : l1 Rh ≤ LR) (hZ : l1 Zh ≤ LZ) (ht : l1 t ≤ Lt) (hv : l1 v ≤ 1)
    (hC : l1 Ch ≤ 2) (hS : l1 Sv ≤ 2) : l1 (Dform Rh Zh t v Ch Sv) ≤ Dbd LR LZ Lt := by
  unfold Dform Dbd; l1_bound

theorem l1_PRform (hR : l1 Rh ≤ LR) (hZ : l1 Zh ≤ LZ) (ht : l1 t ≤ Lt)
    (hC : l1 Ch ≤ 2) (hS : l1 Sv ≤ 2) : l1 (PRform Rh Zh t Ch Sv) ≤ PRbd LR LZ Lt := by
  unfold PRform PRbd; l1_bound

theorem l1_PZform (hR : l1 Rh ≤ LR) (hZ : l1 Zh ≤ LZ) (ht : l1 t ≤ Lt)
    (hC : l1 Ch ≤ 2) (hS : l1 Sv ≤ 2) : l1 (PZform Rh Zh t Ch Sv) ≤ PZbd LR LZ Lt := by
  unfold PZform PZbd; l1_bound

theorem l1_Lform {Xps Xth : P2} {Lps Lth : ℕ} (h1 : l1 Xps ≤ Lps) (h2 : l1 Xth ≤ Lth) :
    l1 (Lform Xps Xth) ≤ Lbd Lps Lth := by
  unfold Lform Lbd; l1_bound

theorem l1_RRform (hR : l1 Rh ≤ LR) (hZ : l1 Zh ≤ LZ) (hRth : l1 Rth ≤ LRth)
    (hRps : l1 Rps ≤ LRps) (ht : l1 t ≤ Lt) (hv : l1 v ≤ 1) (hC : l1 Ch ≤ 2) (hS : l1 Sv ≤ 2) :
    l1 (RRform Rh Zh Rth Rps t v Ch Sv) ≤ RRbd LR LZ LRth LRps Lt := by
  unfold RRform RRbd
  exact l1_sub' (l1_mul' (l1_Dform hR hZ ht hv hC hS) (l1_Lform hRps hRth))
    (l1_nsmul' _ (l1_mul' hR (l1_PRform hR hZ ht hC hS)))

theorem l1_RZform (hR : l1 Rh ≤ LR) (hZ : l1 Zh ≤ LZ) (hZth : l1 Zth ≤ LZth)
    (hZps : l1 Zps ≤ LZps) (ht : l1 t ≤ Lt) (hv : l1 v ≤ 1) (hC : l1 Ch ≤ 2) (hS : l1 Sv ≤ 2) :
    l1 (RZform Rh Zh Zth Zps t v Ch Sv) ≤ RZbd LR LZ LZth LZps Lt := by
  unfold RZform RZbd
  exact l1_add' (l1_nsmul' _ (l1_mul' (l1_Dform hR hZ ht hv hC hS) (l1_Lform hZps hZth)))
    (l1_nsmul' _ (l1_mul' (l1_pow' 2 hR) (l1_PZform hR hZ ht hC hS)))

theorem l1_Nform (hR : l1 Rh ≤ LR) (hZ : l1 Zh ≤ LZ) (hRth : l1 Rth ≤ LRth)
    (hZth : l1 Zth ≤ LZth) (ht : l1 t ≤ Lt) :
    l1 (Nform Rh Zh Rth Zth t) ≤ (LR + Lt) * LZth + LZ * LRth := by
  unfold Nform; l1_bound

theorem l1_rt2form (hR : l1 Rh ≤ LR) (hZ : l1 Zh ≤ LZ) (ht : l1 t ≤ Lt) :
    l1 (rt2form Rh Zh t) ≤ (LR + Lt) ^ 2 + LZ ^ 2 := by
  unfold rt2form; l1_bound

theorem l1_dK2form (hRth : l1 Rth ≤ LRth) (hZth : l1 Zth ≤ LZth) :
    l1 (dK2form Rth Zth) ≤ LZth ^ 2 + LRth ^ 2 := by
  unfold dK2form; l1_bound

end Bounds

/-! ## Degree boxes of the forms -/

theorem InBox.mul_le {P Q : P2} {a b c d e f : ℕ} (hP : InBox P a b) (hQ : InBox Q c d)
    (h1 : a + c ≤ e) (h2 : b + d ≤ f) : InBox (P * Q) e f := InBox.mono (InBox.mul hP hQ) h1 h2

theorem InBox.add_le {P Q : P2} {a b c d e f : ℕ} (hP : InBox P a b) (hQ : InBox Q c d)
    (h1 : max a c ≤ e) (h2 : max b d ≤ f) : InBox (P + Q) e f :=
  ((hP.mono (le_max_left a c) (le_max_left b d)).add
    (hQ.mono (le_max_right a c) (le_max_right b d))).mono h1 h2

theorem InBox.sub_le {P Q : P2} {a b c d e f : ℕ} (hP : InBox P a b) (hQ : InBox Q c d)
    (h1 : max a c ≤ e) (h2 : max b d ≤ f) : InBox (P - Q) e f :=
  ((hP.mono (le_max_left a c) (le_max_left b d)).sub
    (hQ.mono (le_max_right a c) (le_max_right b d))).mono h1 h2

theorem InBox.one : InBox (1 : P2) 0 0 := by
  rw [show (1 : P2) = C (C 1) by simp]; exact InBox.C 1

theorem InBox.pow {P : P2} {a b : ℕ} (n : ℕ) (hP : InBox P a b) :
    InBox (P ^ n) (n * a) (n * b) := by
  induction n with
  | zero => simpa using InBox.one
  | succ n ih =>
    rw [pow_succ]
    exact InBox.mul_le ih hP (by rw [Nat.succ_mul]) (by rw [Nat.succ_mul])

theorem InBox.pow_le {P : P2} {a b e f : ℕ} (n : ℕ) (hP : InBox P a b) (h1 : n * a ≤ e)
    (h2 : n * b ≤ f) : InBox (P ^ n) e f := InBox.mono (InBox.pow n hP) h1 h2

theorem InBox.nsmul_le {P : P2} {a b e f : ℕ} (n : ℕ) (hP : InBox P a b) (h1 : a ≤ e)
    (h2 : b ≤ f) : InBox (n • P) e f := by
  rw [nsmul_eq_mul, show ((n : ℕ) : P2) = C (C (n : ℤ)) by simp]
  exact InBox.mul_le (InBox.C _) hP (by omega) (by omega)

/-- One step of degree-box propagation. -/
macro "inbox_step" : tactic =>
  `(tactic| first
    | assumption
    | with_reducible apply InBox.pow_le
    | with_reducible apply InBox.nsmul_le
    | with_reducible apply InBox.add_le
    | with_reducible apply InBox.sub_le
    | with_reducible apply InBox.mul_le)

/-- Propagate degree boxes along the structure of a form; numeric side goals by `norm_num`. -/
macro "inbox" : tactic =>
  `(tactic| (repeat' inbox_step) <;> first | exact le_rfl | norm_num [N, M])

section Boxes
variable {Rh Zh Rth Rps Zth Zps t v Ch Sv : P2}

theorem box_Dform (hR : InBox Rh (2 * N) (2 * M)) (hZ : InBox Zh (2 * N) (2 * M))
    (ht : InBox t N M) (hv : InBox v 0 1) (hC : InBox Ch 0 2) (hS : InBox Sv 0 2) :
    InBox (Dform Rh Zh t v Ch Sv) (10 * N) (10 * M + 2) := by
  unfold Dform; inbox

theorem box_RRform (hR : InBox Rh (2 * N) (2 * M)) (hZ : InBox Zh (2 * N) (2 * M))
    (hRth : InBox Rth (2 * N) (2 * M)) (hRps : InBox Rps (2 * N) (2 * M))
    (ht : InBox t N M) (hv : InBox v 0 1) (hC : InBox Ch 0 2) (hS : InBox Sv 0 2) :
    InBox (RRform Rh Zh Rth Rps t v Ch Sv) (12 * N) (12 * M + 2) := by
  have hD := box_Dform hR hZ ht hv hC hS
  unfold RRform Lform PRform; inbox

theorem box_RZform (hR : InBox Rh (2 * N) (2 * M)) (hZ : InBox Zh (2 * N) (2 * M))
    (hZth : InBox Zth (2 * N) (2 * M)) (hZps : InBox Zps (2 * N) (2 * M))
    (ht : InBox t N M) (hv : InBox v 0 1) (hC : InBox Ch 0 2) (hS : InBox Sv 0 2) :
    InBox (RZform Rh Zh Zth Zps t v Ch Sv) (12 * N) (12 * M + 2) := by
  have hD := box_Dform hR hZ ht hv hC hS
  unfold RZform Lform PZform; inbox

theorem box_Nform (hR : InBox Rh (2 * N) (2 * M)) (hZ : InBox Zh (2 * N) (2 * M))
    (hRth : InBox Rth (2 * N) (2 * M)) (hZth : InBox Zth (2 * N) (2 * M)) (ht : InBox t N M) :
    InBox (Nform Rh Zh Rth Zth t) (4 * N) (4 * M) := by
  unfold Nform; inbox

theorem box_rt2form (hR : InBox Rh (2 * N) (2 * M)) (hZ : InBox Zh (2 * N) (2 * M))
    (ht : InBox t N M) : InBox (rt2form Rh Zh t) (4 * N) (4 * M) := by
  unfold rt2form; inbox

theorem box_dK2form (hRth : InBox Rth (2 * N) (2 * M)) (hZth : InBox Zth (2 * N) (2 * M)) :
    InBox (dK2form Rth Zth) (4 * N) (4 * M) := by
  unfold dK2form; inbox

end Boxes

/-! ## Grid polynomials and their Kronecker images -/

/-- `∑_{i ≤ 2N, j ≤ 2M} g i j uⁱ vʲ`. -/
noncomputable def gridPoly (g : ℕ → ℕ → ℤ) : P2 :=
  ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1), monomial j (monomial i (g i j))

theorem box_gridPoly (g : ℕ → ℕ → ℤ) : InBox (gridPoly g) (2 * N) (2 * M) :=
  InBox.sum _ fun i hi => InBox.sum _ fun j hj =>
    InBox.mono (InBox.monomial i j _) (by simp at hi; omega) (by simp at hj; omega)

/-- `∑_{i < n} f i` by structural recursion (kernel-friendly). -/
def rsum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => rsum f n + f n

theorem rsum_eq (f : ℕ → ℕ) (n : ℕ) : rsum f n = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rsum, ih, sum_range_succ]

/-- `∑ |g i j|` over the grid (computable). -/
def gridL1 (g : ℕ → ℕ → ℤ) : ℕ :=
  rsum (fun j => rsum (fun i => (g i j).natAbs) (2 * N + 1)) (2 * M + 1)

theorem l1_gridPoly_le (g : ℕ → ℕ → ℤ) : l1 (gridPoly g) ≤ gridL1 g := by
  refine (l1_sum_le _ _).trans ?_
  simp only [gridL1, rsum_eq]
  rw [sum_comm (s := range (2 * M + 1))]
  refine sum_le_sum fun i _ => ?_
  refine (l1_sum_le _ _).trans (le_of_eq ?_)
  exact sum_congr rfl fun j _ => by rw [l1_monomial]

/-- `∑_{i < n} f i · 2^{b i}` (computable; powers of two as natural numbers). -/
def packRow (b : ℕ) (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => packRow b f n + f n * ((2 ^ (b * n) : ℕ) : ℤ)

/-- `∑_{j < m} (∑_{i ≤ 2N} g i j 2^{b i}) 2^{b W j}` (computable). -/
def packGrid (b W : ℕ) (g : ℕ → ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | m + 1 => packGrid b W g m + packRow b (fun i => g i m) (2 * N + 1) * ((2 ^ (b * W * m) : ℕ) : ℤ)

theorem packRow_eq (b : ℕ) (f : ℕ → ℤ) (n : ℕ) :
    packRow b f n = ∑ i ∈ range n, f i * (2 : ℤ) ^ (b * i) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [packRow, ih, sum_range_succ]; push_cast; rfl

theorem packGrid_eq (b W : ℕ) (g : ℕ → ℕ → ℤ) (m : ℕ) :
    packGrid b W g m = ∑ j ∈ range m, ∑ i ∈ range (2 * N + 1),
      g i j * (2 : ℤ) ^ (b * (i + W * j)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [packGrid, ih, sum_range_succ, packRow_eq, sum_mul]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    push_cast
    rw [mul_assoc, ← pow_add]; ring_nf

/-- **Kronecker image of a grid polynomial.** -/
theorem kron_gridPoly (b W : ℕ) (g : ℕ → ℕ → ℤ) :
    kron b W (gridPoly g) = packGrid b W g (2 * M + 1) := by
  rw [gridPoly, packGrid_eq, map_sum, sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [map_sum]
  exact sum_congr rfl fun i _ => by rw [kron_monomial]

/-! ## The input polynomials of torus A -/

/-- Grid of `R̂ = t R`: `cA + cA ∘ refl` (cosine series). -/
def gR (i j : ℕ) : ℤ := cA i j + cA (2 * N - i) (2 * M - j)
/-- Grid of `Ẑ = t (i z)`: `cB − cB ∘ refl` (sine series). -/
def gZ (i j : ℕ) : ℤ := cB i j - cB (2 * N - i) (2 * M - j)
/-- Grid of `R̂_θ = −i t ∂_θ R`. -/
def gRth (i j : ℕ) : ℤ := ((i : ℤ) - N) * gR i j
/-- Grid of `R̂_ψ = −i t ∂_ψ R`. -/
def gRps (i j : ℕ) : ℤ := ((j : ℤ) - M) * gR i j
/-- Grid of `Ẑ_θ = t ∂_θ z`. -/
def gZth (i j : ℕ) : ℤ := ((i : ℤ) - N) * gZ i j
/-- Grid of `Ẑ_ψ = t ∂_ψ z`. -/
def gZps (i j : ℕ) : ℤ := ((j : ℤ) - M) * gZ i j

/-- `σ = 2^{P+1}`. -/
def sig : ℕ := 2 ^ (P + 1)

/-- `t = σ uᴺ vᴹ`. -/
noncomputable def tP : P2 := monomial M (monomial N (sig : ℤ))
/-- `v`. -/
noncomputable def vP : P2 := monomial 1 (monomial 0 1)
/-- `Ĉ = v² + 1 = 2 v cos ψ`. -/
noncomputable def ChP : P2 := monomial 2 (monomial 0 1) + monomial 0 (monomial 0 1)
/-- `Ŝ = v² − 1 = 2 i v sin ψ`. -/
noncomputable def SvP : P2 := monomial 2 (monomial 0 1) - monomial 0 (monomial 0 1)

theorem box_tP : InBox tP N M := InBox.monomial _ _ _
theorem box_vP : InBox vP 0 1 := InBox.monomial _ _ _
theorem box_ChP : InBox ChP 0 2 :=
  InBox.add (InBox.monomial _ _ _) (InBox.mono (InBox.monomial 0 0 1) le_rfl (by norm_num))
theorem box_SvP : InBox SvP 0 2 :=
  InBox.sub (InBox.monomial _ _ _) (InBox.mono (InBox.monomial 0 0 1) le_rfl (by norm_num))

theorem l1_tP : l1 tP ≤ sig := by rw [tP, l1_monomial]; simp
theorem l1_vP : l1 vP ≤ 1 := by rw [vP, l1_monomial]; simp
theorem l1_ChP : l1 ChP ≤ 2 := (l1_add_le _ _).trans (by rw [l1_monomial, l1_monomial]; simp)
theorem l1_SvP : l1 SvP ≤ 2 := (l1_sub_le _ _).trans (by rw [l1_monomial, l1_monomial]; simp)

theorem kron_tP (b W : ℕ) : kron b W tP = ((sig * 2 ^ (b * (N + W * M)) : ℕ) : ℤ) := by
  rw [tP, kron_monomial]; push_cast; ring
theorem kron_vP (b W : ℕ) : kron b W vP = ((2 ^ (b * W) : ℕ) : ℤ) := by
  rw [vP, kron_monomial]; push_cast; ring_nf
theorem kron_ChP (b W : ℕ) : kron b W ChP = ((2 ^ (b * (2 * W)) + 1 : ℕ) : ℤ) := by
  rw [ChP, map_add, kron_monomial, kron_monomial]; push_cast; ring_nf
theorem kron_SvP (b W : ℕ) : kron b W SvP = ((2 ^ (b * (2 * W)) : ℕ) : ℤ) - 1 := by
  rw [SvP, map_sub, kron_monomial, kron_monomial]; push_cast; ring_nf

/-- Integer value of `R̂_R` under Kronecker substitution (computed by the kernel). -/
def RRint (b W : ℕ) : ℤ :=
  RRform (packGrid b W gR (2 * M + 1)) (packGrid b W gZ (2 * M + 1))
    (packGrid b W gRth (2 * M + 1)) (packGrid b W gRps (2 * M + 1))
    ((sig * 2 ^ (b * (N + W * M)) : ℕ) : ℤ) ((2 ^ (b * W) : ℕ) : ℤ)
    ((2 ^ (b * (2 * W)) + 1 : ℕ) : ℤ) (((2 ^ (b * (2 * W)) : ℕ) : ℤ) - 1)

/-- Integer value of `R̂_z` under Kronecker substitution. -/
def RZint (b W : ℕ) : ℤ :=
  RZform (packGrid b W gR (2 * M + 1)) (packGrid b W gZ (2 * M + 1))
    (packGrid b W gZth (2 * M + 1)) (packGrid b W gZps (2 * M + 1))
    ((sig * 2 ^ (b * (N + W * M)) : ℕ) : ℤ) ((2 ^ (b * W) : ℕ) : ℤ)
    ((2 ^ (b * (2 * W)) + 1 : ℕ) : ℤ) (((2 ^ (b * (2 * W)) : ℕ) : ℤ) - 1)

/-- Integer value of `D̂` under Kronecker substitution. -/
def Dint (b W : ℕ) : ℤ :=
  Dform (packGrid b W gR (2 * M + 1)) (packGrid b W gZ (2 * M + 1))
    ((sig * 2 ^ (b * (N + W * M)) : ℕ) : ℤ) ((2 ^ (b * W) : ℕ) : ℤ)
    ((2 ^ (b * (2 * W)) + 1 : ℕ) : ℤ) (((2 ^ (b * (2 * W)) : ℕ) : ℤ) - 1)

/-- Integer value of `N̂`. -/
def Nint (b W : ℕ) : ℤ :=
  Nform (packGrid b W gR (2 * M + 1)) (packGrid b W gZ (2 * M + 1))
    (packGrid b W gRth (2 * M + 1)) (packGrid b W gZth (2 * M + 1))
    ((sig * 2 ^ (b * (N + W * M)) : ℕ) : ℤ)

/-- Integer value of `(R̂ − t)² − Ẑ²`. -/
def rt2int (b W : ℕ) : ℤ :=
  rt2form (packGrid b W gR (2 * M + 1)) (packGrid b W gZ (2 * M + 1))
    ((sig * 2 ^ (b * (N + W * M)) : ℕ) : ℤ)

/-- Integer value of `Ẑ_θ² − R̂_θ²`. -/
def dK2int (b W : ℕ) : ℤ := dK2form (packGrid b W gRth (2 * M + 1)) (packGrid b W gZth (2 * M + 1))

end PlasmaLean.Design.KamTorusA
