/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamFieldData

/-!
# Kernel checks of the flow-form identities of the Dommaschk QA target

The polynomial identities of `Design/DommaschkKamField`, as combinations of the sparse data of
`DommaschkKamFieldData` built with the operations of `DommaschkKamPoly` (`merge`, `scale`, `mul`,
`dU`, `dZ`, `phiS`), each checked to be the empty sum by kernel evaluation (`kernel_fact`: the
proof is `Eq.refl`, checked only by the kernel). With `R = R₀ + u` (`Rl`):

* `divCombo_eq`: `R ∂_φD − 7 n_R + R ∂_u n_R + R ∂_z n_z = 0` (divergence-free, exponent `7`);
* `faCombo_eq`: `R ∂_u P_b − 7 P_b − R ∂_z P_a − R D = 0` (flux identity (a), cleared by `R⁸`);
* `fbCombo_eq`: `∂_φP_a − R⁷ ∂_u P_c − n_z = 0` (flux identity (b) with the `dφ`-component);
* `fcCombo_eq`: `∂_φP_b − R⁷ ∂_z P_c + n_R = 0` (flux identity (c) with the `dφ`-component);
* `obsCombo_eq`: `n_z(u = 0, z = 0) = c₀R₀⁸ + ∂_φQ` (the `φ`-mean of `n_z` on the circle
  `R = R₀, z = 0` is `c₀R₀⁸ ≠ 0`: the obstruction to a primitive without `dφ`-component);
* `AO_dQ`: `Q` is angle-only.

The same combinations are evaluated by the Python mirror in
`scripts/dommaschk_kam/emit_flowfield.py` before the data are written.

**Sanity.** `R7l_ne` (the cleared power `R⁷` is not the empty sum).
-/

@[expose] public section

namespace PlasmaLean.Design.DommaschkKam

open DkPoly

/-- `R = R₀ + u`. -/
def Rl : SP := [⟨R0q, 0, 0, 0, 0⟩, ⟨1, 1, 0, 0, 0⟩]

/-- `R⁷` (seven products with `R`). -/
def R7l : SP :=
  mul Rl (mul Rl (mul Rl (mul Rl (mul Rl (mul Rl (mul Rl [⟨1, 0, 0, 0, 0⟩]))))))

/-- The divergence combination `R ∂_φD − 7 n_R + R ∂_u n_R + R ∂_z n_z`. -/
def divCombo : SP :=
  merge (merge (mul Rl (phiS dD)) (scale (-7) dnR)) (merge (mul Rl (dU dnR)) (mul Rl (dZ dnZ)))

/-- The flux combination (a) `R ∂_u P_b − 7 P_b − R ∂_z P_a − R D`. -/
def faCombo : SP :=
  merge (merge (mul Rl (dU dPb)) (scale (-7) dPb))
    (merge (scale (-1) (mul Rl (dZ dPa))) (scale (-1) (mul Rl dD)))

/-- The flux combination (b) `∂_φP_a − R⁷ ∂_u P_c − n_z`. -/
def fbCombo : SP := merge (merge (phiS dPa) (scale (-1) (mul R7l (dU dPc)))) (scale (-1) dnZ)

/-- The flux combination (c) `∂_φP_b − R⁷ ∂_z P_c + n_R`. -/
def fcCombo : SP := merge (merge (phiS dPb) (scale (-1) (mul R7l (dZ dPc)))) dnR

/-- The obstruction combination `n_z(u = 0, z = 0) − (c₀R₀⁸ + ∂_φQ)`. -/
def obsCombo : SP := merge (atZero dnZ) (scale (-1) (merge [⟨Kq, 0, 0, 0, 0⟩] (phiS dQ)))

/-- **Divergence-free identity** (kernel check). -/
theorem divCombo_eq : divCombo = [] := by kernel_fact

/-- **Flux identity (a)** (kernel check). -/
theorem faCombo_eq : faCombo = [] := by kernel_fact

/-- **Flux identity (b)** with the `dφ`-component (kernel check). -/
theorem fbCombo_eq : fbCombo = [] := by kernel_fact

/-- **Flux identity (c)** with the `dφ`-component (kernel check). -/
theorem fcCombo_eq : fcCombo = [] := by kernel_fact

/-- **The `φ`-mean of `n_z` at `u = z = 0`** (kernel check). -/
theorem obsCombo_eq : obsCombo = [] := by kernel_fact

/-- `Q` is angle-only (kernel check). -/
theorem AO_dQ : AO dQ = true := by kernel_fact

/-- **Sanity (rejected fixture)**: the cleared power `R⁷` is not the empty sum. -/
theorem R7l_ne : R7l ≠ [] := by
  have h8 : R7l.length = 8 := by kernel_fact
  intro h
  rw [h] at h8
  simp at h8

end PlasmaLean.Design.DommaschkKam
