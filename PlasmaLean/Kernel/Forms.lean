/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.Vacuum
public import PlasmaLean.Kernel.Equilibrium
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.InnerProductSpace.Orientation
public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.Matrix.Determinant.Misc

/-!
# Differential-form language for the kernel laws (domain KERNEL file)

**This is a kernel file** of the PlasmaLean domain library (a domain kernel, not an
extension of Lean's logical kernel). It is an *addition* to `Kernel/Vacuum` and
`Kernel/Equilibrium`, not a replacement: it states the same physical laws in the
language of differential forms on `ℝ³`, and proves that the two languages are related
by linear equivalences (maps in both directions, proved inverse to each other).

## Which object is a form of which degree

In `ℝ³` vectors, 1-forms and 2-forms are all three-dimensional, so a vector field can be
written as either. The choice below follows what the object is integrated over.

| Physics | Geometry | Lean |
| --- | --- | --- |
| scalar `p`, `ψ` | 0-form (function) | `Euclid3 → ℝ` |
| gradient `∇p` | 1-form `dp` (integrated along curves) | `flat (∇p)`, `formGrad p` |
| field intensity `B♭` (Ampère) | 1-form `⋆ω_B` | `flat B = hodge (flux B)` |
| magnetic field `B` (flux through surfaces) | 2-form `ω_B = ι_B vol` | `flux B` |
| current density `J` (flux through surfaces) | 2-form `ω_J = ι_J vol` | `flux J` |
| divergence `∇ · B` (integrated over volumes) | 3-form `dω_B` | `density (∇ · B)` |
| `∇ × B` | 2-form `d(⋆ω_B)` | `flux (∇ × B)` |

The equivalences are `flat : Euclid3 ≃ₗ Form 1`, `flux : Euclid3 ≃ₗ Form 2`,
`density : ℝ ≃ₗ Form 3` and the Hodge star `hodge : Form 2 ≃ₗ Form 1`. The exterior
derivative is Mathlib's `extDeriv`. The dictionary theorems are unconditional:
`extDeriv_flat` (`d(B♭) = flux (∇ × B)`), `extDeriv_flux` (`d(ι_B vol) = (∇ · B) vol`)
and `extDeriv_formGrad`.

## Laws

* `VacuumForm Ω ω`: `ω` is a `C²` 2-form on the open set `Ω` with `dω = 0` (Gauss) and
  `d(⋆ω) = 0` (Ampère with no current). `vacuumForm_flux_iff` and
  `vacuumField_fluxSymm_iff` identify it with `Vacuum.VacuumField` in both directions.
* `FormForceBalance ωB ωJ dp`: `ι_B ω_J = dp`, where `B` is the vector of the flux form
  `ω_B`. `formForceBalance_iff` and `forceBalance_iff` identify it with `ForceBalance`.

Not modelled: forms on a manifold other than `ℝ³`, a metric other than the Euclidean
one, integration of forms, de Rham cohomology.
-/

public section
noncomputable section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum Module Matrix

/-- Constant-coefficient real-valued `k`-forms on `ℝ³`: the value of a differential
`k`-form at one point. A differential form is a function `Euclid3 → Form k`. -/
abbrev Form (k : ℕ) := Euclid3 [⋀^Fin k]→L[ℝ] ℝ

/-- The standard orthonormal basis of `ℝ³`. -/
abbrev stdBasis : OrthonormalBasis (Fin 3) ℝ Euclid3 := EuclideanSpace.basisFun (Fin 3) ℝ

instance : Fact (finrank ℝ Euclid3 = 3) := ⟨by simp⟩

/-- The Euclidean volume form `dx ∧ dy ∧ dz` with the standard orientation. -/
def volForm : Form 3 :=
  AlternatingMap.mkContinuous (stdBasis.toBasis.orientation.volumeForm) 1 (fun m => by
    simpa [Real.norm_eq_abs] using
      stdBasis.toBasis.orientation.abs_volumeForm_apply_le m)

/-- The volume form is the determinant of the matrix of components. -/
theorem volForm_apply (v : Fin 3 → Euclid3) :
    volForm v = Matrix.det (Matrix.of fun i j => v i j) := by
  have h := stdBasis.toBasis.orientation.volumeForm_robust stdBasis rfl
  simp only [volForm, AlternatingMap.coe_mkContinuous, h]
  rw [Basis.det_apply, ← Matrix.det_transpose]
  congr 1

/-- The volume form on three vectors, in components (the triple product). -/
theorem volForm_vec (a b c : Euclid3) : volForm ![a, b, c] =
    a 0 * (b 1 * c 2 - b 2 * c 1) - a 1 * (b 0 * c 2 - b 2 * c 0)
      + a 2 * (b 0 * c 1 - b 1 * c 0) := by
  rw [volForm_apply, Matrix.det_fin_three]
  simp
  ring

/-- Components of the Cartesian unit vectors. -/
theorem coordVec_apply (i j : Fin 3) : coordVec i j = if j = i then 1 else 0 := by
  simp [coordVec]

/-- Two forms are equal if they agree on all tuples of distinct Cartesian unit vectors. -/
theorem ext_basis {k : ℕ} {f g : Form k}
    (h : ∀ v : Fin k → Fin 3, Function.Injective v →
      f (fun i => coordVec (v i)) = g (fun i => coordVec (v i))) : f = g := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine Basis.ext_alternating stdBasis.toBasis fun v hv => ?_
  simpa using h v hv

/-- A 2-form changes sign when its arguments are exchanged. -/
theorem form2_swap (ω : Form 2) (a b : Euclid3) : ω ![a, b] = -ω ![b, a] := by
  have h := ω.toAlternatingMap.map_swap ![b, a] (show (0 : Fin 2) ≠ 1 by simp)
  have e : ![b, a] ∘ Equiv.swap (0 : Fin 2) 1 = ![a, b] := by
    ext i; fin_cases i <;> simp
  rw [e] at h
  exact h

/-- A 3-form changes sign when its first two arguments are exchanged. -/
theorem form3_swap01 (ω : Form 3) (a b c : Euclid3) : ω ![a, b, c] = -ω ![b, a, c] := by
  have h := ω.toAlternatingMap.map_swap ![b, a, c] (show (0 : Fin 3) ≠ 1 by simp)
  have e : ![b, a, c] ∘ Equiv.swap (0 : Fin 3) 1 = ![a, b, c] := by
    ext i; fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  rw [e] at h
  exact h

/-- A 3-form changes sign when its last two arguments are exchanged. -/
theorem form3_swap12 (ω : Form 3) (a b c : Euclid3) : ω ![a, b, c] = -ω ![a, c, b] := by
  have h := ω.toAlternatingMap.map_swap ![a, c, b] (show (1 : Fin 3) ≠ 2 by simp)
  have e : ![a, c, b] ∘ Equiv.swap (1 : Fin 3) 2 = ![a, b, c] := by
    ext i; fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  rw [e] at h
  exact h

/-! ## The equivalences -/

/-- **Musical isomorphism `♭`**: the vector `v` as the 1-form `w ↦ ⟪v, w⟫`. Its inverse
`♯` reads off the components `ω(eᵢ)`. Natural for gradients and for the field intensity
in Ampère's law (objects integrated along curves). -/
@[expose] def flat : Euclid3 ≃ₗ[ℝ] Form 1 where
  toFun v := ContinuousAlternatingMap.ofSubsingleton ℝ Euclid3 ℝ (0 : Fin 1) (innerSL ℝ v)
  map_add' u v := by ext w; simp
  map_smul' c v := by ext w; simp
  invFun ω := WithLp.toLp 2 fun i => ω fun _ => coordVec i
  left_inv v := by
    ext i
    simp [coordVec, EuclideanSpace.inner_single_right]
  right_inv ω := by
    apply ext_basis
    intro v _
    simp only [coordVec, ContinuousAlternatingMap.ofSubsingleton_apply_apply, innerSL_apply_apply,
      EuclideanSpace.inner_single_right, conj_trivial, one_mul]
    congr 1
    funext i
    rw [Subsingleton.elim i 0]

/-- **Flux form**: the vector `v` as the 2-form `ι_v vol`, `(a, b) ↦ det (v, a, b)`. Its
inverse reads off `(ω(e₁,e₂), ω(e₂,e₀), ω(e₀,e₁))`. Natural for the magnetic field and
the current density (objects integrated over surfaces). -/
@[expose] def flux : Euclid3 ≃ₗ[ℝ] Form 2 where
  toFun v := volForm.curryLeft v
  map_add' u v := by simp
  map_smul' c v := by simp
  invFun ω := WithLp.toLp 2 ![ω ![coordVec 1, coordVec 2], ω ![coordVec 2, coordVec 0],
    ω ![coordVec 0, coordVec 1]]
  left_inv v := by
    ext i
    fin_cases i <;>
      simp [ContinuousAlternatingMap.curryLeft_apply_apply, volForm_vec]
  right_inv ω := by
    apply ext_basis
    intro v hv
    have hv' : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    have h01 : v 0 ≠ v 1 := fun h => by simpa using hv h
    generalize v 0 = p at *
    generalize v 1 = q at *
    subst hv'
    have : (fun i => coordVec (![p, q] i)) = ![coordVec p, coordVec q] := by
      ext i; fin_cases i <;> rfl
    rw [this]
    fin_cases p <;> fin_cases q <;>
      first
      | exact absurd rfl h01
      | (simp [ContinuousAlternatingMap.curryLeft_apply_apply, volForm_vec]; done)
      | simpa [ContinuousAlternatingMap.curryLeft_apply_apply, volForm_vec] using
          (form2_swap ω _ _).symm

/-- **Density**: the scalar `c` as the 3-form `c · vol`. Its inverse evaluates on
`(e₀, e₁, e₂)`. Natural for divergences and charge or mass densities (objects
integrated over volumes). -/
@[expose] def density : ℝ ≃ₗ[ℝ] Form 3 where
  toFun c := c • volForm
  map_add' a b := add_smul a b volForm
  map_smul' a b := by simp [mul_smul]
  invFun ω := ω ![coordVec 0, coordVec 1, coordVec 2]
  left_inv c := by simp [volForm_vec]
  right_inv ω := by
    apply ext_basis
    intro v hv
    have hv' : v = ![v 0, v 1, v 2] := by ext i; fin_cases i <;> rfl
    have h01 : v 0 ≠ v 1 := fun h => by simpa using hv h
    have h02 : v 0 ≠ v 2 := fun h => by simpa using hv h
    have h12 : v 1 ≠ v 2 := fun h => by simpa using hv h
    generalize v 0 = p at *
    generalize v 1 = q at *
    generalize v 2 = r at *
    subst hv'
    have : (fun i => coordVec (![p, q, r] i)) = ![coordVec p, coordVec q, coordVec r] := by
      ext i; fin_cases i <;> rfl
    rw [this]
    have e1 := form3_swap01 ω (coordVec 1) (coordVec 0) (coordVec 2)
    have e2 := form3_swap12 ω (coordVec 0) (coordVec 2) (coordVec 1)
    have e3 : ω ![coordVec 1, coordVec 2, coordVec 0] =
        ω ![coordVec 0, coordVec 1, coordVec 2] := by
      rw [form3_swap12, form3_swap01, neg_neg]
    have e4 : ω ![coordVec 2, coordVec 0, coordVec 1] =
        ω ![coordVec 0, coordVec 1, coordVec 2] := by
      rw [form3_swap01, form3_swap12, neg_neg]
    have e5 : ω ![coordVec 2, coordVec 1, coordVec 0] =
        -ω ![coordVec 0, coordVec 1, coordVec 2] := by
      rw [form3_swap01, e3]
    fin_cases p <;> fin_cases q <;> fin_cases r <;>
      simp [volForm_vec, e1, e2, e3, e4, e5] at h01 h02 h12 ⊢

/-- **Hodge star** from 2-forms to 1-forms: `⋆(ι_v vol) = v♭`. -/
@[expose] def hodge : Form 2 ≃ₗ[ℝ] Form 1 := flux.symm.trans flat

/-- The Hodge star of a flux form is the flat of the same vector. -/
@[simp] theorem hodge_flux (v : Euclid3) : hodge (flux v) = flat v := by simp [hodge]

/-- The inverse Hodge star of a flat is the flux form of the same vector. -/
@[simp] theorem hodge_symm_flat (v : Euclid3) : hodge.symm (flat v) = flux v := by
  simp [hodge]

/-- `v♭` evaluated on a vector is the inner product. -/
@[simp] theorem flat_apply (v : Euclid3) (w : Fin 1 → Euclid3) :
    flat v w = inner ℝ v (w 0) := rfl

/-- The flux form on two vectors is the triple product. -/
theorem flux_apply (v a b : Euclid3) : flux v ![a, b] = volForm ![v, a, b] := rfl

/-- The flux form on a vector prepended to a one-vector tuple. -/
theorem flux_cons (v a : Euclid3) (w : Fin 1 → Euclid3) :
    flux v (vecCons a w) = volForm ![v, a, w 0] := by
  rw [show vecCons a w = ![a, w 0] from by ext i; fin_cases i <;> rfl]
  rfl

/-- The density on three vectors. -/
theorem density_apply (c : ℝ) (v : Fin 3 → Euclid3) : density c v = c * volForm v := rfl

/-- Components of `♯`. -/
theorem flat_symm_apply (ω : Form 1) (i : Fin 3) : flat.symm ω i = ω fun _ => coordVec i :=
  rfl

/-- The vector of a 2-form. -/
theorem flux_symm_eq (ω : Form 2) : flux.symm ω =
    WithLp.toLp 2 ![ω ![coordVec 1, coordVec 2], ω ![coordVec 2, coordVec 0],
      ω ![coordVec 0, coordVec 1]] := rfl

/-- The scalar of a 3-form. -/
theorem density_symm_apply (ω : Form 3) :
    density.symm ω = ω ![coordVec 0, coordVec 1, coordVec 2] := rfl

/-! ## The exterior derivative is curl and divergence -/

/-- Algebraic dictionary for the curl: alternatizing `v ↦ (L v)♭` gives the flux form of
`curlOp L`. -/
theorem alternatize_flat (L : Euclid3 →L[ℝ] Euclid3) :
    ContinuousAlternatingMap.alternatizeUncurryFin
      ((flat.toContinuousLinearEquiv : Euclid3 →L[ℝ] Form 1) ∘L L) = flux (curlOp L) := by
  rw [← LinearEquiv.symm_apply_eq, flux_symm_eq]
  ext i
  fin_cases i <;>
    simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_two, curlOp,
      Fin.removeNth, coordVec, EuclideanSpace.inner_single_right] <;> ring

/-- Algebraic dictionary for the divergence: alternatizing `v ↦ ι_{L v} vol` gives
`(divOp L) · vol`. -/
theorem alternatize_flux (L : Euclid3 →L[ℝ] Euclid3) :
    ContinuousAlternatingMap.alternatizeUncurryFin
      ((flux.toContinuousLinearEquiv : Euclid3 →L[ℝ] Form 2) ∘L L) = density (divOp L) := by
  rw [← LinearEquiv.symm_apply_eq, density_symm_apply, divOp_apply]
  have r0 : Fin.removeNth (0 : Fin 3) ![coordVec 0, coordVec 1, coordVec 2]
      = ![coordVec 1, coordVec 2] := by ext i; fin_cases i <;> rfl
  have r1 : Fin.removeNth (1 : Fin 3) ![coordVec 0, coordVec 1, coordVec 2]
      = ![coordVec 0, coordVec 2] := by ext i; fin_cases i <;> rfl
  have r2 : Fin.removeNth (2 : Fin 3) ![coordVec 0, coordVec 1, coordVec 2]
      = ![coordVec 0, coordVec 1] := by ext i; fin_cases i <;> rfl
  simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_three, r0, r1, r2,
    flux_apply, volForm_vec]

/-- **`d(B♭) = flux (∇ × B)`**, at every point and with no differentiability hypothesis
(both sides use the Fréchet derivative, which is `0` where `B` is not differentiable). -/
theorem extDeriv_flat (B : Euclid3 → Euclid3) (x : Euclid3) :
    extDeriv (fun y => flat (B y)) x = flux (fieldCurl B x) := by
  have h : fderiv ℝ (fun y => flat (B y)) x
      = (flat.toContinuousLinearEquiv : Euclid3 →L[ℝ] Form 1) ∘L fderiv ℝ B x :=
    flat.toContinuousLinearEquiv.comp_fderiv
  rw [extDeriv, h, alternatize_flat, fieldCurl]

/-- **`d(ι_B vol) = (∇ · B) vol`**, at every point and with no differentiability
hypothesis. -/
theorem extDeriv_flux (B : Euclid3 → Euclid3) (x : Euclid3) :
    extDeriv (fun y => flux (B y)) x = density (fieldDiv B x) := by
  have h : fderiv ℝ (fun y => flux (B y)) x
      = (flux.toContinuousLinearEquiv : Euclid3 →L[ℝ] Form 2) ∘L fderiv ℝ B x :=
    flux.toContinuousLinearEquiv.comp_fderiv
  rw [extDeriv, h, alternatize_flux, fieldDiv]

/-- The differential `dp` of a scalar field, as a 1-form. -/
@[expose] def formGrad (p : Euclid3 → ℝ) (x : Euclid3) : Form 1 :=
  ContinuousAlternatingMap.ofSubsingleton ℝ Euclid3 ℝ (0 : Fin 1) (fderiv ℝ p x)

/-- `dp` is the exterior derivative of `p` regarded as a 0-form. -/
theorem extDeriv_formGrad (p : Euclid3 → ℝ) (x : Euclid3) :
    extDeriv (fun y => ContinuousAlternatingMap.constOfIsEmpty ℝ Euclid3 (Fin 0) (p y)) x
      = formGrad p x :=
  extDeriv_constOfIsEmpty p x

/-- `dp` evaluated on a vector is the directional derivative. -/
@[simp] theorem formGrad_apply (p : Euclid3 → ℝ) (x : Euclid3) (w : Fin 1 → Euclid3) :
    formGrad p x w = fderiv ℝ p x (w 0) := rfl

/-! ## Vacuum fields as closed and co-closed 2-forms -/

/-- **Vacuum magnetic field as a 2-form** on a region `Ω`: `Ω` is open, `ω` is `C²` on
`Ω`, `dω = 0` (Gauss law: no magnetic charge) and `d(⋆ω) = 0` (Ampère's law with no
current), i.e. `ω` is a harmonic 2-form. -/
structure VacuumForm (Ω : Set Euclid3) (ω : Euclid3 → Form 2) : Prop where
  /-- The current-free region is open. -/
  isOpen : IsOpen Ω
  /-- The form is twice continuously differentiable on the region. -/
  contDiffOn : ContDiffOn ℝ 2 ω Ω
  /-- Gauss law for magnetism: the flux form is closed. -/
  closed : ∀ x ∈ Ω, extDeriv ω x = 0
  /-- Ampère's law with zero current: the flux form is co-closed. -/
  coclosed : ∀ x ∈ Ω, extDeriv (fun y => hodge (ω y)) x = 0

/-- Fields of vectors and of 2-forms correspond, pointwise by `flux`. -/
@[expose] def fluxField : (Euclid3 → Euclid3) ≃ (Euclid3 → Form 2) :=
  (Equiv.refl Euclid3).arrowCongr flux.toEquiv

/-- `fluxField` is pointwise `flux`. -/
@[simp] theorem fluxField_apply (B : Euclid3 → Euclid3) (x : Euclid3) :
    fluxField B x = flux (B x) := rfl

/-- The inverse of `fluxField` is pointwise `flux.symm`. -/
@[simp] theorem fluxField_symm_apply (ω : Euclid3 → Form 2) (x : Euclid3) :
    fluxField.symm ω x = flux.symm (ω x) := rfl

/-- **Vector language to form language.** The flux form of `B` is a vacuum form exactly
when `B` is a vacuum field. -/
theorem vacuumForm_flux_iff {Ω : Set Euclid3} {B : Euclid3 → Euclid3} :
    VacuumForm Ω (fluxField B) ↔ VacuumField Ω B := by
  have hc : ContDiffOn ℝ 2 (fluxField B) Ω ↔ ContDiffOn ℝ 2 B Ω :=
    flux.toContinuousLinearEquiv.comp_contDiffOn_iff
  constructor
  · intro h
    refine ⟨h.isOpen, hc.1 h.contDiffOn, fun x hx => ?_, fun x hx => ?_⟩
    · have := h.closed x hx
      rw [show fluxField B = fun y => flux (B y) from rfl, extDeriv_flux] at this
      simpa using this
    · have := h.coclosed x hx
      simp only [fluxField_apply, hodge_flux] at this
      rw [extDeriv_flat] at this
      simpa using this
  · intro h
    refine ⟨h.isOpen, hc.2 h.contDiffOn, fun x hx => ?_, fun x hx => ?_⟩
    · rw [show fluxField B = fun y => flux (B y) from rfl, extDeriv_flux,
        h.div_eq_zero x hx, map_zero]
    · simp only [fluxField_apply, hodge_flux]
      rw [extDeriv_flat, h.curl_eq_zero x hx, map_zero]

/-- **Form language to vector language.** The vector field of `ω` is a vacuum field
exactly when `ω` is a vacuum form. -/
theorem vacuumField_fluxSymm_iff {Ω : Set Euclid3} {ω : Euclid3 → Form 2} :
    VacuumField Ω (fluxField.symm ω) ↔ VacuumForm Ω ω := by
  rw [← vacuumForm_flux_iff, Equiv.apply_symm_apply]

/-! ## Force balance as an interior product -/

/-- The Cartesian data `Vec3` of the algebraic kernel as a vector of `Euclid3`. -/
@[expose] def vec : Vec3 ≃ₗ[ℝ] Euclid3 := (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm

/-- Components of `vec`. -/
@[simp] theorem vec_apply (v : Vec3) (i : Fin 3) : vec v i = v i := rfl

/-- **Static force balance in form language**: `ι_B ω_J = dp`, where `ω_B`, `ω_J` are
the flux 2-forms of the magnetic field and the current density, `B` is the vector of
`ω_B`, and `dp` is the supplied pressure differential (a 1-form). As for
`ForceBalance`, `dp` is supplied data: a claim must also prove that it is the
differential of a pressure field. -/
class FormForceBalance (ωB ωJ : Form 2) (dp : Form 1) : Prop where
  balance : ωJ.curryLeft (flux.symm ωB) = dp

/-- The dictionary for the Lorentz force: `ι_B ι_J vol = (J × B)♭`. -/
theorem curryLeft_flux (B J : Vec3) :
    (flux (vec J)).curryLeft (vec B) = flat (vec (J ⨯₃ B)) := by
  rw [← LinearEquiv.symm_apply_eq]
  ext i
  fin_cases i <;>
    simp [flat_symm_apply, flux_cons, volForm_vec, cross_apply] <;> ring

/-- **Vector language to form language.** -/
theorem formForceBalance_iff {B J g : Vec3} :
    FormForceBalance (flux (vec B)) (flux (vec J)) (flat (vec g)) ↔ ForceBalance B J g := by
  constructor
  · intro h
    have := h.balance
    rw [LinearEquiv.symm_apply_apply, curryLeft_flux] at this
    exact ⟨vec.injective (flat.injective this)⟩
  · intro h
    refine ⟨?_⟩
    rw [LinearEquiv.symm_apply_apply, curryLeft_flux, h.balance]

/-- **Form language to vector language.** -/
theorem forceBalance_iff {ωB ωJ : Form 2} {dp : Form 1} :
    ForceBalance (vec.symm (flux.symm ωB)) (vec.symm (flux.symm ωJ)) (vec.symm (flat.symm dp))
      ↔ FormForceBalance ωB ωJ dp := by
  rw [← formForceBalance_iff]
  simp

/-- The field is tangent to the pressure surfaces: `dp(B) = 0`. This is
`field_tangency` in form language, obtained through the dictionary. -/
theorem form_field_tangency (ωB ωJ : Form 2) (dp : Form 1) [h : FormForceBalance ωB ωJ dp] :
    dp ![flux.symm ωB] = 0 := by
  have := forceBalance_iff.2 h
  have := field_tangency (vec.symm (flux.symm ωB)) (vec.symm (flux.symm ωJ))
    (vec.symm (flat.symm dp))
  have key : dp ![flux.symm ωB] = flat (flat.symm dp) ![flux.symm ωB] := by simp
  rw [key, flat_apply, real_inner_comm]
  simp only [dotProduct, Fin.sum_univ_three, PiLp.inner_apply, vec] at this ⊢
  simp at this ⊢
  linarith

end PlasmaLean.Forms
