/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.Forms
public import PlasmaLean.Theory.Fields.FirstIntegral
public import PlasmaLean.Theory.Fields.FluxSurfaceTwoForm
public import PlasmaLean.Theory.Fields.WeakQuasisymmetry
public import PlasmaLean.Theory.Kinetic.Noether
public import PlasmaLean.Theory.Equilibrium.Slab

/-!
# Differential-form versions of theory-layer notions (bridges to `Kernel/Forms`)

`Kernel/Forms` states the two kernel laws with differential forms on `ℝ³`. This module does
the same for four notions of the theory layer, and adds one case of the wedge product and the
contact condition. Each is stated afresh with forms, and proved
equivalent to the existing vector-language notion; nothing existing is changed. Notation:
`ω_B = flux B = ι_B vol`, `β = flat B = B♭`, `dψ = formGrad ψ`.

* **First integral.** `FirstIntegralOn B ψ U` (`Dψ(B) = 0`) is `FormFirstIntegralOn ω ψ U`
  (`ι_B dψ = 0`, with `B` the vector of `ω`): `formFirstIntegralOn_flux_iff`.
* **Symmetric flux.** `Kinetic.SymmetricFlux B G K` is `FormSymmetricFlux ω γ K`
  (`ι_K ω = -γ`): `formSymmetricFlux_iff`. The 1-form `γ` is supplied data, as `G` is; the
  law has content only when `γ = dψ` is proved separately.
* **Weak quasisymmetry.** `WeakQS B ξ ψ T` is `FormWeakQS ω ξ ψ T` (`d(ι_ξ vol) = 0`,
  `ι_ξ ω = -dψ`, `d|B|(ξ) = 0`): `formWeakQS_flux_iff`.
* **Beltrami fields.** `IsBeltramiOn B lam U` (`B` differentiable and `∇ × B = λB`, new here)
  is `FormBeltramiOn β lam U` (`dβ = λ ⋆β`): `formBeltramiOn_flat_iff`. It is the curl equation
  only: `∇ · B = 0` is **not** part of it, and the zero field satisfies it for every `λ`.

Each bridge also has the converse form (`firstIntegralOn_fluxSymm_iff`, `symmetricFlux_iff`,
`weakQS_fluxSymm_iff`, `isBeltramiOn_flatSymm_iff`).

Algebraic dictionary: `curryLeft_flux_cross` (`ι_w ι_v vol = (v × w)♭`), `flat_gradient`
(`(∇ψ)♭ = dψ`), `flux_apply_eq_magneticTwoForm`, `divOp_eq_divergence`, `curlOp_eq_curl`.

**Contact forms.** `wedge12 a b` is the wedge product of a 1-form and a 2-form; it is defined
through the equivalences (`v♭ ∧ ι_w vol = ⟪v, w⟫ vol`) and `wedge12_apply` proves that it is the
alternating product `a(u) b(v,w) - a(v) b(u,w) + a(w) b(u,v)`. `IsContactAt β x` is
`β ∧ dβ ≠ 0` at `x`. `wedge12_flat_extDeriv` is `β ∧ dβ = ⟪B, ∇ × B⟫ vol`, and
`isContactAt_of_beltrami`: a Beltrami field with `λ(x) ≠ 0` and `B(x) ≠ 0` has a contact form
`B♭` at `x` (the pointwise half of the Etnyre–Ghrist correspondence, Nonlinearity 13 (2000)
441).

## Sanity checks

* The helical field `(cos z, sin z, 0)` is Beltrami with `λ = -1` on all of space, and `B♭` is
  a contact form everywhere (`helicalField_beltrami`, `helicalField_contact`). It is the
  slab field `Equilibrium.helicalSlab` of the theory layer (`helicalField_eq_helicalSlab`).
* A constant field is Beltrami with `λ = 0` and its `B♭` is nowhere contact
  (`const_beltrami`, `const_not_contact`). A curl-free field is never contact
  (`not_isContactAt_of_curl_eq_zero`), so a vacuum field is not.
* Weak quasisymmetry and first integrals: accepted fixtures of the vector language are
  transported (`formWeakQS_uniform`, `formWeakQS_screw`, `clebsch_formFirstIntegral_left`).
* Rejected fixtures, vacuity regressions and checks that do not go through the dictionary are in
  `Sanity/AuditForms` (audit of 16 November 2026).

Scope: `ℝ³` with the Euclidean metric. Not covered: the Reeb field, the converse direction of
the Etnyre–Ghrist correspondence (a metric adapted to a contact form), contact topology.
-/

open scoped RealInnerProductSpace
open InnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum PlasmaLean.Fields Matrix

/-! ## Algebraic dictionary -/

/-- The kernel divergence agrees with `Fields.divergence`. -/
theorem divOp_eq_divergence (L : Space →L[ℝ] Space) : divOp L = divergence L := by
  rw [divOp_apply, divergence_apply]

/-- The kernel curl agrees with `Fields.curl`. -/
theorem curlOp_eq_curl (L : Space →L[ℝ] Space) : curlOp L = curl L := by
  obtain ⟨h0, h1, h2⟩ := curl_coords L
  apply space_ext <;> simp [curlOp, h0, h1, h2]

/-- **`ι_w ι_v vol = (v × w)♭`**: the interior product of a flux form is the flat of a cross
product. -/
theorem curryLeft_flux_cross (v w : Space) : (flux v).curryLeft w = flat (cross v w) := by
  rw [← LinearEquiv.symm_apply_eq]
  obtain ⟨h0, h1, h2⟩ := cross_coords v w
  ext i
  fin_cases i <;>
    simp [flat_symm_apply, flux_cons, volForm_vec, h0, h1, h2] <;> ring

/-- The flux form evaluated on two vectors is `Fields.magneticTwoForm`. -/
theorem flux_apply_eq_magneticTwoForm (B u v : Space) :
    flux B ![u, v] = magneticTwoForm B u v := by
  obtain ⟨h0, h1, h2⟩ := cross_coords u v
  rw [flux_apply, volForm_vec, magneticTwoForm, inner_coords3, h0, h1, h2]
  ring

/-- **`(∇ψ)♭ = dψ`**, with no differentiability hypothesis. -/
theorem flat_gradient (ψ : Space → ℝ) (x : Space) : flat (gradient ψ x) = formGrad ψ x := by
  ext w
  rw [flat_apply, formGrad_apply, inner_gradient_left]

/-- `♯` of `dψ` is the gradient. -/
theorem flat_symm_formGrad (ψ : Space → ℝ) (x : Space) :
    flat.symm (formGrad ψ x) = gradient ψ x := by
  rw [← flat_gradient, LinearEquiv.symm_apply_apply]

/-- A 1-form evaluated on a vector is the inner product with its `♯`. -/
theorem form1_apply (a : Form 1) (v : Space) : a ![v] = ⟪flat.symm a, v⟫ := by
  conv_lhs => rw [← flat.apply_symm_apply a]
  rfl

/-- **`ι_{a♯ × b♯} vol = a ∧ b`** for 1-forms `a`, `b`: the flux form of a cross product is
the wedge product of the two 1-forms, `(u, v) ↦ a(u) b(v) - a(v) b(u)`. -/
theorem flux_cross_apply (a b : Form 1) (u v : Space) :
    flux (cross (flat.symm a) (flat.symm b)) ![u, v] = a ![u] * b ![v] - a ![v] * b ![u] := by
  obtain ⟨h0, h1, h2⟩ := cross_coords (flat.symm a) (flat.symm b)
  rw [flux_apply, volForm_vec, form1_apply, form1_apply, form1_apply, form1_apply, h0, h1, h2]
  simp only [inner_coords3]
  ring

/-! ## First integrals -/

/-- **First integral in form language**: `ψ` is differentiable on `U` and `ι_B dψ = 0`,
where `B` is the vector of the flux form `ω`. -/
@[expose] def FormFirstIntegralOn (ω : Space → Form 2) (ψ : Space → ℝ) (U : Set Space) : Prop :=
  ∀ x ∈ U, DifferentiableAt ℝ ψ x ∧ formGrad ψ x ![flux.symm (ω x)] = 0

/-- Vector language to form language. -/
theorem formFirstIntegralOn_flux_iff {B : Space → Space} {ψ : Space → ℝ} {U : Set Space} :
    FormFirstIntegralOn (fluxField B) ψ U ↔ FirstIntegralOn B ψ U := by
  simp [FormFirstIntegralOn, FirstIntegralOn]

/-- Form language to vector language. -/
theorem firstIntegralOn_fluxSymm_iff {ω : Space → Form 2} {ψ : Space → ℝ} {U : Set Space} :
    FirstIntegralOn (fluxField.symm ω) ψ U ↔ FormFirstIntegralOn ω ψ U := by
  rw [← formFirstIntegralOn_flux_iff, Equiv.apply_symm_apply]

/-- Sanity (transported from `clebsch_firstIntegral_left`): for the Clebsch flux form, the
flux form of `∇ψ × ∇χ` (which is `dψ ∧ dχ` by `flux_cross_apply`), `ψ` is a first integral. -/
theorem clebsch_formFirstIntegral_left (ψ χ : Space → ℝ) (U : Set Space)
    (hψ : ∀ x ∈ U, DifferentiableAt ℝ ψ x) :
    FormFirstIntegralOn (fluxField (clebschField ψ χ)) ψ U :=
  formFirstIntegralOn_flux_iff.2 (clebsch_firstIntegral_left ψ χ U hψ)

/-! ## Symmetric flux: `ι_K ω_B = -dψ` -/

/-- **Symmetric flux in form language**: `ι_K ω = -γ` at every point of space (as
`Kinetic.SymmetricFlux`, it has no region argument). The 1-form `γ` is supplied data: with
`γ = dψ` this says that `K` is a Hamiltonian symmetry of the flux form with Hamiltonian `ψ`,
but for `γ := -ι_K ω` it holds for every `ω` and `K` (regression
`Sanity/AuditForms.formSymmetricFlux_of_interior`). -/
@[expose] def FormSymmetricFlux (ω : Space → Form 2) (γ : Space → Form 1) (K : Space → Space) :
    Prop :=
  ∀ x, (ω x).curryLeft (K x) = -γ x

/-- Vector language to form language: `Kinetic.SymmetricFlux B G K`
(`⟪K, v × B⟫ = -⟪G, v⟫` for all `v`) is `ι_K ω_B = -G♭`. -/
theorem formSymmetricFlux_iff {B G K : Space → Space} :
    FormSymmetricFlux (fluxField B) (fun x => flat (G x)) K ↔ Kinetic.SymmetricFlux B G K := by
  have key : ∀ x v : Space, ⟪K x, cross v (B x)⟫ = ⟪cross (B x) (K x), v⟫ := fun x v => by
    obtain ⟨a0, a1, a2⟩ := cross_coords v (B x)
    obtain ⟨b0, b1, b2⟩ := cross_coords (B x) (K x)
    rw [inner_coords3, inner_coords3, a0, a1, a2, b0, b1, b2]
    ring
  constructor
  · intro h x v
    have hx := h x
    rw [fluxField_apply, curryLeft_flux_cross, ← map_neg] at hx
    rw [key, flat.injective hx, inner_neg_left]
  · intro h x
    rw [fluxField_apply, curryLeft_flux_cross, ← map_neg]
    congr 1
    refine ext_inner_right ℝ fun v => ?_
    rw [← key, h x v, inner_neg_left]

/-- Form language to vector language. -/
theorem symmetricFlux_iff {ω : Space → Form 2} {γ : Space → Form 1} {K : Space → Space} :
    Kinetic.SymmetricFlux (fluxField.symm ω) (fun x => flat.symm (γ x)) K ↔
      FormSymmetricFlux ω γ K := by
  rw [← formSymmetricFlux_iff]
  simp [FormSymmetricFlux]

/-- With `γ = dψ` and `ψ` differentiable, a symmetric flux makes `ψ` a first integral of the
field (the form version of `SymmetricFlux.firstIntegral`): `dψ(B) = -ω(K, B) = ω(B, K)` and
`ι_B ω = 0`. -/
theorem FormSymmetricFlux.formFirstIntegralOn {ω : Space → Form 2} {K : Space → Space}
    {ψ : Space → ℝ} (h : FormSymmetricFlux ω (formGrad ψ) K) (hψ : Differentiable ℝ ψ) :
    FormFirstIntegralOn ω ψ Set.univ := by
  intro x _
  refine ⟨hψ x, ?_⟩
  have hx := h x
  rw [eq_neg_iff_add_eq_zero] at hx
  have h1 := congrArg (fun a : Form 1 => a ![flux.symm (ω x)]) hx
  obtain ⟨B, hB⟩ := flux.surjective (ω x)
  rw [hB.symm, LinearEquiv.symm_apply_apply] at h1 ⊢
  have h2 : (flux B).curryLeft (K x) ![B] = 0 := by
    simp [flux_cons, volForm_vec]
    ring
  have h3 : (flux B).curryLeft (K x) ![B] + formGrad ψ x ![B] = 0 := h1
  linarith

/-! ## Weak quasisymmetry -/

/-- **Weak quasisymmetry in form language** for a flux form `ω` (with `B` its vector), a
generator `ξ` and a potential `ψ`, pointwise on `T`: `d(ι_ξ vol) = 0`, `ι_ξ ω = -dψ` and
`d|B|(ξ) = 0`, with `|B|`, `ξ`, `ψ` differentiable and `ξ ≠ 0`. As in `WeakQS`, `ω` itself
is not required to be closed or differentiable, `|B|` is the Euclidean norm of the vector of
`ω`, and the zero form with a constant generator satisfies it
(`Sanity/AuditForms.formWeakQS_zero`). -/
structure FormWeakQS (ω : Space → Form 2) (ξ : Space → Space) (ψ : Space → ℝ) (T : Set Space) :
    Prop where
  /-- `|B|` is differentiable on `T`. -/
  normB_diff : ∀ x ∈ T, DifferentiableAt ℝ (fun y => ‖flux.symm (ω y)‖) x
  /-- The generator is differentiable on `T`. -/
  xi_diff : ∀ x ∈ T, DifferentiableAt ℝ ξ x
  /-- The potential is differentiable on `T`. -/
  psi_diff : ∀ x ∈ T, DifferentiableAt ℝ ψ x
  /-- The generator does not vanish on `T`. -/
  xi_ne : ∀ x ∈ T, ξ x ≠ 0
  /-- `ξ` is volume preserving: `d(ι_ξ vol) = 0`. -/
  div_free : ∀ x ∈ T, extDeriv (fun y => flux (ξ y)) x = 0
  /-- `ι_ξ ω = -dψ`. -/
  interior : ∀ x ∈ T, (ω x).curryLeft (ξ x) = -formGrad ψ x
  /-- `d|B|(ξ) = 0`. -/
  qs : ∀ x ∈ T, formGrad (fun y => ‖flux.symm (ω y)‖) x ![ξ x] = 0

/-- Vector language to form language. -/
theorem formWeakQS_flux_iff {B ξ : Space → Space} {ψ : Space → ℝ} {T : Set Space} :
    FormWeakQS (fluxField B) ξ ψ T ↔ WeakQS B ξ ψ T := by
  have hdiv : ∀ x, extDeriv (fun y => flux (ξ y)) x = 0 ↔ divergence (fderiv ℝ ξ x) = 0 :=
    fun x => by
      rw [extDeriv_flux, fieldDiv, divOp_eq_divergence]
      simp
  have hint : ∀ x, (fluxField B x).curryLeft (ξ x) = -formGrad ψ x ↔
      cross (B x) (ξ x) = -gradient ψ x := fun x => by
    rw [fluxField_apply, curryLeft_flux_cross, ← flat_gradient, ← map_neg]
    exact flat.injective.eq_iff
  constructor
  · intro h
    exact
      { normB_diff := fun x hx => by simpa using h.normB_diff x hx
        xi_diff := h.xi_diff
        psi_diff := h.psi_diff
        xi_ne := h.xi_ne
        div_free := fun x hx => (hdiv x).1 (h.div_free x hx)
        cross_eq := fun x hx => (hint x).1 (h.interior x hx)
        qs := fun x hx => by simpa [qsError] using h.qs x hx }
  · intro h
    exact
      { normB_diff := fun x hx => by simpa using h.normB_diff x hx
        xi_diff := h.xi_diff
        psi_diff := h.psi_diff
        xi_ne := h.xi_ne
        div_free := fun x hx => (hdiv x).2 (h.div_free x hx)
        interior := fun x hx => (hint x).2 (h.cross_eq x hx)
        qs := fun x hx => by simpa [qsError] using h.qs x hx }

/-- Form language to vector language. -/
theorem weakQS_fluxSymm_iff {ω : Space → Form 2} {ξ : Space → Space} {ψ : Space → ℝ}
    {T : Set Space} : WeakQS (fluxField.symm ω) ξ ψ T ↔ FormWeakQS ω ξ ψ T := by
  rw [← formWeakQS_flux_iff, Equiv.apply_symm_apply]

/-- Sanity (transported from `weakQS_uniform`): the constant flux form `dx ∧ dy` with
generator `e_z`. -/
theorem formWeakQS_uniform :
    FormWeakQS (fluxField fun _ => basis 2) (fun _ => basis 2) (fun _ => 0) Set.univ :=
  formWeakQS_flux_iff.2 weakQS_uniform

/-- Sanity (transported from `weakQS_screw`): the axisymmetric screw-pinch flux form with
the rotation generator. -/
theorem formWeakQS_screw :
    FormWeakQS (fluxField screwField) rotGen screwPsi {x | 0 < x 0 ^ 2 + x 1 ^ 2} :=
  formWeakQS_flux_iff.2 weakQS_screw

/-- A weakly quasisymmetric flux form has `ψ` as a first integral (transported from
`WeakQS.inner_field_gradient`). -/
theorem FormWeakQS.formFirstIntegralOn {ω : Space → Form 2} {ξ : Space → Space} {ψ : Space → ℝ}
    {T : Set Space} (h : FormWeakQS ω ξ ψ T) : FormFirstIntegralOn ω ψ T := by
  have h' := weakQS_fluxSymm_iff.2 h
  intro x hx
  refine ⟨h.psi_diff x hx, ?_⟩
  have := h'.inner_field_gradient hx
  rw [form1_apply, flat_symm_formGrad, real_inner_comm]
  simpa using this

/-! ## Beltrami fields and contact forms -/

/-- **Beltrami curl equation** on `U` with proportionality function `lam`: `B` is
differentiable and `∇ × B = λ B` at each point of `U`.

Scope (audit finding AD-M1). Differentiability is required because Lean's `fderiv` is `0` at
a non-differentiable point, which would make every kinked field "Beltrami with `λ = 0`" there.
The predicate is the curl equation only. It does **not** include `∇ · B = 0`, so a Beltrami
field in this sense need not be a magnetic field (the field `B = x` has `λ = 0` and
`∇ · B = 3`), and the zero field satisfies it for every `λ`. A force-free magnetic field is
`IsBeltramiOn` together with `fieldDiv B x = 0`. -/
@[expose] def IsBeltramiOn (B : Space → Space) (lam : Space → ℝ) (U : Set Space) : Prop :=
  ∀ x ∈ U, DifferentiableAt ℝ B x ∧ fieldCurl B x = lam x • B x

/-- **Beltrami 1-form**: `β` is differentiable and `dβ = λ ⋆β`, where `⋆β = hodge.symm β`
is the Hodge star of the 1-form `β` (the inverse of `hodge`, since `⋆⋆ = 1` on `ℝ³`). -/
@[expose] def FormBeltramiOn (β : Space → Form 1) (lam : Space → ℝ) (U : Set Space) : Prop :=
  ∀ x ∈ U, DifferentiableAt ℝ β x ∧ extDeriv β x = lam x • hodge.symm (β x)

/-- Vector language to form language. -/
theorem formBeltramiOn_flat_iff {B : Space → Space} {lam : Space → ℝ} {U : Set Space} :
    FormBeltramiOn (fun x => flat (B x)) lam U ↔ IsBeltramiOn B lam U := by
  refine forall₂_congr fun x _ => and_congr ?_ ?_
  · exact flat.toContinuousLinearEquiv.comp_differentiableAt_iff
  · rw [extDeriv_flat, hodge_symm_flat, ← map_smul]
    exact flux.injective.eq_iff

/-- The Beltrami equation with the theory layer's `Fields.curl`. -/
theorem isBeltramiOn_iff_curl {B : Space → Space} {lam : Space → ℝ} {U : Set Space} :
    IsBeltramiOn B lam U ↔
      ∀ x ∈ U, DifferentiableAt ℝ B x ∧ curl (fderiv ℝ B x) = lam x • B x := by
  simp only [IsBeltramiOn, fieldCurl, curlOp_eq_curl]

/-- **A Beltrami field is force-free in the sense of the kernel**: with the Ampère current
form `ω_J = d(B♭)` (the flux form of `∇ × B`; the factor `1/μ₀` is omitted), force balance
holds with zero pressure differential, `ι_B ω_J = 0`. -/
theorem IsBeltramiOn.formForceBalance {B : Space → Space} {lam : Space → ℝ} {U : Set Space}
    (h : IsBeltramiOn B lam U) {x : Space} (hx : x ∈ U) :
    FormForceBalance (flux (B x)) (flux (fieldCurl B x)) 0 := by
  refine ⟨?_⟩
  rw [LinearEquiv.symm_apply_apply, curryLeft_flux_cross, (h x hx).2]
  have : cross (lam x • B x) (B x) = 0 := by
    apply space_ext <;> simp [cross]
  rw [this, map_zero]

/-- Form language to vector language. -/
theorem isBeltramiOn_flatSymm_iff {β : Space → Form 1} {lam : Space → ℝ} {U : Set Space} :
    IsBeltramiOn (fun x => flat.symm (β x)) lam U ↔ FormBeltramiOn β lam U := by
  rw [← formBeltramiOn_flat_iff]
  simp

/-- **Wedge product of a 1-form and a 2-form**, a 3-form. It is defined through the
equivalences, `v♭ ∧ ι_w vol = ⟪v, w⟫ vol`; `wedge12_apply` shows that this is the alternating
product. -/
@[expose] def wedge12 (a : Form 1) (b : Form 2) : Form 3 :=
  density ⟪flat.symm a, flux.symm b⟫

/-- `v♭ ∧ ι_w vol = ⟪v, w⟫ vol`. -/
@[simp] theorem wedge12_flat_flux (v w : Space) : wedge12 (flat v) (flux w) = density ⟪v, w⟫ := by
  simp [wedge12]

/-- **The wedge product is the alternating product**:
`(a ∧ b)(u, v, w) = a(u) b(v, w) - a(v) b(u, w) + a(w) b(u, v)`. -/
theorem wedge12_apply (a : Form 1) (b : Form 2) (u v w : Space) :
    wedge12 a b ![u, v, w] =
      a ![u] * b ![v, w] - a ![v] * b ![u, w] + a ![w] * b ![u, v] := by
  obtain ⟨p, rfl⟩ := flat.surjective a
  obtain ⟨q, rfl⟩ := flux.surjective b
  rw [wedge12_flat_flux, density_apply]
  simp only [form1_apply, LinearEquiv.symm_apply_apply, flux_apply, volForm_vec, inner_coords3]
  ring

/-- `wedge12` is nonzero exactly when the inner product of the two vectors is. -/
theorem wedge12_ne_zero_iff (a : Form 1) (b : Form 2) :
    wedge12 a b ≠ 0 ↔ ⟪flat.symm a, flux.symm b⟫ ≠ 0 := by
  simp [wedge12]

/-- **Contact condition** for a 1-form `β` at `x`: `β ∧ dβ ≠ 0`. -/
@[expose] def IsContactAt (β : Space → Form 1) (x : Space) : Prop :=
  wedge12 (β x) (extDeriv β x) ≠ 0

/-- **`β ∧ dβ = ⟪B, ∇ × B⟫ vol`** for `β = B♭`. -/
theorem wedge12_flat_extDeriv (B : Space → Space) (x : Space) :
    wedge12 (flat (B x)) (extDeriv (fun y => flat (B y)) x) = density ⟪B x, fieldCurl B x⟫ := by
  rw [extDeriv_flat, wedge12_flat_flux]

/-- `B♭` is a contact form at `x` exactly when `⟪B, ∇ × B⟫ ≠ 0` there. -/
theorem isContactAt_flat_iff (B : Space → Space) (x : Space) :
    IsContactAt (fun y => flat (B y)) x ↔ ⟪B x, fieldCurl B x⟫ ≠ 0 := by
  rw [IsContactAt, wedge12_flat_extDeriv]
  simp

/-- **A Beltrami field with `λ ≠ 0` and `B ≠ 0` has a contact form `B♭`**:
`β ∧ dβ = λ |B|² vol ≠ 0`. -/
theorem isContactAt_of_beltrami {B : Space → Space} {lam : Space → ℝ} {U : Set Space}
    (h : IsBeltramiOn B lam U) {x : Space} (hx : x ∈ U) (hl : lam x ≠ 0) (hB : B x ≠ 0) :
    IsContactAt (fun y => flat (B y)) x := by
  rw [isContactAt_flat_iff, (h x hx).2, inner_smul_right, real_inner_self_eq_norm_sq]
  exact mul_ne_zero hl (pow_ne_zero 2 (norm_ne_zero_iff.2 hB))

/-- **Sharp form**: for a Beltrami field, `B♭` is a contact form at `x` exactly when
`λ(x) ≠ 0` and `B(x) ≠ 0`. -/
theorem IsBeltramiOn.isContactAt_iff {B : Space → Space} {lam : Space → ℝ} {U : Set Space}
    (h : IsBeltramiOn B lam U) {x : Space} (hx : x ∈ U) :
    IsContactAt (fun y => flat (B y)) x ↔ lam x ≠ 0 ∧ B x ≠ 0 := by
  rw [isContactAt_flat_iff, (h x hx).2, inner_smul_right, real_inner_self_eq_norm_sq,
    mul_ne_zero_iff, ne_eq (‖B x‖ ^ 2), pow_eq_zero_iff two_ne_zero, norm_eq_zero]

/-- A curl-free field is never contact: `β ∧ dβ = 0` when `dβ = 0`. In particular a vacuum
field is not contact. -/
theorem not_isContactAt_of_curl_eq_zero {B : Space → Space} {x : Space}
    (h : fieldCurl B x = 0) : ¬ IsContactAt (fun y => flat (B y)) x := by
  rw [isContactAt_flat_iff, h, inner_zero_right]
  exact fun h => h rfl

/-- A vacuum field has no contact point in its region. -/
theorem not_isContactAt_of_vacuumField {Ω : Set Euclid3} {B : Euclid3 → Euclid3}
    (hV : VacuumField Ω B) {x : Euclid3} (hx : x ∈ Ω) :
    ¬ IsContactAt (fun y => flat (B y)) x :=
  not_isContactAt_of_curl_eq_zero (hV.curl_eq_zero x hx)

/-! ### Sanity: constant and helical fields -/

/-- Degenerate case: a constant field is Beltrami with `λ = 0`. -/
theorem const_beltrami (B₀ : Space) (U : Set Space) :
    IsBeltramiOn (fun _ => B₀) (fun _ => 0) U := by
  intro x _
  refine ⟨differentiableAt_const _, ?_⟩
  have : fderiv ℝ (fun _ : Space => B₀) x = 0 := fderiv_const_apply B₀
  rw [fieldCurl, this, zero_smul, curlOp_eq_zero_iff]
  simp

/-- A constant field is nowhere contact. -/
theorem const_not_contact (B₀ x : Space) : ¬ IsContactAt (fun _ => flat B₀) x := by
  apply not_isContactAt_of_curl_eq_zero (B := fun _ => B₀)
  have := (const_beltrami B₀ Set.univ x (Set.mem_univ x)).2
  simpa using this

/-- The helical field `(cos z, sin z, 0)` on `ℝ³`. -/
@[expose] def helicalField (y : Space) : Space :=
  WithLp.toLp 2 ![Real.cos (y 2), Real.sin (y 2), 0]

/-- It is the one-dimensional Beltrami example `Equilibrium.helicalSlab`, as a field on
`ℝ³`. -/
theorem helicalField_eq_helicalSlab (y : Space) :
    helicalField y = vec (Equilibrium.helicalSlab (y 2)) := rfl

/-- The Fréchet derivative of the helical field. -/
theorem helicalField_hasFDerivAt (x : Space) :
    HasFDerivAt helicalField
      (((-Real.sin (x 2)) • (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)).smulRight
          (basis 0) +
        ((Real.cos (x 2)) • (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)).smulRight
          (basis 1)) x := by
  have hp : HasFDerivAt (fun y : Space => y 2)
      (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt
  have h0 := (hp.cos).smul_const (basis 0 : Space)
  have h1 := (hp.sin).smul_const (basis 1 : Space)
  refine (h0.add h1).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  apply space_ext <;> simp [helicalField, basis]

/-- The helical field is differentiable. -/
theorem helicalField_differentiableAt (x : Space) : DifferentiableAt ℝ helicalField x :=
  (helicalField_hasFDerivAt x).differentiableAt

/-- The derivative of the helical field, in components. -/
theorem helicalField_fderiv_apply (x v : Space) :
    fderiv ℝ helicalField x v =
      WithLp.toLp 2 ![-Real.sin (x 2) * v 2, Real.cos (x 2) * v 2, 0] := by
  rw [(helicalField_hasFDerivAt x).fderiv]
  apply space_ext <;> simp [basis]

/-- `∇ × B = -B` for the helical field. -/
theorem helicalField_curl (x : Space) : fieldCurl helicalField x = (-1 : ℝ) • helicalField x := by
  apply space_ext <;>
    simp [fieldCurl, curlOp, helicalField_fderiv_apply, helicalField, coordVec]

/-- Concrete instance: the helical field is Beltrami with `λ = -1` on all of space. -/
theorem helicalField_beltrami : IsBeltramiOn helicalField (fun _ => -1) Set.univ :=
  fun x _ => ⟨helicalField_differentiableAt x, helicalField_curl x⟩

/-- The same statement for the 1-form `β = cos z dx + sin z dy`: `dβ = -⋆β`. -/
theorem helicalForm_beltrami :
    FormBeltramiOn (fun y => flat (helicalField y)) (fun _ => -1) Set.univ :=
  formBeltramiOn_flat_iff.2 helicalField_beltrami

/-- The helical field has no zeros. -/
theorem helicalField_ne_zero (x : Space) : helicalField x ≠ 0 := by
  intro h
  have h0 : Real.cos (x 2) = 0 := by
    simpa [helicalField] using congrArg (fun v : Space => v 0) h
  have h1 : Real.sin (x 2) = 0 := by
    simpa [helicalField] using congrArg (fun v : Space => v 1) h
  have := Real.sin_sq_add_cos_sq (x 2)
  rw [h0, h1] at this
  norm_num at this

/-- **`cos z dx + sin z dy` is a contact form on all of `ℝ³`**: `β ∧ dβ ≠ 0` at every
point. -/
theorem helicalField_contact (x : Space) : IsContactAt (fun y => flat (helicalField y)) x :=
  isContactAt_of_beltrami helicalField_beltrami (Set.mem_univ x) (by norm_num)
    (helicalField_ne_zero x)

/-- Rejected fixture: the helical field is not Beltrami with `λ = 1`. -/
theorem helicalField_not_beltrami_one : ¬ IsBeltramiOn helicalField (fun _ => 1) Set.univ := by
  intro h
  have h1 := (h 0 (Set.mem_univ 0)).2
  rw [helicalField_curl] at h1
  have h0 := congrArg (fun v : Space => v 0) h1
  simp [helicalField] at h0
  norm_num at h0

end PlasmaLean.Forms
