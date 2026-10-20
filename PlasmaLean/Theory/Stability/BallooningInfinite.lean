/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Stability.Ballooning

/-!
# Ballooning on the infinite line: piecewise Barta certificates and asymptotic tails

The physical ballooning equation lives on the covering-space coordinate `θ ∈ ℝ`:

  `-(P X')' + Q X = λ W X`,   `θ ∈ ℝ`,

with energy `E(ξ) = ∫_ℝ (P ξ'² + Q ξ²)` (`lineEnergy`) and mass `M(ξ) = ∫_ℝ W ξ²`
(`lineMass`). Admissible displacements are `C¹` on `ℝ` and vanish (together with `ξ'`)
outside a bounded interval `[a, b]` (`LineAdmissible ξ ξ' a b`); then both integrals are
interval integrals over `[a, b]` (`lineEnergy_eq`, `lineMass_eq`).

## Piecewise Picone fluxes

The central object is a *flux bound* (`FluxBound f g a b φa φb`):
`φb ξ(b)² − φa ξ(a)² ≤ ∫_a^b (f ξ'² + g ξ²)` for every `C¹` `ξ` on `[a, b]`, with no
boundary condition. A Picone/Riccati flux `φ` with `φ' = h`, `h ≤ g`, `φ² ≤ f (g − h)`
(`PiconeData`) gives one (`PiconeData.fluxBound`); a positive Jacobi supersolution `u` with
`(f u')' ≤ g u` gives the flux `φ = f u'/u` (`JacobiData.toPicone`). Flux bounds on
adjacent intervals **glue** (`FluxBound.glue`) provided the flux does not jump up at the
junction: `ψ(m) ≤ φ(m)` (right-piece flux at most left-piece flux). For Jacobi witnesses
this is implied by continuity of `w` and of the flux `P w'` at the junction
(`flux_junction_of_continuous`); a downward jump is a concave kink, i.e. a measure-valued
supersolution. This is the piecewise-`C²` Barta theorem (`piecewise_barta`).

## Results on the line

* `global_barta`, `global_barta_of_contDiff`: a positive supersolution
  `-(P w')' + Q w ≥ c W w` on all of `ℝ` gives `E(ξ) ≥ c M(ξ)` for every compactly
  supported admissible `ξ` (reduction to a large finite interval).
* `TailCertificate`, `TailCertificate.lower_bound`: an inner Jacobi witness on `[-Θ, Θ]`
  glued to Picone fluxes on the rays `(-∞, -Θ]` and `[Θ, ∞)`;
  `TailCertificate.ofSuydam` builds one from explicit Suydam tails.
* `suydamFlux`: the explicit asymptotic tail. If `P ≥ s² θ²` and `Q − c W ≥ q₀` on a set
  and `α (α + 1) s² ≤ q₀`, then `φ(θ) = α s² θ` (the flux of `w = |θ|^α`) is a Picone
  flux there. `tail_exponent_iff_suydam`: such an `α` exists iff `s² + 4 q₀ ≥ 0`, i.e.
  `q₀/s² ≥ −1/4` — the Suydam threshold (in cylindrical geometry the Mercier criterion,
  `PlasmaLean.Stability.Mercier.mercier_iff_suydam`).
* `tail_unstable`: sharpness. If `P ≤ F θ²` and `Q ≤ G` on `[Θ, ∞)` with `F > 0` and
  `F + 4 G < 0`, an explicit compactly supported `C¹` mode
  `ξ(θ) = η(k log(θ/Θ))/√θ`, `η(u) = (max 0 (u (1 − u)))²`, has `E(ξ) < 0`; hence no tail
  certificate and no global positive supersolution exists
  (`no_tailCertificate_of_bad_tail`, `no_global_supersolution_of_bad_tail`);
  `model_tail_dichotomy` states both directions for the exact model tail.
* `example_line_stable`: a certified example with `P = 1 + θ²`,
  `Q = −1/5 − (1/12) max 0 (4 − θ²)` (`Q(0) = −8/15`, below the frozen Suydam bound
  `−1/4`), using a degree-14 rational inner witness checked by `QPoly.checkOn` on
  `[-2, 2]` and the tail exponent `α = −7/10`.

Scope: the coefficients `P, Q, W` are SUPPLIED continuous functions; the reduction of the
3-D `δW` to this form, and the identification of the tail coefficients of a given
equilibrium, are not formalized. Admissible displacements are compactly supported `C¹`
functions (dense in the natural energy space; the density argument is not formalized).
-/
public section

noncomputable section
namespace PlasmaLean.Stability.BallooningInfinite
open intervalIntegral Set PlasmaLean.Stability MeasureTheory

/-! ## Flux bounds and gluing -/

/-- `C1On` restricts to subintervals. -/
theorem _root_.PlasmaLean.Stability.C1On.mono {ξ ξ' : ℝ → ℝ} {a b c d : ℝ} (h : C1On ξ ξ' a b)
    (hsub : uIcc c d ⊆ uIcc a b) : C1On ξ ξ' c d :=
  ⟨fun x hx => h.deriv x (hsub hx), h.cont.mono hsub⟩

/-- **Flux bound** on `[a, b]`: for every `C¹` displacement (no boundary condition),
`φb ξ(b)² − φa ξ(a)² ≤ ∫_a^b (f ξ'² + g ξ²)`. -/
@[expose] def FluxBound (f g : ℝ → ℝ) (a b φa φb : ℝ) : Prop :=
  ∀ ξ ξ' : ℝ → ℝ, C1On ξ ξ' a b → φb * ξ b ^ 2 - φa * ξ a ^ 2 ≤ newcombForm f g a b ξ ξ'

/-- A flux bound with Dirichlet ends gives nonnegativity of the form. -/
theorem FluxBound.nonneg {f g : ℝ → ℝ} {a b φa φb : ℝ} (hF : FluxBound f g a b φa φb)
    {ξ ξ' : ℝ → ℝ} (hξ : C1On ξ ξ' a b) (h₀ : ξ a = 0) (h₁ : ξ b = 0) :
    0 ≤ newcombForm f g a b ξ ξ' := by
  have := hF ξ ξ' hξ
  rw [h₀, h₁] at this
  simpa using this

/-- Additivity of the Newcomb form over adjacent intervals. -/
theorem newcombForm_add {f g ξ ξ' : ℝ → ℝ} {a m b : ℝ} (ham : a ≤ m) (hmb : m ≤ b)
    (hξ : C1On ξ ξ' a b) (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b)) :
    newcombForm f g a m ξ ξ' + newcombForm f g m b ξ ξ' = newcombForm f g a b ξ ξ' := by
  have hab : a ≤ b := ham.trans hmb
  have s1 : uIcc a m ⊆ uIcc a b := by
    rw [uIcc_of_le ham, uIcc_of_le hab]; exact Icc_subset_Icc le_rfl hmb
  have s2 : uIcc m b ⊆ uIcc a b := by
    rw [uIcc_of_le hmb, uIcc_of_le hab]; exact Icc_subset_Icc ham le_rfl
  rw [← uIcc_of_le hab] at hf hg
  unfold newcombForm
  exact integral_add_adjacent_intervals
    (newcomb_integrable (hξ.mono s1) (hf.mono s1) (hg.mono s1))
    (newcomb_integrable (hξ.mono s2) (hf.mono s2) (hg.mono s2))

/-- **Gluing.** Flux bounds on `[a, m]` and `[m, b]` combine to a flux bound on `[a, b]`
provided the right piece's flux at the junction does not exceed the left piece's:
`ψm ≤ φm`. -/
theorem FluxBound.glue {f g : ℝ → ℝ} {a m b φa φm ψm φb : ℝ} (ham : a ≤ m) (hmb : m ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (h₁ : FluxBound f g a m φa φm) (h₂ : FluxBound f g m b ψm φb) (hj : ψm ≤ φm) :
    FluxBound f g a b φa φb := by
  intro ξ ξ' hξ
  have hab : a ≤ b := ham.trans hmb
  have s1 : uIcc a m ⊆ uIcc a b := by
    rw [uIcc_of_le ham, uIcc_of_le hab]; exact Icc_subset_Icc le_rfl hmb
  have s2 : uIcc m b ⊆ uIcc a b := by
    rw [uIcc_of_le hmb, uIcc_of_le hab]; exact Icc_subset_Icc ham le_rfl
  have e1 := h₁ ξ ξ' (hξ.mono s1)
  have e2 := h₂ ξ ξ' (hξ.mono s2)
  rw [← newcombForm_add ham hmb hξ hf hg]
  nlinarith [mul_le_mul_of_nonneg_right hj (sq_nonneg (ξ m))]

/-- **Picone flux data** on a set `S`: a flux `φ` with derivative `h` such that
`h ≤ g` and `φ² ≤ f (g − h)` on `S`. -/
structure PiconeData (f g : ℝ → ℝ) (S : Set ℝ) where
  /-- The flux (`f w'/w` for a supersolution `w`). -/
  φ : ℝ → ℝ
  /-- Its derivative. -/
  h : ℝ → ℝ
  deriv : ∀ x ∈ S, HasDerivAt φ (h x) x
  cont : ContinuousOn h S
  gap : ∀ x ∈ S, h x ≤ g x
  disc : ∀ x ∈ S, φ x ^ 2 ≤ f x * (g x - h x)

/-- **Picone identity with boundary terms.** Picone data on `[a, b]` (and `f ≥ 0`) give the
flux bound `φ(b) ξ(b)² − φ(a) ξ(a)² ≤ ∫_a^b (f ξ'² + g ξ²)`. -/
theorem PiconeData.fluxBound {f g : ℝ → ℝ} {S : Set ℝ} (D : PiconeData f g S) {a b : ℝ}
    (hab : a ≤ b) (hS : Icc a b ⊆ S) (hfn : ∀ x ∈ S, 0 ≤ f x)
    (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
    FluxBound f g a b (D.φ a) (D.φ b) := by
  intro ξ ξ' hξ
  have hS' : uIcc a b ⊆ S := (uIcc_of_le hab).symm ▸ hS
  have hφ : ∀ x ∈ uIcc a b, HasDerivAt D.φ (D.h x) x := fun x hx => D.deriv x (hS' hx)
  have hh : ContinuousOn D.h (uIcc a b) := D.cont.mono hS'
  have hφc : ContinuousOn D.φ (uIcc a b) :=
    fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have hP : ∀ x ∈ uIcc a b, HasDerivAt (fun y => D.φ y * ξ y ^ 2)
      (D.h x * ξ x ^ 2 + D.φ x * (2 * ξ x * ξ' x)) x := by
    intro x hx
    have := (hφ x hx).mul ((hξ.deriv x hx).pow 2)
    convert this using 1
    simp only [Pi.pow_apply, Nat.cast_ofNat]; ring
  have hPi : IntervalIntegrable (fun x => D.h x * ξ x ^ 2 + D.φ x * (2 * ξ x * ξ' x))
      volume a b :=
    ((hh.mul (hξ.continuousOn.pow 2)).add
      (hφc.mul ((continuousOn_const.mul hξ.continuousOn).mul hξ.cont))).intervalIntegrable
  have hftc : ∫ x in a..b, (D.h x * ξ x ^ 2 + D.φ x * (2 * ξ x * ξ' x)) =
      D.φ b * ξ b ^ 2 - D.φ a * ξ a ^ 2 := integral_eq_sub_of_hasDerivAt hP hPi
  have hmono : ∫ x in a..b, (D.h x * ξ x ^ 2 + D.φ x * (2 * ξ x * ξ' x)) ≤
      newcombForm f g a b ξ ξ' := by
    apply integral_mono_on hab hPi (newcomb_integrable hξ (hf.mono hS') (hg.mono hS'))
    intro x hx
    have hx' : x ∈ S := hS hx
    have q := quadratic_nonneg (p := ξ' x) (q := ξ x) (hfn x hx')
      (by linarith [D.gap x hx']) (D.disc x hx')
    nlinarith [q]
  linarith

/-- Picone data restrict to subsets. -/
@[expose] def PiconeData.mono {f g : ℝ → ℝ} {S T : Set ℝ} (D : PiconeData f g S)
    (hT : T ⊆ S) : PiconeData f g T where
  φ := D.φ
  h := D.h
  deriv x hx := D.deriv x (hT hx)
  cont := D.cont.mono hT
  gap x hx := D.gap x (hT hx)
  disc x hx := D.disc x (hT hx)

/-- **Jacobi supersolution data** on `S`: a positive `u` with derivative `u'`, flux
`f u'` with continuous derivative `k`, and `k ≤ g u` (i.e. `-(f u')' + g u ≥ 0`). -/
structure JacobiData (f g : ℝ → ℝ) (S : Set ℝ) where
  /-- The positive supersolution. -/
  u : ℝ → ℝ
  /-- Its derivative. -/
  u' : ℝ → ℝ
  /-- Derivative of the flux `f u'`. -/
  k : ℝ → ℝ
  hu : ∀ x ∈ S, HasDerivAt u (u' x) x
  hu'c : ContinuousOn u' S
  hk : ∀ x ∈ S, HasDerivAt (fun y => f y * u' y) (k x) x
  hkc : ContinuousOn k S
  pos : ∀ x ∈ S, 0 < u x
  super : ∀ x ∈ S, k x ≤ g x * u x

/-- The logarithmic flux `φ = f u'/u` of a Jacobi supersolution is a Picone flux
(requires `f` continuous and nonnegative on `S`). -/
@[expose] def JacobiData.toPicone {f g : ℝ → ℝ} {S : Set ℝ} (J : JacobiData f g S)
    (hf : ContinuousOn f S) (hfn : ∀ x ∈ S, 0 ≤ f x) : PiconeData f g S where
  φ x := f x * J.u' x / J.u x
  h x := J.k x / J.u x - f x * (J.u' x / J.u x) ^ 2
  deriv x hx := by
    have hne := (J.pos x hx).ne'
    have hd := (J.hk x hx).div (J.hu x hx) hne
    convert hd using 1
    field_simp
  cont := by
    have huc : ContinuousOn J.u S := fun x hx => (J.hu x hx).continuousAt.continuousWithinAt
    have hne : ∀ x ∈ S, J.u x ≠ 0 := fun x hx => (J.pos x hx).ne'
    exact (J.hkc.div huc hne).sub (hf.mul ((J.hu'c.div huc hne).pow 2))
  gap x hx := by
    have hux := J.pos x hx
    have : J.k x / J.u x ≤ g x := by rw [div_le_iff₀ hux]; exact J.super x hx
    nlinarith [mul_nonneg (hfn x hx) (sq_nonneg (J.u' x / J.u x))]
  disc x hx := by
    have hux := J.pos x hx
    have h1 : J.k x / J.u x ≤ g x := by rw [div_le_iff₀ hux]; exact J.super x hx
    have e : f x * J.u' x / J.u x = f x * (J.u' x / J.u x) := by ring
    rw [e]
    nlinarith [mul_nonneg (hfn x hx) (sub_nonneg.mpr h1), sq_nonneg (f x * (J.u' x / J.u x))]

/-- Junction condition from continuity: if two positive Jacobi witnesses agree at `m`
up to a positive factor and so do their fluxes `f u'`, their logarithmic fluxes agree. -/
theorem flux_junction_of_continuous {fm u₁ u₁' u₂ u₂' : ℝ} (hu : u₁ = u₂)
    (hflux : fm * u₁' = fm * u₂') :
    fm * u₂' / u₂ = fm * u₁' / u₁ := by
  rw [hu, hflux]

/-- **Piecewise-`C²` Barta theorem (two pieces).** Positive Jacobi supersolutions `u₁` on
`[a, m]` and `u₂` on `[m, b]` with `w` and the flux `f w'` continuous at the junction
(`u₁ m = u₂ m`, `f m u₁' m = f m u₂' m`) give `∫_a^b (f ξ'² + g ξ²) ≥ 0` for every `C¹`
`ξ` vanishing at `a` and `b`. -/
theorem piecewise_barta {f g : ℝ → ℝ} {a m b : ℝ} (ham : a ≤ m) (hmb : m ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfn : ∀ x ∈ Icc a b, 0 ≤ f x)
    (J₁ : JacobiData f g (Icc a m)) (J₂ : JacobiData f g (Icc m b))
    (hu : J₁.u m = J₂.u m) (hflux : f m * J₁.u' m = f m * J₂.u' m)
    {ξ ξ' : ℝ → ℝ} (hξ : C1On ξ ξ' a b) (h₀ : ξ a = 0) (h₁ : ξ b = 0) :
    0 ≤ newcombForm f g a b ξ ξ' := by
  have s1 : Icc a m ⊆ Icc a b := Icc_subset_Icc le_rfl hmb
  have s2 : Icc m b ⊆ Icc a b := Icc_subset_Icc ham le_rfl
  have F1 := (J₁.toPicone (hf.mono s1) (fun x hx => hfn x (s1 hx))).fluxBound ham le_rfl
    (fun x hx => hfn x (s1 hx)) (hf.mono s1) (hg.mono s1)
  have F2 := (J₂.toPicone (hf.mono s2) (fun x hx => hfn x (s2 hx))).fluxBound hmb le_rfl
    (fun x hx => hfn x (s2 hx)) (hf.mono s2) (hg.mono s2)
  refine (F1.glue ham hmb hf hg F2 ?_).nonneg hξ h₀ h₁
  exact (flux_junction_of_continuous hu hflux).le

/-! ## The infinite line -/

/-- Coefficients of the ballooning operator `-(P X')' + Q X = λ W X` on the whole line
(covering-space coordinate `θ ∈ ℝ`). -/
structure LineOperator where
  /-- Field-line bending stiffness. -/
  P : ℝ → ℝ
  /-- Pressure/curvature drive. -/
  Q : ℝ → ℝ
  /-- Inertial weight. -/
  W : ℝ → ℝ
  P_pos : ∀ x, 0 < P x
  W_nonneg : ∀ x, 0 ≤ W x
  P_cont : Continuous P
  Q_cont : Continuous Q
  W_cont : Continuous W

/-- Compactly supported admissible displacement: `ξ` is `C¹` on `ℝ` with derivative `ξ'`,
and `ξ`, `ξ'` vanish outside `(a, b)`. -/
structure LineAdmissible (ξ ξ' : ℝ → ℝ) (a b : ℝ) : Prop where
  deriv : ∀ x, HasDerivAt ξ (ξ' x) x
  cont : Continuous ξ'
  le : a ≤ b
  vanish : ∀ x, x ≤ a ∨ b ≤ x → ξ x = 0 ∧ ξ' x = 0

/-- Ballooning energy on the line, `E(ξ) = ∫_ℝ (P ξ'² + Q ξ²)`. -/
@[expose] def lineEnergy (P Q ξ ξ' : ℝ → ℝ) : ℝ := ∫ x, (P x * ξ' x ^ 2 + Q x * ξ x ^ 2)

/-- Weighted mass on the line, `M(ξ) = ∫_ℝ W ξ²`. -/
@[expose] def lineMass (W ξ : ℝ → ℝ) : ℝ := ∫ x, W x * ξ x ^ 2

/-- A function vanishing outside `(a, b)` has its line integral equal to the interval
integral over `[a, b]`. -/
theorem integral_eq_interval_of_vanish {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ x, x ≤ a ∨ b ≤ x → F x = 0) : ∫ x, F x = ∫ x in a..b, F x := by
  rw [integral_of_le hab, setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  simp only [mem_Ioc, not_and_or, not_lt, not_le] at hx
  rcases hx with h | h
  · exact hF x (Or.inl h)
  · exact hF x (Or.inr h.le)

namespace LineAdmissible
variable {ξ ξ' : ℝ → ℝ} {a b : ℝ}

/-- An admissible displacement is `C¹` on its support interval. -/
theorem c1On (h : LineAdmissible ξ ξ' a b) (c d : ℝ) : C1On ξ ξ' c d :=
  ⟨fun x _ => h.deriv x, h.cont.continuousOn⟩

/-- It vanishes at the left end of its support interval. -/
theorem left (h : LineAdmissible ξ ξ' a b) : ξ a = 0 := (h.vanish a (Or.inl le_rfl)).1

/-- It vanishes at the right end of its support interval. -/
theorem right (h : LineAdmissible ξ ξ' a b) : ξ b = 0 := (h.vanish b (Or.inr le_rfl)).1

/-- The support interval may be enlarged. -/
theorem mono (h : LineAdmissible ξ ξ' a b) {a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    LineAdmissible ξ ξ' a' b' where
  deriv := h.deriv
  cont := h.cont
  le := ha.trans (h.le.trans hb)
  vanish x hx := h.vanish x (hx.imp (fun h' => h'.trans ha) (fun h' => hb.trans h'))

end LineAdmissible

/-- The line energy of an admissible displacement is its Newcomb form on any support
interval. -/
theorem lineEnergy_eq {P Q ξ ξ' : ℝ → ℝ} {a b : ℝ} (h : LineAdmissible ξ ξ' a b) :
    lineEnergy P Q ξ ξ' = newcombForm P Q a b ξ ξ' :=
  integral_eq_interval_of_vanish h.le fun x hx => by
    obtain ⟨h1, h2⟩ := h.vanish x hx
    simp [h1, h2]

/-- The line mass of an admissible displacement is an interval integral. -/
theorem lineMass_eq {W ξ ξ' : ℝ → ℝ} {a b : ℝ} (h : LineAdmissible ξ ξ' a b) :
    lineMass W ξ = ∫ x in a..b, W x * ξ x ^ 2 :=
  integral_eq_interval_of_vanish h.le fun x hx => by simp [(h.vanish x hx).1]

/-- Shift of the potential: `E_{P,Q} = E_{P,Q-cW} + c ∫ W ξ²` on `[a, b]`. -/
theorem newcombForm_shift {P Q W ξ ξ' : ℝ → ℝ} {a b : ℝ} (c : ℝ) (hξ : C1On ξ ξ' a b)
    (hP : Continuous P) (hQ : Continuous Q) (hW : Continuous W) :
    newcombForm P Q a b ξ ξ' =
      newcombForm P (fun x => Q x - c * W x) a b ξ ξ' + c * ∫ x in a..b, W x * ξ x ^ 2 := by
  have h1 := newcomb_integrable (g := fun x => Q x - c * W x) hξ hP.continuousOn
    (by fun_prop : Continuous fun x => Q x - c * W x).continuousOn
  have h2 : IntervalIntegrable (fun x => c * (W x * ξ x ^ 2)) volume a b :=
    ((hW.continuousOn.mul (hξ.continuousOn.pow 2)).intervalIntegrable).const_mul c
  unfold newcombForm
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add h1 h2]
  congr 1; funext x; ring

namespace LineOperator
variable (op : LineOperator)

/-- The shifted potential `Q − c W`. -/
@[expose] def shifted (c : ℝ) : ℝ → ℝ := fun x => op.Q x - c * op.W x

/-- The shifted potential is continuous. -/
theorem shifted_cont (c : ℝ) : Continuous (op.shifted c) := by
  unfold shifted; have := op.Q_cont; have := op.W_cont; fun_prop

/-- On a support interval, `E - c M` is the Newcomb form of the shifted potential. -/
theorem lineEnergy_shift (c : ℝ) {ξ ξ' : ℝ → ℝ} {a b : ℝ} (h : LineAdmissible ξ ξ' a b) :
    lineEnergy op.P op.Q ξ ξ' =
      newcombForm op.P (op.shifted c) a b ξ ξ' + c * lineMass op.W ξ := by
  rw [lineEnergy_eq h, lineMass_eq h]
  exact newcombForm_shift c (h.c1On a b) op.P_cont op.Q_cont op.W_cont

/-- From a flux bound on a support interval to the line inequality `c M ≤ E`. -/
theorem lower_bound_of_fluxBound {c : ℝ} {ξ ξ' : ℝ → ℝ} {a b φa φb : ℝ}
    (h : LineAdmissible ξ ξ' a b) (hF : FluxBound op.P (op.shifted c) a b φa φb) :
    c * lineMass op.W ξ ≤ lineEnergy op.P op.Q ξ ξ' := by
  rw [op.lineEnergy_shift c h]
  linarith [hF.nonneg (h.c1On a b) h.left h.right]

/-- **Barta on the line (global witness).** A positive supersolution
`-(P w')' + (Q − c W) w ≥ 0` on all of `ℝ` gives `c M(ξ) ≤ E(ξ)` for every compactly
supported admissible `ξ`. -/
theorem global_barta {c : ℝ} (J : JacobiData op.P (op.shifted c) univ) {ξ ξ' : ℝ → ℝ}
    {a b : ℝ} (h : LineAdmissible ξ ξ' a b) :
    c * lineMass op.W ξ ≤ lineEnergy op.P op.Q ξ ξ' :=
  op.lower_bound_of_fluxBound h
    ((J.toPicone op.P_cont.continuousOn fun x _ => (op.P_pos x).le).fluxBound h.le
      (subset_univ _) (fun x _ => (op.P_pos x).le) op.P_cont.continuousOn
      (op.shifted_cont c).continuousOn)

/-- Jacobi data from a `C²` witness (with `P` of class `C¹`), using `deriv`. -/
@[expose] def jacobiOfContDiff {c : ℝ} (w : ℝ → ℝ) (hw : ContDiff ℝ 2 w)
    (hP : ContDiff ℝ 1 op.P) (hpos : ∀ x, 0 < w x)
    (hsuper : ∀ x, c * op.W x * w x ≤ -deriv (fun s => op.P s * deriv w s) x + op.Q x * w x) :
    JacobiData op.P (op.shifted c) univ where
  u := w
  u' := deriv w
  k := deriv (fun s => op.P s * deriv w s)
  hu x _ := ((hw.differentiable (by norm_num)) x).hasDerivAt
  hu'c := (hw.continuous_deriv (by norm_num)).continuousOn
  hk x _ := by
    have h1 : ContDiff ℝ 1 (deriv w) := ((contDiff_succ_iff_deriv (n := 1)).mp hw).2.2
    exact ((hP.mul h1).differentiable (by norm_num) x).hasDerivAt
  hkc := by
    have h1 : ContDiff ℝ 1 (deriv w) := ((contDiff_succ_iff_deriv (n := 1)).mp hw).2.2
    exact ((hP.mul h1).continuous_deriv (by norm_num)).continuousOn
  pos x _ := hpos x
  super x _ := by have := hsuper x; simp only [shifted]; linarith

/-- **Barta on the line, `C²` form.** If `w > 0` is `C²`, `P` is `C¹` and
`-(P w')' + Q w ≥ c W w` everywhere, then `E(ξ) ≥ c M(ξ)` for every compactly supported
admissible `ξ`. -/
theorem global_barta_of_contDiff {c : ℝ} (w : ℝ → ℝ) (hw : ContDiff ℝ 2 w)
    (hP : ContDiff ℝ 1 op.P) (hpos : ∀ x, 0 < w x)
    (hsuper : ∀ x, c * op.W x * w x ≤ -deriv (fun s => op.P s * deriv w s) x + op.Q x * w x)
    {ξ ξ' : ℝ → ℝ} {a b : ℝ} (h : LineAdmissible ξ ξ' a b) :
    c * lineMass op.W ξ ≤ lineEnergy op.P op.Q ξ ξ' :=
  op.global_barta (op.jacobiOfContDiff w hw hP hpos hsuper) h

/-- **Tail certificate at level `c`**: Picone fluxes on the rays `(-∞, -Θ]` and `[Θ, ∞)`
and a positive Jacobi witness on `[-Θ, Θ]` for the shifted potential `Q − c W`, with the
junction conditions (the flux may only jump down when moving to the right). -/
structure TailCertificate (c : ℝ) where
  /-- Junction abscissa. -/
  Θ : ℝ
  hΘ : 0 ≤ Θ
  /-- Left-tail flux. -/
  left : PiconeData op.P (op.shifted c) (Iic (-Θ))
  /-- Inner Jacobi witness. -/
  inner : JacobiData op.P (op.shifted c) (Icc (-Θ) Θ)
  /-- Right-tail flux. -/
  right : PiconeData op.P (op.shifted c) (Ici Θ)
  junctionL : op.P (-Θ) * inner.u' (-Θ) / inner.u (-Θ) ≤ left.φ (-Θ)
  junctionR : right.φ Θ ≤ op.P Θ * inner.u' Θ / inner.u Θ

/-- **Tail-certificate theorem.** A tail certificate at level `c` gives `c M(ξ) ≤ E(ξ)`
for every compactly supported admissible `ξ` on the line. Proof: enlarge the support to
`[-R, R]` with `R ≥ Θ`, glue the three flux bounds and apply the Dirichlet conclusion. -/
theorem TailCertificate.lower_bound {c : ℝ} (T : op.TailCertificate c) {ξ ξ' : ℝ → ℝ}
    {a b : ℝ} (h : LineAdmissible ξ ξ' a b) :
    c * lineMass op.W ξ ≤ lineEnergy op.P op.Q ξ ξ' := by
  set R := max T.Θ (max (-a) b) with hR
  have hΘR : T.Θ ≤ R := le_max_left _ _
  have haR : -R ≤ a := by
    have : -a ≤ R := (le_max_left _ _).trans (le_max_right _ _)
    linarith
  have hbR : b ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have h' := h.mono haR hbR
  have hPn : ∀ {S : Set ℝ}, ∀ x ∈ S, 0 ≤ op.P x := fun x _ => (op.P_pos x).le
  have hPc : ∀ {S : Set ℝ}, ContinuousOn op.P S := op.P_cont.continuousOn
  have hgc : ∀ {S : Set ℝ}, ContinuousOn (op.shifted c) S := (op.shifted_cont c).continuousOn
  have hΘ := T.hΘ
  have FL := T.left.fluxBound (a := -R) (b := -T.Θ) (by linarith)
    (fun x hx => (mem_Iic.mpr hx.2)) hPn hPc hgc
  have FI := (T.inner.toPicone hPc hPn).fluxBound (a := -T.Θ) (b := T.Θ) (by linarith)
    subset_rfl hPn hPc hgc
  have FR := T.right.fluxBound (a := T.Θ) (b := R) hΘR (fun x hx => (mem_Ici.mpr hx.1))
    hPn hPc hgc
  have G1 := FL.glue (by linarith) (by linarith) hPc hgc FI T.junctionL
  have G2 := G1.glue (by linarith) hΘR hPc hgc FR T.junctionR
  exact op.lower_bound_of_fluxBound h' G2

/-- A tail certificate at level `0` gives `E(ξ) ≥ 0` on the line. -/
theorem TailCertificate.energy_nonneg (T : op.TailCertificate 0) {ξ ξ' : ℝ → ℝ}
    {a b : ℝ} (h : LineAdmissible ξ ξ' a b) : 0 ≤ lineEnergy op.P op.Q ξ ξ' := by
  simpa using T.lower_bound op h

end LineOperator

/-! ## The explicit Suydam/Mercier tail -/

/-- **Explicit asymptotic tail flux.** If `P ≥ s² θ²` and `g ≥ q₀` on `S` and the tail
exponent satisfies `α (α + 1) s² ≤ q₀`, then `φ(θ) = α s² θ` — the flux `P w'/w` of
`w = |θ|^α` for `P = s² θ²` — is a Picone flux on `S`. -/
@[expose] def suydamFlux {f g : ℝ → ℝ} {S : Set ℝ} (s α q₀ : ℝ)
    (hα : α * (α + 1) * s ^ 2 ≤ q₀) (hf : ∀ x ∈ S, s ^ 2 * x ^ 2 ≤ f x)
    (hg : ∀ x ∈ S, q₀ ≤ g x) : PiconeData f g S where
  φ x := α * s ^ 2 * x
  h _ := α * s ^ 2
  deriv x _ := by simpa using (hasDerivAt_id x).const_mul (α * s ^ 2)
  cont := continuousOn_const
  gap x hx := by
    have e : α * s ^ 2 = α * (α + 1) * s ^ 2 - α ^ 2 * s ^ 2 := by ring
    nlinarith [hg x hx, mul_nonneg (sq_nonneg α) (sq_nonneg s)]
  disc x hx := by
    have e1 : α * (α + 1) * s ^ 2 = α ^ 2 * s ^ 2 + α * s ^ 2 := by ring
    have h1 : α ^ 2 * s ^ 2 ≤ g x - α * s ^ 2 := by linarith [hg x hx]
    have h2 := hf x hx
    have e : (α * s ^ 2 * x) ^ 2 = (α ^ 2 * s ^ 2) * (s ^ 2 * x ^ 2) := by ring
    rw [e, mul_comm (f x)]
    exact mul_le_mul h1 h2 (by positivity) (le_trans (by positivity) h1)

/-- **The tail threshold is Suydam's.** A tail exponent `α` with `α (α + 1) s² ≤ q₀`
exists iff `s² + 4 q₀ ≥ 0`, i.e. iff the tail coefficients `F = s²`, `G = q₀` satisfy the
Suydam criterion `F + 4 G ≥ 0` of `PlasmaLean.Stability.suydamForm_nonneg` (the
cylindrical Mercier criterion, `Mercier.mercier_iff_suydam`). The optimal exponent is
`α = −1/2`. -/
theorem tail_exponent_iff_suydam (s q₀ : ℝ) :
    (∃ α : ℝ, α * (α + 1) * s ^ 2 ≤ q₀) ↔ 0 ≤ s ^ 2 + 4 * q₀ := by
  constructor
  · rintro ⟨α, hα⟩
    nlinarith [mul_nonneg (sq_nonneg (2 * α + 1)) (sq_nonneg s)]
  · intro h
    exact ⟨-1 / 2, by nlinarith⟩

/-- The threshold in Mercier form: for nonzero shear `s`, a tail exponent exists iff
`q₀ / s² ≥ −1/4`. -/
theorem tail_exponent_iff_ratio {s q₀ : ℝ} (hs : s ≠ 0) :
    (∃ α : ℝ, α * (α + 1) * s ^ 2 ≤ q₀) ↔ -1 / 4 ≤ q₀ / s ^ 2 := by
  have hs2 : 0 < s ^ 2 := by positivity
  rw [tail_exponent_iff_suydam, le_div_iff₀ hs2]
  constructor <;> intro h <;> linarith

namespace LineOperator
variable (op : LineOperator)

/-- **Tail certificate from explicit Suydam tails.** An inner Jacobi witness on `[-Θ, Θ]`,
tail bounds `P ≥ s² θ²` and `Q − c W ≥ q₀` for `|θ| ≥ Θ`, an exponent with
`α (α + 1) s² ≤ q₀`, and the two junction inequalities against the tail flux `α s² θ`. -/
@[expose] def TailCertificate.ofSuydam {c Θ s α q₀ : ℝ} (hΘ : 0 ≤ Θ)
    (J : JacobiData op.P (op.shifted c) (Icc (-Θ) Θ))
    (hα : α * (α + 1) * s ^ 2 ≤ q₀)
    (hP : ∀ x, Θ ≤ |x| → s ^ 2 * x ^ 2 ≤ op.P x)
    (hQ : ∀ x, Θ ≤ |x| → q₀ ≤ op.shifted c x)
    (hL : op.P (-Θ) * J.u' (-Θ) / J.u (-Θ) ≤ α * s ^ 2 * (-Θ))
    (hR : α * s ^ 2 * Θ ≤ op.P Θ * J.u' Θ / J.u Θ) : op.TailCertificate c where
  Θ := Θ
  hΘ := hΘ
  left := suydamFlux s α q₀ hα
    (fun x hx => hP x (by have := neg_le_abs x; have := mem_Iic.mp hx; linarith))
    (fun x hx => hQ x (by have := neg_le_abs x; have := mem_Iic.mp hx; linarith))
  inner := J
  right := suydamFlux s α q₀ hα
    (fun x hx => hP x ((mem_Ici.mp hx).trans (le_abs_self x)))
    (fun x hx => hQ x ((mem_Ici.mp hx).trans (le_abs_self x)))
  junctionL := hL
  junctionR := hR

end LineOperator

/-! ## Sharpness: a compactly supported unstable tail mode -/

/-- The `C¹` ramp square `t ↦ (max 0 t)²`. -/
@[expose] def sqPlus (t : ℝ) : ℝ := max 0 t ^ 2

/-- `(max 0 t)²` is differentiable everywhere with derivative `2 max 0 t`. -/
theorem sqPlus_hasDerivAt (t : ℝ) : HasDerivAt sqPlus (2 * max 0 t) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hev : sqPlus =ᶠ[nhds t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ht] with y hy
      simp [sqPlus, max_eq_left (le_of_lt (mem_Iio.mp hy))]
    rw [max_eq_left ht.le, mul_zero]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
  · subst ht
    have hO : (fun y : ℝ => sqPlus y) =O[nhds 0] (fun y : ℝ => y ^ 2) := by
      refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun y => ?_)
      simp only [sqPlus, Real.norm_eq_abs, one_mul]
      rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
      rcases le_total y 0 with h | h
      · rw [max_eq_left h, zero_pow two_ne_zero]; exact sq_nonneg y
      · rw [max_eq_right h]
    have ho := hO.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num : 1 < 2))
    rw [hasDerivAt_iff_isLittleO]
    simpa [sqPlus] using ho
  · have hev : sqPlus =ᶠ[nhds t] fun y => y ^ 2 := by
      filter_upwards [Ioi_mem_nhds ht] with y hy
      simp [sqPlus, max_eq_right (le_of_lt (mem_Ioi.mp hy))]
    rw [max_eq_right ht.le]
    simpa using (hasDerivAt_pow 2 t).congr_of_eventuallyEq hev

/-- The `C¹` bump `η(u) = (max 0 (u (1 − u)))²`, equal to `u² (1 − u)²` on `[0, 1]` and
`0` outside. -/
@[expose] def bump (u : ℝ) : ℝ := sqPlus (u * (1 - u))

/-- Derivative of the bump, `2 max 0 (u (1 − u)) (1 − 2u)`. -/
@[expose] def bump' (u : ℝ) : ℝ := 2 * max 0 (u * (1 - u)) * (1 - 2 * u)

/-- The bump is differentiable with derivative `bump'`. -/
theorem bump_hasDerivAt (u : ℝ) : HasDerivAt bump (bump' u) u := by
  have h1 : HasDerivAt (fun u : ℝ => u * (1 - u)) (1 - 2 * u) u := by
    have := (hasDerivAt_id' u).mul ((hasDerivAt_id' u).const_sub 1)
    convert this using 1; ring
  exact (sqPlus_hasDerivAt (u * (1 - u))).comp u h1

/-- The bump is continuous. -/
theorem bump_continuous : Continuous bump := by
  unfold bump sqPlus; fun_prop

/-- The bump derivative is continuous. -/
theorem bump'_continuous : Continuous bump' := by
  unfold bump'; fun_prop

/-- The bump and its derivative vanish off `(0, 1)`. -/
theorem bump_eq_zero {u : ℝ} (hu : u ≤ 0 ∨ 1 ≤ u) : bump u = 0 ∧ bump' u = 0 := by
  have : u * (1 - u) ≤ 0 := by rcases hu with h | h <;> nlinarith
  simp [bump, bump', sqPlus, max_eq_left this]

/-- On `[0, 1]` the bump is the polynomial `u² (1 − u)²`. -/
theorem bump_on_unit {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    bump u = (u * (1 - u)) ^ 2 ∧ bump' u = 2 * (u * (1 - u)) * (1 - 2 * u) := by
  have : 0 ≤ u * (1 - u) := mul_nonneg h0 (by linarith)
  simp [bump, bump', sqPlus, max_eq_right this]

/-- The polynomial integral behind the tail-mode energy:
`∫₀¹ [F (k η' − η/2)² + G η²] = F k² (2/105) + (F/4 + G)/630` for `η = u² (1 − u)²`. -/
theorem unit_integral (F G k : ℝ) :
    ∫ u in (0 : ℝ)..1, (F * (k * (2 * (u * (1 - u)) * (1 - 2 * u)) - (u * (1 - u)) ^ 2 / 2) ^ 2
      + G * ((u * (1 - u)) ^ 2) ^ 2) = F * k ^ 2 * (2 / 105) + (F / 4 + G) / 630 := by
  open PlasmaLean.Certificates.QPoly in
  have hd : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun u => F * k ^ 2 * eval [0, 0, 0, 4/3, -6, 52/5, -8, 16/7] u
      - F * k * eval [0, 0, 0, 0, 1, -4, 6, -4, 1] u / 2
      + (F / 4 + G) * eval [0, 0, 0, 0, 0, 1/5, -2/3, 6/7, -1/2, 1/9] u)
      (F * (k * (2 * (u * (1 - u)) * (1 - 2 * u)) - (u * (1 - u)) ^ 2 / 2) ^ 2
        + G * ((u * (1 - u)) ^ 2) ^ 2) u := by
    intro u _
    have h := ((((hasDerivAt_eval [0, 0, 0, 4/3, -6, 52/5, -8, 16/7] u).const_mul (F * k ^ 2)).sub
      (((hasDerivAt_eval [0, 0, 0, 0, 1, -4, 6, -4, 1] u).const_mul (F * k)).div_const 2)).add
      ((hasDerivAt_eval [0, 0, 0, 0, 0, 1/5, -2/3, 6/7, -1/2, 1/9] u).const_mul (F / 4 + G)))
    convert h using 1
    simp [PlasmaLean.Certificates.QPoly.deriv]
    ring
  rw [integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
  simp
  norm_num
  ring

/-- The unstable tail mode `ξ(θ) = η(k log(θ/Θ)) / √θ`, supported in `[Θ, Θ e^{1/k}]`
(the compactly supported `C¹` analogue of the Suydam logarithmic mode). -/
@[expose] def tailMode (Θ k x : ℝ) : ℝ := bump (k * Real.log (x / Θ)) / Real.sqrt x

/-- Derivative of the tail mode. -/
@[expose] def tailMode' (Θ k x : ℝ) : ℝ :=
  (k * bump' (k * Real.log (x / Θ)) - bump (k * Real.log (x / Θ)) / 2) / (x * Real.sqrt x)

/-- The tail mode and its derivative vanish off `(Θ, Θ e^{1/k})`. -/
theorem tailMode_vanish {Θ k : ℝ} (hΘ : 0 < Θ) (hk : 0 < k) {x : ℝ}
    (hx : x ≤ Θ ∨ Θ * Real.exp (1 / k) ≤ x) : tailMode Θ k x = 0 ∧ tailMode' Θ k x = 0 := by
  rcases le_or_gt x 0 with h0 | h0
  · have : Real.sqrt x = 0 := Real.sqrt_eq_zero'.mpr h0
    simp [tailMode, tailMode', this]
  · have hu : k * Real.log (x / Θ) ≤ 0 ∨ 1 ≤ k * Real.log (x / Θ) := by
      rcases hx with h | h
      · left
        have : Real.log (x / Θ) ≤ 0 :=
          Real.log_nonpos (by positivity) ((div_le_one hΘ).mpr h)
        nlinarith
      · right
        have hl : 1 / k ≤ Real.log (x / Θ) := by
          rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hΘ]; linarith
        calc (1 : ℝ) = k * (1 / k) := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hl hk.le
    obtain ⟨h1, h2⟩ := bump_eq_zero hu
    simp [tailMode, tailMode', h1, h2]

/-- Derivative of the logarithmic coordinate `k log(θ/Θ)`. -/
theorem logScale_hasDerivAt {Θ k x : ℝ} (hΘ : 0 < Θ) (hx : 0 < x) :
    HasDerivAt (fun y => k * Real.log (y / Θ)) (k / x) x := by
  have := (((hasDerivAt_id' x).div_const Θ).log (div_pos hx hΘ).ne').const_mul k
  convert this using 1
  field_simp

/-- Derivative of the tail mode at positive points. -/
theorem tailMode_hasDerivAt_pos {Θ k x : ℝ} (hΘ : 0 < Θ) (hx : 0 < x) :
    HasDerivAt (tailMode Θ k) (tailMode' Θ k x) x := by
  have hl : HasDerivAt (fun y => k * Real.log (y / Θ)) (k / x) x := logScale_hasDerivAt hΘ hx
  have hb := (bump_hasDerivAt (k * Real.log (x / Θ))).comp x hl
  have hr : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := Real.hasDerivAt_sqrt hx.ne'
  have hq := hb.div hr (Real.sqrt_pos.mpr hx).ne'
  have h1 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have h2 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have e : tailMode Θ k = fun y => (bump ∘ fun y => k * Real.log (y / Θ)) y / Real.sqrt y := rfl
  rw [e]
  convert hq using 1
  simp only [tailMode', Function.comp]
  field_simp
  rw [h1]
  ring

/-- **The tail mode is admissible on the line**, supported in `[Θ, Θ e^{1/k}]`. -/
theorem tailMode_admissible {Θ k : ℝ} (hΘ : 0 < Θ) (hk : 0 < k) :
    LineAdmissible (tailMode Θ k) (tailMode' Θ k) Θ (Θ * Real.exp (1 / k)) where
  deriv x := by
    rcases le_or_gt x 0 with h0 | h0
    · have hev : tailMode Θ k =ᶠ[nhds x] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds (show x < Θ by linarith)] with y hy
        exact (tailMode_vanish hΘ hk (Or.inl (mem_Iio.mp hy).le)).1
      rw [(tailMode_vanish hΘ hk (Or.inl (by linarith))).2]
      exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
    · exact tailMode_hasDerivAt_pos hΘ h0
  cont := by
    rw [continuous_iff_continuousAt]
    intro x
    rcases le_or_gt x 0 with h0 | h0
    · have hev : (fun _ => (0 : ℝ)) =ᶠ[nhds x] tailMode' Θ k := by
        filter_upwards [Iio_mem_nhds (show x < Θ by linarith)] with y hy
        exact ((tailMode_vanish hΘ hk (Or.inl (mem_Iio.mp hy).le)).2).symm
      exact continuousAt_const.congr hev
    · have hlog : ContinuousAt (fun y => k * Real.log (y / Θ)) x :=
        continuousAt_const.mul ((continuousAt_id.div_const Θ).log (div_pos h0 hΘ).ne')
      apply ContinuousAt.div
      · exact (continuousAt_const.mul (bump'_continuous.continuousAt.comp hlog)).sub
          ((bump_continuous.continuousAt.comp hlog).div_const 2)
      · exact continuousAt_id.mul Real.continuous_sqrt.continuousAt
      · exact (mul_pos h0 (Real.sqrt_pos.mpr h0)).ne'
  le := by
    have := Real.one_le_exp (by positivity : (0 : ℝ) ≤ 1 / k)
    nlinarith
  vanish x hx := tailMode_vanish hΘ hk hx

/-- **Exact energy of the tail mode** for the model tail `P = F θ²`, `Q = G`:
`E = k⁻¹ (F k² · 2/105 + (F/4 + G)/630)`. -/
theorem tailMode_energy (F G : ℝ) {Θ k : ℝ} (hΘ : 0 < Θ) (hk : 0 < k) :
    newcombForm (fun x => F * x ^ 2) (fun _ => G) Θ (Θ * Real.exp (1 / k))
      (tailMode Θ k) (tailMode' Θ k) = k⁻¹ * (F * k ^ 2 * (2 / 105) + (F / 4 + G) / 630) := by
  set b := Θ * Real.exp (1 / k) with hbdef
  have hb : Θ ≤ b := (tailMode_admissible hΘ hk).le
  have pos : ∀ x ∈ uIcc Θ b, 0 < x := fun x hx => by
    rw [uIcc_of_le hb] at hx; linarith [hx.1]
  let g : ℝ → ℝ := fun u => F * (k * bump' u - bump u / 2) ^ 2 + G * bump u ^ 2
  have hpt : ∀ x ∈ uIcc Θ b, F * x ^ 2 * tailMode' Θ k x ^ 2 + G * tailMode Θ k x ^ 2 =
      k⁻¹ * ((g ∘ fun y => k * Real.log (y / Θ)) x * (k / x)) := by
    intro x hx
    have hx0 := pos x hx
    have h1 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
    have h2 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    simp only [tailMode, tailMode', g, Function.comp]
    field_simp
    rw [h1]
  unfold newcombForm
  rw [integral_congr hpt, intervalIntegral.integral_const_mul]
  have hgc : Continuous g := by
    have := bump_continuous; have := bump'_continuous; fun_prop
  have hsub := integral_comp_mul_deriv (a := Θ) (b := b) (g := g)
    (f := fun y => k * Real.log (y / Θ)) (f' := fun y => k / y)
    (fun x hx => logScale_hasDerivAt hΘ (pos x hx))
    (fun x hx => (continuousAt_const.div continuousAt_id (pos x hx).ne').continuousWithinAt)
    hgc
  rw [hsub]
  have e0 : k * Real.log (Θ / Θ) = 0 := by simp [div_self hΘ.ne']
  have e1 : k * Real.log (b / Θ) = 1 := by
    rw [hbdef, mul_div_cancel_left₀ _ hΘ.ne', Real.log_exp]; field_simp
  rw [e0, e1]
  have hcongr : ∀ u ∈ uIcc (0 : ℝ) 1, g u =
      F * (k * (2 * (u * (1 - u)) * (1 - 2 * u)) - (u * (1 - u)) ^ 2 / 2) ^ 2
        + G * ((u * (1 - u)) ^ 2) ^ 2 := by
    intro u hu
    rw [uIcc_of_le zero_le_one] at hu
    obtain ⟨h1, h2⟩ := bump_on_unit hu.1 hu.2
    simp only [g, h1, h2]
  rw [integral_congr hcongr, unit_integral]

/-- **Sharpness of the tail threshold.** If on `[Θ, ∞)` (`Θ > 0`) the coefficients satisfy
`P ≤ F θ²`, `Q ≤ G` with `F > 0` and `F + 4 G < 0` (tail ratio `G/F < −1/4`), then a
compactly supported `C¹` displacement, supported in `[Θ, ∞)`, has negative line energy:
the explicit tail mode with `k = min 1 (−(F + 4G)/(96 F))`. -/
theorem tail_unstable {P Q : ℝ → ℝ} {F G Θ : ℝ} (hPc : Continuous P) (hQc : Continuous Q)
    (hF : 0 < F) (hS : F + 4 * G < 0) (hΘ : 0 < Θ) (hPt : ∀ x, Θ ≤ x → P x ≤ F * x ^ 2)
    (hQt : ∀ x, Θ ≤ x → Q x ≤ G) :
    ∃ ξ ξ' : ℝ → ℝ, ∃ a b : ℝ, Θ ≤ a ∧ LineAdmissible ξ ξ' a b ∧ lineEnergy P Q ξ ξ' < 0 := by
  set k := min 1 (-(F + 4 * G) / (96 * F)) with hkdef
  have hr : 0 < -(F + 4 * G) / (96 * F) := div_pos (by linarith) (by linarith)
  have hk : 0 < k := lt_min one_pos hr
  have hk1 : k ≤ 1 := min_le_left _ _
  have hkr : F * k ≤ -(F + 4 * G) / 96 := by
    have := mul_le_mul_of_nonneg_left (min_le_right 1 (-(F + 4 * G) / (96 * F))) hF.le
    rw [← hkdef] at this
    calc F * k ≤ F * (-(F + 4 * G) / (96 * F)) := this
      _ = -(F + 4 * G) / 96 := by field_simp
  have hA := tailMode_admissible hΘ hk
  refine ⟨_, _, Θ, Θ * Real.exp (1 / k), le_rfl, hA, ?_⟩
  rw [lineEnergy_eq hA]
  have hb := hA.le
  have hmono : newcombForm P Q Θ (Θ * Real.exp (1 / k)) (tailMode Θ k) (tailMode' Θ k) ≤
      newcombForm (fun x => F * x ^ 2) (fun _ => G) Θ (Θ * Real.exp (1 / k))
        (tailMode Θ k) (tailMode' Θ k) := by
    apply integral_mono_on hb (newcomb_integrable (hA.c1On _ _) hPc.continuousOn hQc.continuousOn)
      (newcomb_integrable (hA.c1On _ _) (by fun_prop) continuousOn_const)
    intro x hx
    nlinarith [mul_le_mul_of_nonneg_right (hPt x hx.1) (sq_nonneg (tailMode' Θ k x)),
      mul_le_mul_of_nonneg_right (hQt x hx.1) (sq_nonneg (tailMode Θ k x))]
  rw [tailMode_energy F G hΘ hk] at hmono
  refine lt_of_le_of_lt hmono (mul_neg_of_pos_of_neg (inv_pos.mpr hk) ?_)
  have hk2 : k ^ 2 ≤ k := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hk2 hF.le]

/-- A bad tail rules out every tail certificate at level `0`: if `P ≤ F θ²`, `Q ≤ G` on
`[Θ, ∞)` with `F > 0`, `F + 4 G < 0`, the line problem is unstable. -/
theorem no_tailCertificate_of_bad_tail (op : LineOperator) {F G Θ : ℝ} (hF : 0 < F)
    (hS : F + 4 * G < 0) (hΘ : 0 < Θ) (hPt : ∀ x, Θ ≤ x → op.P x ≤ F * x ^ 2)
    (hQt : ∀ x, Θ ≤ x → op.Q x ≤ G) : IsEmpty (op.TailCertificate 0) := by
  obtain ⟨ξ, ξ', a, b, -, hA, hneg⟩ := tail_unstable op.P_cont op.Q_cont hF hS hΘ hPt hQt
  exact ⟨fun T => absurd (T.energy_nonneg op hA) (not_le.mpr hneg)⟩

/-- A bad tail also rules out every global positive supersolution on `ℝ`. -/
theorem no_global_supersolution_of_bad_tail (op : LineOperator) {F G Θ : ℝ} (hF : 0 < F)
    (hS : F + 4 * G < 0) (hΘ : 0 < Θ) (hPt : ∀ x, Θ ≤ x → op.P x ≤ F * x ^ 2)
    (hQt : ∀ x, Θ ≤ x → op.Q x ≤ G) : IsEmpty (JacobiData op.P (op.shifted 0) univ) := by
  obtain ⟨ξ, ξ', a, b, -, hA, hneg⟩ := tail_unstable op.P_cont op.Q_cont hF hS hΘ hPt hQt
  exact ⟨fun J => absurd (by simpa using op.global_barta J hA) (not_le.mpr hneg)⟩

/-- **Threshold, both directions, for the model tail.** For an operator whose tail is
exactly `P = s² θ²`, `Q = q₀` on `|θ| ≥ Θ` (`s ≠ 0`), the explicit tail flux exists iff
`q₀/s² ≥ −1/4`, and if `q₀/s² < −1/4` the line problem has negative-energy compactly
supported modes. -/
theorem model_tail_dichotomy {P Q : ℝ → ℝ} {s q₀ Θ : ℝ} (hPc : Continuous P)
    (hQc : Continuous Q) (hs : s ≠ 0) (hΘ : 0 < Θ) (hPt : ∀ x, Θ ≤ x → P x = s ^ 2 * x ^ 2)
    (hQt : ∀ x, Θ ≤ x → Q x = q₀) :
    ((∃ α : ℝ, α * (α + 1) * s ^ 2 ≤ q₀) ↔ -1 / 4 ≤ q₀ / s ^ 2) ∧
      (q₀ / s ^ 2 < -1 / 4 →
        ∃ ξ ξ' : ℝ → ℝ, ∃ a b : ℝ, Θ ≤ a ∧ LineAdmissible ξ ξ' a b ∧
          lineEnergy P Q ξ ξ' < 0) := by
  refine ⟨tail_exponent_iff_ratio hs, fun h => ?_⟩
  have hs2 : 0 < s ^ 2 := by positivity
  have hS : s ^ 2 + 4 * q₀ < 0 := by
    rw [div_lt_iff₀ hs2] at h; linarith
  exact tail_unstable hPc hQc hs2 hS hΘ (fun x hx => (hPt x hx).le) (fun x hx => (hQt x hx).le)

/-! ## A certified example on the line -/

section certifiedExample
open PlasmaLean.Certificates.QPoly

/-- Example operator: `P = 1 + θ²` (unit shear, `P ≥ θ²`), drive
`Q = −1/5 − (1/12) max 0 (4 − θ²)` (bad curvature `Q(0) = −8/15` near `θ = 0`, tail value
`q₀ = −1/5` for `|θ| ≥ 2`), `W = 1`. -/
@[expose] def exampleLineOp : LineOperator where
  P := fun x => 1 + x ^ 2
  Q := fun x => -1 / 5 - 1 / 12 * max 0 (4 - x ^ 2)
  W := fun _ => 1
  P_pos x := by positivity
  W_nonneg _ := zero_le_one
  P_cont := by fun_prop
  Q_cont := by fun_prop
  W_cont := continuous_const

/-- Inner witness on `[-2, 2]`: an even degree-14 rational polynomial, a least-squares
fit (found outside Lean, untrusted) to the Jacobi solution of the shifted equation
`-(P w')' + (Q − 3/100) w = 0`, `w(0) = 1`, `w'(0) = 0`. -/
@[expose] def lineW : List ℚ :=
  [1, 0, -36079 / 131072, 0, 141437 / 1048576, 0, -124471 / 2097152, 0,
    319243 / 16777216, 0, -65903 / 16777216, 0, 123357 / 268435456, 0, -24707 / 1073741824]

/-- Sixteen uniform pieces of `[-2, 2]`. -/
@[expose] def lineGrid16 : List ℚ := (List.range 16).map (fun i : ℕ => -2 + ((i : ℚ) + 1) / 4)

/-- 128 uniform pieces of `[-2, 2]`. -/
@[expose] def lineGrid128 : List ℚ :=
  (List.range 128).map (fun i : ℕ => -2 + ((i : ℚ) + 1) / 32)

/-- Accepted check: the inner witness is at least `1/2` on `[-2, 2]`. -/
theorem lineW_check : checkOn lineW (1 / 2) (-2) 2 lineGrid16 = true := by decide +kernel

/-- Accepted check: `(Q − 0) w − (P w')' ≥ 0` on `[-2, 2]`, with `Q = −8/15 + θ²/12`
there. -/
theorem lineResidual_check :
    checkOn (jacobiResidual [1, 0, 1] [-8 / 15, 0, 1 / 12] lineW 0) 0 (-2) 2 lineGrid128 =
      true := by decide +kernel

/-- Rejected fixture: the constant witness `w = 1` fails on `[-2, 2]` (`Q(0) < 0`). -/
theorem lineConst_reject :
    checkOn (jacobiResidual [1, 0, 1] [-8 / 15, 0, 1 / 12] [1] 0) 0 (-2) 2 lineGrid16 =
      false := by decide +kernel

/-- On `[-2, 2]` the (unshifted) drive is the polynomial `−8/15 + θ²/12`. -/
theorem exampleQ_eq {x : ℝ} (hx : x ∈ Icc (-2 : ℝ) 2) :
    exampleLineOp.shifted 0 x = eval [-8 / 15, 0, 1 / 12] x := by
  have : 0 ≤ 4 - x ^ 2 := by nlinarith [hx.1, hx.2]
  simp [LineOperator.shifted, exampleLineOp, max_eq_right this]
  ring

/-- Cast bookkeeping for the rational endpoints `±2`. -/
theorem mem_Icc_cast {x : ℝ} (hx : x ∈ Icc (-2 : ℝ) 2) :
    x ∈ Icc (((-2 : ℚ)) : ℝ) ((2 : ℚ) : ℝ) := by
  simpa using hx

/-- The inner Jacobi witness of the example, from the two exact checks. -/
@[expose] def exampleInner : JacobiData exampleLineOp.P (exampleLineOp.shifted 0) (Icc (-2) 2) where
  u := eval lineW
  u' := eval (PlasmaLean.Certificates.QPoly.deriv lineW)
  k := eval (PlasmaLean.Certificates.QPoly.deriv
    (mul [1, 0, 1] (PlasmaLean.Certificates.QPoly.deriv lineW)))
  hu x _ := hasDerivAt_eval lineW x
  hu'c := (continuous_eval _).continuousOn
  hk x _ := by
    have := hasDerivAt_eval (mul [1, 0, 1] (PlasmaLean.Certificates.QPoly.deriv lineW)) x
    convert this using 1
    funext y
    have e : eval [1, 0, 1] y = 1 + y ^ 2 := by simp; ring
    rw [eval_mul, e]
    rfl
  hkc := (continuous_eval _).continuousOn
  pos x hx := by
    have := checkOn_sound lineW_check x (mem_Icc_cast hx)
    have h2 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
    linarith
  super x hx := by
    have := checkOn_sound lineResidual_check x (mem_Icc_cast hx)
    rw [exampleQ_eq hx]
    simp [jacobiResidual] at this ⊢
    linarith

/-- Left junction: inner flux at `−2` is at most the tail flux `α s² θ = 7/5`. -/
theorem example_junctionL :
    exampleLineOp.P (-2) * exampleInner.u' (-2) / exampleInner.u (-2) ≤
      (-7 / 10) * (1 : ℝ) ^ 2 * (-2) := by
  simp only [exampleLineOp, exampleInner, lineW]
  rw [div_le_iff₀ (by simp; norm_num)]
  simp [PlasmaLean.Certificates.QPoly.deriv]
  norm_num

/-- Right junction: the tail flux `α s² θ = −7/5` is at most the inner flux at `2`. -/
theorem example_junctionR :
    (-7 / 10) * (1 : ℝ) ^ 2 * 2 ≤
      exampleLineOp.P 2 * exampleInner.u' 2 / exampleInner.u 2 := by
  simp only [exampleLineOp, exampleInner, lineW]
  rw [le_div_iff₀ (by simp; norm_num)]
  simp [PlasmaLean.Certificates.QPoly.deriv]
  norm_num

/-- The example's tail certificate: inner witness on `[-2, 2]`, Suydam tails with `s = 1`,
`α = −7/10`, `q₀ = −1/5` (`α (α + 1) = −21/100 ≤ −1/5`). -/
@[expose] def exampleTail : exampleLineOp.TailCertificate 0 :=
  LineOperator.TailCertificate.ofSuydam exampleLineOp (Θ := 2) (s := 1) (α := -7 / 10)
    (q₀ := -1 / 5) (by norm_num) exampleInner (by norm_num)
    (fun x _ => by simp [exampleLineOp])
    (fun x hx => by
      have h4 : 4 ≤ x ^ 2 := by
        have := sq_abs x
        nlinarith [abs_nonneg x]
      simp [LineOperator.shifted, exampleLineOp, max_eq_left (by linarith : 4 - x ^ 2 ≤ 0)])
    example_junctionL example_junctionR

/-- **Certified ballooning stability on the whole line.** For `P = 1 + θ²` and
`Q = −1/5 − (1/12) max 0 (4 − θ²)`, every compactly supported `C¹` displacement has
`∫_ℝ (P ξ'² + Q ξ²) ≥ 0`, although `Q(0) = −8/15` is below the frozen Suydam bound
`−1/4` (`example_frozen_fails`). -/
theorem example_line_stable {ξ ξ' : ℝ → ℝ} {a b : ℝ} (h : LineAdmissible ξ ξ' a b) :
    0 ≤ lineEnergy (fun x => 1 + x ^ 2) (fun x => -1 / 5 - 1 / 12 * max 0 (4 - x ^ 2)) ξ ξ' :=
  exampleTail.energy_nonneg exampleLineOp h

/-- Sanity: the explicit tail flux alone cannot certify the example globally — no
exponent works for the frozen value `Q(0) = −8/15` with `s = 1`. -/
theorem example_frozen_fails : ¬ ∃ α : ℝ, α * (α + 1) * (1 : ℝ) ^ 2 ≤ -8 / 15 := by
  rw [tail_exponent_iff_suydam]; norm_num

end certifiedExample

end PlasmaLean.Stability.BallooningInfinite
