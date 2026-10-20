/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilSoundA
public import PlasmaLean.Design.PolygonCoilData

/-!
# Symmetries of the polygonal coil set

The coil set `fils = ⋃ orbit K V` is invariant under the two-element-generated group
`{id, Rot_π, σ, Rot_π σ}` with currents `K, K, -K, -K`. Here:

* `IsSym g`: `g` is linear, isometric and commutes with the cross product (a rotation);
  `isSym_rotPi`, `isSym_σ`;
* `segClosed_sym`: the closed-form segment field is equivariant under rotations;
* `Bseg_rotPi`, `Bseg_σ`: `Bseg (Rot_π y) = Rot_π (Bseg y)`, `Bseg (σ y) = -σ (Bseg y)` for
  every coil set built from orbits;
* `hel_rotPi`, `hel_σ`: the same for the target `hel`;
* `coilPt_rotPi`, `coilPt_σ`: the set of points on the segments is invariant.
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator
    PlasmaLean.Design.RationalStellarator.Coils
  PlasmaLean.Design.RationalStellarator.CoilsTF Set Real
open scoped RealInnerProductSpace

/-- A rotation of space: linear, isometric, commuting with the cross product. -/
@[expose] def IsSym (g : Space → Space) : Prop :=
  (∀ u v, g (u + v) = g u + g v) ∧ (∀ (c : ℝ) u, g (c • u) = c • g u) ∧
    (∀ u v, ⟪g u, g v⟫ = ⟪u, v⟫) ∧ (∀ u v, cross (g u) (g v) = g (cross u v))

theorem IsSym.sub {g : Space → Space} (h : IsSym g) (u v : Space) : g (u - v) = g u - g v := by
  have := h.1 v (u - v)
  rw [add_sub_cancel] at this
  rw [this]; abel

theorem IsSym.neg {g : Space → Space} (h : IsSym g) (u : Space) : g (-u) = -g u := by
  have := h.2.1 (-1) u
  simpa using this

theorem IsSym.zero {g : Space → Space} (h : IsSym g) : g 0 = 0 := by
  have := h.2.1 0 0
  simpa using this

theorem IsSym.norm {g : Space → Space} (h : IsSym g) (u : Space) : ‖g u‖ = ‖u‖ := by
  have := h.2.2.1 u u
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this

theorem IsSym.list_sum {g : Space → Space} (h : IsSym g) {ι : Type} (L : List ι) (f : ι → Space) :
    g (L.map f).sum = (L.map fun i => g (f i)).sum := by
  induction L with
  | nil => simp [h.zero]
  | cons i L ih => simp only [List.map_cons, List.sum_cons, h.1, ih]

theorem isSym_rotPi : IsSym rotPi := by
  refine ⟨fun u v => ?_, fun c u => ?_, fun u v => ?_, fun u v => ?_⟩
  · ext k; fin_cases k <;> simp [rotPi] <;> ring
  · ext k; fin_cases k <;> simp [rotPi]
  · simp only [EuclideanSpace.inner_eq_star_dotProduct, rotPi]
    simp [dotProduct, Fin.sum_univ_three]
  · ext k; fin_cases k <;> simp [cross, rotPi, cross_apply] <;> ring

theorem isSym_σ : IsSym σ := by
  refine ⟨fun u v => ?_, fun c u => ?_, fun u v => ?_, fun u v => ?_⟩
  · ext k; fin_cases k <;> simp [σ]; ring
  · ext k; fin_cases k <;> simp [σ]
  · simp only [EuclideanSpace.inner_eq_star_dotProduct, σ]
    simp [dotProduct, Fin.sum_univ_three]; ring
  · ext k; fin_cases k <;> simp [cross, σ, cross_apply] <;> ring

theorem rotPi_rotPi (y : Space) : rotPi (rotPi y) = y := by
  ext k; fin_cases k <;> simp [rotPi]

theorem σ_σ (y : Space) : σ (σ y) = y := by
  ext k; fin_cases k <;> simp [σ]

/-- **Equivariance of the closed-form segment field** under rotations. -/
theorem segClosed_sym {g : Space → Space} (h : IsSym g) (κ : ℝ) (p q y : Space) :
    segClosed κ (g p) (g q) (g y) = g (segClosed κ p q y) := by
  unfold segClosed
  rw [← h.sub, ← h.sub, h.norm, h.norm, h.2.2.1, h.2.2.2, h.2.1]

theorem seg_sym {g : Space → Space} (h : IsSym g) (p q : Space) (t : ℝ) :
    seg (g p) (g q) t = g (seg p q t) := by
  unfold seg; rw [h.1, h.2.1, h.sub]

theorem ptR_gRi (p : ℤ × ℤ × ℤ) : ptR (gRi p) = rotPi (ptR p) := by
  ext k; fin_cases k <;> simp [ptR, gRi, rotPi, neg_div]

theorem ptR_gSi (p : ℤ × ℤ × ℤ) : ptR (gSi p) = σ (ptR p) := by
  ext k; fin_cases k <;> simp [ptR, gSi, σ, neg_div]

theorem gRi_gRi (p : ℤ × ℤ × ℤ) : gRi (gRi p) = p := by simp [gRi]
theorem gSi_gSi (p : ℤ × ℤ × ℤ) : gSi (gSi p) = p := by simp [gSi]
theorem gSi_gRi (p : ℤ × ℤ × ℤ) : gSi (gRi p) = gRi (gSi p) := by simp [gSi, gRi]

/-! ## The field of one filament -/

/-- The closed-form field of one filament (current numerator, vertices). -/
@[expose] def BF (f : ℤ × List (ℤ × ℤ × ℤ)) (y : Space) : Space :=
  ((List.zip f.2 (rot1 f.2)).map fun pq => segClosed ((f.1 : ℝ) / S32) (ptR pq.1) (ptR pq.2) y).sum

theorem Bseg_eq_sum (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (y : Space) :
    Bseg fils y = (fils.map fun f => BF f y).sum := by
  induction fils with
  | nil => rfl
  | cons f fs ih =>
    simp only [Bseg, allSegs, List.flatMap_cons, List.map_append, List.sum_append, List.map_map,
      List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih]; rfl

theorem rot1_map {α β : Type} (f : α → β) (l : List α) : rot1 (l.map f) = (rot1 l).map f := by
  cases l <;> simp [rot1]

theorem list_sum_map_neg' {ι : Type} (L : List ι) (f : ι → Space) :
    (L.map fun i => -f i).sum = -(L.map f).sum := by
  induction L with
  | nil => simp
  | cons i L ih => simp only [List.map_cons, List.sum_cons, ih, neg_add]

theorem BF_neg (K : ℤ) (vs : List (ℤ × ℤ × ℤ)) (y : Space) : BF (-K, vs) y = -BF (K, vs) y := by
  unfold BF
  rw [← list_sum_map_neg']
  congr 1
  apply List.map_congr_left
  intro pq _
  simp only [segClosed, Int.cast_neg, neg_div, neg_mul, neg_smul]

/-- Equivariance of a filament field under an integer symmetry `gi` realising `g`. -/
theorem BF_sym {g : Space → Space} (h : IsSym g) {gi : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ}
    (hpt : ∀ p, ptR (gi p) = g (ptR p)) (hinv : ∀ p, gi (gi p) = p)
    (K : ℤ) (ws : List (ℤ × ℤ × ℤ)) (y : Space) :
    BF (K, ws) (g y) = g (BF (K, ws.map gi) y) := by
  unfold BF
  rw [h.list_sum]
  simp only [rot1_map, List.zip_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro pq _
  simp only [Function.comp, Prod.map]
  rw [← segClosed_sym h, ← hpt, ← hpt, hinv, hinv]

/-- The field of one orbit. -/
theorem Bseg_orbit (K : ℤ) (vs : List (ℤ × ℤ × ℤ)) (y : Space) :
    Bseg (orbit K vs) y = BF (K, vs) y + BF (K, vs.map gRi) y + BF (-K, vs.map gSi) y +
      BF (-K, vs.map fun p => gRi (gSi p)) y := by
  rw [Bseg_eq_sum]; simp [orbit, add_assoc]

theorem Bseg_orbit_rotPi (K : ℤ) (vs : List (ℤ × ℤ × ℤ)) (y : Space) :
    Bseg (orbit K vs) (rotPi y) = rotPi (Bseg (orbit K vs) y) := by
  have hs := BF_sym isSym_rotPi ptR_gRi gRi_gRi
  rw [Bseg_orbit, Bseg_orbit, hs, hs, hs, hs]
  simp only [List.map_map, Function.comp_def, gRi_gRi, List.map_id']
  simp only [isSym_rotPi.1]
  abel

theorem Bseg_orbit_σ (K : ℤ) (vs : List (ℤ × ℤ × ℤ)) (y : Space) :
    Bseg (orbit K vs) (σ y) = -σ (Bseg (orbit K vs) y) := by
  have hs := BF_sym isSym_σ ptR_gSi gSi_gSi
  rw [Bseg_orbit, Bseg_orbit, hs, hs, hs, hs]
  simp only [List.map_map, Function.comp_def, gSi_gSi, gSi_gRi, List.map_id']
  simp only [BF_neg, isSym_σ.1, isSym_σ.neg]
  abel

theorem Bseg_append (a b : List (ℤ × List (ℤ × ℤ × ℤ))) (y : Space) :
    Bseg (a ++ b) y = Bseg a y + Bseg b y := by
  rw [Bseg_eq_sum, Bseg_eq_sum, Bseg_eq_sum, List.map_append, List.sum_append]

/-- **Two field periods of the coil field.** -/
theorem Bseg_rotPi (L : List (ℤ × List (ℤ × ℤ × ℤ))) (y : Space) :
    Bseg (L.flatMap fun kv => orbit kv.1 kv.2) (rotPi y) =
      rotPi (Bseg (L.flatMap fun kv => orbit kv.1 kv.2) y) := by
  induction L with
  | nil => simp [Bseg, allSegs, isSym_rotPi.zero]
  | cons kv L ih =>
    rw [List.flatMap_cons, Bseg_append, Bseg_append, ih, Bseg_orbit_rotPi, isSym_rotPi.1]

/-- **Stellarator symmetry of the coil field.** -/
theorem Bseg_σ (L : List (ℤ × List (ℤ × ℤ × ℤ))) (y : Space) :
    Bseg (L.flatMap fun kv => orbit kv.1 kv.2) (σ y) =
      -σ (Bseg (L.flatMap fun kv => orbit kv.1 kv.2) y) := by
  induction L with
  | nil => simp [Bseg, allSegs, isSym_σ.zero]
  | cons kv L ih =>
    rw [List.flatMap_cons, Bseg_append, Bseg_append, ih, Bseg_orbit_σ, isSym_σ.1, neg_add]

/-! ## The target -/

theorem toroidal_rotPi (y : Space) : toroidal (rotPi y) = rotPi (toroidal y) := by
  ext k; fin_cases k <;> simp [toroidal, winv_rotPi] <;> simp [rotPi]

theorem toroidal_σ (y : Space) : toroidal (σ y) = -σ (toroidal y) := by
  ext k; fin_cases k <;> simp [toroidal, winv_σ] <;> simp [σ]

theorem hel_rotPi (y : Space) : hel (rotPi y) = rotPi (hel y) := by
  unfold hel; rw [field_rotPi, toroidal_rotPi, isSym_rotPi.sub]

theorem hel_σ (y : Space) : hel (σ y) = -σ (hel y) := by
  unfold hel; rw [field_stellSym, toroidal_σ, isSym_σ.sub]; abel

/-! ## The points of the coil -/

/-- `x` lies on one of the segments. -/
@[expose] def coilPt (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (x : Space) : Prop :=
  ∃ z ∈ allSegs fils, ∃ t ∈ Icc (0 : ℝ) 1, x = seg (ptR z.2.1) (ptR z.2.2) t

theorem mem_allSegs {fils : List (ℤ × List (ℤ × ℤ × ℤ))} {z : ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)} :
    z ∈ allSegs fils ↔ ∃ f ∈ fils, (z.2.1, z.2.2) ∈ List.zip f.2 (rot1 f.2) ∧ z.1 = f.1 := by
  unfold allSegs
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨f, hf, pq, hpq, rfl⟩; exact ⟨f, hf, hpq, rfl⟩
  · rintro ⟨f, hf, hpq, h⟩
    exact ⟨f, hf, _, hpq, by rcases z with ⟨a, b, c⟩; simp_all⟩

/-- A segment of a filament mapped by `gi` is a segment of the mapped filament. -/
theorem zip_rot1_map {gi : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ} {vs : List (ℤ × ℤ × ℤ)}
    {p q : ℤ × ℤ × ℤ} (h : (p, q) ∈ List.zip vs (rot1 vs)) :
    (gi p, gi q) ∈ List.zip (vs.map gi) (rot1 (vs.map gi)) := by
  rw [rot1_map, List.zip_map]
  exact List.mem_map.mpr ⟨(p, q), h, rfl⟩

/-- Invariance of the coil points under a symmetry permuting the filament vertex lists. -/
theorem coilPt_sym {g : Space → Space} (h : IsSym g) {gi : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ}
    (hpt : ∀ p, ptR (gi p) = g (ptR p)) {fils : List (ℤ × List (ℤ × ℤ × ℤ))}
    (hperm : ∀ f ∈ fils, ∃ f' ∈ fils, f'.2 = f.2.map gi) {x : Space} (hx : coilPt fils x) :
    coilPt fils (g x) := by
  obtain ⟨z, hz, t, ht, rfl⟩ := hx
  obtain ⟨f, hf, hpq, -⟩ := mem_allSegs.mp hz
  obtain ⟨f', hf', he⟩ := hperm f hf
  refine ⟨(f'.1, gi z.2.1, gi z.2.2), mem_allSegs.mpr ⟨f', hf', ?_, rfl⟩, t, ht, ?_⟩
  · rw [he]; exact zip_rot1_map hpq
  · simp only [hpt, seg_sym h]

theorem orbits_perm_rotPi (L : List (ℤ × List (ℤ × ℤ × ℤ))) :
    ∀ f ∈ L.flatMap (fun kv => orbit kv.1 kv.2),
      ∃ f' ∈ L.flatMap (fun kv => orbit kv.1 kv.2), f'.2 = f.2.map gRi := by
  intro f hf
  obtain ⟨kv, hkv, hf⟩ := List.mem_flatMap.mp hf
  simp only [orbit, List.mem_cons, List.not_mem_nil, or_false] at hf
  have hin : ∀ f', f' ∈ orbit kv.1 kv.2 → f' ∈ L.flatMap (fun kv => orbit kv.1 kv.2) :=
    fun f' h => List.mem_flatMap.mpr ⟨kv, hkv, h⟩
  rcases hf with rfl | rfl | rfl | rfl
  · exact ⟨(kv.1, kv.2.map gRi), hin _ (by simp [orbit]), rfl⟩
  · exact ⟨(kv.1, kv.2), hin _ (by simp [orbit]), by simp [Function.comp_def, gRi_gRi]⟩
  · exact ⟨(-kv.1, kv.2.map fun p => gRi (gSi p)), hin _ (by simp [orbit]),
      by simp [Function.comp_def]⟩
  · exact ⟨(-kv.1, kv.2.map gSi), hin _ (by simp [orbit]), by simp [Function.comp_def, gRi_gRi]⟩

theorem orbits_perm_σ (L : List (ℤ × List (ℤ × ℤ × ℤ))) :
    ∀ f ∈ L.flatMap (fun kv => orbit kv.1 kv.2),
      ∃ f' ∈ L.flatMap (fun kv => orbit kv.1 kv.2), f'.2 = f.2.map gSi := by
  intro f hf
  obtain ⟨kv, hkv, hf⟩ := List.mem_flatMap.mp hf
  simp only [orbit, List.mem_cons, List.not_mem_nil, or_false] at hf
  have hin : ∀ f', f' ∈ orbit kv.1 kv.2 → f' ∈ L.flatMap (fun kv => orbit kv.1 kv.2) :=
    fun f' h => List.mem_flatMap.mpr ⟨kv, hkv, h⟩
  rcases hf with rfl | rfl | rfl | rfl
  · exact ⟨(-kv.1, kv.2.map gSi), hin _ (by simp [orbit]), rfl⟩
  · exact ⟨(-kv.1, kv.2.map fun p => gRi (gSi p)), hin _ (by simp [orbit]),
      by simp [Function.comp_def, gSi_gRi]⟩
  · exact ⟨(kv.1, kv.2), hin _ (by simp [orbit]), by simp [Function.comp_def, gSi_gSi]⟩
  · exact ⟨(kv.1, kv.2.map gRi), hin _ (by simp [orbit]),
      by simp [Function.comp_def, gSi_gRi, gSi_gSi]⟩

theorem coilPt_rotPi (L : List (ℤ × List (ℤ × ℤ × ℤ))) {x : Space}
    (hx : coilPt (L.flatMap fun kv => orbit kv.1 kv.2) x) :
    coilPt (L.flatMap fun kv => orbit kv.1 kv.2) (rotPi x) :=
  coilPt_sym isSym_rotPi ptR_gRi (orbits_perm_rotPi L) hx

theorem coilPt_σ (L : List (ℤ × List (ℤ × ℤ × ℤ))) {x : Space}
    (hx : coilPt (L.flatMap fun kv => orbit kv.1 kv.2) x) :
    coilPt (L.flatMap fun kv => orbit kv.1 kv.2) (σ x) :=
  coilPt_sym isSym_σ ptR_gSi (orbits_perm_σ L) hx

end PlasmaLean.Design.PolygonCoil
