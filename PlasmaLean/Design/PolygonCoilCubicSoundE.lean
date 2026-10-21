/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCubicSoundD

/-!
# Soundness of the cubic checker, part E: lines

The records of a grid line (`lineOut4`) carry, conditionally on the geometric conditions that
the cell check verifies:

* `LVal`: the value bounds at their corner;
* `LW`: the `w`-remainder of their window;
* `LT`: the `t`-remainder of the strip of their window and the distance `≥ 1/5` to the coil.

`lineOut4_sound` proves these for every record (`QuadP` expresses the window structure).
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator
  PlasmaLean.Design.RationalStellarator.Coils PlasmaLean.Design.RationalStellarator.CoilsTF Set Real
open scoped RealInnerProductSpace

/-- The distance from the cell `[T₁, T₂] × [W₁, W₂]` to every coil segment is `≥ 1/5`. -/
@[expose] def DGood (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (kind : ℕ) (T1 T2 W1 W2 : ℝ) : Prop :=
  ∀ w ∈ Icc W1 W2, ∀ t ∈ Icc T1 T2, ∀ z ∈ allSegs fils, ∀ s ∈ Icc (0 : ℝ) 1,
    1 / 5 ≤ ‖ptF kind t w - seg (ptR z.2.1) (ptR z.2.2) s‖

/-- Value facts of the record of corner `(m, wn)` (if it passed and the radius is positive). -/
@[expose] def LVal (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (F : Face4) (m wn : ℤ) (r : CRec) : Prop :=
  (F.kind < 2 ∨ 0 < wn) → r.ok = true →
    ValGood fils F.kind ((m : ℝ) / 4096) ((wn : ℝ) / F.wd) r

/-- The geometric conditions of a `w`-window. -/
@[expose] def CondW (F : Face4) (wp wn wn1 wn2 : ℤ) : Prop :=
  wp < wn ∧ wn < wn1 ∧ wn1 < wn2 ∧ (F.kind < 2 ∨ 17 / 20 ≤ (wp : ℝ) / F.wd)

/-- `w`-remainder fact of the record with window `(wp, wn, wn1, wn2)` on line `m`. -/
@[expose] def LW (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (F : Face4) (m wp wn wn1 wn2 : ℤ)
    (r : CRec) : Prop :=
  CondW F wp wn wn1 wn2 → r.ok = true →
    WGood fils F.kind ((m : ℝ) / 4096) ((wp : ℝ) / F.wd) ((wn : ℝ) / F.wd) ((wn1 : ℝ) / F.wd)
      ((wn2 : ℝ) / F.wd) (r.rw / ((two40 : ℕ) : ℝ))

/-- The geometric conditions of a `t`-strip. -/
@[expose] def CondT (F : Face4) (mp m mn mn2 wp wn wn1 wn2 : ℤ) : Prop :=
  mp < m ∧ m < mn ∧ mn < mn2 ∧ CondW F wp wn wn1 wn2 ∧
    (∀ w ∈ Icc ((wn : ℝ) / F.wd) ((wn1 : ℝ) / F.wd), 17 / 20 ≤ faceRho F.kind w ∧
      faceRho F.kind w ≤ 23 / 20 ∧ |faceZeta F.kind w| ≤ 3 / 25) ∧
    -1 / 2 ≤ (mp : ℝ) / 4096 ∧ (mn2 : ℝ) / 4096 ≤ 1 / 2

/-- `t`-remainder and distance facts of the record with window `(wp, wn, wn1, wn2)` on line `m`
with `t`-neighbours `mp, mn, mn2`. -/
@[expose] def LT (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (F : Face4) (mp m mn mn2 wp wn wn1 wn2 : ℤ)
    (r : CRec) : Prop :=
  CondT F mp m mn mn2 wp wn wn1 wn2 → r.ok = true →
    TGood fils F.kind ((mp : ℝ) / 4096) ((m : ℝ) / 4096) ((mn : ℝ) / 4096) ((mn2 : ℝ) / 4096)
      ((wn : ℝ) / F.wd) ((wn1 : ℝ) / F.wd) (r.rt / ((two40 : ℕ) : ℝ)) ∧
    DGood fils F.kind ((m : ℝ) / 4096) ((mn : ℝ) / 4096) ((wn : ℝ) / F.wd) ((wn1 : ℝ) / F.wd)

/-- A property of the windows `(w₀, w₁, w₂, w₃)` of a list with the record of `w₁`. -/
@[expose] def QuadP (P : ℤ → ℤ → ℤ → ℤ → CRec → Prop) : List ℤ → List CRec → Prop
  | w0 :: w1 :: w2 :: w3 :: ws, _ :: r1 :: r2 :: r3 :: rs =>
    P w0 w1 w2 w3 r1 ∧ QuadP P (w1 :: w2 :: w3 :: ws) (r1 :: r2 :: r3 :: rs)
  | _, _ => True

/-- Value facts of a corner record (any remainder parameters). -/
theorem corner_val (o : Offs) (nS : ℕ) (fils : List (ℤ × List (ℤ × ℤ × ℤ)))
    (hfv : FilsOK4 o nS fils) (F : Face4) (hk4 : F.kind < 4) (hwd : 0 < F.wd) (m wn : ℤ)
    (hρ : F.kind < 2 ∨ 0 < wn) (P : Option RemP) (gs : List (List ℕ))
    (hxyz : (cornerXYZ4 F m wn).2 = true)
    (hok : (cornerEval4 o nS (fils.map fun f => mkFil o f.1 f.2) (cornerXYZ4 F m wn).1.1
      (cornerXYZ4 F m wn).1.2.1 (cornerXYZ4 F m wn).1.2.2.1 (cornerXYZ4 F m wn).1.2.2.2
      (helAt (helCoef (faceRZ4 F wn).1 (faceRZ4 F wn).2) (trigOf4 m)) P gs).ok = true) :
    let co := cornerEval4 o nS (fils.map fun f => mkFil o f.1 f.2) (cornerXYZ4 F m wn).1.1
      (cornerXYZ4 F m wn).1.2.1 (cornerXYZ4 F m wn).1.2.2.1 (cornerXYZ4 F m wn).1.2.2.2
      (helAt (helCoef (faceRZ4 F wn).1 (faceRZ4 F wn).2) (trigOf4 m)) P gs
    ‖errF fils (ptF F.kind ((m : ℝ) / 4096) ((wn : ℝ) / F.wd))‖ * ((two40 : ℕ) : ℝ) ≤ co.fin.e ∧
    |errF fils (ptF F.kind ((m : ℝ) / 4096) ((wn : ℝ) / F.wd)) 0 * ((two40 : ℕ) : ℝ) - co.fin.ex|
      ≤ co.fin.rho ∧
    |errF fils (ptF F.kind ((m : ℝ) / 4096) ((wn : ℝ) / F.wd)) 1 * ((two40 : ℕ) : ℝ) - co.fin.ey|
      ≤ co.fin.rho ∧
    |errF fils (ptF F.kind ((m : ℝ) / 4096) ((wn : ℝ) / F.wd)) 2 * ((two40 : ℕ) : ℝ) - co.fin.ez|
      ≤ co.fin.rho := by
  intro co
  obtain ⟨hc, hD⟩ := cornerR_cornerXYZ4 F hwd m wn hxyz
  obtain ⟨hh0, hhv⟩ := helAt_corner4 F ⟨hk4, hwd⟩ m wn hρ
  rw [← hc] at hhv
  have hs := (cornerEval4_sound o nS fils hfv.1 hfv.2.1 hfv.2.2 _ _ _ _ hD _ hh0 hhv P gs hok).1
  simp only [errF, ptF]
  rw [← hc]
  exact hs

/-- `lineGo4` returns one record per `w`-node. -/
theorem lineGo4_length (o : Offs) (nS : ℕ) (fs : List Fil) (F : Face4) (mp m mn mn2 : ℤ)
    (t : Trig) :
    ∀ (ws : List ℤ) (prev : Option ℤ) (hcs : List HC) (gs : List (List ℕ)),
      hcs.length = ws.length → (lineGo4 o nS fs F mp m mn mn2 t prev ws hcs gs).length = ws.length
  | [], prev, hcs, gs, _ => by
    rw [lineGo4.eq_3 _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a b c d h _ => by cases h)]; rfl
  | w :: ws, prev, [], gs, h => by simp at h
  | w :: ws, prev, hc :: hcs, gs, h => by
    have h' : hcs.length = ws.length := by simpa using h
    by_cases hw : ∃ p w1 w2 ws'', prev = some p ∧ ws = w1 :: w2 :: ws''
    · obtain ⟨p, w1, w2, ws'', rfl, rfl⟩ := hw
      rw [lineGo4.eq_1, List.length_cons, lineGo4_length o nS fs F mp m mn mn2 t _ _ _ _ h']; rfl
    · push Not at hw
      rw [lineGo4.eq_2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a b c d h1 h2 => hw a b c d h1 h2),
        List.length_cons, lineGo4_length o nS fs F mp m mn mn2 t _ _ _ _ h']; rfl

/-- **Soundness of the records of a line.** -/
theorem lineGo4_sound (o : Offs) (nS : ℕ) (fils : List (ℤ × List (ℤ × ℤ × ℤ)))
    (hfv : FilsOK4 o nS fils) (F : Face4) (hF : Face4OK F) (mp m mn mn2 : ℤ) :
    ∀ (ws : List ℤ) (prev : Option ℤ) (gs : List (List ℕ)),
      List.Forall₂ (LVal fils F m) ws (lineGo4 o nS (fils.map fun f => mkFil o f.1 f.2) F mp m mn
        mn2 (trigOf4 m) prev ws (ws.map fun wn => helCoef (faceRZ4 F wn).1 (faceRZ4 F wn).2) gs) ∧
      ∀ p, prev = some p → ∀ x : CRec,
        QuadP (LW fils F m) (p :: ws) (x :: lineGo4 o nS (fils.map fun f => mkFil o f.1 f.2) F mp
          m mn mn2 (trigOf4 m) prev ws (ws.map fun wn => helCoef (faceRZ4 F wn).1
            (faceRZ4 F wn).2) gs) ∧
        QuadP (LT fils F mp m mn mn2) (p :: ws) (x :: lineGo4 o nS (fils.map fun f => mkFil o f.1
            f.2)
          F mp m mn mn2 (trigOf4 m) prev ws (ws.map fun wn => helCoef (faceRZ4 F wn).1
            (faceRZ4 F wn).2) gs)
  | [], prev, gs => by
    refine ⟨by simp [lineGo4], fun p _ x => ?_⟩
    simp [QuadP]
  | w :: ws, prev, gs => by
    have hF' := hF
    obtain ⟨hk4, hwd, -, -, -, -⟩ := hF
    have IH := fun prev gs => lineGo4_sound o nS fils hfv F hF' mp m mn mn2 ws prev gs
    set fs := fils.map fun f => mkFil o f.1 f.2
    set cx := cornerXYZ4 F m w
    set hcw := helCoef (faceRZ4 F w).1 (faceRZ4 F w).2
    have hval : ∀ (P : Option RemP) (r8 r9 : ℕ), LVal fils F m w
        ⟨(cornerEval4 o nS fs cx.1.1 cx.1.2.1 cx.1.2.2.1 cx.1.2.2.2 (helAt hcw (trigOf4 m)) P gs).ok
            &&
          cx.2, (cornerEval4 o nS fs cx.1.1 cx.1.2.1 cx.1.2.2.1 cx.1.2.2.2 (helAt hcw (trigOf4 m)) P
            gs).fin.e,
          (cornerEval4 o nS fs cx.1.1 cx.1.2.1 cx.1.2.2.1 cx.1.2.2.2 (helAt hcw (trigOf4 m)) P
              gs).fin.ex,
          (cornerEval4 o nS fs cx.1.1 cx.1.2.1 cx.1.2.2.1 cx.1.2.2.2 (helAt hcw (trigOf4 m)) P
              gs).fin.ey,
          (cornerEval4 o nS fs cx.1.1 cx.1.2.1 cx.1.2.2.1 cx.1.2.2.2 (helAt hcw (trigOf4 m)) P
              gs).fin.ez,
          (cornerEval4 o nS fs cx.1.1 cx.1.2.1 cx.1.2.2.1 cx.1.2.2.2 (helAt hcw (trigOf4 m)) P
              gs).fin.rho,
          r8, r9⟩ := by
      intro P r8 r9 hρ hok
      simp only [Bool.and_eq_true] at hok
      obtain ⟨h1, h2, h3, h4⟩ := corner_val o nS fils hfv F hk4 hwd m w hρ P gs hok.2 hok.1
      exact ⟨h1, h2, h3, h4⟩
    by_cases hw : ∃ p w1 w2 ws'', prev = some p ∧ ws = w1 :: w2 :: ws''
    · obtain ⟨p, w1, w2, ws'', rfl, rfl⟩ := hw
      rw [List.map_cons, lineGo4.eq_1]
      set co := cornerEval4 o nS fs cx.1.1 cx.1.2.1 cx.1.2.2.1 cx.1.2.2.2 (helAt hcw (trigOf4 m))
        (some (remP4 F mp m mn2 p w w1 w2 cx.1.2.2.2)) gs
      obtain ⟨IHv, IHq⟩ := IH (some w) co.gs
      refine ⟨List.Forall₂.cons (hval _ _ _) IHv, fun p' hp' x => ?_⟩
      cases hp'
      obtain ⟨q1, q2⟩ := IHq w rfl ⟨co.ok && cx.2, co.fin.e, co.fin.ex, co.fin.ey, co.fin.ez,
        co.fin.rho, rwC F p w w1 w2 co.rw, rtC F mp m mn mn2 co.rt⟩
      -- the records of `w1 :: w2 :: ws''`
      have hlen : ∃ r1 r2 rest, lineGo4 o nS fs F mp m mn mn2 (trigOf4 m) (some w) (w1 :: w2 ::
          ws'')
          (List.map (fun wn => helCoef (faceRZ4 F wn).1 (faceRZ4 F wn).2) (w1 :: w2 :: ws''))
              co.gs =
          r1 :: r2 :: rest := by
        have hl := lineGo4_length o nS fs F mp m mn mn2 (trigOf4 m) (w1 :: w2 :: ws'') (some w)
          (List.map (fun wn => helCoef (faceRZ4 F wn).1 (faceRZ4 F wn).2) (w1 :: w2 :: ws''))
          co.gs (by simp)
        generalize lineGo4 o nS fs F mp m mn mn2 (trigOf4 m) (some w) (w1 :: w2 :: ws'')
          (List.map (fun wn => helCoef (faceRZ4 F wn).1 (faceRZ4 F wn).2) (w1 :: w2 :: ws''))
          co.gs = L at hl ⊢
        rcases L with _ | ⟨r1, _ | ⟨r2, rest⟩⟩
        · simp at hl
        · simp at hl
        · exact ⟨r1, r2, rest, rfl⟩
      obtain ⟨r1, r2, rest, hrs⟩ := hlen
      rw [hrs] at q1 q2 ⊢
      refine ⟨⟨?_, q1⟩, ⟨?_, q2⟩⟩
      · intro hcw' hok
        simp only [Bool.and_eq_true] at hok
        obtain ⟨c1, c2, c3, c4⟩ := hcw'
        exact corner_w_bound o nS fils hfv F hF' mp m mn2 p w w1 w2 c1 c2 c3 c4 gs hok.2 hok.1
      · intro hct hok
        simp only [Bool.and_eq_true] at hok
        obtain ⟨m1, m2, m3, ⟨c1, c2, c3, c4⟩, hcell, hlo, hhi⟩ := hct
        refine ⟨fun n hn w' hw' t ht => corner_t_bound o nS fils hfv F hF' mp m mn mn2 p w w1 w2
          m1 m2 m3 c1 c2 c3 c4 hcell hlo hhi gs hok.2 hok.1 n hn w' hw' t ht, ?_⟩
        intro w' hw' t ht z hz s hs
        exact corner_t_dist o nS fils hfv F hF' mp m mn mn2 p w w1 w2 m1 m2 m3 c1 c2 c3 c4 hcell gs
          hok.2 hok.1 w' hw' t ⟨by linarith [ht.1, (div4096_lt m1)], by linarith [ht.2,
            (div4096_lt m3)]⟩ z hz s hs
    · push Not at hw
      rw [List.map_cons, lineGo4.eq_2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a b c d h1 h2 => hw a b c d
          h1 h2)]
      obtain ⟨IHv, IHq⟩ := IH (some w) _
      refine ⟨List.Forall₂.cons (hval _ _ _) IHv, fun p' hp' x => ?_⟩
      cases hp'
      rcases ws with _ | ⟨w1, _ | ⟨w2, ws''⟩⟩
      · simp [QuadP]
      · simp [QuadP]
      · exact absurd rfl (hw p' w1 w2 ws'' rfl)

/-- **Soundness of a line** `lineOut4`. -/
theorem lineOut4_sound (o : Offs) (nS : ℕ) (fils : List (ℤ × List (ℤ × ℤ × ℤ)))
    (hfv : FilsOK4 o nS fils) (F : Face4) (hF : Face4OK F) (mp m mn mn2 : ℤ) :
    let L := lineOut4 o nS (fils.map fun f => mkFil o f.1 f.2) F mp m mn mn2
    List.Forall₂ (LVal fils F m) F.wn L ∧ QuadP (LW fils F m) F.wn L ∧
      QuadP (LT fils F mp m mn mn2) F.wn L := by
  intro L
  have e : L = lineGo4 o nS (fils.map fun f => mkFil o f.1 f.2) F mp m mn mn2 (trigOf4 m) none F.wn
      (F.wn.map fun wn => helCoef (faceRZ4 F wn).1 (faceRZ4 F wn).2) [] := rfl
  rw [e]
  refine ⟨(lineGo4_sound o nS fils hfv F hF mp m mn mn2 F.wn none []).1, ?_⟩
  rcases hws : F.wn with _ | ⟨w0, ws⟩
  · simp [QuadP]
  · rw [List.map_cons, lineGo4.eq_2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a b c d h _ => by cases h)]
    obtain ⟨-, hq⟩ := lineGo4_sound o nS fils hfv F hF mp m mn mn2 ws (some w0) _
    exact hq w0 rfl _

end PlasmaLean.Design.PolygonCoil
