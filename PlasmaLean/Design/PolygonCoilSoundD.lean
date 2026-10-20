/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilSoundC

/-!
# Soundness of the polygonal-coil checker, part D: lines, chunks, grids

* `FaceGood fils F a b`: on the part `φ ∈ [a, b]` of face `F`, `‖Bseg - hel‖ ≤ η·2⁻⁴⁰` and the
  distance to every segment is `≥ 1/5`;
* `line_sound`: two consecutive grid lines passing `cellsOK` give `FaceGood` between them;
* `checkChunk_sound`: a passing chunk gives `FaceGood` from its first to its last line;
* `grid_cover`: passing chunks `(g.drop (4 i)).take 5`, `i < n`, give `FaceGood` from the first
  to the last line of `g`.
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator
    PlasmaLean.Design.RationalStellarator.Coils
  PlasmaLean.Design.RationalStellarator.CoilsTF Set Real
open scoped RealInnerProductSpace

/-- The certified property at a face point. -/
@[expose] def Good (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (kind : ℕ) (φ w : ℝ) : Prop :=
  ‖Bseg fils (faceSigma kind φ w) - hel (faceSigma kind φ w)‖ ≤ (etaFp : ℝ) / ((two40 : ℕ) : ℝ) ∧
    ∀ s ∈ allSegs fils, ∀ t ∈ Icc (0 : ℝ) 1,
      1 / 5 ≤ ‖faceSigma kind φ w - seg (ptR s.2.1) (ptR s.2.2) t‖

/-- The certified property on the part `φ ∈ [a, b]` of a face. -/
@[expose] def FaceGood (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (F : Face) (a b : ℝ) : Prop :=
  ∀ φ ∈ Icc a b, ∀ w, inFace F.kind w → Good fils F.kind φ w

theorem faceGood_join {fils : List (ℤ × List (ℤ × ℤ × ℤ))} {F : Face} {a b c : ℝ}
    (h1 : FaceGood fils F a b) (h2 : FaceGood fils F b c) : FaceGood fils F a c := by
  intro φ hφ w hw
  rcases le_total φ b with h | h
  · exact h1 φ ⟨hφ.1, h⟩ w hw
  · exact h2 φ ⟨h, hφ.2⟩ w hw

/-- The `hel` coefficients at a grid value. -/
@[expose] def hcOf (F : Face) (wn : ℤ) : HC := helCoef (faceRZ F wn).1 (faceRZ F wn).2

theorem faceHC_eq (F : Face) : faceHC F = F.wn.map (hcOf F) := rfl

/-- One step of `lineGo` with a following grid value and a next line. -/
theorem lineGo_cons2 (o : Offs) (fs : List Fil) (F : Face) (m m1 : ℕ) (wn wn' : ℤ)
    (ws : List ℤ) (hcs : List HC) (gs : List (List ℕ)) :
    lineGo o fs F m (some m1) (trigOf m) (wn :: wn' :: ws) (hcOf F wn :: hcs) gs =
      ((cornerAt o fs F m wn (cellRC F m m1 wn wn' (cornerXYZ F m wn).1.2.2.2).1 gs).ok &&
          (cornerXYZ F m wn).2,
        (cornerAt o fs F m wn (cellRC F m m1 wn wn' (cornerXYZ F m wn).1.2.2.2).1 gs).e,
        Nat.add (cornerAt o fs F m wn (cellRC F m m1 wn wn' (cornerXYZ F m wn).1.2.2.2).1 gs).rem
          (cellRC F m m1 wn wn' (cornerXYZ F m wn).1.2.2.2).2) ::
      lineGo o fs F m (some m1) (trigOf m) (wn' :: ws) hcs
        (cornerAt o fs F m wn (cellRC F m m1 wn wn' (cornerXYZ F m wn).1.2.2.2).1 gs).gs := rfl

/-- One step of `lineGo` in general. -/
theorem lineGo_cons_any (o : Offs) (fs : List Fil) (F : Face) (m : ℕ) (mo : Option ℕ) (wn : ℤ)
    (ws : List ℤ) (hcs : List HC) (gs : List (List ℕ)) :
    ∃ (r : RC) (k : ℕ), lineGo o fs F m mo (trigOf m) (wn :: ws) (hcOf F wn :: hcs) gs =
      ((cornerAt o fs F m wn r gs).ok && (cornerXYZ F m wn).2, (cornerAt o fs F m wn r gs).e, k) ::
      lineGo o fs F m mo (trigOf m) ws hcs (cornerAt o fs F m wn r gs).gs := by
  rcases mo with _ | m1 <;> rcases ws with _ | ⟨w1, ws⟩ <;> exact ⟨_, _, rfl⟩

theorem incr_tail {a : ℤ} {l : List ℤ} (h : incr (a :: l) = true) : incr l = true := by
  rcases l with _ | ⟨b, l⟩
  · rfl
  · simp only [incr, Bool.and_eq_true] at h; exact h.2

theorem incr_head_lt : ∀ {a : ℤ} {l : List ℤ}, incr (a :: l) = true → ∀ x ∈ l, a < x
  | _, [], _, _, hx => by simp at hx
  | a, b :: l, h, x, hx => by
    simp only [incr, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact h.1.trans (incr_head_lt h.2 x hx)

theorem incr_le_last : ∀ {l : List ℤ}, incr l = true → ∀ x ∈ l, x ≤ l.getLastD 0
  | [], _, _, hx => by simp at hx
  | [a], _, x, hx => by simp at hx; simp [hx]
  | a :: b :: l, h, x, hx => by
    have ih := incr_le_last (incr_tail h)
    have e : (a :: b :: l).getLastD 0 = (b :: l).getLastD 0 := by simp
    rw [e]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ((incr_head_lt h) b (by simp)).le.trans (ih b (by simp))
    · exact ih x hx

/-- The first cell along a pair of lines, and the rest of the check. -/
theorem cells_head (o : Offs) (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (hfv : FilsValid o fils)
    (F : Face) (hF : FaceOK F) {m m' : ℕ} (hm : m < m') (mo : Option ℕ)
    (ws : List ℤ) (wn wn' : ℤ) (gs gs' : List (List ℕ))
    (hin : ∀ x ∈ wn :: wn' :: ws, inFace F.kind ((x : ℝ) / F.wd))
    (hinc : incr (wn :: wn' :: ws) = true)
    (hc : cellsOK (lineGo o (fils.map fun f => mkFil o f.1 f.2) F m (some m') (trigOf m)
          (wn :: wn' :: ws) ((wn :: wn' :: ws).map (hcOf F)) gs)
        (lineGo o (fils.map fun f => mkFil o f.1 f.2) F m' mo (trigOf m')
          (wn :: wn' :: ws) ((wn :: wn' :: ws).map (hcOf F)) gs') = true) :
    (∀ φ ∈ Icc (phiM m) (phiM m'), ∀ w ∈ Icc ((wn : ℝ) / F.wd) ((wn' : ℝ) / F.wd),
      Good fils F.kind φ w) ∧
    ∃ gsA gsB, cellsOK (lineGo o (fils.map fun f => mkFil o f.1 f.2) F m (some m') (trigOf m)
          (wn' :: ws) ((wn' :: ws).map (hcOf F)) gsA)
        (lineGo o (fils.map fun f => mkFil o f.1 f.2) F m' mo (trigOf m')
          (wn' :: ws) ((wn' :: ws).map (hcOf F)) gsB) = true := by
  set fs := fils.map fun f => mkFil o f.1 f.2
  rw [List.map_cons, List.map_cons, lineGo_cons2] at hc
  set gsA := (cornerAt o fs F m wn (cellRC F m m' wn wn' (cornerXYZ F m wn).1.2.2.2).1 gs).gs
  obtain ⟨r1, k1, e1⟩ := lineGo_cons_any o fs F m (some m') wn' ws (ws.map (hcOf F)) gsA
  obtain ⟨r2, k2, e2⟩ := lineGo_cons_any o fs F m' mo wn (wn' :: ws) ((wn' :: ws).map (hcOf F)) gs'
  rw [List.map_cons] at e2
  rw [e2] at hc
  set gsB := (cornerAt o fs F m' wn r2 gs').gs
  obtain ⟨r3, k3, e3⟩ := lineGo_cons_any o fs F m' mo wn' ws (ws.map (hcOf F)) gsB
  rw [e1, e3] at hc
  simp only [cellsOK, Bool.and_eq_true, Nat.ble_eq] at hc
  obtain ⟨⟨⟨⟨⟨h00, hx00⟩, ⟨h01, hx01⟩⟩, ⟨⟨h10, hx10⟩, ⟨h11, hx11⟩⟩⟩, hη⟩, hrest⟩ := hc
  have hwn : wn < wn' := incr_head_lt hinc wn' (by simp)
  refine ⟨fun φ hφ w hw => cell_sound o fils hfv F hF hm hwn (hin wn (by simp))
    (hin wn' (by simp)) r2 r1 r3 gs _ _ _ hx00 hx10 hx01 hx11 h00 h10 h01 h11 hη φ hφ w hw,
    gsA, gsB, ?_⟩
  rw [List.map_cons, e1, e3]
  exact hrest

/-- **Cells along a pair of lines.** -/
theorem cells_go (o : Offs) (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (hfv : FilsValid o fils)
    (F : Face) (hF : FaceOK F) {m m' : ℕ} (hm : m < m') (mo : Option ℕ) (ws : List ℤ) :
    ∀ (wn wn' : ℤ) (gs gs' : List (List ℕ)),
      (∀ x ∈ wn :: wn' :: ws, inFace F.kind ((x : ℝ) / F.wd)) → incr (wn :: wn' :: ws) = true →
      cellsOK (lineGo o (fils.map fun f => mkFil o f.1 f.2) F m (some m') (trigOf m)
          (wn :: wn' :: ws) ((wn :: wn' :: ws).map (hcOf F)) gs)
        (lineGo o (fils.map fun f => mkFil o f.1 f.2) F m' mo (trigOf m')
          (wn :: wn' :: ws) ((wn :: wn' :: ws).map (hcOf F)) gs') = true →
      ∀ φ ∈ Icc (phiM m) (phiM m'),
        ∀ w ∈ Icc ((wn : ℝ) / F.wd) (((wn' :: ws).getLastD 0 : ℤ) / F.wd), Good fils F.kind φ w :=
            by
  induction ws with
  | nil =>
    intro wn wn' gs gs' hin hinc hc φ hφ w hw
    exact (cells_head o fils hfv F hF hm mo [] wn wn' gs gs' hin hinc hc).1 φ hφ w
      (by simpa using hw)
  | cons wn'' ws ih =>
    intro wn wn' gs gs' hin hinc hc φ hφ w hw
    obtain ⟨hcell, gsA, gsB, hrest⟩ := cells_head o fils hfv F hF hm mo _ wn wn' gs gs' hin hinc hc
    have ih' := ih wn' wn'' gsA gsB (fun x hx => hin x (List.mem_cons_of_mem _ hx))
      (incr_tail hinc) hrest
    have e : (wn' :: wn'' :: ws).getLastD 0 = (wn'' :: ws).getLastD 0 := by
      simp
    rw [e] at hw
    rcases le_total w ((wn' : ℝ) / F.wd) with h | h
    · exact hcell φ hφ w ⟨hw.1, h⟩
    · exact ih' φ hφ w ⟨h, hw.2⟩

/-- What `faceOK` guarantees about the `w`-grid. -/
theorem faceOK_spec {F : Face} (h : faceOK F = true) :
    ∃ wn wn' ws, F.wn = wn :: wn' :: ws ∧ incr (wn :: wn' :: ws) = true ∧
      ∀ w : ℝ, inFace F.kind w ↔ w ∈ Icc ((wn : ℝ) / F.wd) (((wn' :: ws).getLastD 0 : ℤ) / F.wd) :=
          by
  unfold faceOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hwd, hinc⟩, hm⟩, -⟩, -⟩, -⟩ := h
  have hwd' : (0 : ℝ) < F.wd := by exact_mod_cast hwd
  rcases hF : F.wn with _ | ⟨lo, _ | ⟨wn', ws⟩⟩
  · rw [hF] at hm; simp at hm
  · rw [hF] at hm
    simp only [List.head?_cons, List.getLast?_singleton] at hm
    split_ifs at hm <;> simp only [Bool.and_eq_true, decide_eq_true_eq] at hm <;> omega
  · refine ⟨lo, wn', ws, rfl, hF ▸ hinc, ?_⟩
    rw [hF] at hm
    have hl : (lo :: wn' :: ws).getLast? = some ((wn' :: ws).getLastD 0) := by
      rw [List.getLast?_cons, List.getLastD_eq_getLast?]
      cases h : (wn' :: ws).getLast? with
      | none => simp at h
      | some x => rfl
    simp only [List.head?_cons, hl] at hm
    set hi := (wn' :: ws).getLastD 0
    intro w
    unfold inFace
    split_ifs at hm ⊢ with hk
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
      obtain ⟨h1, h2⟩ := hm
      have e1 : (lo : ℝ) / F.wd = -aF := by
        rw [div_eq_iff hwd'.ne', aF]
        have : (lo : ℝ) * 32761 = -3420 * F.wd := by exact_mod_cast h1
        linarith
      have e2 : (hi : ℝ) / F.wd = aF := by
        rw [div_eq_iff hwd'.ne', aF]
        have : 3420 * (F.wd : ℝ) = hi * 32761 := by exact_mod_cast h2
        linarith
      rw [e1, e2, abs_le]; rfl
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
      obtain ⟨h1, h2⟩ := hm
      have e1 : (lo : ℝ) / F.wd = 161 / 181 := by
        rw [div_eq_iff hwd'.ne']
        have : (lo : ℝ) * 181 = 161 * F.wd := by exact_mod_cast h1
        linarith
      have e2 : (hi : ℝ) / F.wd = 199 / 181 := by
        rw [div_eq_iff hwd'.ne']
        have : 199 * (F.wd : ℝ) = hi * 181 := by exact_mod_cast h2
        linarith
      rw [e1, e2]; rfl

/-- **Soundness of a pair of lines.** -/
theorem line_sound (o : Offs) (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (hfv : FilsValid o fils)
    (F : Face) (hF : FaceOK F) (hok : faceOK F = true) {m m' : ℕ} (hm : m < m') (mo : Option ℕ)
    (hc : cellsOK (lineOut o (fils.map fun f => mkFil o f.1 f.2) F (faceHC F) m (some m'))
      (lineOut o (fils.map fun f => mkFil o f.1 f.2) F (faceHC F) m' mo) = true) :
    FaceGood fils F (phiM m) (phiM m') := by
  obtain ⟨wn, wn', ws, hwn, hinc, hiff⟩ := faceOK_spec hok
  have hin : ∀ x ∈ wn :: wn' :: ws, inFace F.kind ((x : ℝ) / F.wd) := by
    intro x hx
    rw [hiff]
    have hwd' : (0 : ℝ) < F.wd := by exact_mod_cast hF.1.2
    constructor
    · apply div_le_div_of_nonneg_right _ hwd'.le
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_rfl
      · exact_mod_cast (incr_head_lt hinc x hx).le
    · apply div_le_div_of_nonneg_right _ hwd'.le
      have := incr_le_last hinc x hx
      have e : (wn :: wn' :: ws).getLastD 0 = (wn' :: ws).getLastD 0 := by simp
      rw [e] at this; exact_mod_cast this
  unfold lineOut at hc
  rw [faceHC_eq, hwn] at hc
  intro φ hφ w hw
  exact cells_go o fils hfv F hF hm mo ws wn wn' [] [] hin hinc hc φ hφ w ((hiff w).mp hw)

/-- **Soundness of `checkLines`.** -/
theorem checkLines_sound (o : Offs) (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (hfv : FilsValid o fils)
    (F : Face) (hF : FaceOK F) (hok : faceOK F = true) (rest : List ℕ) :
    ∀ m0 m : ℕ, checkLines o (fils.map fun f => mkFil o f.1 f.2) F (faceHC F)
      (lineOut o (fils.map fun f => mkFil o f.1 f.2) F (faceHC F) m0 (some m)) m0 (m :: rest) =
        true → FaceGood fils F (phiM m0) (phiM ((m :: rest).getLastD 0)) := by
  induction rest with
  | nil =>
    intro m0 m h
    simp only [checkLines, Bool.and_eq_true, Nat.blt_eq] at h
    simpa using line_sound o fils hfv F hF hok h.1 none h.2
  | cons m' rest ih =>
    intro m0 m h
    simp only [checkLines, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨hlt, hc⟩, hr⟩ := h
    have e : (m :: m' :: rest).getLastD 0 = (m' :: rest).getLastD 0 := by simp
    rw [e]
    exact faceGood_join (line_sound o fils hfv F hF hok hlt (some m') hc) (ih m m' hr)

/-- **Soundness of a chunk.** -/
theorem checkChunk_sound (o : Offs) (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (hfv : FilsValid o fils)
    (F : Face) (hF : FaceOK F) (l : List ℕ)
    (h : checkChunk o (fils.map fun f => mkFil o f.1 f.2) F l = true) :
    FaceGood fils F (phiM (l.headD 0)) (phiM (l.getLastD 0)) := by
  rcases l with _ | ⟨m, _ | ⟨m', rest⟩⟩
  · simp [checkChunk] at h
  · simp [checkChunk] at h
  · simp only [checkChunk, Bool.and_eq_true] at h
    have e : (m :: m' :: rest).getLastD 0 = (m' :: rest).getLastD 0 := by simp
    rw [e]
    exact checkLines_sound o fils hfv F hF h.1 rest m m' h.2

/-- **Grid cover.** Passing chunks `(g.drop (4 i)).take 5` for `i < n`, with `2 ≤ |g| ≤ 4n + 1`,
give `FaceGood` from the first to the last grid line. -/
theorem grid_cover (o : Offs) (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (hfv : FilsValid o fils)
    (F : Face) (hF : FaceOK F) (n : ℕ) :
    ∀ g : List ℕ, 2 ≤ g.length → g.length ≤ 4 * n + 1 →
      (∀ i < n, checkChunk o (fils.map fun f => mkFil o f.1 f.2) F ((g.drop (4 * i)).take 5) =
        true) → FaceGood fils F (phiM (g.headD 0)) (phiM (g.getLastD 0)) := by
  induction n with
  | zero => intro g h1 h2; omega
  | succ n ih =>
    intro g h1 h2 hch
    have h0 := hch 0 (by omega)
    simp only [Nat.mul_zero, List.drop_zero] at h0
    by_cases hl : g.length ≤ 5
    · rw [List.take_of_length_le hl] at h0
      exact checkChunk_sound o fils hfv F hF g h0
    · rcases g with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, r⟩⟩⟩⟩⟩⟩ <;>
        simp only [List.length_cons, List.length_nil] at hl h1 h2 <;> try omega
      have hA := checkChunk_sound o fils hfv F hF _ h0
      have hB := ih (e :: f :: r) (by simp) (by simp only [List.length_cons]; omega)
        (fun i hi => by
          have := hch (i + 1) (by omega)
          rwa [show 4 * (i + 1) = 4 + 4 * i by ring, ← List.drop_drop] at this)
      have e1 : (a :: b :: c :: d :: e :: f :: r).getLastD 0 = (e :: f :: r).getLastD 0 := by
        simp
      rw [e1]
      exact faceGood_join (by simpa using hA) (by simpa using hB)

end PlasmaLean.Design.PolygonCoil
