/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscTrig
public import PlasmaLean.Design.NearAxisQATrappedTimeCells

/-!
# Cell certificate for the oscillatory kick integrals of trapped alphas (exact QA)

Companion to `Design/NearAxisQATrappedOscKick` and `notes/theory/trapped-alpha-status.md` §6.
Model only: the exactly quasi-axisymmetric member `exactQA` of the reactor near-axis family,
vacuum Boozer guiding-centre equations.

**What is enclosed.** Along an exact-QA bounce of the start window (constants of motion
`ψ₀, B_t = E/μ`), the normalised kick integrals

`Ĉ = ∫₀ᴾ A w cos 2(φ − φ₀) dt`, `Ŝ = ∫₀ᴾ A w sin 2(φ − φ₀) dt`

(`A = μ/q + qρ²B/m`, `w = 2ψ/B₀`; the reference kick amplitude is `g = −2 b₁ q A w`), the
precession integral `ι₀ Δ = ∫₀ᴾ Ω dt` and the bounce time `P`.

**Rates.** Every rate along the orbit is `A` times an explicit function of the leg coordinate
`x = |ψ − ψ₀|` and `c = cos θ` (`OrbitRel`): `ẋ = A |∂_θB|` (`denR`), `Ω = A (−∂_ψB)` (`numR`),
`|φ̇| = A K/ι₀` and `θ̇ = −A (−∂_ψB + K)` (inner leg), `θ̇ = A (K − (−∂_ψB))` (outer leg), with
`K = 2λ B_t x B³/(2B_t − B)` (`KR`). So `A` cancels from every ratio:

* flank cells (`x`-cells of width `1/40`, `|θ| ≥ 3/5`): `Ω/ẋ`, `|φ̇|/ẋ`, `A w/ẋ = w/|∂_θB|`, and
  `dt/dx` (`flankCellO`);
* bottom cells (`θ`-cells of width `1/40`, `|θ| ≤ 3/5`): `Ω/|θ̇|`, `A w/|θ̇|`, `dt/dθ`
  (`bottomCellO`); the leg coordinate of a bottom cell is enclosed by scanning `x`-subcells of
  width `1/320` whose cosine enclosure meets the cosine range of the `θ`-cell (`hullX`).

**Phase.** The phase `Φ = 2(φ − φ₀)` is tracked without accumulating the large streaming swings:
on the flanks it is accumulated from the nearer turning point (`accI` of `|φ̇|/ẋ`, all cells
between the point and the tip being full), and on the bottom it is
`Φ = (2/ι₀)(θ − θ₀ + I(t))`, with `θ` known to the cell width, `θ₀` enclosed once per box from
the tip cosine (oracle bounds checked with `cosSinC`), and the small precession integral
`I(t) = ∫₀ᵗ Ω` accumulated cell by cell. At the lower tip `θ = −θ₀`, at the end of the bounce
`θ = θ₀`.

**Checker.** The box check is split into the two legs to bound the kernel's memory:
`legAOk P T Θ0 Cin Sin J1 Tin` (inner leg: all cells valid, `θ₀` bounds checked with `cosSinC`,
and the leg's enclosures of `Ĉ`, `Ŝ`, `I(z₁)` and of its duration equal the stated literals),
`legBOk P T Θ0 J1 Cout Sout J2 Tout` (outer leg, from `J1 ∋ I(z₁)`), and the cheap
`finalOk … Kn 1 Pmin Pmax DlS DhS` on the literals (`√(Ĉ² + Ŝ²) ≤ Kn sin Δ`, bounce time in
`[Pmin, Pmax]` μs, `ι₀ Δ ∈ [DlS, DhS]`). `OscLeaf` packages the three checks on an index box and
`OscCover` is an adaptive binary subdivision of the window into leaves (`OscCover.sound`).
The real-number meaning of the per-cell data is `flankCellO_sound`, `flankCellO_full`,
`bottomCellO_sound`, `hullX_sound`, `mem_CTL`, `theta0_sound`; the assembly along the orbit is in
`Design/NearAxisQATrappedOscLegs` and `Design/NearAxisQATrappedOscKick`.

Sanity fixtures: `fixture_flankO_alive` (a valid live flank cell), `fixture_flankO_dead` (a dead
flank cell has zero densities), `fixture_bottomO_ok` (a valid bottom cell), and the rejected
fixture `fixture_theta0_rejected` (a wrong thin guess for `θ₀` fails `theta0Ok`).
-/
public section
noncomputable section
namespace PlasmaLean.Design.NearAxisQATrappedOsc
open PlasmaLean.Certificates.ValidatedQuadrature PlasmaLean.Design.NearAxisQATrappedCells
  FIvX Real Set

/-! ## The streaming factor `K` -/

/-- `K = 2λ B_t x B³/(2B_t − B)`, `B = BsR x B_t`: along the orbit `A K = q (ι₀/G)² x B²/m`, so
`|φ̇| = A K/ι₀` and the streaming part of `θ̇` is `∓ A K`. -/
@[expose] def KR (x Bt : ℝ) : ℝ :=
  2 * lam * (Bt * x) * (BsR x Bt * BsR x Bt ^ 2) * (2 * Bt - BsR x Bt)⁻¹

/-- Interval version of `KR`. -/
@[expose] def KI (X T : FIv) : FIv :=
  dv ((((C 2 1).mul lamI).mul (T.mul X)).mul ((BsI X T).mul (BsI X T).sq))
    (((C 2 1).mul T).sub (BsI X T))

/-- Soundness of `KI`. -/
theorem mem_KI {X T : FIv} {x b : ℝ} (hX : X.Mem x) (hT : T.Mem b) : (KI X T).Mem (KR x b) := by
  have h1 := mem_BsI hX hT
  have hl := mem_lamI
  unfold KI KR
  fiv_mem

/-! ## Sums and accumulations -/

/-- `Σ_{i < n} f i` by recursion (kernel-friendly). -/
@[expose] def sumF (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumF f n + f n

/-- `sumF` is the finite sum. -/
theorem sumF_eq (f : ℕ → ℤ) (n : ℕ) : sumF f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumF, ih, Finset.sum_range_succ]

/-- All of `D 0, …, D (n−1)` are valid. -/
@[expose] def okAll (D : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => okAll D n && D n

/-- `okAll` gives validity of each entry. -/
theorem okAll_spec {D : ℕ → Bool} {n : ℕ} (h : okAll D n = true) : ∀ i < n, D i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    simp only [okAll, Bool.and_eq_true] at h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
    · exact ih h.1 i h'
    · subst h'; exact h.2

/-! ## Cells -/

/-- Per-cell data: four density enclosures, validity, and the dead / full flags. -/
structure OCell where
  /-- Precession density (`Ω` per unit of the cell coordinate). -/
  om : FIv
  /-- Toroidal-angle density (`|φ̇|` per unit of the cell coordinate). -/
  ph : FIv
  /-- Amplitude density (`A w` per unit of the cell coordinate). -/
  g : FIv
  /-- Time density in microseconds per unit of the cell coordinate. -/
  tt : FIv
  /-- Validity. -/
  ok : Bool
  /-- No orbit point of the piece lies in the cell. -/
  dead : Bool
  /-- Every orbit point with coordinate in the cell lies strictly inside the piece. -/
  full : Bool

/-- The zero enclosure. -/
@[expose] def zeroI : FIv := ⟨0, 0, true⟩

/-- **Flank cell** on the `x`-cell `X` (`|θ| ≥ 3/5`): densities `Ω/ẋ = (−∂_ψB)/|∂_θB|`,
`|φ̇|/ẋ = K/(ι₀ |∂_θB|)`, `A w/ẋ = w/|∂_θB|`, `10⁶ dt/dx = 1/(A_μ |∂_θB|)`. A dead cell
(cosine enclosure above `cos(3/5)`) has zero densities. `full` records that the cosine enclosure
lies below `cos(3/5)`. -/
@[expose] def flankCellO (inner : Bool) (X P T : FIv) : OCell :=
  if (cI inner X P T).ok && decide (cdHi < (cI inner X P T).lo) then
    ⟨zeroI, zeroI, zeroI, zeroI, true, true, false⟩
  else
    ⟨dv (numI inner X P (flankC inner X P T)) (flankDen inner X P T),
      dv (KI X T) ((C 211 500).mul (flankDen inner X P T)),
      dv (wI inner X P) (flankDen inner X P T),
      dv (C 1 1) ((AmI X T).mul (flankDen inner X P T)),
      (dv (numI inner X P (flankC inner X P T)) (flankDen inner X P T)).ok &&
        (dv (KI X T) ((C 211 500).mul (flankDen inner X P T))).ok &&
        (dv (wI inner X P) (flankDen inner X P T)).ok &&
        (dv (C 1 1) ((AmI X T).mul (flankDen inner X P T))).ok &&
        decide (0 ≤ (dv (numI inner X P (flankC inner X P T)) (flankDen inner X P T)).lo) &&
        decide (0 ≤ (dv (KI X T) ((C 211 500).mul (flankDen inner X P T))).lo),
      false,
      (cI inner X P T).ok && decide ((cI inner X P T).hi < cdLo)⟩

/-- The `θ`-cell index map: bottom cell `j < 48` has `|θ| ∈ [k/40, (k+1)/40]` with
`k = 23 − j` (`j ≤ 23`) or `k = j − 24` (`j ≥ 24`). -/
@[expose] def kOf (j : ℕ) : ℕ := if j ≤ 23 then 23 - j else j - 24

/-- Enclosure of `cos θ` for `|θ| ∈ [k/40, (k+1)/40]`. -/
@[expose] def CTI (k : ℕ) : FIv :=
  ⟨(cosSinC (C ((k : ℤ) + 1) 40)).1.lo, (cosSinC (C (k : ℤ) 40)).1.hi,
    (cosSinC (C ((k : ℤ) + 1) 40)).1.ok && (cosSinC (C (k : ℤ) 40)).1.ok⟩

/-- Precomputed scaled endpoints of `CTI k`, `k < 24` (checked by `CTI_tab`). -/
@[expose] def CTtab : List (ℤ × ℤ) :=
  [(4293625184, 4294967296), (4289599700, 4293625191), (4282893356, 4289599711),
    (4273510342, 4282893367), (4261456526, 4273510357), (4246739432, 4261456538),
    (4229368270, 4246739451), (4209353886, 4229368291), (4186708796, 4209353913),
    (4161447152, 4186708821), (4133584732, 4161447176), (4103138962, 4133584767),
    (4070128858, 4103138999), (4034575056, 4070128905), (3996499784, 4034575115),
    (3955926820, 3996499844), (3912881540, 3955926893), (3867390830, 3912881625),
    (3819483120, 3867390935), (3769188372, 3819483261), (3716537982, 3769188540),
    (3661564886, 3716538203), (3604303432, 3661565171), (3544789406, 3604303785)]

/-- Table version of `CTI` (valid for `k < 24`). -/
@[expose] def CTL (k : ℕ) : FIv :=
  ⟨(CTtab.getD k (0, 0)).1, (CTtab.getD k (0, 0)).2, decide (k < 24)⟩

set_option maxRecDepth 100000 in
/-- The table agrees with the computed enclosures. -/
theorem CTI_tab : okAll (fun k => decide ((CTL k).lo = (CTI k).lo) &&
    decide ((CTL k).hi = (CTI k).hi) && (CTI k).ok) 24 = true := by decide +kernel

/-- The bottom cosine `c ∈ CTL k ∩ [cos(3/5), 1]`. -/
@[expose] def bcI (k : ℕ) : FIv := meetHi (meetLo (CTL k) cdLo) fxScale

/-- The `x`-cells that may contain a bottom point (`|θ| ≤ 3/5`), with their cosine
enclosures: cells whose cosine enclosure lies below `cos(3/5)` are skipped. -/
@[expose] def subList (inner : Bool) (P T : FIv) : List (FIv × FIv) :=
  (List.range 100).flatMap fun i =>
    if (cI inner (cellX i) P T).ok && decide ((cI inner (cellX i) P T).hi < cdLo) then []
    else [(cellX i, cI inner (cellX i) P T)]

/-- Hull of the cells whose cosine enclosure meets `CT`: `(found, lo, hi)`. -/
@[expose] def hullScan (CT : FIv) : List (FIv × FIv) → Bool × ℤ × ℤ
  | [] => (false, 0, 0)
  | p :: rest =>
    let r := hullScan CT rest
    if p.2.ok && CT.ok && (decide (p.2.hi < CT.lo) || decide (CT.hi < p.2.lo)) then r
    else (p.1.ok, if r.1 then min p.1.lo r.2.1 else p.1.lo,
      if r.1 then max p.1.hi r.2.2 else p.1.hi)

/-- The enclosure of the leg coordinate on the bottom `θ`-cell `k`. -/
@[expose] def hullX (inner : Bool) (P T : FIv) (k : ℕ) : FIv :=
  ⟨(hullScan (CTL k) (subList inner P T)).2.1, (hullScan (CTL k) (subList inner P T)).2.2,
    (hullScan (CTL k) (subList inner P T)).1⟩

/-- `|θ̇|/A` at the bottom: `K + (−∂_ψB)` (inner leg) or `K − (−∂_ψB)` (outer leg). -/
@[expose] def bDenI (inner : Bool) (X P T c : FIv) : FIv :=
  if inner then (KI X T).add (numI inner X P c) else (KI X T).sub (numI inner X P c)

/-- **Bottom cell** for `|θ| ∈ [k/40, (k+1)/40]`: densities `Ω/|θ̇|`, `A w/|θ̇|` and
`10⁶ dt/dθ` over the leg-coordinate hull `hullX` (the `ph` field is unused). -/
@[expose] def bottomCellO (inner : Bool) (P T : FIv) (k : ℕ) : OCell :=
  ⟨dv (numI inner (hullX inner P T k) P (bcI k)) (bDenI inner (hullX inner P T k) P T (bcI k)),
    zeroI,
    dv (wI inner (hullX inner P T k) P) (bDenI inner (hullX inner P T k) P T (bcI k)),
    dv (C 1 1) ((AmI (hullX inner P T k) T).mul (bDenI inner (hullX inner P T k) P T (bcI k))),
    (dv (numI inner (hullX inner P T k) P (bcI k))
        (bDenI inner (hullX inner P T k) P T (bcI k))).ok &&
      (dv (wI inner (hullX inner P T k) P) (bDenI inner (hullX inner P T k) P T (bcI k))).ok &&
      (dv (C 1 1) ((AmI (hullX inner P T k) T).mul
        (bDenI inner (hullX inner P T k) P T (bcI k)))).ok &&
      decide (0 ≤ (dv (numI inner (hullX inner P T k) P (bcI k))
        (bDenI inner (hullX inner P T k) P T (bcI k))).lo),
    false, true⟩

/-- **Partial accumulation** over cells `0, …, i` (cells `< i` full, cell `i` partial), times
the cell width `1/40`. -/
@[expose] def accI (D : ℕ → FIv) (i : ℕ) : FIv :=
  (⟨sumF (fun j => (D j).lo) i + min (D i).lo 0, sumF (fun j => (D j).hi) i + max (D i).hi 0,
    true⟩ : FIv).mul (C 1 40)

/-- **Total over the first `n` cells** with the full-cell flags `F` (unflagged cells may be
partial), times the cell width `1/40`. -/
@[expose] def totI (D : ℕ → FIv) (F : ℕ → Bool) (n : ℕ) : FIv :=
  (⟨sumF (fun i => if F i then (D i).lo else min (D i).lo 0) n,
    sumF (fun i => if F i then (D i).hi else max (D i).hi 0) n, true⟩ : FIv).mul (C 1 40)

/-! ## Legs -/

/-- Flank cell `i` of a leg. -/
@[expose] def fcell (inner : Bool) (P T : FIv) (i : ℕ) : OCell := flankCellO inner (cellX i) P T

/-- Bottom cell `j` of a leg. -/
@[expose] def bcell (inner : Bool) (P T : FIv) (j : ℕ) : OCell := bottomCellO inner P T (kOf j)

/-- Prefix flags: cells `0, …, i` are all full. -/
@[expose] def fullPre (inner : Bool) (P T : FIv) : ℕ → Bool
  | 0 => (fcell inner P T 0).full
  | i + 1 => fullPre inner P T i && (fcell inner P T (i + 1)).full

/-- Flank phase in cell `i` from an anchor `A`: `A + 2 acc` (`σ = true`) or `A − 2 acc`. -/
@[expose] def phF (A : FIv) (σ : Bool) (inner : Bool) (P T : FIv) (i : ℕ) : FIv :=
  if σ then A.add ((C 2 1).mul (accI (fun j => (fcell inner P T j).ph) i))
  else A.sub ((C 2 1).mul (accI (fun j => (fcell inner P T j).ph) i))

/-- The bottom `θ`-cell `j`: `θ ∈ [(23 − j)/40, (24 − j)/40]` (inner leg, `θ` decreasing from
`3/5`) or `[(j − 24)/40, (j − 23)/40]` (outer leg, `θ` increasing from `−3/5`). -/
@[expose] def thI (inner : Bool) (j : ℕ) : FIv :=
  if inner then hull (23 - (j : ℤ)) 40 (24 - (j : ℤ)) 40
  else hull ((j : ℤ) - 24) 40 ((j : ℤ) - 23) 40

/-- Bottom phase in cell `j`: `(2/ι₀)(θ − θ₀ + I_s + acc)`. -/
@[expose] def phB (Θ0 Is : FIv) (inner : Bool) (P T : FIv) (j : ℕ) : FIv :=
  (C 1000 211).mul (((thI inner j).sub Θ0).add (Is.add (accI (fun k => (bcell inner P T k).om) j)))

/-- Densities of the flank contributions in cell `i`: `(A w/ẋ) cos Φ`, `(A w/ẋ) sin Φ` (zero on
dead cells, where no trigonometric evaluation is made). -/
@[expose] def flankD (A : FIv) (σ : Bool) (inner : Bool) (P T : FIv) (i : ℕ) : FIv × FIv :=
  if (fcell inner P T i).dead then (zeroI, zeroI) else
    ((fcell inner P T i).g.mul (cosSinC (phF A σ inner P T i)).1,
      (fcell inner P T i).g.mul (cosSinC (phF A σ inner P T i)).2)

/-- Flank contribution to `(Ĉ, Ŝ)` with anchor `A` and direction `σ`. -/
@[expose] def flankCS (A : FIv) (σ : Bool) (inner : Bool) (P T : FIv) : FIv × FIv :=
  (totI (fun i => (flankD A σ inner P T i).1) (fullPre inner P T) 100,
    totI (fun i => (flankD A σ inner P T i).2) (fullPre inner P T) 100)

/-- Validity of the flank contributions. -/
@[expose] def flankCSok (A : FIv) (σ : Bool) (inner : Bool) (P T : FIv) : Bool :=
  okAll (fun i => (flankD A σ inner P T i).1.ok && (flankD A σ inner P T i).2.ok) 100

/-- Bottom contribution to `(Ĉ, Ŝ)`. -/
@[expose] def botCS (Θ0 Is : FIv) (inner : Bool) (P T : FIv) : FIv × FIv :=
  (totI (fun j => (bcell inner P T j).g.mul (cosSinC (phB Θ0 Is inner P T j)).1) (fun _ => true) 48,
    totI (fun j => (bcell inner P T j).g.mul (cosSinC (phB Θ0 Is inner P T j)).2)
      (fun _ => true) 48)

/-- Validity of the bottom contributions. -/
@[expose] def botCSok (Θ0 Is : FIv) (inner : Bool) (P T : FIv) : Bool :=
  okAll (fun j => ((bcell inner P T j).g.mul (cosSinC (phB Θ0 Is inner P T j)).1).ok &&
    ((bcell inner P T j).g.mul (cosSinC (phB Θ0 Is inner P T j)).2).ok) 48

/-- Precession over one flank piece. -/
@[expose] def flankI (inner : Bool) (P T : FIv) : FIv :=
  totI (fun i => (fcell inner P T i).om) (fullPre inner P T) 100

/-- Precession over one bottom crossing. -/
@[expose] def botI (inner : Bool) (P T : FIv) : FIv :=
  totI (fun j => (bcell inner P T j).om) (fun _ => true) 48

/-- Time (microseconds) over one flank piece. -/
@[expose] def flankTm (inner : Bool) (P T : FIv) : FIv :=
  totI (fun i => (fcell inner P T i).tt) (fullPre inner P T) 100

/-- Time (microseconds) over one bottom crossing. -/
@[expose] def botTm (inner : Bool) (P T : FIv) : FIv :=
  totI (fun j => (bcell inner P T j).tt) (fun _ => true) 48

/-- Validity of all cells of a leg. -/
@[expose] def legOk (inner : Bool) (P T : FIv) : Bool :=
  okAll (fun i => (fcell inner P T i).ok) 100 && okAll (fun j => (bcell inner P T j).ok) 48

/-! ## The tip angle -/

/-- The tip cosine `c₀ = cR(x = 0)` (both legs). -/
@[expose] def c0I (P T : FIv) : FIv := cI true (C 0 1) P T

/-- Check of the oracle bounds `Θ0 ∋ θ₀`: `0 ≤ lo ≤ hi ≤ 3`, `cos hi ≤ c₀ ≤ cos lo`. -/
@[expose] def theta0Ok (P T Θ0 : FIv) : Bool :=
  Θ0.ok && decide (0 ≤ Θ0.lo) && decide (Θ0.lo ≤ Θ0.hi) && decide (Θ0.hi ≤ 3 * fxScale) &&
    (c0I P T).ok &&
    (cosSinC ⟨Θ0.hi, Θ0.hi, true⟩).1.ok && (cosSinC ⟨Θ0.lo, Θ0.lo, true⟩).1.ok &&
    decide ((cosSinC ⟨Θ0.hi, Θ0.hi, true⟩).1.hi ≤ (c0I P T).lo) &&
    decide ((c0I P T).hi ≤ (cosSinC ⟨Θ0.lo, Θ0.lo, true⟩).1.lo)

/-! ## The box, split into the two legs -/

/-- Exact equality test of two enclosures (all three fields). -/
@[expose] def eqI (I J : FIv) : Bool :=
  decide (I.lo = J.lo) && decide (I.hi = J.hi) && (I.ok == J.ok)

/-- `eqI` decides equality. -/
theorem eq_of_eqI {I J : FIv} (h : eqI I J = true) : I = J := by
  simp only [eqI, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  cases I; cases J; simp_all

/-- Precession integral `I(s₁)` at the end of the inner upper flank. -/
@[expose] def Is1 (P T : FIv) : FIv := flankI true P T

/-- Precession integral `I(z₁)` at the lower tip (end of the inner leg). -/
@[expose] def Iz1 (P T : FIv) : FIv := ((Is1 P T).add (botI true P T)).add (flankI true P T)

/-- Precession integral `I(s₁')` at the end of the outer lower flank, from `J1 ∋ I(z₁)`. -/
@[expose] def Is3 (J1 P T : FIv) : FIv := J1.add (flankI false P T)

/-- Precession integral `I(z₂) = ι₀ Δ` at the end of the bounce, from `J1 ∋ I(z₁)`. -/
@[expose] def Iz2 (J1 P T : FIv) : FIv := ((Is3 J1 P T).add (botI false P T)).add (flankI false P T)

/-- Phase at the lower tip: `(2/ι₀)(−2θ₀ + I(z₁))`, from `J1 ∋ I(z₁)`. -/
@[expose] def phZ1 (Θ0 J1 : FIv) : FIv := (C 1000 211).mul ((Θ0.mul (C (-2) 1)).add J1)

/-- Phase at the end of the bounce: `(2/ι₀) I(z₂) = 2Δ`, from `J2 ∋ I(z₂)`. -/
@[expose] def phZ2 (J2 : FIv) : FIv := (C 1000 211).mul J2

/-- The inner-leg contribution to `(Ĉ, Ŝ)`: upper flank, bottom, lower flank. -/
@[expose] def legACS (P T Θ0 : FIv) : FIv × FIv :=
  (((flankCS zeroI false true P T).1.add (botCS Θ0 (Is1 P T) true P T).1).add
      (flankCS (phZ1 Θ0 (Iz1 P T)) true true P T).1,
    ((flankCS zeroI false true P T).2.add (botCS Θ0 (Is1 P T) true P T).2).add
      (flankCS (phZ1 Θ0 (Iz1 P T)) true true P T).2)

/-- The outer-leg contribution to `(Ĉ, Ŝ)`, from `J1 ∋ I(z₁)` and `J2 ∋ I(z₂)`. -/
@[expose] def legBCS (P T Θ0 J1 J2 : FIv) : FIv × FIv :=
  (((flankCS (phZ1 Θ0 J1) true false P T).1.add (botCS Θ0 (Is3 J1 P T) false P T).1).add
      (flankCS (phZ2 J2) false false P T).1,
    ((flankCS (phZ1 Θ0 J1) true false P T).2.add (botCS Θ0 (Is3 J1 P T) false P T).2).add
      (flankCS (phZ2 J2) false false P T).2)

/-- Time (microseconds) of one leg: two flanks and one bottom crossing. -/
@[expose] def legTm (inner : Bool) (P T : FIv) : FIv :=
  ((flankTm inner P T).mul (C 2 1)).add (botTm inner P T)

/-- **Inner-leg check**: all cells valid, `θ₀` bounds checked, all contributions valid, and the
results equal the stated enclosures `Cin, Sin` (of the leg's `Ĉ, Ŝ` parts), `J1` (of `I(z₁)`)
and `Tin` (of the leg's time). -/
@[expose] def legAOk (P T Θ0 Cin Sin J1 Tin : FIv) : Bool :=
  legOk true P T && theta0Ok P T Θ0 && flankCSok zeroI false true P T &&
    botCSok Θ0 (Is1 P T) true P T && flankCSok (phZ1 Θ0 (Iz1 P T)) true true P T &&
    eqI (legACS P T Θ0).1 Cin && eqI (legACS P T Θ0).2 Sin && eqI (Iz1 P T) J1 &&
    eqI (legTm true P T) Tin

/-- **Outer-leg check** (given `J1 ∋ I(z₁)`): all cells valid, all contributions valid, and the
results equal the stated enclosures `Cout, Sout`, `J2` (of `I(z₂)`) and `Tout`. -/
@[expose] def legBOk (P T Θ0 J1 Cout Sout J2 Tout : FIv) : Bool :=
  legOk false P T && flankCSok (phZ1 Θ0 J1) true false P T &&
    botCSok Θ0 (Is3 J1 P T) false P T && flankCSok (phZ2 J2) false false P T &&
    eqI (Iz2 J1 P T) J2 && eqI (legBCS P T Θ0 J1 J2).1 Cout &&
    eqI (legBCS P T Θ0 J1 J2).2 Sout && eqI (legTm false P T) Tout

/-- `sin Δ` enclosure from `J2 ∋ ι₀ Δ`. -/
@[expose] def sinDI (J2 : FIv) : FIv := (cosSinC (J2.mul (C 500 211))).2

/-- **Final check on the leg enclosures** with amplitude target `Kn/Kd`, period range
`[Pmin, Pmax]` (microseconds) and precession range `ι₀ Δ ∈ [DlS, DhS]` (scaled): all enclosures
valid, `Kn ≥ 0`, and with `C = Cin + Cout`, `S = Sin + Sout`, `sin Δ > 0` on `J2` and
`Kd² (max|C|² + max|S|²) ≤ Kn² (min sin Δ)²`, the bounce time `Tin + Tout` in `[Pmin, Pmax]`,
and `J2 ⊆ [DlS, DhS]`. -/
@[expose] def finalOk (Cin Sin Cout Sout J2 Tin Tout : FIv) (Kn Kd Pmin Pmax DlS DhS : ℤ) :
    Bool :=
  Cin.ok && Sin.ok && Cout.ok && Sout.ok && Tin.ok && Tout.ok && J2.ok && decide (0 ≤ Kn) &&
    (sinDI J2).ok && decide (0 < (sinDI J2).lo) &&
    decide (Kd * Kd * (max (-(Cin.add Cout).lo) (Cin.add Cout).hi *
        max (-(Cin.add Cout).lo) (Cin.add Cout).hi +
      max (-(Sin.add Sout).lo) (Sin.add Sout).hi * max (-(Sin.add Sout).lo) (Sin.add Sout).hi) ≤
      Kn * Kn * ((sinDI J2).lo * (sinDI J2).lo)) &&
    decide (Pmin * fxScale ≤ (Tin.add Tout).lo) && decide ((Tin.add Tout).hi ≤ Pmax * fxScale) &&
    decide (DlS ≤ J2.lo) && decide (J2.hi ≤ DhS)

/-! ## Leaves and covers -/

/-- **Leaf condition** on the index box `[a, b] × [c, d]`: oracle enclosures exist for which
both leg checks and the final check (amplitude target `Kn`, period range `[Pmin, Pmax]` μs,
precession range `[DlS, DhS]`) pass. -/
@[expose] def OscLeaf (Kn Pmin Pmax DlS DhS : ℤ) (a b c d : ℕ) : Prop :=
  ∃ Θ0 Cin Sin J1 Tin Cout Sout J2 Tout : FIv,
    legAOk (PBI a b) (TBI c d) Θ0 Cin Sin J1 Tin = true ∧
      legBOk (PBI a b) (TBI c d) Θ0 J1 Cout Sout J2 Tout = true ∧
      finalOk Cin Sin Cout Sout J2 Tin Tout Kn 1 Pmin Pmax DlS DhS = true

/-- **Adaptive cover**: a binary subdivision of `[a, b] × [c, d]` into `OscLeaf` boxes. -/
inductive OscCover (Kn Pmin Pmax DlS DhS : ℤ) : ℕ → ℕ → ℕ → ℕ → Prop where
  /-- A leaf box. -/
  | leaf (a b c d : ℕ) : OscLeaf Kn Pmin Pmax DlS DhS a b c d →
      OscCover Kn Pmin Pmax DlS DhS a b c d
  /-- Split the flux range at `m`. -/
  | splitP (a m b c d : ℕ) : OscCover Kn Pmin Pmax DlS DhS a m c d →
      OscCover Kn Pmin Pmax DlS DhS m b c d → OscCover Kn Pmin Pmax DlS DhS a b c d
  /-- Split the tip-field range at `m`. -/
  | splitT (a b c m d : ℕ) : OscCover Kn Pmin Pmax DlS DhS a b c m →
      OscCover Kn Pmin Pmax DlS DhS a b m d → OscCover Kn Pmin Pmax DlS DhS a b c d

/-- **The leaf data at a point**: an enclosing parameter box with passing checks. -/
@[expose] def OscAt (Kn Pmin Pmax DlS DhS : ℤ) (ψ₀ Bt : ℝ) : Prop :=
  ∃ P Tb Θ0 Cin Sin J1 Tin Cout Sout J2 Tout : FIv, P.Mem ψ₀ ∧ Tb.Mem Bt ∧
    legAOk P Tb Θ0 Cin Sin J1 Tin = true ∧ legBOk P Tb Θ0 J1 Cout Sout J2 Tout = true ∧
    finalOk Cin Sin Cout Sout J2 Tin Tout Kn 1 Pmin Pmax DlS DhS = true

/-- **Soundness of a cover.** -/
theorem OscCover.sound {Kn Pmin Pmax DlS DhS : ℤ} {a b c d : ℕ}
    (h : OscCover Kn Pmin Pmax DlS DhS a b c d) {ψ₀ Bt : ℝ}
    (hψ : ψ₀ ∈ Icc ((4864 + 9 * (a : ℝ)) / 1024) ((4864 + 9 * (b : ℝ)) / 1024))
    (hB : Bt ∈ Icc ((6912 + (c : ℝ)) / 1280) ((6912 + (d : ℝ)) / 1280)) :
    OscAt Kn Pmin Pmax DlS DhS ψ₀ Bt := by
  induction h with
  | leaf a b c d hl =>
    obtain ⟨Θ0, Cin, Sin, J1, Tin, Cout, Sout, J2, Tout, h1, h2, h3⟩ := hl
    exact ⟨_, _, Θ0, Cin, Sin, J1, Tin, Cout, Sout, J2, Tout,
      mem_hull (by norm_num) (by norm_num) (by push_cast; exact hψ.1) (by push_cast; exact hψ.2),
      mem_hull (by norm_num) (by norm_num) (by push_cast; exact hB.1) (by push_cast; exact hB.2),
      h1, h2, h3⟩
  | splitP a m b c d _ _ ih1 ih2 =>
    rcases le_total ψ₀ ((4864 + 9 * (m : ℝ)) / 1024) with h | h
    · exact ih1 ⟨hψ.1, h⟩ hB
    · exact ih2 ⟨h, hψ.2⟩ hB
  | splitT a b c m d _ _ ih1 ih2 =>
    rcases le_total Bt ((6912 + (m : ℝ)) / 1280) with h | h
    · exact ih1 hψ ⟨hB.1, h⟩
    · exact ih2 hψ ⟨h, hB.2⟩

/-! ## Soundness of the cells -/

/-- Real form of the reduced bottom divisor: `|θ̇|/A = K + (−∂_ψB)` (inner leg) or
`K − (−∂_ψB)` (outer leg). -/
@[expose] def bDenR (inner : Bool) (p x b c : ℝ) : ℝ :=
  if inner then KR x b + numR inner p x c else KR x b - numR inner p x c

/-- Soundness of `bDenI`. -/
theorem mem_bDenI {inner : Bool} {X P T c : FIv} {x p b cr : ℝ} (hX : X.Mem x) (hP : P.Mem p)
    (hT : T.Mem b) (hc : c.Mem cr) : (bDenI inner X P T c).Mem (bDenR inner p x b cr) := by
  have h1 := mem_KI hX hT
  have h2 := mem_numI (inner := inner) hX hP hc
  cases inner
  · simp only [bDenI, bDenR, Bool.false_eq_true, ite_false]; exact FIv.mem_sub h1 h2
  · simp only [bDenI, bDenR, ite_true]; exact FIv.mem_add h1 h2

/-- A scaled value below a strict scaled bound. -/
theorem fxVal_lt_of_lt {a b : ℤ} (h : a < b) : fxVal a < fxVal b := by
  unfold fxVal; exact div_lt_div_of_pos_right (by exact_mod_cast h) fxScale_pos

/-- A scaled value below a scaled bound. -/
theorem fxVal_le_of_le {a b : ℤ} (h : a ≤ b) : fxVal a ≤ fxVal b := by
  unfold fxVal; exact div_le_div_of_nonneg_right (by exact_mod_cast h) fxScale_pos.le

/-- `fxVal 0 = 0`. -/
theorem fxVal_zero : fxVal 0 = 0 := by simp [fxVal]

/-- **Soundness of a flank cell.** For an orbit point with leg coordinate `x ∈ X`, constants of
motion in `P × T` and `|θ| ≥ 3/5` (`c ≤ cos(3/5)`): the cell is alive, `|∂_θB| > 0`, and the
four densities enclose `(−∂_ψB)/|∂_θB|`, `K/(ι₀ |∂_θB|)`, `w/|∂_θB|`, `1/(A_μ |∂_θB|)`, the first
two with nonnegative lower ends. -/
theorem flankCellO_sound {inner : Bool} {X P T : FIv} {x p b c : ℝ}
    (hok : (flankCellO inner X P T).ok = true) (hX : X.Mem x) (hP : P.Mem p) (hT : T.Mem b)
    (hrel : OrbitRel inner x p b c) (hc : c ≤ cos (3 / 5)) :
    (flankCellO inner X P T).dead = false ∧ 0 < denR inner p x c (√(1 - c ^ 2)) ∧
      (flankCellO inner X P T).om.Mem (numR inner p x c * (denR inner p x c (√(1 - c ^ 2)))⁻¹) ∧
      (flankCellO inner X P T).ph.Mem
        (KR x b * (211 / 500 * denR inner p x c (√(1 - c ^ 2)))⁻¹) ∧
      (flankCellO inner X P T).g.Mem (wR inner p x * (denR inner p x c (√(1 - c ^ 2)))⁻¹) ∧
      (flankCellO inner X P T).tt.Mem (1 * (AmR x b * denR inner p x c (√(1 - c ^ 2)))⁻¹) ∧
      (flankCellO inner X P T).om.ok = true ∧ (flankCellO inner X P T).ph.ok = true ∧
      (flankCellO inner X P T).g.ok = true ∧ (flankCellO inner X P T).tt.ok = true ∧
      0 ≤ fxVal (flankCellO inner X P T).om.lo ∧ 0 ≤ fxVal (flankCellO inner X P T).ph.lo := by
  have hcI := mem_cI (inner := inner) hX hP hT
  rw [cR_eq hrel] at hcI
  unfold flankCellO at hok ⊢
  split_ifs at hok ⊢ with hdead
  · exfalso
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hdead
    obtain ⟨h1, _⟩ := hcI hdead.1
    linarith [le_cdHi, fxVal_lt_of_lt hdead.2]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨hom, hph⟩, hg⟩, htt⟩, hom0⟩, hph0⟩ := hok
    have hc2 : (flankC inner X P T).Mem c :=
      mem_meetLo (mem_meetHi hcI (hc.trans le_cdHi)) (by simp [fxVal, hrel.c_nonneg])
    have hs : (flankS inner X P T).Mem (√(1 - c ^ 2)) :=
      mem_meetLo (FIv.mem_sqrt (FIv.mem_sub (mem_C (by norm_num)) (FIv.mem_sq hc2)))
        (sdLo_le.trans (sqrt_one_sub_sq_ge hrel.c_nonneg hc))
    have hden : (flankDen inner X P T).Mem (denR inner p x c (√(1 - c ^ 2))) :=
      mem_denI hX hP hc2 hs
    have hnum := mem_numI (inner := inner) hX hP hc2
    have hpos := dv_pos hom hden
    refine ⟨rfl, hpos, mem_dv hnum hden, ?_, mem_dv (mem_wI hX hP) hden,
      mem_dv (mem_C (by norm_num)) (FIv.mem_mul (mem_AmI hX hT) hden), hom, hph, hg, htt,
      by rw [← fxVal_zero]; exact fxVal_le_of_le hom0,
      by rw [← fxVal_zero]; exact fxVal_le_of_le hph0⟩
    exact mem_dv (mem_KI hX hT) (FIv.mem_mul (mem_C (by norm_num)) hden)

/-- **Full flank cells.** If the cell is flagged `full`, every orbit point with leg coordinate in
`X` has `c < cos(3/5)` (it is strictly inside the flank). -/
theorem flankCellO_full {inner : Bool} {X P T : FIv} {x p b c : ℝ}
    (hfull : (flankCellO inner X P T).full = true) (hX : X.Mem x) (hP : P.Mem p) (hT : T.Mem b)
    (hrel : OrbitRel inner x p b c) : c < cos (3 / 5) := by
  have hcI := mem_cI (inner := inner) hX hP hT
  rw [cR_eq hrel] at hcI
  unfold flankCellO at hfull
  split_ifs at hfull with hdead
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfull
  obtain ⟨_, h2⟩ := hcI hfull.1
  linarith [cdLo_le, fxVal_lt_of_lt hfull.2]

/-- **The cosine table.** For `k < 24` and `|θ| ∈ [k/40, (k+1)/40]`, `cos θ ∈ CTL k`. -/
theorem mem_CTL {k : ℕ} (hk : k < 24) {θ : ℝ} (h1 : (k : ℝ) / 40 ≤ |θ|)
    (h2 : |θ| ≤ ((k : ℝ) + 1) / 40) : (CTL k).Mem (cos θ) := by
  have htab := okAll_spec CTI_tab k hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htab
  obtain ⟨⟨hlo, hhi⟩, hok⟩ := htab
  have hok' := hok
  simp only [CTI, Bool.and_eq_true] at hok'
  have hk' : ((k : ℝ) + 1) / 40 ≤ 24 / 40 := by
    have : (k : ℝ) + 1 ≤ 24 := by exact_mod_cast hk
    linarith
  have ha := (mem_cosSinC (z := ((k : ℤ) + 1 : ℤ) / (40 : ℤ))
    (mem_C (p := (k : ℤ) + 1) (q := 40) rfl)).1 hok'.1
  have hb := (mem_cosSinC (z := ((k : ℤ) : ℝ) / (40 : ℤ))
    (mem_C (p := (k : ℤ)) (q := 40) rfl)).1 hok'.2
  push_cast at ha hb
  have hθ0 : 0 ≤ (k : ℝ) / 40 := by positivity
  have hcos1 : cos (((k : ℝ) + 1) / 40) ≤ cos |θ| :=
    cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith [pi_gt_three]) h2
  have hcos2 : cos |θ| ≤ cos ((k : ℝ) / 40) :=
    cos_le_cos_of_nonneg_of_le_pi hθ0 (by linarith [pi_gt_three]) h1
  rw [cos_abs] at hcos1 hcos2
  intro _
  refine ⟨?_, ?_⟩
  · show fxVal (CTL k).lo ≤ cos θ
    rw [hlo]; exact ha.1.trans hcos1
  · show cos θ ≤ fxVal (CTL k).hi
    rw [hhi]; exact hcos2.trans hb.2

/-- Every entry of a `subList` has a valid cell enclosure. -/
theorem subList_ok {inner : Bool} {P T : FIv} : ∀ q ∈ subList inner P T, q.1.ok = true := by
  intro q hq
  simp only [subList, List.mem_flatMap, List.mem_range] at hq
  obtain ⟨i, _, hi⟩ := hq
  split_ifs at hi
  · simp at hi
  · simp only [List.mem_singleton] at hi; rw [hi]; rfl

/-- **Hull scan.** If every entry is valid and some entry `q` is compatible with `CT`, then the
scan finds a hull containing `q.1`. -/
theorem hullScan_spec (CT : FIv) (L : List (FIv × FIv)) (hL : ∀ q ∈ L, q.1.ok = true)
    (q : FIv × FIv) (hq : q ∈ L)
    (hcomp : (q.2.ok && CT.ok && (decide (q.2.hi < CT.lo) || decide (CT.hi < q.2.lo))) = false) :
    (hullScan CT L).1 = true ∧ (hullScan CT L).2.1 ≤ q.1.lo ∧ q.1.hi ≤ (hullScan CT L).2.2 := by
  induction L with
  | nil => simp at hq
  | cons p rest ih =>
    have hrest : ∀ q ∈ rest, q.1.ok = true := fun q hq => hL q (List.mem_cons_of_mem _ hq)
    simp only [hullScan]
    rcases List.mem_cons.mp hq with h | h
    · subst h
      rw [hcomp]
      simp only [Bool.false_eq_true, ite_false]
      refine ⟨hL _ (List.mem_cons_self), ?_, ?_⟩
      · split_ifs <;> simp
      · split_ifs <;> simp
    · obtain ⟨i1, i2, i3⟩ := ih hrest h
      split_ifs with hp
      · exact ⟨i1, i2, i3⟩
      · simp only
        exact ⟨hL _ (List.mem_cons_self), min_le_of_right_le i2, le_max_of_le_right i3⟩

/-- **Soundness of the leg-coordinate hull at the bottom.** For `k < 24`, an orbit point with
`x ∈ [0, 5/2]`, constants in `P × T`, `cos(3/5) ≤ c` and `c ∈ CTL k` has `x ∈ hullX`. -/
theorem hullX_sound {inner : Bool} {P T : FIv} {k : ℕ} {x p b c : ℝ} (hP : P.Mem p)
    (hT : T.Mem b) (hx : x ∈ Icc (0 : ℝ) (5 / 2)) (hrel : OrbitRel inner x p b c)
    (hc : cos (3 / 5) ≤ c) (hCT : (CTL k).Mem c) : (hullX inner P T k).Mem x := by
  obtain ⟨i, hi, hxi⟩ := exists_cell hx
  have hX := mem_cellX hxi
  have hcI := mem_cI (inner := inner) hX hP hT
  rw [cR_eq hrel] at hcI
  have hnot : ((cI inner (cellX i) P T).ok && decide ((cI inner (cellX i) P T).hi < cdLo)) =
      false := by
    by_contra hcon
    simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hcon
    obtain ⟨_, h2⟩ := hcI hcon.1
    linarith [cdLo_le, fxVal_lt_of_lt hcon.2]
  have hmem : (cellX i, cI inner (cellX i) P T) ∈ subList inner P T := by
    simp only [subList, List.mem_flatMap, List.mem_range]
    exact ⟨i, hi, by rw [hnot]; simp⟩
  have hcomp : ((cI inner (cellX i) P T).ok && (CTL k).ok &&
      (decide ((cI inner (cellX i) P T).hi < (CTL k).lo) ||
        decide ((CTL k).hi < (cI inner (cellX i) P T).lo))) = false := by
    by_contra hcon
    simp only [Bool.not_eq_false, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hcon
    obtain ⟨⟨hok1, hok2⟩, hor⟩ := hcon
    obtain ⟨a1, a2⟩ := hcI hok1
    obtain ⟨b1, b2⟩ := hCT hok2
    rcases hor with h | h
    · linarith [fxVal_lt_of_lt h]
    · linarith [fxVal_lt_of_lt h]
  obtain ⟨hf, hlo, hhi⟩ := hullScan_spec (CTL k) (subList inner P T) subList_ok _ hmem hcomp
  intro _
  have hXb := hX rfl
  exact ⟨(fxVal_le_of_le hlo).trans hXb.1, hXb.2.trans (fxVal_le_of_le hhi)⟩

/-- **Soundness of a bottom cell.** For `k < 24`, an orbit point with `x ∈ [0, 5/2]`, constants
in `P × T`, `cos(3/5) ≤ c` and `c ∈ CTL k`: `|θ̇|/A = bDenR > 0` and the densities enclose
`(−∂_ψB)/bDenR` (with nonnegative lower end), `w/bDenR` and `1/(A_μ bDenR)`. -/
theorem bottomCellO_sound {inner : Bool} {P T : FIv} {k : ℕ} {x p b c : ℝ}
    (hok : (bottomCellO inner P T k).ok = true) (hP : P.Mem p) (hT : T.Mem b)
    (hx : x ∈ Icc (0 : ℝ) (5 / 2)) (hrel : OrbitRel inner x p b c) (hc : cos (3 / 5) ≤ c)
    (hCT : (CTL k).Mem c) :
    0 < bDenR inner p x b c ∧
      (bottomCellO inner P T k).om.Mem (numR inner p x c * (bDenR inner p x b c)⁻¹) ∧
      (bottomCellO inner P T k).g.Mem (wR inner p x * (bDenR inner p x b c)⁻¹) ∧
      (bottomCellO inner P T k).tt.Mem (1 * (AmR x b * bDenR inner p x b c)⁻¹) ∧
      (bottomCellO inner P T k).om.ok = true ∧ (bottomCellO inner P T k).g.ok = true ∧
      (bottomCellO inner P T k).tt.ok = true ∧ 0 ≤ fxVal (bottomCellO inner P T k).om.lo := by
  have hX := hullX_sound (inner := inner) (k := k) hP hT hx hrel hc hCT
  have hc2 : (bcI k).Mem c :=
    mem_meetHi (mem_meetLo hCT (cdLo_le.trans hc))
      (by rw [show fxVal fxScale = 1 by unfold fxVal; exact div_self fxScale_pos.ne']
          exact hrel.c_le)
  have hd := mem_bDenI (inner := inner) hX hP hT hc2
  simp only [bottomCellO, Bool.and_eq_true, decide_eq_true_eq] at hok ⊢
  obtain ⟨⟨⟨hom, hg⟩, htt⟩, hom0⟩ := hok
  exact ⟨dv_pos hom hd, mem_dv (mem_numI hX hP hc2) hd, mem_dv (mem_wI hX hP) hd,
    mem_dv (mem_C (by norm_num)) (FIv.mem_mul (mem_AmI hX hT) hd), hom, hg, htt,
    by rw [← fxVal_zero]; exact fxVal_le_of_le hom0⟩

/-- **Soundness of the tip-angle bounds.** If `theta0Ok`, the tip cosine `cos θ₀` lies in
`c0I P T` and `θ₀ ∈ [0, 3]`, then `θ₀ ∈ Θ0`. -/
theorem theta0_sound {P T Θ0 : FIv} (h : theta0Ok P T Θ0 = true) {θ₀ : ℝ}
    (hc : (c0I P T).Mem (cos θ₀)) (hθ : θ₀ ∈ Icc (0 : ℝ) 3) : Θ0.Mem θ₀ := by
  simp only [theta0Ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hok, h0⟩, hlh⟩, h3⟩, hcok⟩, hcos1⟩, hcos2⟩, hle1⟩, hle2⟩ := h
  have hA := (mem_cosSinC (Φ := ⟨Θ0.hi, Θ0.hi, true⟩) (z := fxVal Θ0.hi)
    (fun _ => ⟨le_rfl, le_rfl⟩)).1 hcos1
  have hB := (mem_cosSinC (Φ := ⟨Θ0.lo, Θ0.lo, true⟩) (z := fxVal Θ0.lo)
    (fun _ => ⟨le_rfl, le_rfl⟩)).1 hcos2
  obtain ⟨c1, c2⟩ := hc hcok
  have hlo0 : 0 ≤ fxVal Θ0.lo := by rw [← fxVal_zero]; exact fxVal_le_of_le h0
  have hlohi : fxVal Θ0.lo ≤ fxVal Θ0.hi := fxVal_le_of_le hlh
  have hhi3 : fxVal Θ0.hi ≤ 3 := by
    have := fxVal_le_of_le h3
    rwa [show fxVal (3 * fxScale) = 3 by
      unfold fxVal; push_cast; rw [mul_div_assoc, div_self fxScale_pos.ne', mul_one]] at this
  intro _
  constructor
  · by_contra hcon
    push Not at hcon
    have := cos_lt_cos_of_nonneg_of_le_pi hθ.1 (by linarith [pi_gt_three]) hcon
    linarith [hB.1, fxVal_le_of_le hle2]
  · by_contra hcon
    push Not at hcon
    have := cos_lt_cos_of_nonneg_of_le_pi (hlo0.trans hlohi) (by linarith [pi_gt_three, hθ.2])
      hcon
    linarith [hA.2, fxVal_le_of_le hle1]

/-- **Scaled totals.** `⟨L, H⟩ · (1/40)` contains `v` whenever `L ≤ 40 v ≤ H` (scaled). -/
theorem mem_div40 {L H : ℤ} {v : ℝ} (h1 : fxVal L ≤ 40 * v) (h2 : 40 * v ≤ fxVal H) :
    ((⟨L, H, true⟩ : FIv).mul (C 1 40)).Mem v := by
  have := FIv.mem_mul (I := ⟨L, H, true⟩) (x := 40 * v) (fun _ => ⟨h1, h2⟩)
    (mem_C (p := 1) (q := 40) (r := 1 / 40) (by norm_num))
  rwa [show 40 * v * (1 / 40) = v by ring] at this

/-! ## Sanity fixtures -/

set_option maxRecDepth 100000 in
/-- Sanity (accepted fixture): a flank cell near the tip of the corner box is alive and valid. -/
theorem fixture_flankO_alive : (flankCellO true (cellX 10) (PBI 0 15) (TBI 0 16)).ok = true ∧
    (flankCellO true (cellX 10) (PBI 0 15) (TBI 0 16)).dead = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Sanity (degenerate case): far from the tips (`x ≈ 2.25`) the inner flank cell is dead and has
zero densities. -/
theorem fixture_flankO_dead : (flankCellO true (cellX 90) (PBI 0 15) (TBI 0 16)).dead = true ∧
    (flankCellO true (cellX 90) (PBI 0 15) (TBI 0 16)).g = zeroI := by
  have h : ((flankCellO true (cellX 90) (PBI 0 15) (TBI 0 16)).dead &&
      eqI (flankCellO true (cellX 90) (PBI 0 15) (TBI 0 16)).g zeroI) = true := by
    decide +kernel
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1, eq_of_eqI h.2⟩

set_option maxRecDepth 100000 in
/-- Sanity (accepted fixture): a bottom cell of the corner box is valid. -/
theorem fixture_bottomO_ok : (bcell true (PBI 0 15) (TBI 0 16) 10).ok = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Sanity (rejected fixture): a wrong thin guess `θ₀ = 1.0477…` for the tip angle of the corner
box fails `theta0Ok`. -/
theorem fixture_theta0_rejected :
    theta0Ok (PBI 0 15) (TBI 0 16) ⟨4500000000, 4500000000, true⟩ = false := by
  decide +kernel

end PlasmaLean.Design.NearAxisQATrappedOsc
