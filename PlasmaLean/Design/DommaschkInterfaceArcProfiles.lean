/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkInterfaceArcGeometry
public import PlasmaLean.Design.DommaschkInterfaceJets
public import PlasmaLean.Design.DommaschkKamAInterfaceFourier

/-!
# The real cylindrical jets on the interface arc of torus A

An exact torus yields continuous profiles on the arc. Their eleven coordinates
are compared with the mixed derivatives of the *stored* seed in geometric
radian angles, including the factor of two in the toroidal angle. The remaining
numerical hypotheses concern only the explicitly packed seed.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkInterfaceArcProfiles

open PlasmaLean.Theory.KAM WEll1Z2
open PlasmaLean.Certificates.ValidatedQuadrature
open PlasmaLean.Stability.InterfacePrincipalDirection
open KamNewton DommaschkKamA DommaschkInterfaceArcGeometry DommaschkKamAInterfaceFourier
open DommaschkKamC (RofC)
open ProfileAngle

/-- Radius, first derivatives, and second derivatives in the angular chart at θ = 0. -/
def cylindricalJet (u z : FA) (φ : ℝ) : Jet → ℝ
  | .radius => RofC u 0 φ
  | .rθ => poloidal.partialD (RofC u) 0 φ
  | .rφ => toroidal.partialD (RofC u) 0 φ
  | .zθ => poloidal.partialD (Zof z) 0 φ
  | .zφ => toroidal.partialD (Zof z) 0 φ
  | .rθθ => poloidal.partialD (poloidal.partialD (RofC u)) 0 φ
  | .rθφ => toroidal.partialD (poloidal.partialD (RofC u)) 0 φ
  | .rφφ => toroidal.partialD (toroidal.partialD (RofC u)) 0 φ
  | .zθθ => poloidal.partialD (poloidal.partialD (Zof z)) 0 φ
  | .zθφ => toroidal.partialD (poloidal.partialD (Zof z)) 0 φ
  | .zφφ => toroidal.partialD (toroidal.partialD (Zof z)) 0 φ

/-- The radial displacement array excludes the chart's constant reference radius. -/
def seedOffset : Jet → ℝ
  | .radius => 29 / 32
  | _ => 0

/-- The actual finite trigonometric formula for a stored seed jet on the arc. -/
def packedSeedJet (φ : ℝ) (k : Jet) : ℝ :=
  let (h, a, b) := k.source
  seedOffset k + if h then gridJet Sc Nc Mc 1 gZ a b 0 φ else gridJet Sc Nc Mc 0 gU a b 0 φ

private theorem partial_offset (p : ProfileAngle) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    p.partialD (fun θ φ => c + f θ φ) = p.partialD f := by
  funext θ φ
  cases p <;> exact deriv_const_add _

private theorem continuous_slice {w : FA} (hw : Ana w) : Continuous (Zof w 0) :=
  continuous_iff_continuousAt.mpr fun φ => (hasDerivAt_Zof_φ hw 0 φ).continuousAt

/-- Analytic Fourier profiles have continuous real jets through order two on the entire slice. -/
theorem continuous_cylindricalJet {u z : FA} (hu : Ana u) (hz : Ana z) (k : Jet) :
    Continuous fun φ => cylindricalJet u z φ k := by
  have hr : RofC u = fun θ φ => DommaschkKam.dkR0 + Zof u θ φ := rfl
  cases k <;> simp only [cylindricalJet, hr, partial_offset,
    ProfileAngle.partial_Zof _ hu, ProfileAngle.partial_Zof _ hz,
    ProfileAngle.partial_Zof _ (ProfileAngle.analytic _ hu),
    ProfileAngle.partial_Zof _ (ProfileAngle.analytic _ hz)]
  all_goals first
    | exact continuous_const.add (continuous_slice hu)
    | apply continuous_slice
      repeat first | exact hu | exact hz | apply ProfileAngle.analytic

private theorem grid_poloidal (S N M p : ℕ) (g : ℕ → ℕ → ℤ) (a b : ℕ) :
    poloidal.partialD (gridJet S N M p g a b) = gridJet S N M p g (a+1) b := by
  funext θ φ
  exact (gridJet_poloidal S N M p g a b θ φ).deriv

private theorem grid_toroidal (S N M p : ℕ) (g : ℕ → ℕ → ℤ) (a b : ℕ) :
    toroidal.partialD (gridJet S N M p g a b) = gridJet S N M p g a (b+1) := by
  funext θ φ
  exact (gridJet_toroidal S N M p g a b θ φ).deriv

/-- Every component of the geometric seed jet is its indexed packed finite sum. -/
theorem cylindricalJet_seed (φ : ℝ) (k : Jet) :
    cylindricalJet u₀A z₀A φ k = packedSeedJet φ k := by
  have hr : RofC u₀A = fun θ φ => 29 / 32 + gridJet Sc Nc Mc 0 gU 0 0 θ φ := by
    funext θ φ; exact radius_seed_eq θ φ
  have hz : Zof z₀A = gridJet Sc Nc Mc 1 gZ 0 0 := by
    funext θ φ; exact height_seed_eq θ φ
  cases k <;> simp [cylindricalJet, hr, hz, partial_offset, grid_poloidal, grid_toroidal,
    packedSeedJet, Jet.source, seedOffset]

/-- Uniform error for an (a,b) jet when the strip radius is 9 / 1400 and the
profile error is M. Each geometric toroidal derivative contributes a factor of two. -/
def jetError (M : ℝ) (k : Jet) : ℝ :=
  2 ^ k.source.2.2 / (9 / 1400) ^ (k.source.2.1 + k.source.2.2) * M

/-- The actual jets of any torus in the certified strip neighborhood are this close
to the finite trigonometric polynomial for the same jet. -/
theorem cylindricalJet_error {u z : FA} {M : ℝ}
    (h : Close (9 / 1400) DommaschkKamDio.dkIotaA u z u₀A z₀A M) (φ : ℝ) (k : Jet) :
    |cylindricalJet u z φ k - packedSeedJet φ k| ≤ jetError M k := by
  rw [← cylindricalJet_seed]
  obtain ⟨hr, hz⟩ := profileJets_of_close h
  cases k <;> dsimp only [jetError, Jet.source, cylindricalJet]
  case' radius => simpa using hr.value 0 φ
  case' rθ => apply (hr.first .poloidal 0 φ).trans
  case' rφ => apply (hr.first .toroidal 0 φ).trans
  case' zθ => apply (hz.first .poloidal 0 φ).trans
  case' zφ => apply (hz.first .toroidal 0 φ).trans
  case' rθθ => apply (hr.second .poloidal .poloidal 0 φ).trans
  case' rθφ => apply (hr.second .poloidal .toroidal 0 φ).trans
  case' rφφ => apply (hr.second .toroidal .toroidal 0 φ).trans
  case' zθθ => apply (hz.second .poloidal .poloidal 0 φ).trans
  case' zθφ => apply (hz.second .poloidal .toroidal 0 φ).trans
  case' zφφ => apply (hz.second .toroidal .toroidal 0 φ).trans
  all_goals norm_num [ProfileAngle.factor]
  all_goals linarith

/-- Every seed value stays inside the requested dyadic box by its exact profile error. -/
def SeedMargin (box : Jet → FIv) (φ : ℝ) : Prop := ∀ k,
  fxVal (box k).lo + jetError ((1 / 10 ^ 12 : ℚ) : ℝ) k ≤ packedSeedJet φ k ∧
  packedSeedJet φ k ≤ fxVal (box k).hi - jetError ((1 / 10 ^ 12 : ℚ) : ℝ) k

/-- Strip closeness to the analytic seed implies continuity of all eleven arc jets. -/
theorem continuous_cylindricalJet_of_close {u z : FA} {M : ℝ}
    (h : Close (9 / 1400) DommaschkKamDio.dkIotaA u z u₀A z₀A M) (k : Jet) :
    Continuous fun φ => cylindricalJet u z φ k := by
  have analytic {x y : FA} (hd : Bd (9 / 1400) (x - y) M) (hy : Ana y) : Ana x := by
    have hxy : Ana (x - y) := ⟨9 / 1400, M, by norm_num, hd⟩
    simpa only [sub_add_cancel] using hxy.add hy
  exact continuous_cylindricalJet (analytic h.du ana_u₀A) (analytic h.dz ana_z₀A) k

/-- The strip error transfers a packed seed margin to any two profiles covered by Q-16. -/
theorem inBox_of_close_of_seedMargin {u z : FA}
    (h : Close (9 / 1400) DommaschkKamDio.dkIotaA u z u₀A z₀A ((1 / 10 ^ 12 : ℚ) : ℝ))
    {box : Jet → FIv} {φ : ℝ}
    (hs : SeedMargin box φ) : InBox box (cylindricalJet u z φ) := by
  intro k _
  have he := abs_le.mp (cylindricalJet_error h φ k)
  obtain ⟨hl, hu⟩ := hs k
  constructor <;> linarith [he.1, he.2]

/-- Each exact torus gives these box memberships using its own closeness certificate. -/
theorem inBox_of_seedMargin {u z : FA} (h : ExactTorusA u z) {box : Jet → FIv} {φ : ℝ}
    (hs : SeedMargin box φ) : InBox box (cylindricalJet u z φ) :=
  inBox_of_close_of_seedMargin h.close hs

/-- An exact torus A has a local sign obstruction once the finite seed sum meets
the three explicit margin checks. -/
theorem exactTorusA_obstruction_of_seedMargin {u z : FA} (h : ExactTorusA u z)
    (hl : SeedMargin leftBox 0) (hr : SeedMargin rightBox (1 / 5))
    (ha : ∀ φ ∈ Set.Icc 0 (1 / 5), SeedMargin arcBox φ) :
    ∃ φ ∈ Set.Icc 0 (1 / 5), ∀ v,
      0 < pair (metricRow DommaschkKamDio.dkIotaA (cylindricalJet u z φ)) v →
      0 < pair (curvatureRow DommaschkKamDio.dkIotaA (cylindricalJet u z φ)) v :=
  exists_obstruction (fun k => (continuous_cylindricalJet h.ana_u h.ana_z k).continuousOn)
    (inBox_of_seedMargin h hl) (inBox_of_seedMargin h hr)
    (fun φ hφ => inBox_of_seedMargin h (ha φ hφ))

end PlasmaLean.Design.DommaschkInterfaceArcProfiles
