/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamFieldCheck
public import PlasmaLean.Design.DommaschkQA2RData

/-!
# Kernel checks identifying the flow-form polynomials with `field candidate`

Two families of kernel checks (`kernel_fact`, the leaf `Eq.refl` checked only by the kernel),
used by `Design/DommaschkKamIdent`:

1. **The substitution `R = R₀ + u`.** `substR p` replaces `R` (slot `0`) by `R₀ + u` in an
   `R`-form sparse polynomial (`RpowL n = (R₀ + u)ⁿ`). Checks: `substR dDR = dD`,
   `substR (R · dnRh) = dnR`, `substR dnZR = dnZ` (`subst_D`, `subst_nR`, `subst_nZ`).
2. **The Cartesian identity.** An `R`-form term `q R^{2k} z^b c^i s^j` (`c = cos 2φ`, `s = sin 2φ`)
   is the cylindrical potential `q r₂^{k−i−j} z^b (x² − y²)^i (2xy)^j` (`convT`, scaled by a common
   denominator `N` to integer coefficients; `convOK`). The field side is
   * `Gphi = r₂³ (L + Σ_k L w_k (x ∂_y P_k − y ∂_x P_k))`, i.e. `L R⁶(−y B_x + x B_y) = L R⁷ B_φ`;
   * `GRh = r₂³ Σ_k L w_k (x ∂_x P_k + y ∂_y P_k)`, i.e. `L R⁶(x B_x + y B_y) = L R⁷ B_R`;
   * `GZ = r₂⁴ Σ_k L w_k ∂_z P_k`, i.e. `L R⁸ B_z`;
   with `w_k = a_k · scale k` the weights of `DommaschkQA2R.field candidate` and `L = Lw` their
   common denominator (`LW_int`). Checks: `L · convAll N D_R − N · Gphi` (and the same for
   `n_R/R`, `n_z`) has empty normal form slice by slice in the degree in `R` and the power of `z`
   (`degCheck`, built on `CylAlgebra.sliceCheck`):
   `ident_nZ` here, `ident_D` in `DommaschkKamIdentCheckD` and `ident_nR` in
   `DommaschkKamIdentCheckR` (separate modules, to keep each Lean process within the memory
   budget).

The same computations are mirrored and validated in `scripts/dommaschk_kam/emit_flowfield.py`.

**Sanity.** `trigC_fixture` (`(x² − y²)(2xy) = 2x³y − 2xy³`) and the rejected fixture
`ident_nZ_bad` (dropping the first term of `n_{z,R}` breaks the identity).
-/

@[expose] public section

namespace PlasmaLean.Design.DommaschkKam

open DkPoly PlasmaLean.Fields.CylAlgebra

/-! ## The substitution `R = R₀ + u` -/

/-- `(R₀ + u)ⁿ`. -/
def RpowL : ℕ → SP
  | 0 => [⟨1, 0, 0, 0, 0⟩]
  | n + 1 => mul Rl (RpowL n)

/-- Substitute `R = R₀ + u` into an `R`-form sparse polynomial. -/
def substR (p : SP) : SP :=
  p.foldr (fun t acc => merge (mulMono ⟨t.q, 0, t.b, t.c, t.d⟩ (RpowL t.a)) acc) []

/-- `D(u) = D_R(R₀ + u)` (kernel check). -/
theorem subst_D : substR dDR = dD := by kernel_fact

/-- `n_R(u) = (R · n_R/R)(R₀ + u)` (kernel check). -/
theorem subst_nR : substR (mulMono ⟨1, 1, 0, 0, 0⟩ dnRh) = dnR := by kernel_fact

/-- `n_z(u) = n_{z,R}(R₀ + u)` (kernel check). -/
theorem subst_nZ : substR dnZR = dnZ := by kernel_fact

/-! ## Cylindrical potentials -/

/-- Product of a monomial and a cylindrical potential. -/
def cmulMono (m : Mono) (f : CylPoly) : CylPoly :=
  f.map fun n => ⟨m.c * n.c, m.a + n.a, m.b + n.b, m.j + n.j, m.s + n.s, m.q + n.q⟩

/-- Product of cylindrical potentials. -/
def cmul (f g : CylPoly) : CylPoly := f.flatMap fun m => cmulMono m g

/-- Power of a cylindrical potential. -/
def cpow (f : CylPoly) : ℕ → CylPoly
  | 0 => [⟨1, 0, 0, 0, 0, 0⟩]
  | n + 1 => cmul f (cpow f n)

/-- Integer multiple of a cylindrical potential. -/
def cscale (k : ℤ) (f : CylPoly) : CylPoly := f.map fun m => ⟨k * m.c, m.a, m.b, m.j, m.s, m.q⟩

/-- `x² − y²` (`= r₂ cos 2φ`). -/
def X2 : CylPoly := [⟨1, 2, 0, 0, 0, 0⟩, ⟨-1, 0, 2, 0, 0, 0⟩]

/-- `2xy` (`= r₂ sin 2φ`). -/
def XY : CylPoly := [⟨2, 1, 1, 0, 0, 0⟩]

/-- `(x² − y²)^i (2xy)^j`. -/
def trigC (i j : ℕ) : CylPoly := cmul (cpow X2 i) (cpow XY j)

/-- The term `q R^a z^b c^i s^j` (`a` even) as the potential `N q r₂^{a/2 − i − j} z^b
(x² − y²)^i (2xy)^j` (`N q` an integer). -/
def convT (N : ℕ) (t : Tm) : CylPoly :=
  cscale ((N * t.q).num) (cmulMono ⟨1, 0, 0, t.b, ((t.a / 2 : ℕ) : ℤ) - t.c - t.d, 0⟩
    (trigC t.c t.d))

/-- An `R`-form sparse polynomial as a cylindrical potential (times `N`). -/
def convAll (N : ℕ) (p : SP) : CylPoly := p.flatMap (convT N)

/-- The conversion is exact: `N q` is an integer and the power of `R` is even, for every term. -/
def convOK (N : ℕ) (p : SP) : Bool := p.all fun t => (N * t.q).den == 1 && t.a % 2 == 0

/-- `D_R` converts exactly (kernel check). -/
theorem convOK_D : convOK NDn dDR = true := by kernel_fact
/-- `n_R / R` converts exactly (kernel check). -/
theorem convOK_nR : convOK NRn dnRh = true := by kernel_fact
/-- `n_{z,R}` converts exactly (kernel check). -/
theorem convOK_nZ : convOK NZn dnZR = true := by kernel_fact

/-! ## The field side -/

/-- The weight `w_k = a_k · scale k` of `∇P_k` in `field candidate`, times `L`. -/
def LWq (k : Fin 42) : ℚ :=
  Lw * (DommaschkQA2R.candidate k * DommaschkQA2R.scale k)

/-- The `L w_k` are integers (kernel check). -/
theorem LW_int : ((List.finRange 42).all fun k => (LWq k).den == 1) = true := by kernel_fact

/-- Drop the monomials with coefficient `0` (the formal derivatives produce many). -/
def nz (f : CylPoly) : CylPoly := f.filter fun m => m.c != 0

/-- `Σ_k L w_k f_k` (terms with `w_k = 0` omitted). -/
def Gpart (f : Fin 42 → CylPoly) : CylPoly :=
  (List.finRange 42).flatMap fun k => if LWq k == 0 then [] else cscale (LWq k).num (f k)

/-- `r₂³ (L + Σ_k L w_k (x ∂_y P_k − y ∂_x P_k))` (`= L R⁷ B_φ`). -/
def Gphi : CylPoly :=
  cmulMono ⟨1, 0, 0, 0, 3, 0⟩ (⟨(Lw : ℤ), 0, 0, 0, 0, 0⟩ :: Gpart fun k =>
    cmulMono ⟨1, 1, 0, 0, 0, 0⟩ (nz (d1 (DommaschkQA2R.P k))) ++
      cmulMono ⟨-1, 0, 1, 0, 0, 0⟩ (nz (d0 (DommaschkQA2R.P k))))

/-- `r₂³ Σ_k L w_k (x ∂_x P_k + y ∂_y P_k)` (`= L R⁷ B_R`). -/
def GRh : CylPoly :=
  cmulMono ⟨1, 0, 0, 0, 3, 0⟩ (Gpart fun k =>
    cmulMono ⟨1, 1, 0, 0, 0, 0⟩ (nz (d0 (DommaschkQA2R.P k))) ++
      cmulMono ⟨1, 0, 1, 0, 0, 0⟩ (nz (d1 (DommaschkQA2R.P k))))

/-- `r₂⁴ Σ_k L w_k ∂_z P_k` (`= L R⁸ B_z`). -/
def GZ : CylPoly := cmulMono ⟨1, 0, 0, 0, 4, 0⟩ (Gpart fun k => nz (d2 (DommaschkQA2R.P k)))

/-- The degree `a + b + 2s` in `R` of a monomial (invariant under `y² ↦ r₂ − x²`). -/
def rdeg (m : Mono) : ℤ := (m.a : ℤ) + m.b + 2 * m.s

/-- Normal-form check sliced by the degree in `R` (`ks`) and then by the power of `z` (`js`):
each slice is small enough for the quadratic normal form in the kernel. -/
def degCheck (js : List ℕ) : List ℤ → CylPoly → Bool
  | [], L => sliceCheck js L
  | k :: ks, L => sliceCheck js (L.filter fun m => rdeg m == k) &&
      degCheck js ks (L.filter fun m => !(rdeg m == k))

/-- The slices used: `z`-powers `0, …, 6`. -/
def zs : List ℕ := [0, 1, 2, 3, 4, 5, 6]

/-- The slices used: `R`-degrees `0, 2, …, 18`. -/
def rs : List ℤ := [0, 2, 4, 6, 8, 10, 12, 14, 16, 18]

/-- **`n_z = R⁸ B_z`** as a Cartesian identity (kernel check). -/
theorem ident_nZ :
    degCheck zs rs (cscale Lw (convAll NZn dnZR) ++ cscale (-NZn) GZ) = true := by
  kernel_fact

/-! ## Sanity -/

/-- **Sanity**: `(x² − y²)(2xy) = 2x³y − 2xy³`. -/
theorem trigC_fixture : trigC 1 1 = [⟨2, 3, 1, 0, 0, 0⟩, ⟨-2, 1, 3, 0, 0, 0⟩] := by kernel_fact

/-- **Sanity (rejected fixture)**: dropping the first term of `n_{z,R}` breaks the identity. -/
theorem ident_nZ_bad :
    degCheck zs rs (cscale Lw (convAll NZn dnZR.tail) ++ cscale (-NZn) GZ) = false := by
  kernel_fact

end PlasmaLean.Design.DommaschkKam
