# Patch to N-32: orientation of the holomorphic lift

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-37` |
| Title | Orientation convention for the anti-self-dual lift of a vacuum field (patch to N-32) |
| Kind | patch |
| Addresses | `Q-24`, `Q-25` (context only); `N-21`, `N-32` |
| Depends on | N-32 (summary item 5), N-36 (claim 30) |
| Dependency requirement | none (convention) |
| Produces | the corrected statement below; audit item AK-3 resolved by this note |
| Difficulty | routine |
| Status | verified by exact computation (`scripts/kinetic_brief/check_brief.py`, checks 11–12) |
| Lean evidence | none (the lift is not formalized); no declaration affected |
| Audit evidence | AK-3 (low, prose), resolved by this patch |
| Last updated | 4 November 2026: created |
| Patches | N-32, "Summary of the brief", item 5 (Holomorphic lift), and any later statement that ℱ is anti-self-dual |

## Patched item

**Original (N-32, item 5):** "On X = Ω × ℝ_t with ℱ = β + dt ∧ α, ℱ is closed and anti-self-dual, so
B is a Hermitian–Yang–Mills line bundle (abelian Bogomolny)."

**Replacement:** On X = Ω × ℝ_τ, let α = B♭ and β = ∗₃α = ι_B vol₃. With the orientation
dτ ∧ dx₁ ∧ dx₂ ∧ dx₃:
- dτ ∧ α + β is **self-dual**;
- dτ ∧ α − β is **anti-self-dual**.

Swapping either the sign of β or the orientation (vol₃ ∧ dτ = −dτ ∧ vol₃) exchanges the two. So
"ℱ = β + dt ∧ α is ASD" holds for the orientation vol₃ ∧ dt. The kinetic/coil brief (N-36, §7.3)
uses F = dτ ∧ α − ∗₃α with orientation dτ ∧ vol₃. In either convention:
- the form is closed iff dα = 0 and d∗₃α = 0 (for τ-independent α);
- with the complex structure z₁ = τ + ix₁, z₂ = x₂ + ix₃ (whose orientation is dτ ∧ vol₃), the ASD
  forms are the primitive (1,1) forms.

**Reason.** N-32 states the duality without an orientation. The kinetic brief's sanity check B.5
asks for the Hodge-star sign to be verified, and checks 11–12 of `check_brief.py` do so: ∗₄ computed
from the Levi-Civita symbol on ℝ⁴.

**Effect on Lean:** none. No declaration encodes the lift. The compiled Q-25 results
(`Fields.QSLinear.*`, `Design.QSJetExample.*`, `Design.RationalStellaratorJetObstruction.*`) use
only ι_u β = dΨ, i.e. B × u = ∇Ψ, which is orientation-consistent with the brief (N-36, claim 28).
N-32's conclusion stands: the lift re-encodes the unique vacuum field and produces no new fields.
