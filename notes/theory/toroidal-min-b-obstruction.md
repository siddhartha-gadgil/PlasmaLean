# Why exact minimum-B / maximum-J is restricted in toroidal fields

**Lane:** A (theory discovery), Cycle 1, track T1/T8. **Date:** 2026-10-20.
**Replaces:** the false "subharmonic ⇒ no interior minimum of |B|" claim (implementation plan §1.1).
**Scratch computations:** `/tmp/lanea/minb.py` (sympy, outside the repo; reproduced inline below).

Status tags used: **[published]** = theorem/argument located in the cited source, with locator;
**[published, formal asymptotic]** = near-axis/ordering result, not a rigorous theorem;
**[proved informally]** = complete elementary proof given here; **[conjectured]**; **[lead]** = source
suggested but the claimed statement was *not* located.

---

## 0. What subharmonicity actually gives (and does not)

For a vacuum field (div B = 0, curl B = 0, C² on open Ω ⊂ ℝ³), Δ|B|² = 2‖∇B‖²_F ≥ 0.

* **[proved informally]** |B|² has no strict interior local **maximum**: by the weak maximum principle
  max over the closure of a small ball is attained on its boundary sphere. (Lean: `vacuum_normSq_no_strict_interior_max`.)
* **Counterexample to the old claim (exact, sympy-checked).** B = ∇(½(x²+y²) − z²) = (x, y, −2z):
  harmonic potential, |B|² = x² + y² + 4z², strict minimum at 0 (Hessian eigenvalues 2, 2, 8).
* **Counterexample with |B| ≠ 0 at the minimum (Ioffe–Pritchard).**
  Φ = B₀z + c(z³ − (3/2)z(x²+y²)) + (g/2)(x² − y²), ΔΦ = 0. At 0: |B|² = B₀², ∇|B|² = 0,
  Hessian = diag(2g² − 6B₀c, 2g² − 6B₀c, 12B₀c): a strict minimum iff c > 0 and g² > 3B₀c
  (checked with B₀ = 1, c = 1, g = 2: eigenvalues 2, 2, 12). Note the field line through the minimum
  (the z-axis) is **straight** — this is forced, see §1.

So the obstruction to min-B in a torus is *not* a maximum principle. It is a local curvature identity
plus the topology of a closed axis.

---

## 1. The curvature identity and its consequences

### Theorem A (curvature identity) — [published] Helander (2014) Eq. (24); vacuum case [proved informally, sympy-checked]

Let b = B/|B|, κ = (b·∇)b, ∇⊥ = ∇ − b(b·∇).

* **Vacuum.** If B is C¹ with symmetric Jacobian (curl B = 0) on an open set, then
  ∇(|B|²/2) = (DB)ᵀB = (DB)B = (B·∇)B. Where B ≠ 0 this gives **∇⊥|B| = |B| κ**.
  (Proof: (B·∇)B = |B|(b·∇|B|) b + |B|² κ.) sympy: `grad|B|^2/2 − (B·∇)B = 0` for B = ∇Φ.
* **Finite β (MHS).** With J×B = ∇p and μ₀J = ∇×B:  κ = μ₀∇p/B² + ∇⊥B/B
  (Helander, *Theory of plasma confinement in non-axisymmetric magnetic fields*, Rep. Prog. Phys. 77
  (2014) 087001, §2.4, Eq. (24); open-access preprint at pure.mpg.de). Hence **∇⊥B = Bκ wherever ∇p = 0**,
  in particular on the magnetic axis when p = p(ψ) is C¹ in ψ and ∇ψ = 0 on the axis.

Hypotheses: C¹ field, B ≠ 0 at the point; for finite β, ideal MHS force balance and ∇p = 0 at the point.

### Corollary B (a minimum of |B| forces a straight field line there) — [proved informally]

If |B| has a local minimum (indeed any critical point) at x with B(x) ≠ 0, in vacuum or at a point where
∇p(x) = 0, then κ(x) = 0. More weakly: if |B| restricted to the plane normal to B at x has a critical point
at x, then κ(x) = 0 (only ∇⊥B enters).

### Corollary C (no minimum-B around a closed magnetic axis) — [proved informally]; argument is Helander (2014) §3.3

*Statement.* Let Γ be a closed C² field line (magnetic axis) with B ≠ 0 on Γ, in a vacuum region or with
∇p = 0 on Γ. Then it is impossible that for every x ∈ Γ, |B| restricted to the normal plane at x has a
local minimum at x ("|B| non-decreasing outward from the axis in every direction").

*Proof.* By Corollary B, κ ≡ 0 on Γ. Parametrize Γ by arc length: γ'' = κ n = 0, so γ is affine with
|γ'| = 1, which cannot be periodic. ∎ (Quantitatively, Fenchel: ∮κ ds ≥ 2π for a closed curve.)

*Source.* Helander (2014) §3.3 ("Orbit confinement in a torus", after Eq. (64)) uses exactly this
argument to show |B| = B(ψ) (isodynamic, no trapped particles) and quasi-poloidal symmetry are impossible
near the axis: "the field strength thus increases in the direction of the curvature vector … But the
curvature must be finite somewhere along the magnetic axis".

### Theorem D (what maximum-J actually requires) — [published] Helander (2014) §3.7

For deeply trapped particles in an omnigenous field, v_d·∇α = (v⊥²/2Ω) ∂B/∂ψ at B = B_min; correct
(maximum-J, ∂J/∂ψ < 0) precession needs **∂B/∂ψ > 0 at B_min**, so B has a local minimum on the axis at the
B_min point and, by Eq. (24), **the axis curvature vanishes there**. Helander adds that finite pressure
(diamagnetic effect) makes such a minimum easier to reach than in vacuum.

So maximum-J is not forbidden in a torus. It forces **zero curvature at the B_min points of the axis**,
and Corollary C forbids the *global* (all-axis) version.

### Theorem E (QS fields cannot be maximum-J) — [published, formal asymptotic]

Rodríguez, Helander & Goodman, *The maximum-J property in quasi-isodynamic stellarators*, J. Plasma Phys.
90, 905900212 (2024), arXiv:2311.14439. Abstract: "this property cannot be attained in quasisymmetric
stellarators, in which deeply trapped particles experience average bad curvature and therefore precess in
the diamagnetic direction close to the magnetic axis". §2.3 and Eq. (11):
ω_α^QS ≈ −(mv²/2q)(η/(rB₀))(2E(k)/K(k) − 1), so in QS there are always trapped particles precessing in
opposite directions. They rely on Rodríguez & Mackenbach, JPP 89, 905890521 (2023). Also §2.3 point 1:
in near-axis omnigenous (QI) fields omnigeneity must break at first order near the well tops, so there is a
finite r_a inside which particles trapped near the well tops are not maximum-J. QI near-axis maximum-J needs
binormal elongation ᾱ < 1 and sufficient torsion (vacuum: τ₀L_B > √(R_M/2)) (§2.4.3). These are near-axis
expansions, not rigorous theorems.

### Theorem F (exact omnigenity is restricted) — [published]

* Cary & Shasharina, *Omnigenity and quasihelicity in helical plasma confinement systems*, Phys. Plasmas
  4, 3323 (1997), doi:10.1063/1.872473. Abstract: exactly omnigenous magnetic strengths far from
  quasihelical are all **nonanalytic**, though analytic truncations can be arbitrarily close.
* Helander (2014) §3.8 ("Negative results"): exact quasi-isodynamic fields must be quasi-poloidally
  symmetric, so "only quasisymmetric fields are omnigenous" (attributed to Cary & Shasharina). Combined
  with §3.3, exact QI is impossible near a curved axis. Garren & Boozer (Phys. Fluids B 3, 2805 and 2822 (1991); page numbers from memory, not re-checked):
  QS can hold on one surface but is broken at third order in the near-axis expansion
  ([published, formal asymptotic], as quoted in Helander §3.8).
* Bernardin, Moses & Tataronis, *Isodynamical (omnigenous) equilibrium in symmetrically confined plasma
  configurations*, Phys. Fluids 29, 2605 (1986), doi:10.1063/1.865501. Abstract: with one ignorable
  coordinate, isodynamic (|B| = B(ψ)) equilibria fall into three classes: straight axis; curved axis with
  B = 0 on axis; or curved axis with finite B and **open** surfaces. This matches Corollary C (curved axis
  plus finite B on axis is incompatible with closed surfaces). Only the abstract was read; the full text was not.

### Conjecture G — [conjectured]

Chaining E and F: no analytic toroidal MHS field is simultaneously exactly omnigenous on a neighbourhood
of the axis and maximum-J for all trapped particles. This chains asymptotic results, so treat it as a
conjecture. It is not a theorem.

### Leads (not located; do not cite as theorems)

* Hall & McNamara, Phys. Fluids 18, 552 (1975), doi:10.1063/1.861189. Located bibliographically and
  widely cited for **introducing omnigenity** and for the magnetostatic formulation of anisotropic guiding-centre
  equilibria. No min-B impossibility statement was found (full text paywalled). **[lead]**
* Landreman & Catto (near-axis omnigenity / max-J): not searched in detail. **[lead]**
* Infeld (1975), "Class of quasi-minimum B toroidal equilibria" (OSTI 6279916): uses the term
  "quasi-minimum-B" for tori; the abstract claims no impossibility theorem. **[lead]**

---

## 2. Formalizability (recommended Lean targets)

| Target | Content | Difficulty | Status |
| --- | --- | --- | --- |
| `vacuum_normSq_no_strict_interior_max` | from subharmonicity + weak max principle (T1) | medium (needs WMP) | in plan |
| `vacuum_minB_counterexample` | B = (x,y,−2z) is a vacuum field, ‖B‖² has strict min at 0 | easy (polynomial) | ready now |
| `grad_normSq_half_eq_directional` | pointwise: ∇(‖B‖²/2) = (DB)ᵀB, and = (DB)B when DB is symmetric; so a critical point of ‖B‖² gives (B·∇)B = 0 | easy (finite-dim linear algebra) | ready now |
| `curvature_zero_of_normSq_critical` | B(x) ≠ 0, DB(x) symmetric, ∇‖B‖²(x) = 0 ⇒ κ(x) = 0 | easy | ready now |
| `closed_axis_not_minB` | an arc-length C² curve with γ'' ≡ 0 is not periodic; with the above, Corollary C | easy–medium | ready now |
| finite-β version | add ∇p(x) = 0 and MHS; Eq. (24) as identity | medium | Cycle 2 |
| Theorems D–F | only as *cited interfaces* (docstring locators), not proved | n/a | cite only |

Design implication: maximum-J candidates (M4) should be checked for **κ = 0 at every B_min point of the
axis**. A near-axis QS candidate should not be advertised as maximum-J (Theorem E).
