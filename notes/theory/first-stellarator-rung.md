# The first genuinely stellarator rung: an exact rational vacuum field with rotational transform

Lane-A discovery note (Phase 6 input). Status tags follow `README.md`. **Nothing here is a compiled Lean
theorem.** Numerical work: Python/numpy/scipy/sympy in a scratch venv (`/tmp/laneA6`; scripts `cand.py`,
`fam.py`, `fine3.py`, `wba3.py`, `local.py`, `invfit.py`, `inveval2.py`, `feas.py`, `tf.py`). pyQSC/simsopt were
not needed. The algorithms are described below so the numbers can be reproduced without those files.

## 0. Verdict

1. **Candidate field (exact, proved informally, sympy-checked).** In cylindrical coordinates (R, φ, z), with
   R₀ = 1 and B₀ = 1:

   ```
   B_ε = ∇φ + ε ∇h,   h = f(R,z) cos 2φ + g(R,z) sin 2φ,
   f = ((R² − 1)² − 4z²) / (4R²),     g = −z ((R² − 1)(R² − 5) − 4z²) / (4R²),
   ```

   with **ε = 1/4**. In Cartesian coordinates, r₂ = x² + y²:

   ```
   ∇φ = (−y, x, 0)/r₂,    h = H/4,   H(x,y,z) = Hnum(x,y,z) / r₂²,
   Hnum = ((r₂ − 1)² − 4z²)(x² − y²) − 2xyz((r₂ − 1)(r₂ − 5) − 4z²).
   ```

   Hnum is a degree-6 polynomial, and ∇H = (Px, Py, r₂·Pz)/r₂³ with explicit degree-7 numerators (§1.2). B is
   **exactly** divergence- and curl-free on Ω = {r₂ > 0}, since ΔH = 0 there and ∇φ is the field of a line
   current on the z-axis. It is non-axisymmetric, has 2 field periods and is stellarator-symmetric. It has an
   **exact closed magnetic axis**, the unit circle R = 1, z = 0. The on-axis rotational transform is exactly
   **ι₀ = 1 − √(1 − 4ε²) = 1 − √3/2 ≈ 0.13397**, which is a quadratic irrational (Diophantine).
2. **Numbers (numerical observation).** Poincaré sections show nested surfaces out to an area-equivalent minor
   radius **r_eff ≈ 0.40** (aspect ratio ≈ 2.5). ι rises monotonically from 0.134 to ≈ 0.180 (positive shear).
   - The edge is the **2/11 island chain**, with width ≈ 0.021 in the launch radius along the φ = 3π/4 symmetry
     line. Outside it field lines are chaotic and lost.
   - Inside, the only resolved chain is **1/6**, width ≈ 5×10⁻⁴.
   - 1/7 and 2/13 are below the 5×10⁻⁵ resolution: with 2 periods, every resonance in the window has poloidal
     number m ≥ 11.
   - In r ≤ 0.3, B·∇φ > 0 and |B| ∈ [0.75, 1.55].
3. **Recommended proof route: (a), an approximate first integral.** A polynomial I in the structured basis of
   §2.1, fitted by least squares, has a field-line defect that falls **geometrically** with the order:
   - **tube r ≤ 0.1:** 5 → 126 → 1.9×10³ → 6.9×10⁴ → 1.7×10⁶ → 3.5×10⁷ guaranteed toroidal transits as the
     order K = 4…14;
   - **tube r ≤ 0.2:** up to 10⁶ transits.

   The certificate is a **3-variable polynomial inequality** checked on a box cover. It is cheap enough for Lean
   at K = 6 (≈ 6×10³ boxes, ≥ 40 certified transits). The Lean consequence is a finite-length confinement theorem
   on a *Maxwell-exact* non-axisymmetric field, which is the first in the library. Route (b), a posteriori KAM,
   is the long-term all-length upgrade (§2.3). Route (c), converse KAM, is an optional edge obstruction.
4. **Coils (§3).** A perturbation theorem composes route (a) with the library's maximum-principle error
   transfer. But the worst-case bound needs coil-field error η ≲ (I_b − I_a)/(2π n G): **η ≈ 10⁻⁷ for 10⁴
   transits**, far beyond the present Lipschitz surface cover (η ~ 10⁻²). Realistic paths: higher-order (Taylor)
   surface covers, or an exact harmonic surrogate of the coil field followed by refitting I. The 36-coil toroidal
   field (TF) ripple alone is 5×10⁻⁵.

---

## 1. The candidate field

### 1.1 Construction: Laurent-harmonic completions (proved informally, sympy-checked)

Write a harmonic function as F(R,z)·cos mφ. Then ΔF = F_RR + F_R/R + F_zz − m²F/R². For a seed R^s z^k with
s = ±m, define the completion

```
C_{s,k} = Σ_i c_i R^{s+2i} z^{k−2i},  c_0 = 1,  c_i = −c_{i−1}(k−2i+2)(k−2i+1) / ((s+2i)² − m²).
```

The sum telescopes, so C_{s,k} cos mφ is exactly harmonic. For s = −m the denominators are 4i(i − m), which are
nonzero for k < 2m. So the potential is a **rational** function with no logarithms; logarithms appear in
Dommaschk's general potentials at k ≥ 2m. In Cartesian form, R^m cos mφ = Re((x+iy)^m) and R^{−m} cos mφ =
Re((x+iy)^m)/r₂^m, so every term is a polynomial in x, y, z divided by a power of r₂.

For m = N = 2, the helical potential h = f cos 2φ + g sin 2φ is fitted to the local rotating-ellipse form
`h ≈ (u² − z²) cos 2φ + 2uz sin 2φ = Re[(u + iz)² e^{−2iφ}]`, with u = R − 1:
- f is even in z and uses C_{±2,0} and C_{±2,2};
- g is odd in z and uses C_{±2,1} and C_{±2,3};
- the constraints are f = f_R = 0, f_zz = −2, g_z = 0 and g_Rz = 2 at (1, 0).

This leaves 3 free coefficients (d, γ, δ). A grid search over them, keeping the member with the largest region of
surviving field lines, selected (d, γ, δ) = (−1, 0, 1). That member is the compact pair (f, g) in §0.

The simplest member (d = γ = δ = 0) is f₀ = R⁴/6 − R²z² − R²/4 + 1/(12R²) with g₀ = (R² − R⁻²)z/2. It has
nested surfaces only to ρ ≈ 0.12, with ι *decreasing* from 0.134 to 0.078. The higher (l = 3, 4) content of the
selected member supplies positive shear and quadruples the confinement radius.

### 1.2 Exact properties (each a short Lean target)

| Property | Statement | Proof idea |
| --- | --- | --- |
| Harmonic | ΔH = 0 on {r₂ > 0} | rational identity (sympy: Cartesian Laplacian simplifies to 0) |
| Vacuum | `VacuumField {x \| 0 < r₂ x} (field ε)` | B = ∇φ + ε∇h. C^∞ as a rational function. div B = ΔΦ = 0, curl B = curl ∇ = 0, via symmetric second derivatives or by direct `field_simp; ring` on the explicit Jacobian |
| Gradient | ∂ₓH = Px/r₂³, ∂_yH = Py/r₂³, ∂_zH = Pz/r₂² | Px, Py are degree 7 (≈ 20 monomials each); Pz = −2x⁵y − 4x³y³ + 12x³y − 8x²z − 2xy⁵ + 12xy³ + 24xyz² − 10xy + 8y²z |
| Exact axis | γ(t) = (cos t, sin t, 0) is a field line of B_ε for every ε | ∇H = 0 on the circle (f, g and their first derivatives vanish at (1, 0)), and ∇φ(γ t) = γ′(t) |
| Field periods | B_ε ∘ Rot_π = Rot_π ∘ B_ε | Hnum(−x,−y,z) = Hnum(x,y,z) |
| Stellarator symmetry | σ(x,y,z) = (y,x,−z) (rotation by π about the line x = y, z = 0): H ∘ σ = −H and φ ∘ σ = π/2 − φ, so B ∘ σ = −σB | polynomial identity |
| Non-axisymmetric | for ε ≠ 0, B_ε ∘ Rot_α ≠ Rot_α ∘ B_ε for some α | evaluate at one point |
| B_φ > 0 | 1 + ∂_φh ≥ 0.93 on r ≤ 0.3 (numerical; certify by cover) | needed to convert field-line parameter into toroidal transits |

### 1.3 Exact on-axis rotational transform (proved informally, numerically confirmed to 5 digits)

Parametrize field lines by φ: dR/dφ = R²h_R/(1 + h_φ) and dz/dφ = R²h_z/(1 + h_φ). Linearizing at the axis
(u, z) = 0 gives

```
v′ = 2ε S(φ) v,    S(φ) = [[cos 2φ, sin 2φ], [sin 2φ, −cos 2φ]]   (reflection through angle φ).
```

With v = Rot(φ) w this becomes autonomous: w′ = M w, with M = [[2ε, 1], [−1, −2ε]]. The eigenvalues are
±iκ, where κ = √(1 − 4ε²). Then:
- the fundamental matrix is Φ(φ) = Rot(φ)(cos κφ · I + (sin κφ/κ) M);
- the monodromy is Φ(2π) = exp(2πM), with trace 2cos 2πκ;
- the axis is elliptic for 0 < 4ε² < 1 with κ ∉ ℤ;
- the lab-frame rotation number is **ι₀ = 1 − κ**;
- the exact quadratic invariant of the linear flow is `I₂ = u² + z² + 2ε[(z² − u²) sin 2φ + 2uz cos 2φ]`, which
  follows from PM + MᵀP = 0 with P = [[1, 2ε], [2ε, 1]]. Its level sets are ellipses with axis ratio
  √((1+2ε)/(1−2ε)) = √3, rotating at half the toroidal rate.

For general N: M = [[2ε, N/2], [−N/2, −2ε]] and ι₀ = N/2 − √(N²/4 − 4ε²). This agrees with the numerics for
(N, ε) = (3, 0.4) → 0.2311 and (5, 0.8) → 0.579. Pythagorean choices of ε make ι₀ rational. For example ε = 3/10
gives ι₀ = 1/5, and this resonance was observed numerically. ε = 1/4 is deliberately chosen so that ι₀ is a
badly approximable quadratic irrational.

### 1.4 Poincaré numerics (numerical observation)

Method:
- Classical RK4 in φ with 200 steps per field period π. The step was checked by halving: section points agree
  to 10⁻⁸ after 200 periods.
- 1200 launch points per ray, 2500 periods each, on rays along z = 0 at the sections φ = 0, π/4, π/2 and 3π/4,
  inboard and outboard. The symmetry lines of σ lie in φ = π/4 and 3π/4.
- Classification uses the weighted Birkhoff average of the poloidal angle increment about the axis (Das–Saiki–
  Sander–Yorke 2017). "Digits" means agreement between the two halves of the orbit. Regular orbits show 8–14
  digits; RK4 drift caps the outer ones near 8.
- Local scans with 400 launch points and 4000 periods measure the island plateaus.

| Quantity | Value |
| --- | --- |
| ι on axis (numerical / exact) | 0.133975 / 1 − √3/2 = 0.1339746 |
| ι profile | monotone increasing: 0.1340 (axis), 0.1527 (r_eff 0.29), 0.169 (0.37), 0.1800 (0.40) |
| Nested-surface region | r_eff ≤ 0.40. At φ = 0 it spans R ∈ [≈0.60, 1.45]; surfaces are tilted ellipses with axis ratio ≈ √3 near the axis, shaped further out |
| Edge chain | ι = 2/11 (11 islands per section). Plateau 0.3365–0.3578 in launch radius ρ₀ (width 0.021) on the φ = 3π/4 outboard line; first losses just outside (ρ₀ = 0.371 there; ρ₀ = 0.274 on the φ = 3π/4 inboard line) |
| Internal chains | 1/6 (= 2/12): width ≈ 5×10⁻⁴ in ρ₀ (φ = π/4 inboard line, ρ₀ ≈ 0.4260–0.4264) with a thin stochastic layer (digits 4–5). 1/7 (= 2/14) and 2/13: no plateau at step 5×10⁻⁵ |
| Field magnitude | r ≤ 0.1: \|B\| ∈ [0.906, 1.119], B·∇φ ∈ [0.82, 1.24]. r ≤ 0.2: [0.82, 1.29], [0.68, 1.60]. r ≤ 0.3: [0.75, 1.55], [0.57, 2.18] |

Here r is the distance from the axis in the (R, z) plane, and r_eff = √(area/π) of the section curve.

Rejected or weaker candidates:
- (N, ε) = (2, 1/4) with the simplest (f₀, g₀): ρ_max ≈ 0.12;
- (3, 0.4) with the best (d, γ, δ): r ≈ 0.24, ι₀ = 0.231;
- (3, 0.5): ρ ≈ 0.04;
- (5, 0.8) and (5, 1.2): tiny or no region.

Larger N or ε raises ι₀ but shrinks the separatrix, which is the classical l = 2 trade-off.

---

## 2. What can be proved about field-line confinement

### 2.1 Route (a): approximate first integral (recommended)

**Theorem A (proved informally; elementary first-exit argument).** Let B: ℝ³ → ℝ³, let T be a closed set, and let
I be C¹ on a neighbourhood of T. Write K = T ∩ {I ≤ I_b}. Assume:
- (i) I > I_b on the frontier of T;
- (ii) |DI(x)·B(x)| ≤ δ for all x ∈ K.

Let γ be a forward field line (γ′ = B(γ)) with γ(0) ∈ T and I(γ(0)) ≤ I_a < I_b. Then for every
s ∈ [0, (I_b − I_a)/δ) we have γ(s) ∈ T and I(γ(s)) ≤ I_a + δs.

Proof sketch:
- Let s₁ be the supremum of the times up to which the curve stays in K.
- On [0, s₁], `Kinetic.invariant_drift` gives I ≤ I_a + δs < I_b.
- At s₁, either I = I_b (contradiction) or γ reaches the frontier of T (contradiction with (i)).
- Continuity then extends past s₁.

If in addition |B| ≥ b_min on K, the confined line has arc length at least b_min·(I_b − I_a)/δ.

**Basis.** Use the polynomials s^j z^k · Re/Im((x + iy)^{2n}) with s = (r₂ − 1)/2, 2 ≤ j + k ≤ K for n = 0 and
0 ≤ j + k ≤ K for 1 ≤ n ≤ M. These are Cartesian polynomials whose span equals that of the functions
u^j z^k {cos, sin}(2nφ) near R = 1. The defect R⁶·(B·∇I) is then a Cartesian polynomial.

**Fit.** Minimize Σ |dI/dφ|²/r² over random points in the tube, relative to Σ I²/r⁴. This is the smallest
generalized singular vector: a plain constraint on one coefficient yields degenerate I. Normalize the z²
coefficient to 1. The quadratic part reproduces I₂ of §1.3: the fitted coefficients are (1, 1, −0.51, 1.00, 0.49)
against the exact (1, 1, −1/2, 1, 1/2).

**Evaluation.** On a 100×96×40 grid in (r, θ, φ):
- I_b = min of I over the tube boundary;
- δ_φ = max |dI/dφ| on {I ≤ I_b};
- transits = (I_b − I_a)/(2π δ_φ).

| Tube | (K, M) | basis | δ_φ | transits, I_a = I_b/4 (r_in) | transits, I_a = I_b/2 (r_in) | r covered by {I ≤ I_b} |
| --- | --- | --- | --- | --- | --- | --- |
| 0.1 | (2,1) | 15 | 1.2e-3 | 0.47 | 0.31 | 0.052 |
| 0.1 | (4,2) | 72 | 1.1e-4 | 4.9 (0.027) | 3.2 (0.038) | 0.055 |
| 0.1 | **(6,3)** | 193 | 4.3e-6 | **126** | 84 | 0.055 |
| 0.1 | (8,4) | 402 | 2.9e-7 | 1.9e3 | 1.3e3 | 0.055 |
| 0.1 | (10,5) | 723 | 7.9e-9 | 6.9e4 | 4.6e4 | 0.055 |
| 0.1 | (12,6) | 1180 | 3.3e-10 | 1.7e6 | 1.1e6 | 0.055 |
| 0.1 | (14,7) | 1797 | 1.6e-11 | 3.5e7 | 2.3e7 | 0.055 |
| 0.2 | (10,5) | 723 | 7.5e-7 | 2.8e3 (0.053) | 1.8e3 (0.073) | 0.103 |
| 0.2 | (14,7) | 1797 | 2.2e-9 | 9.6e5 | 6.4e5 | 0.103 |
| 0.3 | (14,7) | 1797 | 1.2e-6 | 3.5e3 (0.073) | 2.3e3 (0.103) | 0.145 |

r_in is the radius of the disk (all φ) contained in {I ≤ I_a}. These are grid maxima, not rigorous suprema; a
rigorous cover is expected to cost about a factor 2 in δ.

**Cross-check.** Traced field lines show |I − I₀|/I₀ ≈ 3×10⁻³, 3×10⁻⁵ and 4×10⁻⁷ over 300 transits for
K = 6, 8, 10. They oscillate with no secular drift: the true lines lie on KAM tori, so the linear-in-length bound
is pessimistic.

**Physical scale.** At R₀ = 10 m, a 3.5 MeV alpha travels ≈ 5×10⁶ m (≈ 8×10⁴ transits) during slowing-down.
Field-line confinement over that length needs K ≈ 10–12 in a tube with aspect ratio 5–10, which is within reach
of the same method. (Field-line confinement is not guiding-centre confinement; see the caveats in §5.)

**Conversion to the Lean parameter.** Lean field lines use the parameter s (m/T), and dI/ds = (B·∇φ)·dI/dφ. On
r ≤ 0.1, B·∇φ ≤ 1.25 and |B| ≥ 0.906. For (K, M) = (6, 3) this gives δ_s ≤ 5.3×10⁻⁶, a confinement parameter
s* ≈ 630 and a length ≥ 570 R₀ ≈ 90 transits. With a factor 2 kept for the rigorous cover: **s* = 300, length
≥ 270 R₀ ≈ 43 transits.**

**Certificate cost (estimate).** A first-order (mean-value) box cover of the defect polynomial over a quarter
period (2-fold symmetry and stellarator symmetry reduce φ to [π/4, 3π/4]) needs about:
- 7.6×10² boxes at (4,2);
- 5.8×10³ boxes at (6,3);
- 9.6×10³ boxes at (8,4);
- 5.7×10⁴ boxes at (10,5) in the 0.2 tube.

The estimate uses sampled Lipschitz constants with a factor 2 margin. Phase 5's `CoverCert` handled 324 leaves
of a comparable polynomial in 59 s, so (4,2) and (6,3) are feasible now and (8,4) is feasible with the
fixed-point interval library. For φ, use the rational circle parametrization (1 − t²)/(1 + t²) and 2t/(1 + t²)
on t ∈ [tan(π/8), tan(3π/8)] after clearing denominators, so that the cover is purely polynomial in (u, z, t).

### 2.2 Route (c): converse KAM / island obstruction (optional, later)

The MacKay–Percival (1985) cone-crossing criterion certifies that *no* rotational invariant circle passes through a
region. This is a finite validated orbit-and-tangent computation, and it would bound the confinement radius from
above (≈ the 2/11 chain at r_eff ≈ 0.40). It needs validated ODE integration of the Poincaré map, which the
library lacks. It is useful as an honesty check on the outer edge, not as a confinement result.

### 2.3 Route (b): a posteriori KAM (long term)

Candidate theorems:
- **de la Llave–González–Jorba–Villanueva 2005** (*Nonlinearity* 18, 855): KAM without action-angle variables,
  for exact symplectic maps. Its constants are not tracked explicitly.
- **Figueras–Haro–Luque 2017** (*Found. Comput. Math.* 17, 1123): the same a posteriori scheme with *fully
  explicit* constants, applied by computer assistance to the standard and Froeschlé maps. **This is the most
  formalizable published version.**
- For vector fields, the parameterization-method monograph (Haro–Canadell–Figueras–Luque–Mondelo 2016, Springer
  AMS 195, ch. 4) contains the flow analogue.

Recommended formulation for this field, which avoids validated ODE integration: seek a torus K: 𝕋² → (R, z) and
solve the **invariance equation for the φ-dependent vector field directly**,
`∂_φK + ι ∂_θK = X(K, φ)`, where X = (R²h_R, R²h_z)/(1 + h_φ) is an explicit rational function. Then:
- the error e = ∂_φK + ι∂_θK − X(K, φ) is a composition of rationals with a Fourier series, which can be bounded
  in the library's ℓ¹_ν Banach algebra (`Certificates/WeightedEll1`, `ConvAlgebra`);
- ι can be chosen as a noble number near the axis value;
- the twist is supplied by the positive shear of §1.4.

Obstacle: the KAM theorem itself (shrinking analytic strips, small divisors, Rüssmann estimates) must be
formalized. That is months of work, not a Phase 6 deliverable. Route (a) is the right first rung: its conclusion
is weaker (finite length) but it composes with coil errors (§3) and is checkable now.

---

## 3. Linking to coils (sketch)

1. **What is exact.** B₀R₀∇φ is exactly the field of an infinite straight current I = 2πB₀R₀/μ₀ on the z-axis.
   ε∇h grows like R² at large R, so it must come from sources *outside* the plasma region, such as helical windings
   or modular coils on a winding surface. A finite filament set cannot reproduce B exactly, so the link is always
   an error estimate.
2. **Composable transfer (proved informally).** Let Ω_T be a bounded open torus around the tube that excludes the
   coils and the z-axis. Then:
   - if the coil field B_c and B are both `VacuumField Ω_T` and |B_c − B| ≤ η on the frontier of Ω_T, then
     `VacuumField.error_le_of_frontier` gives |B_c − B| ≤ η in Ω_T;
   - with G = sup ‖∇I‖ on K, the defect of I for B_c is at most δ + ηG;
   - so Theorem A holds for the coil field with confinement parameter (I_b − I_a)/(δ + ηG).

   B_c is vacuum on Ω_T by `filamentField_vacuum_maxwell` / `Sanity.filamentField_vacuumField'`; the
   boundary bound comes from `Theory/Geometry/SurfaceCover` and `volume_error_of_boundary_samples`.
3. **Numbers (numerical observation).**
   - **Sensitivity:** on the 0.1 tube, G ≈ 0.2 and I_b − I_a ≈ 3.4×10⁻³, so n transits require
     η ≤ 2.7×10⁻³/n: **η ≈ 3×10⁻⁵ for 100 transits and 3×10⁻⁷ for 10⁴.**
   - **TF ripple:** replacing the line current by N_TF circular TF coils of minor radius a_c centred on R = 1
     gives a maximum relative ripple error in r ≤ 0.2 of
     - 0.12 for (N_TF, a_c) = (12, 0.5);
     - 2.7×10⁻² for (18, 0.5);
     - 7.1×10⁻³ for (24, 0.5);
     - 8.7×10⁻³ for (18, 0.6);
     - 4.9×10⁻⁵ for (36, 0.6).

     The helical part has a similar exponential trade-off between winding-surface distance and the number of
     filaments, as in NESCOIL/REGCOIL current-potential designs (Merkel 1987; Landreman 2017).
   - **Present certification ability:** a Lipschitz (first-order) surface cover with ~10⁴–10⁵ samples gives
     η ~ L·h ~ 10⁻²–10⁻³, which is **less than one certified transit.** This is an obstruction for the current
     tooling, recorded honestly.
4. **Paths that work.** Either:
   - (i) a **degree-p Taylor surface cover**: cost ~ (C/η)^{2/(p+1)}, so p = 6 reaches η ~ 10⁻⁶–10⁻⁷ with
     ~10⁵ samples, but it needs higher-derivative bounds for Biot–Savart (Cauchy estimates); or
   - (ii) a **harmonic surrogate**: fit the coil field by an exact rational Laurent-harmonic series B_fit (§1.1
     basis, many modes), certify |B_c − B_fit| ≤ η on the frontier of Ω_T, then *refit I to B_fit* (polynomial
     again). Ripple and helical-winding errors that are non-resonant are absorbed into I instead of entering the
     worst-case bound. Only the residual η of the surrogate, which converges exponentially because B_c is
     analytic in Ω_T, enters linearly.

   Option (ii) reuses every piece of route (a) and is the recommended M5 path.

---

## 4. Lean modules (proposed statements)

All in `namespace PlasmaLean.Design.RationalStellarator`, with `Space = EuclideanSpace ℝ (Fin 3)`. The first
three modules contain no numerics.

**Module 1: `Design/RationalStellarator/Field.lean`** (≈ 1 agent-day, 400–700 lines)

```lean
def r2 (x : Space) : ℝ := x 0 ^ 2 + x 1 ^ 2
def Hnum (x : Space) : ℝ := ((r2 x - 1) ^ 2 - 4 * x 2 ^ 2) * (x 0 ^ 2 - x 1 ^ 2)
  - 2 * x 0 * x 1 * x 2 * ((r2 x - 1) * (r2 x - 5) - 4 * x 2 ^ 2)
def H (x : Space) : ℝ := Hnum x / r2 x ^ 2
def gradH (x : Space) : Space := toLp 2 ![Px x / r2 x ^ 3, Py x / r2 x ^ 3, Pz x / r2 x ^ 2]
def toroidal (x : Space) : Space := toLp 2 ![-x 1 / r2 x, x 0 / r2 x, 0]
def field (ε : ℝ) (x : Space) : Space := toroidal x + (ε / 4) • gradH x
def domain : Set Space := {x | 0 < r2 x}

theorem H_hasGradientAt {x} (hx : x ∈ domain) : HasGradientAt H (gradH x) x
theorem field_vacuum (ε : ℝ) : Vacuum.VacuumField domain (field ε)
theorem axis_fieldLine (ε : ℝ) :
  Fields.IsForwardFieldLine (field ε) (fun t => toLp 2 ![Real.cos t, Real.sin t, 0])
theorem field_rotPi (ε) (x) : field ε (rotPi x) = rotPi (field ε x)          -- 2 field periods
theorem field_stellSym (ε) (x) : field ε (σ x) = - σ (field ε x)              -- σ(x,y,z) = (y,x,-z)
theorem field_not_axisymmetric {ε} (hε : ε ≠ 0) : ¬ ∀ α x, field ε (rotZ α x) = rotZ α (field ε x)
```

Here Px, Py and Pz are the explicit numerators of §1.2. The vacuum proof follows `HelicalDivergence` and
`ClebschTorusDivergence`: an explicit `HasFDerivAt` for each component, then `field_simp; ring` for div and curl.
C² follows from `ContDiffOn` of rational functions on the domain.

**Module 2: `Design/RationalStellarator/AxisMonodromy.lean`** (≈ 1 agent-day)

```lean
def S (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![cos (2*φ), sin (2*φ); sin (2*φ), -cos (2*φ)]
def κ (ε : ℝ) : ℝ := Real.sqrt (1 - 4 * ε ^ 2)
def Φ (ε φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  rot φ * (cos (κ ε * φ) • 1 + (sin (κ ε * φ) / κ ε) • !![2*ε, 1; -1, -2*ε])
/-- The φ-parametrized field-line vector field X(u,z,φ) = R²(h_R, h_z)/(1 + h_φ) has Jacobian 2ε S(φ) at the axis. -/
theorem axis_jacobian (ε φ : ℝ) : jacobianAtAxis ε φ = (2 * ε) • S φ
theorem Φ_solves {ε} (h : 4 * ε ^ 2 < 1) (φ : ℝ) :
  HasDerivAt (Φ ε) ((2 * ε) • S φ * Φ ε φ) φ ∧ Φ ε 0 = 1
theorem monodromy_trace {ε} (h : 4 * ε ^ 2 < 1) : (Φ ε (2 * π)).trace = 2 * cos (2 * π * κ ε)
theorem axis_elliptic : |(Φ (1/4) (2 * π)).trace| < 2        -- κ = √3/2, ι₀ = 1 − √3/2
theorem I₂_invariant (ε φ) (v) : quadratic invariant of v′ = 2ε S(φ) v (exact identity)
```

The derivative identity is a 2×2 trig identity; `monodromy_trace` uses rot(2π) = 1. For `axis_elliptic`,
|2cos(√3π)| ≈ 1.33. It needs a rigorous enclosure of cos(√3π); alternatively state ι₀ = 1 − κ as a
rotation-number statement for the explicit linear flow.

**Module 3: `Theory/Fields/ApproxFirstIntegral.lean`** (generic, ≈ 1 agent-day)

```lean
theorem fieldLine_confined_of_defect {B : Space → Space} {I : Space → ℝ} {T : Set Space}
    {Ia Ib δ : ℝ} (hT : IsClosed T) (hδ : 0 < δ)
    (hI : ∀ x ∈ T, DifferentiableAt ℝ I x) (hIc : ContinuousOn I T)
    (hfront : ∀ x ∈ frontier T, Ib < I x)
    (hdef : ∀ x ∈ T, I x ≤ Ib → |fderiv ℝ I x (B x)| ≤ δ)
    {γ : ℝ → Space} (hγ : IsForwardFieldLine B γ) (h0 : γ 0 ∈ T) (hIa : I (γ 0) ≤ Ia) :
    ∀ s, 0 ≤ s → δ * s < Ib - Ia → γ s ∈ T ∧ I (γ s) ≤ Ia + δ * s
theorem defect_of_perturbation {B B' : Space → Space} {I} {K : Set Space} {δ η G : ℝ}
    (hdef : ∀ x ∈ K, |fderiv ℝ I x (B x)| ≤ δ) (hη : ∀ x ∈ K, ‖B' x - B x‖ ≤ η)
    (hG : ∀ x ∈ K, ‖gradient I x‖ ≤ G) (hη0 : 0 ≤ η) :
    ∀ x ∈ K, |fderiv ℝ I x (B' x)| ≤ δ + η * G
theorem fieldLine_length_of_confined : arc length ≥ b_min * s on [0, s] when ‖B‖ ≥ b_min along γ
```

Sanity corollaries:
- δ → 0 recovers `sublevel_confined`;
- a uniform field with I = ‖x‖² gives an explicit escape bound, consistent with `Sanity.ProbeEscape`;
- `defect_of_perturbation` with η = 0.

**Module 4 (certificate): `Design/RationalStellarator/ConfinementCert.lean`**

- I is the (6,3) polynomial, 193 terms with dyadic rational coefficients. The tube is
  T = {((r₂ − 1)/2)² + z² ≤ (1/10)²}.
- The obligations are three polynomial cover certificates, proved as `CoverCert`-style proof terms:
  - **defect:** |r₂³·(B·∇I)| ≤ δ̃ on T ∩ {I ≤ I_b}, with about 6×10³ leaves;
  - **frontier:** I > I_b on the frontier of T, a 2-D cover;
  - **inner set:** a disk of radius ≥ 0.025 lies in {I ≤ I_a}.
- Headline theorem `rationalStellarator_confined`: every field line of `field (1/4)` starting within distance
  1/40 of the unit circle stays in T for s ∈ [0, 300], hence over a length ≥ 270 (≈ 43 transits).
- Estimated build: 15–40 min with the present checkers. The (4,2) version is a ~10× smaller "hello world" with
  about 3 transits. The new infrastructure needed is a 3-variable polynomial interval/centered-form evaluator
  (`Certificates/PolyBox3`).

**Feasibility.** Modules 1–3: about one cycle, with low risk (all identities are rational or trig algebra). Module
4: one further cycle; the risk is build time, mitigated by the (4,2) fallback and by symmetry reduction. The K = 10
version (≈ 2×10⁴ certified transits) needs the fixed-point interval library and a centered form, about 5×10⁴
leaves. That is a Phase 7 stretch.

---

## 5. Caveats and counterexample checks

- **Field-line, not particle, confinement.** The Lean parameter s has units m/T, and the length bound is a
  field-line statement. Guiding-centre confinement in this field is a separate (M4/M5) question. The field is
  vacuum (β = 0), so it carries no plasma equilibrium.
- **The bound is worst-case linear in length.** It certifies a finite length only. All-length confinement needs
  route (b). Traced lines show no drift, so the conservatism is in the theorem, not in the field.
- **Numerics.** RK4 is not symplectic; it caps the Birkhoff digits near 8 for the outer orbits, but the step was
  verified by halving. Island widths are plateau widths along symmetry lines; the plateaus might pass through
  X-points, in which case the widths are lower bounds there. δ values are grid maxima. The first-exit theorem
  needs the frontier and defect bounds *on the whole set*, and the cover provides that; no sample grid enters a
  theorem.
- **Global structure.** h grows like R² and has a singularity on the z-axis, so the field is only meaningful on
  a bounded torus away from R = 0. That is all every statement uses (T ⊂ {r₂ > 0}).
- **Symmetry pitfall found.** The naive stellarator-symmetric basis (cos with even z-powers) is wrong for this h:
  the symmetry is σ(x,y,z) = (y,x,−z), so the symmetric sections are φ = π/4 and 3π/4, not φ = 0. Fitting with the
  naive parity gave I ≈ s² + z², contradicting the √3 tilted ellipses. The full basis fixed this.
- **Degenerate normalization pitfall.** Least squares with only "z²-coefficient = 1" returns I ≈ z² (a small
  absolute but O(1) relative defect). Normalization must be relative (generalized SVD).

## 6. Sources (from memory; verify locators before citing in Lean docstrings)

- W. Dommaschk, *Representations for vacuum potentials in stellarators*, Comput. Phys. Commun. **40** (1986) 203.
- S. Das, Y. Saiki, E. Sander, J. A. Yorke, *Quantitative quasiperiodicity*, Nonlinearity **30** (2017) 4111.
- R. de la Llave, A. González, À. Jorba, J. Villanueva, *KAM theory without action-angle variables*, Nonlinearity
  **18** (2005) 855.
- J.-Ll. Figueras, À. Haro, A. Luque, *Rigorous computer-assisted application of KAM theory: a modern approach*,
  Found. Comput. Math. **17** (2017) 1123.
- À. Haro, M. Canadell, J.-Ll. Figueras, A. Luque, J. M. Mondelo, *The Parameterization Method for Invariant
  Manifolds*, Springer Appl. Math. Sci. **195** (2016).
- R. S. MacKay, I. C. Percival, *Converse KAM: theory and practice*, Commun. Math. Phys. **98** (1985) 469.
- P. Merkel, Nucl. Fusion **27** (1987) 867 (NESCOIL); M. Landreman, Nucl. Fusion **57** (2017) 046003 (REGCOIL).

Novelty is **provisional and not claimed.** The rotating-ellipse ι₀ formula is classical in spirit; the specific
rational potential and the certificate design are this note's.

## 7. Next dependency

Modules 1–3, then `Certificates/PolyBox3`, then Module 4 at (4,2) and then (6,3). In parallel, M5 option
3(ii): a Laurent-harmonic surrogate fit of the existing four-coil (CNT-type) dataset once VD1 freezes it.
