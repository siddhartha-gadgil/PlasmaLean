# From finite-length to all-time field-line confinement in the rational stellarator: the KAM route

Lane-A discovery note (Phase 8 input). Status tags follow `README.md`. **Nothing here is a compiled Lean
theorem.**
- Numerics: Python/numpy/scipy/sympy (venv `/tmp/laneA6/venv`) in `/tmp/laneA7/scripts`: `fieldmap.py`,
  `profile.py`, `dioph.py`, `torus.py`, `flowtorus.py`, `twist.py`, `area.py`. Logs are `torus.log`,
  `flow.log` and `twist.log`.
- Sources: the FHL 2017 and ELP-S 2025 PDFs were read (arXiv versions), and the locators below come from them.
  Other locators are flagged where they are from memory.

The field is `field (1/4)` of `Design/RationalStellarator`: `B = ∇φ + ε∇h`, ε = 1/4, two field periods,
stellarator-symmetric. It has an exact circular axis R = 1, z = 0 with ι₀ = 1 − √3/2. The Phase-7 theorem
`RationalStellarator.Confined.rationalStellarator_confined` gives ≥ 95 toroidal transits from a tube of radius
≈ 0.023 by an approximate first integral (worst-case drift linear in length).

## 0. Verdict

1. **All-time confinement needs one exact invariant torus, and nothing else (§3, proved informally).**
   - Let S be an invariant 2-torus of B (B tangent to S), encircling the axis inside the tube.
   - Every field line starting strictly inside S stays inside for **all** s ∈ ℝ. The proof uses only uniqueness
     of field lines (B is locally Lipschitz).
   - Area preservation and twist are needed only to *produce* S (KAM), not to use it.
   - The topological step can be made Lean-cheap. Either write S as a polar graph r = ρ(ϑ, φ) about the exact
     axis, or use a level function G with |B·∇G| ≤ L|G| near S, which makes it a Grönwall barrier, the all-time
     analogue of `Fields.fieldLine_confined_of_defect`.
2. **The bottleneck is existence of one invariant torus: an a posteriori KAM theorem.**
   - **Formulate it for the flow, not the Poincaré map.** The rational field is explicit, so the invariance
     error `E = ∂_φK + (ι/2π)∂_θK − X(K, φ)` of a Fourier torus K(θ, φ) is a finite algebraic computation in the
     library's ℓ¹_ν Banach algebras. The Poincaré map would need validated complex ODE integration, which the
     library lacks.
   - **Best-matched theorem: Enciso–Luque–Peralta-Salas, JEMS 27 (2025), Theorem 6.2.** It is an a posteriori
     KAM theorem for **divergence-free fields in ℝ³** that needs no Poincaré map, no integrable approximation
     and no symplectic coordinates. Its twist condition (Definition 6.1) is an explicit average over the
     approximate torus. Its constants are **not** explicit.
   - **Explicit constants exist for the map version:** Figueras–Haro–Luque, FoCM 17 (2017), Theorem 2.5, with
     C₁ and C₂ in their Eqs. (72)–(73). The book by Haro–Canadell–Figueras–Luque–Mondelo (2016), ch. 4, and
     Haro–Luque (arXiv:1711.05515) cover Hamiltonian flows with explicit estimates. Recommendation: **prove an
     explicit-constant version of ELP-S Theorem 6.2 in ℓ¹ analytic norms**, following the FHL bookkeeping.
3. **Numbers for our field (§4, numerical observation).** Four Diophantine tori (noble tails), with launch radius
   along φ = 0, z = 0 (outboard):
   - A: ι = [0;7,3,1̄] = 0.13743 at r = 0.131;
   - B: [0;6,1,1̄] = 0.15110 at r = 0.287;
   - C: [0;6,2,1̄] = 0.15669 at r = 0.328;
   - D: [0;5,1,1̄] = 0.17800 at r = 0.442.

   In double precision:
   - Invariance errors are **E ≈ 2×10⁻¹⁴** for the map (A–C, 48 θ-modes) and ≈ 3×10⁻¹³ for the flow torus
     (96 × 64 grid). D is worse: E ≈ 3×10⁻¹³ (map) and 10⁻¹¹ (flow).
   - Fourier strips: ρ_K ≈ 0.27 / 0.13 / 0.11 / 0.04 (θ in turns).
   - The ELP-S twist constant is T ≈ +1.0×10⁻³ for all four, non-zero with one sign; relative to |ω| it is
     3–5×10⁻³ (weak shear).
4. **Can the smallness condition be met? (estimate).** The FHL form is `C₁‖E‖_ρ / (γ⁴ρ^{4τ}) < 1` with τ = 1.
   - Take γ ≈ 0.07 (period map) and ρ ≈ ρ_K/3. Then γ⁴ρ⁴ ≈ 1.5×10⁻⁹ (A), 1.3×10⁻¹⁰ (B), 7×10⁻¹¹ (C) and
     2×10⁻¹² (D).
   - In double precision (‖E‖_ρ ≈ 10⁻¹³) this tolerates C₁ up to ~10⁴ (A) or ~10³ (B, C). That is marginal,
     because the weak twist inflates C₁.
   - With extended precision (E ≈ 10⁻²⁵–10⁻³⁰, as FHL use), A–C pass with a margin of ≥ 10¹⁰ in C₁.
   - **Verdict: met for the interior tori A–C once the torus is computed in multiprecision; not for D** (near
     the 2/11 edge chain) without far more modes.
5. **Plan (§5).**
   - **K0**, the Grönwall invariant-barrier lemma: about 1 agent-day.
   - **K1**, polar-graph tori ⇒ all-time confinement: 2–3 agent-days.
   - **K2**, a ℓ¹(ℤ²) torus-residual certificate (a validated approximate torus): about 1 week.
   - **K2′**, an untrusted multiprecision run of FHL's Algorithm 5.1 / a flow analogue in Python–arb, to fix
     the constants before any Lean KAM work: 2–3 days.
   - **K3**, the KAM theorem in Lean (explicit ELP-S/FHL in ℓ¹_ν): 4–8 weeks. It is the only hard part.
   - **K4**, `rationalStellarator_confined_forever`.

   The Gómez-Serrano–Liehr–Taylor Lean library (Nash–Moser, analytic weights, Neumann inverses;
   github.com/lukasliehr/Grad-Conjecture, no licence file found) is the nearest existing Lean infrastructure for
   K3.

---

## 1. The Poincaré map is an exact symplectic map of a 2-D domain

**Field-line equations in φ.** In the tube, B·∇φ = (1 + εh_φ)/R² > 0 (≥ 4/5 is certified on T in
`phiRate_lower`). Hence field lines are graphs over φ:

```
dR/dφ = X_R = R² ε h_R/(1 + ε h_φ),   dz/dφ = X_z = R² ε h_z/(1 + ε h_φ),
```

π-periodic in φ (two field periods). The period map P = Φ_{0→π} acts on the section φ = 0, and the full-turn
map is P².

**Area form (proved informally; numerically confirmed).** P preserves μ = w(φ, R, z) dR∧dz with
`w = B·ê_φ = (1 + εh_φ)/R`, the toroidal flux density. Liouville: along a solution, with M = DΦ,

```
d/dφ [ w(φ, x(φ)) det M ] = [ ∂_φ w + ∇·(w X) ] det M = R·(∇·B)·det M = 0.
```

Here `∂_φw + ∂_R(wX_R) + ∂_z(wX_z) = ∂_φ(B_φ) + ∂_R(R B^R) + ∂_z(R B^z) = R ∇·B` in cylindrical
coordinates. `area.py` checks `w(Px)·det DP(x)/w(x) − 1 ≈ 10⁻¹⁴` at random points, with det DP ∈ [0.95, 1.03],
so the plain Lebesgue area is *not* preserved.

**Exactness.** The axis (1, 0) is a fixed point of P in every section. On the punctured domain D \ {axis}, take
polar coordinates (ϑ, r) about the axis and the action `A(r, ϑ) = ∫₀^r w r′ dr′`, the flux through the
"sector". Then μ = dA ∧ dϑ, so μ = d(A dϑ) is exact. A closed curve Γ around the axis and P(Γ) enclose the same
μ-area (P preserves μ and fixes the axis), so the flux `∫_{P(Γ)} A dϑ − ∫_Γ A dϑ = 0`. This is the
exact-symplectic ("zero net flux") property required by FHL Theorem 2.5. In the annulus coordinates
(ϑ/2π, A) ∈ T × ℝ, P is homotopic to the identity and analytic away from the axis. So the setting of FHL §2
holds, with a non-constant Ω(z) (FHL allow general ω = dα: constants c_Ω, c_DΩ, c_Da, c_D2a).

**Lean form of area preservation (target).** `poincare_area_preserving`: Jacobi's formula
`d(det M)/dφ = tr(DX)·det M` plus the identity above. It is a 2×2 algebraic statement once the variational
equation is stated. Mathlib has `Matrix.det` derivative lemmas via `Matrix.det_fin_two`. It is not needed by K0,
K1 or K3-flow; only a map-based KAM needs it.

## 2. A posteriori KAM: candidates, hypotheses, constants, formalization cost

### 2.1 Candidates compared

| Source | Object | Coordinates needed | Constants | Fit for us |
| --- | --- | --- | --- | --- |
| de la Llave–González–Jorba–Villanueva, *Nonlinearity* 18 (2005) 855–895 | Lagrangian tori of exact symplectic maps and Hamiltonian flows | none (no action-angle) | implicit | the method (approximate reducibility from geometry) |
| **Figueras–Haro–Luque**, *FoCM* 17 (2017) 1123–1193, Thm 2.5 | exact symplectic maps of T^n × ℝ^n, general ω = dα | annulus, F homotopic to id | **explicit** (C₁, C₂ in Eqs. (72)–(73); ad hoc Rüssmann constant (90)) | needs complex bounds on the *Poincaré map* → validated complex ODE integration |
| Haro–Canadell–Figueras–Luque–Mondelo, *The Parameterization Method for Invariant Manifolds*, Springer AMS 195 (2016), ch. 4 | maps and Hamiltonian flows | general symplectic form | explicit (book) | flow version applies after making 1.5 DOF autonomous; non-canonical form needed (section numbers not checked) |
| Haro–Luque, arXiv:1711.05515 (J. Differential Equations 2019, from memory) | Hamiltonian flows, isotropic tori, iso-energetic | covariant, no action-angle | explicit | as above |
| **Enciso–Luque–Peralta-Salas**, *JEMS* 27 (2025) 2251–2291, §6, **Thm 6.2**, Def. 6.1, Cor. 6.3 | invariant 2-tori of **divergence-free B in ℝ³** | none; Euclidean metric only | not explicit | **exact match**: our B is div-free and explicit, and no Poincaré map is needed |
| Celletti–Chierchia, CMP 118 (1988) 119–161; Memoirs AMS 187 no. 878 (2007) | Kolmogorov normal form near integrable | **action-angle variables** | explicit, computer-assisted | poor: our field has no action-angle form |
| Calleja–Haro–Porras, arXiv:2503.09740 (2025) | quasi-periodically time-dependent Hamiltonians | | explicit (appendix) | lead only |

### 2.2 FHL Theorem 2.5 (explicit version; exact hypotheses)

Setting: ω = dα exact symplectic on the annulus 𝒜 = T^n × ℝ^n (n = 1 for us), F: 𝒜 → 𝒜 exact symplectic and
homotopic to the identity, frequency ω ∈ ℝ^n. Norms are sup norms on complex strips T^n_ρ = {|Im θ| < ρ}, with
the Fourier norm `‖u‖_{F,ρ} = Σ|û_k| e^{2π|k|ρ} ≥ ‖u‖_ρ`.
- **H1:** F, α and ω extend analytically to a complex strip ℬ, with ‖DF‖_ℬ ≤ c_DF, ‖D²F‖_ℬ ≤ c_D2F,
  ‖Ω‖ ≤ c_Ω, ‖DΩ‖ ≤ c_DΩ, ‖Da‖ ≤ c_Da and ‖D²a‖ ≤ c_D2a.
- **H2:** K: T^n → 𝒜 is homotopic to the zero section and analytic on T^n_ρ, with K(T^n_ρ) ⊂ ℬ,
  ‖DK‖_ρ < σ_DK, ‖DKᵀ‖_ρ < σ_DKᵀ and dist(K(T^n_ρ), ∂ℬ) > 0.
- **H3:** a transversal frame N₀, with ‖N₀‖ ≤ c_N0 (and similar), and ‖B‖_ρ < σ_B, where
  B = −(DKᵀ Ω(K) N₀)⁻¹.
- **H4 (twist / non-degeneracy):** the torsion T(θ) = N(θ+ω)ᵀ Ω(K(θ+ω)) DF(K(θ)) N(θ) satisfies
  |⟨T⟩⁻¹| < σ_T, where N = DK·A + N₀B and A = −½ BᵀN₀ᵀΩ(K)N₀B.
- **H5 (Diophantine):** |k·ω − m| ≥ γ|k|₁^{−τ} for all k ≠ 0, with τ ≥ n.
- **Smallness:** for each 0 < ρ_∞ < ρ there is an explicit C₁ with `C₁ ‖E‖_ρ / (γ⁴ ρ^{4τ}) < 1`, where
  E(θ) = F(K(θ)) − K(θ+ω).
- **Conclusion:** there is an invariant torus K_∞ analytic on T^n_{ρ_∞}, with
  ‖K_∞ − K‖_{ρ_∞} < C₂‖E‖_ρ/(γ²ρ^{2τ}).
- **Constants:**
  - C₁ = max{(a₁a₃)^{4τ} Ĉ₅, a₃^{2τ+1} Ĉ₈ γ²ρ^{2τ−1}} and C₂ = a₃^{2τ} Ĉ₂/(1 − a₁^{1−2τ}) (Eqs. (72)–(73)).
  - The Ĉᵢ are polynomial in the c's, the σ's, the reciprocals of the margins (σ − b)⁻¹ and dist⁻¹, and c_R.
  - The Rüssmann constant controls the cohomological equation: ‖ℛv‖_{ρ−δ} ≤ c_R γ⁻¹δ^{−τ}‖v‖_ρ. It is
    improved by computing the first L divisors exactly (Lemma 4.3, Eq. (90); classical (96)).
  - The iterative lemma (Lemma 2.8) has the quadratic estimate ‖Ē‖_{ρ−2δ} < Ĉ₅ γ⁻⁴δ^{−4τ}‖E‖²_ρ.
- **Calibration (FHL §6, Table 5, golden curve of the standard map, τ = 1, γ = (3−√5)/2):**
  - ε = 0.06: 128 grid points, ρ = 1.6×10⁻², condition value 1.4×10⁻²⁸;
  - ε = 0.96: 32768 points, condition 2.3×10⁻¹²;
  - ε = 0.9716: 8 388 608 points, ‖E‖ ≤ 2.7×10⁻⁴¹, condition 0.082 (367-bit intervals, 3.2 h, 32 GB).
  - Tori are computed to tolerance 10⁻³³ and validated with 267-bit MPFI intervals.
  - **Every near-integrable FHL case passes by 10⁺¹⁰ or more once E is in multiprecision.**

### 2.3 ELP-S Theorem 6.2 (the formulation to make explicit)

- Data: B analytic and divergence-free on ℝ³ (for us, on {r₂ > 0}); ω ∈ ℝ² Diophantine; K: T² → ℝ³ an analytic
  embedding.
- Error: E(ϕ) = L_ωK − B∘K, with L_ω = DK·ω.
- **Twist (Def. 6.1):** 𝒯 = [A₁]ω₂ − [A₂]ω₁ ≠ 0, where [·] is the T²-average,
  A = −G_K⁻¹ DKᵀ (DBᵀ + DB)∘K · n/|n|², G_K = DKᵀDK and n = ∂₁K × ∂₂K.
- **Conclusion:** if ‖E‖_ρ is small enough, there are λ* and an analytic invariant torus with frequency
  (1 + λ*)ω, with |λ*| ≤ C‖E‖_ρ, and C‖E‖_ρ-close to K(T²).
- **Only the ratio ω₂/ω₁, which is ι, is fixed**; the speed is the counterterm λ. This is exactly right for field
  lines.
- Cor. 6.3 (accumulation by tori on both sides) also gives "a positive-measure family of tori".

The proof follows the parameterization method of de la Llave et al. It solves `L_ωΔK − DB(K)ΔK = −E − DK·δω`
in the frame (DK, n/|n|²), where it is upper-triangular up to O(E), so it reduces to two cohomological equations
and a twist solve.

### 2.4 Why a fixed-space radii polynomial cannot replace KAM (obstruction, proved informally)

- On ℓ¹_ν(ℤ²) the operator L = ∂_φ + (ι/2π)∂_θ has symbol i(2k_φ + ιk_θ), whose inverse is ≥ |k|^τ/γ along
  near-resonant directions.
- For a Newton map T(K) = K − A F(K) in a single Banach space to be a contraction, A must approximate DF⁻¹. The
  required ‖I − A DF‖ < 1 fails because the O(1) multiplication part D_K X of DF composed with L⁻¹ is unbounded.
  Weighted domain/codomain pairs cannot make L and L⁻¹ both bounded, since one would need |k| ≤ w_X/w_Y ≤ γ|k|^{−τ}.
- Hence the loss of analyticity (ρ → ρ − δ at each step) and the quadratic Newton scheme are unavoidable. The
  existing `Certificates/RadiiPolynomial` handles each **finite** step's estimates but not the iteration.

### 2.5 What a Lean formalization of K3 needs

1. **Analytic function spaces on strips: use weighted ℓ¹, not sup norms.** Use ℓ¹_ν(ℤ²) with
   ν = e^{2πρ}, generalizing `Certificates/WeightedEll1`, which is ℤ-indexed. It is a Banach algebra with constant
   1 (`norm_conv_le`), and ‖·‖_sup ≤ ‖·‖_ν. Doing the whole KAM in ℓ¹ makes three estimates one-line sups:
   - **Cauchy estimate:** ‖∂_θu‖_{ρ−δ} ≤ (eδ)⁻¹‖u‖_ρ, since sup_k 2π|k|e^{−2π|k|δ} = 1/(eδ).
   - **Rüssmann-type small-divisor estimate:**
     ‖L⁻¹v‖_{ρ−δ} ≤ sup_{k≠0} e^{−2π|k|δ}/|ℓ(k)| · ‖v‖_ρ ≤ (τ/(2πeδ))^τ/(2πγ)·‖v‖_ρ, with the first L
     divisors handled exactly as in FHL's ad hoc improvement.
   - **Composition:** for our polynomial/rational X, composition with K is algebra operations. Division by
     1 + εh_φ and R² is a Neumann series in the Banach algebra (`NormedRing.inverse` estimates). No complex
     sup-norm bounds on ℬ are needed.
2. **Iterative lemma** (one Newton step with explicit Ĉᵢ): the approximate-reducibility identities (ELP-S §6.3 /
   FHL Lemmas 2.9–2.10) and the twist solve.
3. **Convergence lemma:** a real-sequence statement, the easy, separable first Lean piece. With δ_j = δ₀a^{−j}
   and e_{j+1} ≤ C δ_j^{−4τ} e_j², if C δ₀^{−4τ} a^{4τ} e₀ < 1 then Σ_j C' δ_j^{−2τ} e_j < ∞ and e_j → 0.
4. **Limit:** completeness of ℓ¹_{ν_∞}, continuity of the residual map, and identification of the Fourier limit
   as a classical C¹ torus (the 2-D analogue of `Certificates/FourierRegularity.classical_of_coeff`).
5. **Existing pieces:**
   - library: `Contraction`, `RadiiPolynomial`, `WeightedEll1` (1-D), `ConvAlgebra`, `FourierRegularity`,
     Grönwall uniqueness (`exactQA_reference_bounce`), and the polynomial (`LiePoly`) and cover (`Cover.check`)
     machinery from Phase 7;
   - external: GSLT's `NashMoser/{GuardedNewtonIteration, NewtonConvergence, NewtonGradeLimits,
     NewtonExactZero}` and `AnalyticAlgebras/{Neumann,Perturbation}Inverse`. Their README says they are reusable
     components without a packaged Hamilton theorem. Use them as a design reference; vendoring needs permission
     (no licence file).

## 3. "A single invariant torus suffices": the cheap topological half

**Theorem B (proved informally).** Let B be locally Lipschitz on an open set U ⊂ ℝ³. Let S ⊂ U be a compact set
such that through every point of S passes a field line defined for all s ∈ ℝ and contained in S. Suppose
V ⊂ U is open with frontier V ⊆ S and V ∩ S = ∅. Then every field line γ with γ(0) ∈ V that stays in U satisfies γ(s) ∈ V for
all s.

*Proof.* Let s₁ = inf{s > 0 : γ(s) ∉ V}. Since V is open, γ(s₁) ∉ V and γ(s₁) ∈ closure V, so
γ(s₁) ∈ frontier V ⊆ S. The field line through γ(s₁) lying in S agrees with γ for all s by uniqueness (both
are solutions through the same point and stay in U), so γ(0) ∈ S. But γ(0) ∈ V and V ∩ S = ∅. Contradiction.
Backwards is the same.

No area preservation is used. The topology (frontier V ⊆ S) is the only issue, and there are two Lean-cheap ways
to supply it:

- **(B1) Level function / Grönwall barrier.** Suppose G is C¹ on the tube T with:
  - G > 0 on frontier T;
  - |DG·B| ≤ L|G| on T ∩ {−g₀ ≤ G ≤ 0};
  - G(γ(0)) < 0.

  Then G(γ(s)) ≤ max(G(γ(0)), −g₀)·e^{−Ls} < 0 for all s ≥ 0, and γ stays in T. This is
  `fieldLine_confined_of_defect` with the constant defect δ replaced by L|G|. It is an all-time statement and
  needs no uniqueness theorem at all. For an exact invariant torus {G = 0} with ∇G ≠ 0, the bound holds with
  L = sup |∂_G(DG·B)| over a collar.
- **(B2) Polar graph about the exact axis.** In section coordinates (ϑ, r) about (R, z) = (1, 0), suppose the
  torus is S = {r = ρ(ϑ, φ)} with ρ continuous, positive and periodic. Then V = {r < ρ} has frontier V ⊆ S ∪ ∂T,
  so Theorem B applies. From a KAM parameterization K_∞(θ, φ), a polar-graph representation follows if
  ∂_θϑ(K(θ, φ)) ≥ m > 0 for the explicit approximation K. This is a Fourier inequality, together with
  ‖K_∞ − K‖_{C¹} ≤ (Cauchy estimate on the strip)·C₂‖E‖/(γ²ρ²) < m·(…). Inverting a strictly monotone circle map
  uses Mathlib's order-isomorphism API on lifts ℝ → ℝ.

**Corollary (shells).** Two nested invariant tori trap all field lines between them for all time, which gives a
flux-shell confinement statement. Birkhoff's theorem says a rotational invariant circle of a twist map is a
Lipschitz graph in angle–action coordinates. Its cone bound is an a priori Lipschitz bound for ρ, useful for
(B2), and a *necessary* condition used by converse KAM.

**Converse KAM (nonexistence, for honesty at the edge).**
- MacKay–Percival (CMP 98 (1985) 469) give the cone-crossing criterion.
- Duignan–Meiss (Chaos 31 (2021) 013124) treat tori transverse to a foliation built from approximate integrals,
  which fits our polynomial I.
- Kallinikos–MacKay–Martínez-del-Río (PPCF 65 (2023) 095021) and Martínez-del-Río (arXiv:2501.06796, conefields;
  Zenodo code) apply this to toroidal magnetic fields.
- These certify regions with **no** invariant torus (the 2/11 chain at r ≈ 0.45 and the chaos beyond), so
  confinement radius bounds are two-sided. All need validated orbit/tangent integration, so they come after K3.

**Nekhoroshev / exponentially long times.** These are not needed: for 1.5 DOF, KAM tori are barriers. The
finite-length route already improves geometrically with polynomial order (126 → 3.5×10⁷ transits for orders
6–14), so an intermediate "very long" theorem is available without KAM, at the cost of bigger covers.

## 4. Numbers for the rational field (numerical observation)

**Rotational transform profile** (`profile.py`; launch along φ = 0, z = 0, outboard, 2000 periods, weighted
Birkhoff averages with 8–14 digits):

| r | 0.01 | 0.10 | 0.13 | 0.20 | 0.29 | 0.33 | 0.40 | 0.44 | 0.45 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| ι | 0.13400 | 0.13601 | 0.13739 | 0.14208 | 0.15143 | 0.15695 | 0.16901 | 0.17747 | 2/11 chain |

Low-digit points mark the chains 1/7 (r ≈ 0.21), 2/13 (0.31), 1/6 (0.39) and 2/11 (0.45). The profile is
monotone with dι/dr ≈ 0.05 → 0.2.

**Candidate rotation numbers.** These are noble tails placed between the low-order resonances; `dioph.py` checks
k ≤ 10⁶ in floating point, so the values are indicative. γ uses τ = 1, |kω − m| ≥ γ/k:

| torus | ι (continued fraction) | gap | γ (full turn ω = ι): k = 1 / min over k ≥ 2 | γ (period map ω = ι/2) | asymptotic |
| --- | --- | --- | --- | --- | --- |
| A | [0;7,3,1̄] = 0.1374307259 | (2/15, 1/7) | 0.137 / 0.266 (k = 7) | 0.069 | 1/√5 (full), 1/(2√5) (period) |
| B | [0;6,1,1̄] = 0.1511022763 | (1/7, 2/13) | 0.151 / 0.404 | 0.076 | same |
| C | [0;6,2,1̄] = 0.1566915271 | (2/13, 1/6) | 0.157 / 0.359 | 0.078 | same |
| D | [0;5,1,1̄] = 0.1779982111 | (1/6, 2/11) | 0.178 / 0.408 | 0.089 | same |
| axis | 1 − √3/2 = 0.1339745962 | | 0.134 / 0.144 (k = 15) | 0.067 | |

The binding divisor is the trivial k = 1 term (small ι). FHL's ad hoc Rüssmann estimate treats such low modes
exactly, so the effective γ is the k ≥ 2 value.

**Approximate invariant tori** (`torus.py`):
- Method: bisection on the launch radius to the target ι, then weighted-Birkhoff Fourier coefficients of the
  conjugacy, then Newton on `P(K(θ)) = K(θ + ω)` with ω = ι/2 fixed. Collocation uses 4N + 8 points, P comes from
  DOP853 at rtol 10⁻¹³, and the phase condition fixes the z-cos₁ coefficient.
- Pitfall: fixing z-sin₁ is degenerate because z ≈ sin, and Newton then diverges.
- Newton converges quadratically: 9×10⁻⁸ → 8×10⁻¹² → 2×10⁻¹⁵.

| torus | r | N (θ-modes) | E_map sup, off-grid | ‖K̂_k‖ at k = 8 / 16 / 32 | ρ_K (strip, θ in turns) | flow residual (N_θ × N_φ) | ELP-S twist 𝒯 (rel. 𝒯/\|ω_s\|) |
| --- | --- | --- | --- | --- | --- | --- | --- |
| A | 0.131 | 48 | 1.6e-14 | 8e-9 / 1e-14 / – | ≈ 0.27 | 2.7e-13 (96 × 64) | 9.7e-4 (3.1e-3) |
| B | 0.287 | 48 | 2.4e-14 | 9e-6 / 2e-8 / 2e-14 | ≈ 0.13 | 4.8e-13 (96 × 64) | 1.05e-3 (3.6e-3) |
| C | 0.328 | 48 | 2.3e-14 | 4e-5 / 1e-7 / 1e-12 | ≈ 0.11 | 4.1e-13 (96 × 64) | 1.07e-3 (3.8e-3) |
| D | 0.442 | 96 | 3.2e-13 | 2e-3 / 4e-5 / 2e-6 | ≈ 0.04 (plateau near k = 11–22) | 1.0e-11 (192 × 64) | 1.19e-3 (4.8e-3) |

How the columns were obtained:
- E values are limited by double precision and the integrator tolerance, not by truncation (A–C).
- The flow torus is `K(θ, φ) = Φ_{0→φ}(k(θ − ωφ/π))`, π-periodic in φ. Its residual
  `|∂_φK + (ω/π)∂_θK − X(K, φ)|` is evaluated off-grid by spectral interpolation.
- φ-spectra decay to 10⁻¹⁵ by φ-frequency ≈ 12–16 (in units of e^{2iφ}) for A–C, about 24 for D.
- 𝒯 is computed after reparametrizing to field-line time s: solve `L_v u = 1 − c/b` with b = B·∇φ and
  c = ⟨1/b⟩⁻¹, then average Â·det DΨ over the (θ, φ) grid. Angles are normalized to [0, 1)², and
  ω_s = c(ω/π, 1/π) ≈ (0.022, 0.29).
- The sign is the same for all four, consistent with positive shear.

**Certificate size (estimate).** A K2 residual certificate for torus B needs 2 components × ~32 θ-modes ×
~16 φ-modes ≈ 10³ coefficients. X is rational of degree ≈ 7 in (R, z) with trigonometric φ-dependence of
degree 2. Cleared of denominators, as in `RationalStellaratorConfined.rate0`–`rate3`, the residual is a
polynomial in K of degree ≈ 8, so products of ~10³-term 2-D series are needed. These are exact dyadic
convolutions of size ~10⁵–10⁶ terms. That is heavy for `decide +kernel` but within reach of a native-arithmetic
checker or a proof-term split as in Phase 7. Torus A needs ~4× fewer terms.

**Smallness estimate (estimate, not a certificate).**
- With ρ = ρ_K/3 and γ (period map): γ⁴ρ⁴ ≈ 1.5e-9 (A), 1.3e-10 (B), 7e-11 (C), 2e-12 (D).
- FHL's C₁ is polynomial in the margins and in 1/twist. Our twist is weak (relative 𝒯 ≈ 4×10⁻³, from the shear
  dι/dr ≈ 0.05–0.2), which inflates C₁ by perhaps 10²–10⁴ over a strongly twisting map.
- With double-precision E (‖E‖_ρ ~ 10⁻¹³), the condition needs C₁ ≲ 10⁴ (A) or 10³ (B, C): marginal.
- With E ~ 10⁻²⁸ (achievable: the Newton iteration converges quadratically, so it is limited only by working
  precision and the integrator), the tolerance is C₁ ≲ 10¹⁹ (A) or 10¹⁸ (B, C). **That passes for any plausible
  C₁.**
- D (ρ_K ≈ 0.04, near the 2/11 chain) needs ≥ 200 modes and is not recommended.
- **The decisive check is K2′:** compute C₁ honestly with FHL Algorithm 5.1 in interval arithmetic, outside
  Lean.

## 5. Staged plan with Lean module statements

**K0. `Theory/Fields/InvariantBarrier.lean`** (generic; ≈ 1 agent-day; no KAM)

```lean
/-- All-time Grönwall barrier: a function whose rate along B is proportional to itself near its
zero level cannot change sign along field lines. -/
theorem fieldLine_confined_of_proportional_defect {B : Space → Space} {G : Space → ℝ} {T : Set Space}
    {L g₀ : ℝ} (hT : IsClosed T) (hL : 0 ≤ L) (hg₀ : 0 < g₀)
    (hG : ∀ x ∈ T, DifferentiableAt ℝ G x) (hfront : ∀ x ∈ frontier T, 0 < G x)
    (hdef : ∀ x ∈ T, -g₀ ≤ G x → G x ≤ 0 → fderiv ℝ G x (B x) ≤ L * |G x|)
    {γ : ℝ → Space} (hγ : IsForwardFieldLine B γ) (h0 : γ 0 ∈ T) (hneg : G (γ 0) < 0) :
    ∀ s, 0 ≤ s → γ s ∈ T ∧ G (γ s) ≤ max (G (γ 0)) (-g₀) * Real.exp (-L * s)
/-- Sanity: L = 0 is an exact first integral (`sublevel_confined`); the bound is attained by
`G = -e^{-Ls}` along the 1-D flow `ẋ = -Lx`. -/
```

Proof: H = G·e^{Ls} is non-increasing while −g₀ ≤ G ≤ 0. Deeper than −g₀ nothing is needed, because G must pass
−g₀ to approach 0. So the conclusion is an all-time barrier, proved by the same first-exit argument as
`DefectConfinementLocal`.

**K1. `Theory/Fields/InvariantTorusTrap.lean`** (≈ 2–3 agent-days)

```lean
/-- Theorem B: an invariant compact set containing the frontier of an open set traps field lines (uniqueness only). -/
theorem trapped_of_invariant_frontier {B : Space → Space} {U V S : Set Space}
    (hB : LocallyLipschitzOn U B) (hVU : V ⊆ U) (hV : IsOpen V) (hfr : frontier V ⊆ S) (hSV : Disjoint S V)
    (hS : ∀ y ∈ S, ∃ η : ℝ → Space, η 0 = y ∧ (∀ t, η t ∈ S) ∧ ∀ t, HasDerivAt η (B (η t)) t)
    {γ : ℝ → Space} (hγ : ∀ t, HasDerivAt γ (B (γ t)) t) (hγU : ∀ t, γ t ∈ U) (h0 : γ 0 ∈ V) :
    ∀ t, γ t ∈ V
/-- Torus data: a C¹ map K : ℝ² → Space, 1-periodic in θ and π-periodic in φ, with exact invariance
`∂_φK + ω' ∂_θK = (B/B^φ)∘K` and a polar-graph condition about the axis. -/
structure InvariantPolarTorus (B : Space → Space) (ω' : ℝ) where
  K : ℝ → ℝ → Space
  periodic : ... ; invariant : ... ; polar_monotone : ∀ θ φ, 0 < ∂_θ (axisAngle (K θ φ))
theorem confined_forever (T : InvariantPolarTorus (field (1/4)) ω') {γ} (hγ : ∀ t, HasDerivAt γ (field (1/4) (γ t)) t)
    (h0 : axisRadius (γ 0) < T.radius (axisAngle (γ 0)) (phi (γ 0))) : ∀ t, γ t ∈ T.interior
```

The orbit through a point of S is explicit: η(t) = K(θ₀ + ω'φ(t), φ(t)), with φ(t) solving the scalar ODE
φ′ = B^φ(K(…)). Its existence comes from 1-D ODE existence (Mathlib `IsPicardLindelof`), or better by
reparametrizing in φ. The library's field lines are supplied curves, so state everything with
`IsForwardFieldLine` and a φ-reparametrization lemma.

**K2. `Certificates/WeightedEll1Z2.lean` + `Design/RationalStellaratorTorus.lean`** (≈ 1 week)

```lean
/-- ℓ¹_ν(ℤ²) with Banach-algebra estimate, point evaluation, termwise derivatives (2-D FourierRegularity). -/
theorem norm_conv2_le (hν : 1 ≤ ν) (x y : WeightedEll1Z2 ν) : ‖conv2 ν x y‖ ≤ ‖x‖ * ‖y‖
theorem norm_deriv_le (hδ : 0 < δ) : ‖dθ x‖_{ν e^{-2πδ}} ≤ (Real.exp 1 * δ)⁻¹ * ‖x‖_ν
theorem norm_cohomological_inv_le (hD : Diophantine ω γ τ) : ‖Linv x‖_{ν e^{-2πδ}} ≤ (τ/(2π e δ))^τ/(2π γ) * ‖x‖_ν
/-- Certified approximate torus B: a finite Fourier K with exact dyadic coefficients and
‖den(K)·(∂_φK + ω'∂_θK) − num(K)‖_ν ≤ ε_cert, ‖1/den(K)‖_ν ≤ c_inv. -/
theorem torusB_residual : ‖torusError torusB‖_{ν₀} ≤ eB
theorem torusB_twist : twistELPS torusB ∈ Set.Icc tlo thi   -- 𝒯 ≠ 0 with sign
theorem torusB_polar : ∀ θ φ, m ≤ ∂_θ axisAngle (torusB.K θ φ)
```

**K2′ (outside Lean, untrusted oracle).** Before investing in K3, run FHL Algorithm 5.1 (map) and the analogous
flow bookkeeping with arb/MPFI at ≥ 256 bits for tori A and B, and record C₁, C₂, ρ and δ. If C₁·E/(γ⁴ρ⁴) is
not ≪ 1 for A, stop and reconsider: a stronger twist field, or better norms.

**K3. `Theory/KAM/{Iterative,Convergence,DivergenceFree}.lean`** (4–8 weeks; the research-grade piece)

```lean
/-- Real-number convergence of the KAM scheme (first, easy piece). -/
theorem kam_sequence_converges {C a δ₀ e₀ τ : ℝ} (h : C * a ^ (4*τ) * δ₀ ^ (-4*τ) * e₀ < 1) ... :
    Summable (fun j => C' * (δ₀ * a ^ (-j)) ^ (-2*τ) * e j) ∧ Tendsto e atTop (𝓝 0)
/-- Explicit a posteriori KAM for divergence-free fields in ℓ¹_ν norms (ELP-S Thm 6.2 with FHL-style constants),
specialized to polynomial/rational B. -/
theorem kam_divFree {B} (hB : IsRationalField B) (hdiv : ∀ x ∈ U, divergence B x = 0)
    (K : Torus2) (hω : Diophantine (ω.2/ω.1) γ τ) (htwist : twistELPS B K ω ≠ 0)
    (hsmall : kamC1 B K ω ρ * ‖torusError B K ω‖_ρ < γ ^ 4 * ρ ^ (4*τ)) :
    ∃ K∞ λ, IsInvariantTorus B K∞ ((1 + λ) • ω) ∧ ‖K∞ - K‖_{ρ/a} ≤ kamC2 * ‖torusError B K ω‖_ρ / (γ^2 * ρ^(2*τ))
```

**K4. `Design/RationalStellaratorForever.lean`**

```lean
/-- All-time field-line confinement in the exact rational stellarator field: every field line starting
inside the KAM torus with ι = [0;6,1,1,1,…] stays inside forever (r ≲ 0.29 at φ = 0 outboard). -/
theorem rationalStellarator_confined_forever {γ} (hγ : ∀ t, HasDerivAt γ (field (1/4) (γ t)) t)
    (h0 : γ 0 ∈ torusB_interior) : ∀ t, γ t ∈ torusB_interior
```

It composes K3(torusB) → K1 (with K2's polar bound plus the C¹ closeness) → the conclusion. It upgrades
`rationalStellarator_confined` (95 transits, r ≲ 0.023) to **all time, r ≲ 0.29**. That is a ~12× larger radius
and covers most of the nested-surface region (r_eff ≈ 0.40). It also supplies the inner region Ω₁ for the
stepped-pressure equilibrium of `finite-beta-stellarator.md` §4.

**Order and risk.**
- K0 and K1 are low-risk and useful immediately. K0 with an *exact* first integral reproves the M0 results; K1
  applies to any later invariant torus.
- K2 is medium-risk (certificate size).
- K3 is high-risk but well-defined. Its separable sub-lemmas are the ℓ¹ Cauchy/Rüssmann estimates and the scalar
  convergence lemma (1–2 days each), and both are useful beyond KAM.
- Coil transfer: KAM tori are robust (Cor. 6.3), but the coil-field error must itself be put into the KAM
  smallness (η·Lip ≲ γ⁴ρ⁴/C₁ ~ 10⁻¹⁰). So the all-time result does **not** transfer to filament coils with
  present error bounds (2.4×10⁻⁴ sampled). The finite-length route remains the coil route.

## 6. Caveats

- All numbers in §4 are floating-point observations. Diophantine constants were checked to k ≤ 10⁶ only; the
  continued fractions with noble tails give the stated asymptotics exactly. ρ_K is read off Fourier decay.
- The ELP-S twist value depends on my normalization of T² and on the time reparametrization. Its *non-vanishing
  and sign* are the content. The value was computed spectrally from a double-precision torus.
- Theorem B and (B1) give **field-line** confinement only (β = 0, no guiding centres, no coils).
- FHL constants were transcribed from the arXiv v1 PDF (Thm 2.5 on pp. 8–9, Eqs. (72)–(73), Table 5, Thm 6.1).
  ELP-S Theorem 6.2 and Definition 6.1 are on pp. 24–25 of arXiv:2104.08149v3. Haro–Luque's journal locator and
  the HCFLM chapter structure are from search results and memory. Novelty: none claimed. The flow-form
  certificate design, the numbers and the staged statements are this note's.

## 7. Sources

- J.-Ll. Figueras, À. Haro, A. Luque, *Rigorous computer-assisted application of KAM theory: a modern approach*,
  Found. Comput. Math. 17 (2017) 1123–1193; arXiv:1601.00084.
- R. de la Llave, A. González, À. Jorba, J. Villanueva, *KAM theory without action-angle variables*, Nonlinearity
  18 (2005) 855–895.
- À. Haro, M. Canadell, J.-Ll. Figueras, A. Luque, J. M. Mondelo, *The Parameterization Method for Invariant
  Manifolds*, Springer Appl. Math. Sci. 195 (2016), ch. 4.
- À. Haro, A. Luque, *A-posteriori KAM theory with optimal estimates for partially integrable systems*,
  arXiv:1711.05515.
- A. Enciso, A. Luque, D. Peralta-Salas, *MHD equilibria with nonconstant pressure in nondegenerate toroidal
  domains*, J. Eur. Math. Soc. 27 (2025) 2251–2291; arXiv:2104.08149 (§6).
- A. Celletti, L. Chierchia, Commun. Math. Phys. 118 (1988) 119–161; *KAM Stability and Celestial Mechanics*,
  Mem. AMS 187 (2007) no. 878.
- R. S. MacKay, I. C. Percival, Commun. Math. Phys. 98 (1985) 469; N. Duignan, J. D. Meiss, Chaos 31 (2021)
  013124; N. Kallinikos, R. S. MacKay, D. Martínez-del-Río, Plasma Phys. Control. Fusion 65 (2023) 095021;
  D. Martínez-del-Río, arXiv:2501.06796.
- S. Das, Y. Saiki, E. Sander, J. A. Yorke, Nonlinearity 30 (2017) 4111 (weighted Birkhoff averages).
- J. Gómez-Serrano, L. Liehr, M. A. Taylor, arXiv:2609.24739; Lean code github.com/lukasliehr/Grad-Conjecture.
