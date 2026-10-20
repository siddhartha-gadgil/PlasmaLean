# Relative-entropy dissipation for the heat equation with fixed n, T*

**Lane:** A, Cycle 1 (track T3, implementation plan §1.5). **Date:** 2026-10-20.
**Checks:** `/tmp/lanea/relent.py`, `/tmp/lanea/cex.py` (sympy, outside the repo). All residuals are 0.
**Verdict:** the identity in `bkm-regularity-and-perelman-burn-bounds.md` §3.1 is **refuted** for non-constant
T* (exact counterexample below). The corrected identity and the regime where dissipation holds are stated here.
Status: **proved informally + symbolically checked**.

## Setting and hypotheses

* M ⊂ ℝ^d bounded with Lipschitz boundary and outward normal ν (or a radial interval; see the end).
* n(x) > 0, T*(x) > 0 fixed (time-independent) and C¹; χ(x) a symmetric, positive-semidefinite matrix field, C¹,
  **independent of T** (if χ depends on T the cross-term argument below fails).
* T(x,t) > 0 a classical solution (C^{2,1}) of n ∂_t T = ∇·(nχ∇T) + Q(x,T).
* H[T|T*] = ∫_M n T* φ(T/T*), with φ(s) = s − 1 − ln s ≥ 0, φ(1) = 0.

## Identity (exact)

Write s = T/T*. Then d/dt (nT*φ(s)) = n(1 − T*/T) ∂_tT, and pointwise (sympy-checked in 2-D with a full
symmetric χ):

(1 − T*/T) ∇·(nχ∇T) = − nT* ⟨∇ln s, χ∇ln s⟩ + ln s · ∇·(nχ∇T*) + ∇·[ (1 − T*/T) nχ∇T − ln s · nχ∇T* ].

Hence

**dH/dt = − 𝓕 + 𝓒 + 𝓡 + 𝓑**, where
* 𝓕 = ∫ nT* ⟨∇ln(T/T*), χ ∇ln(T/T*)⟩ ≥ 0 (Fisher-type information),
* 𝓒 = ∫ ln(T/T*) ∇·(nχ∇T*) (**cross term, no sign**),
* 𝓡 = ∫ (1 − T*/T) Q(x,T) (reaction; the note's "ΔQ" is a typo for Q),
* 𝓑 = ∮ [ (1 − T*/T) nχ∇T − ln(T/T*) nχ∇T* ]·ν.

Equivalent un-integrated form (also checked): (1−T*/T)∇·(nχ∇T) = −nT*⟨∇T,χ∇T⟩/T² + n⟨∇T*,χ∇T⟩/T + ∇·[(1−T*/T)nχ∇T].
So the dissipation is ∫ nT*|∇T|²_χ/T², and there is a cross term ∫ n⟨∇T*,χ∇T⟩/T. The note's claim (dH/dt = −𝓕 + reaction) is
exactly the claim 𝓒 + 𝓑 = 0.

## Counterexample to the note's version (exact)

M = [0,1], n = χ = 1, Q = 0, T* = 1 + x², and at some instant T = 1 + x. Then T = T* at x = 0, 1, so 𝓑 = 0.
True: dH/dt = ∫(1 − T*/T) T'' dx = 0 (T'' = 0). Note's formula: −𝓕 ≈ −0.2447 < 0. (𝓒 ≈ +0.2447.)

## When the negative-definite structure holds

The generalized relative entropy mechanism (cross-term = ∫ G(s) ∇·(nχ∇T*) with G' = sφ''(s) = 1/s) gives:

1. **T* constant**, Q = 0, and either Dirichlet T = T* or no-flux nχ∇T·ν = 0: dH/dt = −𝓕 ≤ 0. Equality holds iff T is
   constant on each component, where χ is positive definite.
2. **T* steady and Dirichlet-matched.** Suppose ∇·(nχ∇T*) + Q(x,T*) = 0 in M and T = T* on ∂M (then 𝓑 = 0). Then
   dH/dt = −𝓕 + ∫ [ (1 − 1/s − ln s) Q(x,T*) + (1 − 1/s)(Q(x,T) − Q(x,T*)) ].
   Since 1 − 1/s − ln s ≤ 0 (maximum 0 at s = 1) and 1 − 1/s has the sign of T − T*:
   **dH/dt ≤ −𝓕 ≤ 0 whenever Q(x,T*) ≥ 0 and T ↦ Q(x,T) is non-increasing** (fixed heating minus a monotone loss).
3. **Fails when ∂_TQ > 0** (alpha heating exceeding losses, i.e. the thermally unstable branch). The second reaction term
   can then be positive, and H can grow. This is exactly the physics of thermal runaway. So the Perelman-style claim
   that diffusion "strongly damps toward T*" holds only on the stable branch, and the stable branch is an extra hypothesis.
4. With non-matching boundary data, or a T* that is not steady, 𝓒 + 𝓑 is generally non-zero and of either sign.

Literature: this is an instance of the general relative entropy principle (Michel, Mischler & Perthame,
J. Math. Pures Appl. 84 (2005) 1235–1260) **[lead: standard reference, not re-checked here]**.

## Radial (flux-surface-averaged) version for `Kernel/Transport`

With M = [0,1] in ψ, measure V′(ψ)dψ, and n∂_tT = (1/V′)∂_ψ(V′ n D ∂_ψT) + Q (D = χ⟨|∇ψ|²⟩ > 0), the same identity
holds with ∇ → ∂_ψ and dV → V′dψ. The axis boundary term vanishes if V′(0) = 0 and the fluxes stay bounded (the
axis-regularity hypothesis). The edge term vanishes under matched Dirichlet data T(1) = T*(1).

## Lean targets

* **Now:** the pointwise 1-D identity as a `HasDerivAt`/`deriv` computation
  (`(1 - Ts/T) * (a*T')' = -a*Ts*((log(T/Ts))')^2 + log(T/Ts)*(a*Ts')' + (flux)'` for C² functions with T, Ts > 0),
  and the scalar lemma `1 - 1/s - log s ≤ 0`, together with the sign lemma for case 2.
* **Cycle 2:** integrate on [0,1] (FTC, `intervalIntegral`) to get `dH/dt ≤ -𝓕` under the hypotheses of case 2, plus the
  counterexample as a `decide`-free exact sanity theorem (T* = 1+x², T = 1+x).
