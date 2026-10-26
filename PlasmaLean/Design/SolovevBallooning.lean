/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningLine
public import PlasmaLean.Design.SolovevBallooningData
public import PlasmaLean.Design.SolovevBallooningCells00
public import PlasmaLean.Design.SolovevBallooningCells01
public import PlasmaLean.Design.SolovevBallooningCells02
public import PlasmaLean.Design.SolovevBallooningCells03
public import PlasmaLean.Design.SolovevBallooningCells04
public import PlasmaLean.Design.SolovevBallooningCells05
public import PlasmaLean.Design.SolovevBallooningCells06
public import PlasmaLean.Design.SolovevBallooningCells07
public import PlasmaLean.Design.SolovevBallooningCells08
public import PlasmaLean.Design.SolovevBallooningCells09
public import PlasmaLean.Design.SolovevBallooningCells10
public import PlasmaLean.Design.SolovevBallooningCells11
public import PlasmaLean.Design.SolovevBallooningCells12
public import PlasmaLean.Design.SolovevBallooningCells13
public import PlasmaLean.Design.SolovevBallooningCells14
public import PlasmaLean.Design.SolovevBallooningCells15
public import PlasmaLean.Certificates.KernelFact

/-!
# Ideal-ballooning stability of ALL flux surfaces of the reactor Solov'ev equilibrium

For the reactor Solov'ev equilibrium of `SolovevAlpha` (`A = 7/4 T`, `L = 10 m`,
`F = 50 T m`, `ψ̃ = R²z²/2 + (R² − L²)²/4`) we prove

  `reactor_ballooning_all : ∀ s, 0 < s → s ≤ 25 → ∀ c, (reactorLine … s … c).Stable`,

i.e. on EVERY flux surface `ψ̃ = s²` of the plasma (`0 < s ≤ 25`, from the magnetic axis to the
edge `ψ̃ = L⁴/16`) and for EVERY eikonal family (shift `c`, i.e. every `θ_k`), the ballooning
line operator along the exact field line `SolovevMercier.lineS` has nonnegative energy
`∫ (P X'² + Q X²) dt` for every compactly supported `C¹` mode, with `P, Q` the SUPPLIED
ballooning reduction of `BallooningReduction` computed from the actual equilibrium
(`SolovevBallooningGeom`). The integer surfaces `s = 1, 2, 3, 4` are corollaries
(`reactor_ballooning_s1` … `reactor_ballooning_s4`).

## Structure of the proof

* **Scaling** (`SolovevBallooningDefs`, `SolovevBallooningLine`). With `σ̃ = s σ` all
  coefficients are polynomial in `s` (no `1/s`): `s² P = Π(σ̃) = p̂₀ + p̂₁ σ̃ + p̂₂ σ̃²`,
  `s Q = s q₀ + σ̃ q₁`, `s σ' = d̂`. The two-variable Riccati certificate
  `Φ = σ̃ a + f₀ + f₁ ρ(σ̃) + f₂ ν(σ̃)` (`riccatiScaled`, `riccati2D_energy_nonneg`) reduces the
  stability of all lines of the surface to the positivity of the numerator
  `N̂ = Π · I − s G² = Σₖ eₖ σ̃ᵏ` (`reactorLine_stable_of_N`).
* **One certificate for all surfaces.** The data `gdata` (`SolovevBallooningData`) are
  quadratic polynomials in `s` (untrusted convex SOCP). On the magnetic axis the coefficients
  `eₖ` vanish identically (`gdata_axis`), and `N̂/s` stays positive as `s → 0`.
* **The `(τ, s)` cover** (`SolovevBallooningChart`). The half circle `x ≥ 0` is
  `τ ∈ [−1, 1]`; the rectangle `[−1, 1] × [0, 25]` is cut into 825 boxes (`cover_all`, an
  explicit `Cover` proof term assembled from 825 kernel-checked box lemmas in the 16 parallel
  modules `SolovevBallooningCells00` … `15`). On a box the coefficients are bounded below by
  the bilinear interpolation of exact corner values minus `Mτ Δτ²/8 + Ms Δs²/8`, with `Mτ, Ms`
  rigorous second-derivative bounds (second-order forward mode in fixed-point ball arithmetic,
  `hessOK`); positivity at the corners is a Pólya test (`cornerOK`, shared between neighbouring
  boxes; `leaf2_sound`). Boxes touching the axis use the exact vanishing at `s = 0`
  (`axis2_sound`). The half circle `x < 0` follows by up–down
  symmetry (`Nline_pos_of_psi`).

## Scope and trust

The ballooning reduction (high-`n` eikonal `δW` ↦ line energy) is the SUPPLIED interface of
`BallooningReduction`; the curvature enters through `B × k · κ`. All box checks are kernel
evaluations of integer arithmetic (standard axioms only); the certificate data and the
subdivision plan come from the untrusted oracle `scripts/solovev_ballooning_oracle.py` and are
not part of the trusted base.
-/

public section
noncomputable section

namespace PlasmaLean.Design.SolovevBallooning

open Real Set Tm
open PlasmaLean.Stability.BallooningReduction

/-! ## The certificate data are admissible and vanish on the axis -/

/-- The certificate data only involve `√2` and `s`. -/
theorem gdata_ok : DataOK gdata := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [gdata, UsesOnly, tS, tr]

/-- Coefficients vanish when `A = g₁ = g₂ = d̂ = s = 0`. -/
theorem etree_axis {b : ℕ → ℝ} (h3 : b 3 = 0) (h4 : b 4 = 0) (h5 : b 5 = 0) (h6 : b 6 = 0)
    (h11 : b 11 = 0) (k : ℕ) : (etree k).eval b = 0 := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;>
    simp [etree, tin, tgg, Tm.eval, Tm.sub, h3, h4, h5, h6, h11]

/-- A Horner tree with vanishing coefficients vanishes. -/
theorem ptree_eval_zero {l : List Tm} {ρ : ℕ → ℝ} (hl : ∀ e ∈ l, e.eval ρ = 0) (y : Tm) :
    (ptree l y).eval ρ = 0 := by
  induction l with
  | nil => simp [ptree, Tm.eval]
  | cons e l ih =>
    simp [ptree, Tm.eval, hl e (by simp), ih (fun e' he' => hl e' (by simp [he']))]

/-- The derivative of a Horner tree with vanishing data coefficients vanishes. -/
theorem diff_ptree_zero {l : List Tm} {ρ : ℕ → ℝ} (hl : ∀ e ∈ l, e.eval ρ = 0)
    (hd : ∀ e ∈ l, e.UsesOnly DV) : (diff dvT (ptree l tY)).eval ρ = 0 := by
  induction l with
  | nil => simp [ptree, diff, Tm.eval]
  | cons e l ih =>
    have hl' : ∀ e' ∈ l, e'.eval ρ = 0 := fun e' he' => hl e' (by simp [he'])
    have hd' : ∀ e' ∈ l, e'.UsesOnly DV := fun e' he' => hd e' (by simp [he'])
    simp [ptree, diff, Tm.eval, diff_data_zero (hd e (by simp)), ih hl' hd',
      ptree_eval_zero hl']

/-- `R = L = 10` on the magnetic axis. -/
theorem Rcc_axis (τ : ℝ) : Rcc τ 0 = 10 := by
  rw [Rcc, show (100 : ℝ) + 2 * (0 * ycc τ) = 10 ^ 2 by ring, Real.sqrt_sq (by norm_num)]

/-- `|B|² = (F/L)² = 25` on the magnetic axis. -/
theorem B2c_axis (τ : ℝ) : B2c τ 0 = 25 := by
  simp only [B2c, tB2, tBR, tBP, tBZ, tWh, tzh, tX, tY, tR, tr, tiR, tS, Tm.eval, env0, envR,
    Rcc_axis]
  norm_num

/-- **The coefficients of the certificate vanish on the magnetic axis** `s = 0` (the leading
oscillation `s q₀ = −(3√2/35) y` of the drive is cancelled exactly by `f₀ = (3√2/35) x`). -/
theorem gdata_axis (τ : ℝ) (k : ℕ) : ecE gdata k τ 0 = 0 := by
  have hD := gdata_ok
  obtain ⟨h0, h1, h2⟩ := dataA_DV hD
  have hρ0 : ∀ e ∈ gdata.A1, e.eval (chartEnv τ 0) = 0 := by
    simp [gdata, Tm.eval, tS, chartEnv, envR]
  have hρ2 : ∀ e ∈ gdata.A2, e.eval (chartEnv τ 0) = 0 := by
    simp [gdata, Tm.eval, tS, chartEnv, envR]
  have hA0 : ∀ e ∈ gdata.A0.tail, e.eval (chartEnv τ 0) = 0 := by
    simp [gdata, Tm.eval, tS, chartEnv, envR]
  have hr : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply etree_axis
  · -- `A = s q₀ − f₀' = 0`
    simp only [bAt, baseT, Tm.sub, Tm.eval]
    have hf0 : (diff dvT (tf0 gdata)).eval (chartEnv τ 0) = -(3 / 35 * √2) * ycc τ := by
      have e1 : (diff dvT (ptree gdata.A0.tail tY)).eval (chartEnv τ 0) = 0 :=
        diff_ptree_zero hA0 (fun e he => h0 e (List.mem_of_mem_tail he))
      have e2 : (ptree gdata.A0.tail tY).eval (chartEnv τ 0) = 0 := ptree_eval_zero hA0 _
      simp only [gdata, List.tail] at e1 e2
      simp [tf0, gdata, ptree, diff, dvT, Tm.eval, tX, tY, tr, tS, chartEnv, envR]
      ring
    rw [hf0]
    simp only [tsq0, tcross, tkR, tkP, tkZ, tgtR, tgtZ, tGR, tGZ, tBR, tBP, tBZ, tWh, tzh, tiR3,
      trate, tell, tX, tY, tR, tr, tiR, tiB, tS, Tm.sub, Tm.eval, chartEnv, envR, Rcc_axis,
      B2c_axis]
    ring_nf
    rw [show √2 ^ 3 = √2 ^ 2 * √2 by ring, hr]
    ring
  · simp only [bAt, baseT]
    simp only [tf1, diff, Tm.eval, diff_ptree_zero hρ0 h1, ptree_eval_zero hρ0]
    ring
  · simp only [bAt, baseT, tf2]
    exact diff_ptree_zero hρ2 h2
  · simp [bAt, baseT, td, Tm.eval, tS, chartEnv, envR]
  · simp [bAt, baseT, tS, Tm.eval, chartEnv, envR]

/-! ## The cover of the `(τ, s)` rectangle -/

set_option maxRecDepth 100000 in
/-- **The cover certificate of `[−1, 1] × [0, 25]`**, assembled from the 825 kernel-checked
boxes of the cell modules. -/
theorem cover_all : Cover gdata (-4096) 4096 0 25600 := by
  ballooning_cover "S1024 T-3072 T-3584 T-3840 T-3968 S512 @cov0 @cov1 S512 @cov2 @cov3 T-3712 \
    S512 @cov4 @cov5 S512 @cov6 @cov7 T-3328 T-3456 S512 @cov8 @cov9 S512 @cov10 @cov11 T-3200 \
    S512 @cov12 @cov13 S512 @cov14 @cov15 T-2048 T-2560 T-2816 T-2944 S512 @cov16 @cov17 S512 \
    @cov18 @cov19 T-2688 S512 @cov20 @cov21 S512 @cov22 @cov23 T-2304 T-2432 S512 @cov24 \
    @cov25 S512 @cov26 @cov27 T-2176 S512 @cov28 @cov29 T-2112 @cov30 @cov31 T-1024 T-1536 \
    T-1792 T-1920 T-1984 @cov32 @cov33 T-1856 @cov34 @cov35 T-1664 T-1728 @cov36 @cov37 T-1600 \
    @cov38 @cov39 T-1280 T-1408 T-1472 @cov40 @cov41 @cov42 T-1152 @cov43 @cov44 T0 T-512 \
    T-768 T-896 @cov45 @cov46 T-640 @cov47 @cov48 T-256 T-384 @cov49 @cov50 @cov51 T1024 T512 \
    T256 @cov52 T384 @cov53 @cov54 T768 T640 @cov55 @cov56 T896 @cov57 @cov58 T2048 T1536 \
    T1280 T1152 @cov59 @cov60 T1408 @cov61 @cov62 T1792 T1664 @cov63 @cov64 T1920 @cov65 \
    @cov66 T3072 T2560 T2304 T2176 @cov67 @cov68 T2432 @cov69 T2496 @cov70 @cov71 T2816 T2688 \
    T2624 @cov72 @cov73 T2752 @cov74 @cov75 T2944 T2880 @cov76 @cov77 T3008 @cov78 @cov79 \
    T3584 T3328 T3200 T3136 @cov80 @cov81 T3264 @cov82 @cov83 S512 T3456 @cov84 @cov85 @cov86 \
    T3840 T3712 T3648 @cov87 @cov88 @cov89 T3968 @cov90 @cov91 S2048 T-3072 T-3584 T-3840 \
    T-3968 @cov92 @cov93 T-3712 @cov94 @cov95 T-3328 T-3456 @cov96 @cov97 T-3200 @cov98 @cov99 \
    T-2048 T-2560 T-2816 T-2944 @cov100 @cov101 T-2688 @cov102 @cov103 T-2304 T-2432 @cov104 \
    @cov105 T-2176 @cov106 @cov107 T-1024 T-1536 T-1792 T-1920 @cov108 @cov109 T-1664 @cov110 \
    @cov111 T-1280 T-1408 @cov112 @cov113 T-1152 @cov114 @cov115 T0 T-512 T-768 T-896 @cov116 \
    @cov117 T-640 @cov118 @cov119 T-256 @cov120 @cov121 T1024 T512 T256 @cov122 T384 @cov123 \
    @cov124 T768 T640 @cov125 @cov126 T896 @cov127 @cov128 T2048 T1536 T1280 T1152 @cov129 \
    @cov130 T1408 @cov131 @cov132 T1792 T1664 @cov133 @cov134 T1920 @cov135 @cov136 T3072 \
    T2560 T2304 T2176 @cov137 @cov138 T2432 @cov139 @cov140 T2816 T2688 @cov141 @cov142 T2944 \
    @cov143 @cov144 T3584 T3328 @cov145 @cov146 T3840 @cov147 @cov148 S4096 T-3072 T-3584 \
    T-3840 S3072 @cov149 @cov150 S3072 @cov151 @cov152 T-3328 S3072 @cov153 @cov154 S3072 \
    T-3200 @cov155 @cov156 @cov157 T-2048 T-2560 T-2816 S3072 T-2944 @cov158 @cov159 @cov160 \
    S3072 T-2688 @cov161 @cov162 @cov163 T-2304 S3072 T-2432 @cov164 @cov165 @cov166 S3072 \
    T-2176 @cov167 @cov168 @cov169 T-1024 T-1536 T-1792 S3072 @cov170 @cov171 T-1664 @cov172 \
    @cov173 T-1280 T-1408 @cov174 @cov175 T-1152 @cov176 @cov177 T0 T-512 T-768 T-896 @cov178 \
    @cov179 T-640 @cov180 @cov181 T-256 T-384 @cov182 @cov183 @cov184 T1024 T512 T256 @cov185 \
    T384 @cov186 @cov187 T768 T640 @cov188 @cov189 T896 @cov190 @cov191 T2048 T1536 T1280 \
    T1152 @cov192 @cov193 T1408 @cov194 @cov195 T1792 T1664 @cov196 @cov197 T1920 @cov198 \
    @cov199 T3072 T2560 T2304 T2176 @cov200 @cov201 T2432 @cov202 @cov203 T2816 T2688 @cov204 \
    @cov205 T2944 @cov206 @cov207 T3584 T3328 T3200 @cov208 @cov209 T3456 @cov210 @cov211 \
    T3840 T3712 @cov212 @cov213 T3968 @cov214 @cov215 S6144 T-3072 T-3584 T-3840 S5120 @cov216 \
    @cov217 S5120 @cov218 @cov219 T-3328 S5120 @cov220 @cov221 S5120 @cov222 @cov223 T-2048 \
    T-2560 T-2816 S5120 @cov224 @cov225 S5120 @cov226 @cov227 T-2304 T-2432 @cov228 @cov229 \
    T-2176 @cov230 @cov231 T-1024 T-1536 T-1792 T-1920 @cov232 @cov233 T-1664 @cov234 @cov235 \
    T-1280 T-1408 @cov236 @cov237 T-1152 @cov238 @cov239 T0 T-512 T-768 T-896 @cov240 @cov241 \
    @cov242 T-256 @cov243 @cov244 T1024 T512 T256 @cov245 @cov246 T768 T640 @cov247 @cov248 \
    T896 @cov249 @cov250 T2048 T1536 T1280 T1152 @cov251 @cov252 T1408 @cov253 @cov254 T1792 \
    T1664 @cov255 @cov256 T1920 @cov257 @cov258 T3072 T2560 T2304 T2176 @cov259 @cov260 T2432 \
    @cov261 @cov262 T2816 T2688 @cov263 @cov264 T2944 @cov265 @cov266 T3584 T3328 T3200 \
    @cov267 @cov268 @cov269 T3840 @cov270 @cov271 S8192 T-3072 T-3584 T-3840 S7168 @cov272 \
    @cov273 S7168 @cov274 @cov275 T-3328 S7168 @cov276 @cov277 S7168 @cov278 @cov279 T-2048 \
    T-2560 T-2816 S7168 @cov280 @cov281 S7168 @cov282 @cov283 T-2304 T-2432 @cov284 @cov285 \
    T-2176 @cov286 @cov287 T-1024 T-1536 T-1792 T-1920 @cov288 @cov289 T-1664 @cov290 @cov291 \
    T-1280 T-1408 @cov292 @cov293 T-1152 @cov294 @cov295 T0 T-512 T-768 T-896 @cov296 @cov297 \
    @cov298 T-256 @cov299 @cov300 T1024 T512 T256 @cov301 @cov302 T768 @cov303 T896 @cov304 \
    @cov305 T2048 T1536 T1280 T1152 @cov306 @cov307 @cov308 T1792 @cov309 @cov310 T3072 T2560 \
    T2304 @cov311 @cov312 T2816 @cov313 @cov314 T3584 T3328 @cov315 @cov316 T3840 @cov317 \
    @cov318 S12288 T-3072 T-3584 T-3840 S10240 S9216 @cov319 @cov320 S11264 @cov321 @cov322 \
    S10240 S9216 @cov323 @cov324 S11264 @cov325 @cov326 T-3328 S10240 S9216 @cov327 @cov328 \
    S11264 @cov329 @cov330 S10240 S9216 @cov331 @cov332 T-3200 T-3264 @cov333 @cov334 T-3136 \
    @cov335 @cov336 T-2048 T-2560 T-2816 T-2944 T-3008 S10240 @cov337 @cov338 S10240 @cov339 \
    @cov340 T-2880 S10240 @cov341 @cov342 S10240 @cov343 @cov344 T-2688 T-2752 S10240 @cov345 \
    @cov346 S10240 @cov347 @cov348 T-2624 S10240 @cov349 @cov350 S10240 @cov351 @cov352 T-2304 \
    T-2432 S10240 @cov353 T-2496 @cov354 @cov355 S10240 @cov356 T-2368 @cov357 @cov358 T-2176 \
    S10240 @cov359 @cov360 S10240 @cov361 @cov362 T-1024 T-1536 T-1792 T-1920 S10240 @cov363 \
    @cov364 S10240 @cov365 @cov366 T-1664 S10240 @cov367 @cov368 S10240 @cov369 @cov370 T-1280 \
    T-1408 S10240 @cov371 @cov372 T-1344 @cov373 @cov374 T-1152 T-1216 @cov375 @cov376 T-1088 \
    @cov377 @cov378 T0 T-512 T-768 T-896 @cov379 @cov380 T-640 @cov381 @cov382 T-256 T-384 \
    @cov383 @cov384 @cov385 T1024 T512 T256 @cov386 T384 @cov387 @cov388 T768 T640 @cov389 \
    @cov390 T896 @cov391 @cov392 T2048 T1536 T1280 T1152 @cov393 @cov394 T1408 @cov395 @cov396 \
    T1792 T1664 @cov397 @cov398 S10240 @cov399 @cov400 T3072 T2560 T2304 S10240 @cov401 \
    @cov402 S10240 @cov403 @cov404 T2816 S10240 @cov405 @cov406 S10240 @cov407 @cov408 T3584 \
    T3328 S10240 @cov409 @cov410 S10240 @cov411 @cov412 T3840 S10240 @cov413 @cov414 S10240 \
    @cov415 @cov416 S16384 T-3072 T-3584 T-3840 T-3968 S14336 @cov417 @cov418 S14336 @cov419 \
    @cov420 S14336 S13312 @cov421 @cov422 S15360 @cov423 @cov424 T-3328 S14336 S13312 @cov425 \
    @cov426 S15360 @cov427 @cov428 T-3200 T-3264 S14336 @cov429 @cov430 S14336 @cov431 @cov432 \
    T-3136 S14336 @cov433 @cov434 S14336 @cov435 @cov436 T-2048 T-2560 T-2816 T-2944 T-3008 \
    S14336 @cov437 @cov438 S14336 @cov439 @cov440 S14336 T-2880 @cov441 @cov442 S15360 @cov443 \
    @cov444 T-2688 S14336 T-2752 @cov445 @cov446 S15360 @cov447 @cov448 S14336 T-2624 @cov449 \
    @cov450 S15360 @cov451 @cov452 T-2304 T-2432 T-2496 S14336 @cov453 @cov454 S14336 @cov455 \
    @cov456 T-2368 S14336 @cov457 @cov458 S14336 @cov459 @cov460 T-2176 T-2240 S14336 @cov461 \
    @cov462 S14336 @cov463 @cov464 T-2112 S14336 @cov465 @cov466 S14336 @cov467 @cov468 T-1024 \
    T-1536 T-1792 T-1920 S14336 @cov469 T-1984 @cov470 @cov471 S14336 @cov472 @cov473 T-1664 \
    S14336 @cov474 @cov475 S14336 @cov476 @cov477 T-1280 T-1408 S14336 @cov478 @cov479 T-1344 \
    @cov480 @cov481 T-1152 T-1216 @cov482 @cov483 T-1088 @cov484 @cov485 T0 T-512 T-768 T-896 \
    @cov486 @cov487 T-640 @cov488 @cov489 T-256 T-384 @cov490 @cov491 @cov492 T1024 T512 T256 \
    T128 @cov493 @cov494 T384 @cov495 @cov496 T768 T640 @cov497 @cov498 T896 @cov499 @cov500 \
    T2048 T1536 T1280 T1152 @cov501 @cov502 T1408 @cov503 @cov504 T1792 T1664 @cov505 @cov506 \
    T1920 @cov507 @cov508 T3072 T2560 T2304 T2176 @cov509 @cov510 S14336 @cov511 @cov512 T2816 \
    S14336 @cov513 @cov514 S14336 @cov515 @cov516 T3584 T3328 S14336 @cov517 @cov518 S14336 \
    @cov519 @cov520 T3840 T3712 @cov521 @cov522 T3968 @cov523 @cov524 S20480 T-3072 T-3584 \
    T-3840 T-3968 S18432 @cov525 @cov526 S18432 @cov527 @cov528 T-3712 S18432 @cov529 @cov530 \
    S18432 @cov531 @cov532 T-3328 S18432 S17408 @cov533 @cov534 S19456 @cov535 @cov536 T-3200 \
    T-3264 S18432 @cov537 @cov538 S18432 @cov539 @cov540 T-3136 S18432 @cov541 @cov542 S18432 \
    @cov543 @cov544 T-2048 T-2560 T-2816 T-2944 T-3008 S18432 @cov545 @cov546 S18432 @cov547 \
    @cov548 T-2880 S18432 @cov549 @cov550 S18432 @cov551 @cov552 T-2688 S18432 S17408 @cov553 \
    @cov554 T-2752 @cov555 @cov556 S18432 S17408 @cov557 @cov558 S19456 @cov559 @cov560 T-2304 \
    T-2432 S18432 S17408 @cov561 @cov562 S19456 @cov563 @cov564 S18432 S17408 @cov565 @cov566 \
    S19456 @cov567 @cov568 T-2176 S18432 S17408 @cov569 @cov570 S19456 @cov571 @cov572 S18432 \
    T-2112 @cov573 @cov574 S19456 @cov575 @cov576 T-1024 T-1536 T-1792 T-1920 S18432 T-1984 \
    @cov577 @cov578 S19456 @cov579 @cov580 T-1856 S18432 @cov581 @cov582 S18432 @cov583 \
    @cov584 T-1664 T-1728 S18432 @cov585 @cov586 S18432 @cov587 @cov588 S18432 @cov589 T-1600 \
    @cov590 @cov591 T-1280 T-1408 S18432 @cov592 T-1472 @cov593 @cov594 S18432 @cov595 @cov596 \
    T-1152 T-1216 @cov597 @cov598 T-1088 @cov599 @cov600 T0 T-512 T-768 T-896 @cov601 @cov602 \
    T-640 @cov603 @cov604 T-256 T-384 @cov605 @cov606 T-128 @cov607 @cov608 T1024 T512 T256 \
    T128 @cov609 @cov610 T384 @cov611 @cov612 T768 T640 @cov613 @cov614 T896 @cov615 @cov616 \
    T2048 T1536 T1280 T1152 @cov617 @cov618 T1408 @cov619 @cov620 T1792 T1664 @cov621 @cov622 \
    T1920 @cov623 @cov624 T3072 T2560 T2304 T2176 @cov625 @cov626 T2432 @cov627 @cov628 T2816 \
    T2688 @cov629 @cov630 T2944 @cov631 @cov632 T3584 T3328 T3200 @cov633 @cov634 T3456 \
    @cov635 @cov636 T3840 T3712 @cov637 @cov638 T3968 @cov639 @cov640 T-3072 T-3584 T-3840 \
    S23040 S21760 @cov641 @cov642 S24320 @cov643 @cov644 S23040 S21760 @cov645 @cov646 S24320 \
    @cov647 @cov648 T-3328 T-3456 S23040 S21760 @cov649 @cov650 S24320 @cov651 @cov652 S23040 \
    S21760 @cov653 @cov654 S24320 @cov655 @cov656 T-3200 S23040 S21760 @cov657 @cov658 S24320 \
    @cov659 @cov660 S23040 S21760 @cov661 @cov662 S24320 @cov663 @cov664 T-2048 T-2560 T-2816 \
    T-2944 S23040 S21760 @cov665 @cov666 S24320 @cov667 @cov668 S23040 S21760 @cov669 @cov670 \
    S24320 @cov671 @cov672 T-2688 S23040 S21760 @cov673 @cov674 S24320 @cov675 @cov676 S23040 \
    S21760 @cov677 @cov678 S24320 @cov679 @cov680 T-2304 T-2432 S23040 S21760 @cov681 @cov682 \
    S24320 @cov683 @cov684 S23040 S21760 @cov685 @cov686 S24320 @cov687 @cov688 T-2176 T-2240 \
    S23040 S21760 @cov689 @cov690 S24320 @cov691 @cov692 S23040 S21760 @cov693 @cov694 S24320 \
    @cov695 @cov696 T-2112 S23040 S21760 @cov697 @cov698 S24320 @cov699 @cov700 S23040 S21760 \
    @cov701 @cov702 S24320 @cov703 @cov704 T-1024 T-1536 T-1792 T-1920 T-1984 S23040 S21760 \
    @cov705 @cov706 S24320 @cov707 @cov708 S23040 S21760 @cov709 @cov710 S24320 @cov711 \
    @cov712 T-1856 S23040 S21760 @cov713 @cov714 S24320 @cov715 @cov716 S23040 S21760 @cov717 \
    @cov718 S24320 @cov719 @cov720 T-1664 T-1728 S23040 S21760 @cov721 @cov722 S24320 @cov723 \
    @cov724 S23040 S21760 @cov725 @cov726 S24320 @cov727 T-1696 @cov728 @cov729 S23040 S21760 \
    @cov730 T-1600 @cov731 @cov732 T-1600 S24320 @cov733 T-1632 @cov734 @cov735 S24320 @cov736 \
    T-1568 @cov737 @cov738 T-1280 T-1408 S23040 S21760 @cov739 @cov740 T-1472 S24320 @cov741 \
    T-1504 @cov742 @cov743 S24320 @cov744 @cov745 T-1344 S23040 @cov746 S24320 @cov747 @cov748 \
    S23040 @cov749 S24320 @cov750 @cov751 T-1152 T-1216 S23040 @cov752 T-1248 @cov753 @cov754 \
    S23040 @cov755 @cov756 S23040 @cov757 T-1088 @cov758 @cov759 T0 T-512 T-768 T-896 S23040 \
    @cov760 T-960 @cov761 @cov762 S23040 @cov763 T-832 @cov764 @cov765 T-640 S23040 @cov766 \
    @cov767 T-576 @cov768 @cov769 T-256 T-384 T-448 @cov770 @cov771 @cov772 T-128 @cov773 \
    @cov774 T1024 T512 T256 T128 @cov775 @cov776 T384 @cov777 @cov778 T768 T640 @cov779 \
    @cov780 T896 T832 @cov781 @cov782 T960 @cov783 @cov784 T2048 T1536 T1280 T1152 T1088 \
    @cov785 @cov786 T1216 @cov787 @cov788 T1408 T1344 @cov789 @cov790 S23040 @cov791 @cov792 \
    T1792 T1664 S23040 @cov793 @cov794 S23040 @cov795 @cov796 T1920 S23040 @cov797 @cov798 \
    S23040 @cov799 @cov800 T3072 T2560 T2304 T2176 S23040 @cov801 @cov802 S23040 @cov803 \
    @cov804 T2432 S23040 @cov805 @cov806 S23040 @cov807 @cov808 T2816 T2688 S23040 @cov809 \
    @cov810 S23040 @cov811 @cov812 T2944 S23040 @cov813 @cov814 T3008 @cov815 @cov816 T3584 \
    T3328 S23040 @cov817 @cov818 S23040 @cov819 @cov820 T3840 S23040 @cov821 @cov822 S23040 \
    @cov823 @cov824"

/-- **Positivity of the numerator on the whole chart**: `Ψ(τ, s, σ̃) > 0` for `τ ∈ [−1, 1]`,
`0 < s ≤ 25`, `σ̃ ∈ ℝ`. -/
theorem psi_pos_all {τ s : ℝ} (hτ : τ ∈ Icc (-1 : ℝ) 1) (hs0 : 0 < s) (hs : s ≤ 25) (σ : ℝ) :
    0 < Psi gdata τ s σ := by
  refine Cover.sound gdata_axis cover_all ?_ ?_ hs0 σ
  · rw [NT_real]; norm_num; exact hτ
  · rw [NS_real]; norm_num; exact ⟨hs0.le, hs⟩

/-! ## Ballooning stability of all surfaces -/

/-- **Ideal-ballooning stability of ALL flux surfaces of the reactor Solov'ev equilibrium.**
For every surface `ψ̃ = s²`, `0 < s ≤ 25` (magnetic axis to plasma edge), and every eikonal
family (shift `c`, i.e. every `θ_k`), the ballooning line of the exact field line `lineS`
has nonnegative energy for every compactly supported `C¹` mode. -/
theorem reactor_ballooning_all (s : ℝ) (hs0 : 0 < s) (hs : s ≤ 25) (c : ℝ) :
    (reactorLine hs0 hs c).Stable :=
  reactorLine_stable_of_N gdata_ok hs0 hs
    (Nline_pos_of_psi gdata_ok hs0 hs fun _ hτ σ => psi_pos_all hτ hs0 hs σ) c

/-- **Ideal-ballooning stability of the reactor surface `ψ̃ = 1`** (`s = 1`). -/
theorem reactor_ballooning_s1 (c : ℝ) :
    (reactorLine (s := 1) (by norm_num) (by norm_num) c).Stable :=
  reactor_ballooning_all 1 _ _ c

/-- **Ideal-ballooning stability of the reactor surface `ψ̃ = 4`** (`s = 2`). -/
theorem reactor_ballooning_s2 (c : ℝ) :
    (reactorLine (s := 2) (by norm_num) (by norm_num) c).Stable :=
  reactor_ballooning_all 2 _ _ c

/-- **Ideal-ballooning stability of the reactor surface `ψ̃ = 9`** (`s = 3`). -/
theorem reactor_ballooning_s3 (c : ℝ) :
    (reactorLine (s := 3) (by norm_num) (by norm_num) c).Stable :=
  reactor_ballooning_all 3 _ _ c

/-- **Ideal-ballooning stability of the reactor surface `ψ̃ = 16`** (`s = 4`). -/
theorem reactor_ballooning_s4 (c : ℝ) :
    (reactorLine (s := 4) (by norm_num) (by norm_num) c).Stable :=
  reactor_ballooning_all 4 _ _ c

/-- **Ideal-ballooning stability of the plasma edge** `ψ̃ = L⁴/16` (`s = 25`). -/
theorem reactor_ballooning_edge (c : ℝ) :
    (reactorLine (s := 25) (by norm_num) le_rfl c).Stable :=
  reactor_ballooning_all 25 _ _ c

/-! ## Sanity checks -/

/-- Rejected fixture: without the oscillating profiles (`A₀ = A₁ = A₂ = 0`, same `δ`) an
outboard box near `s = 4` fails, so the profiles are essential and the checker is not
vacuous. -/
theorem noProfile_rejected :
    boxOK ⟨gdata.dl, [], [], []⟩ 2048 2304 4096 5120 = false := by bl_cert

/-- Accepted fixture: a single box of the cover passes. -/
theorem box_accepted : boxOK gdata (-3584) (-3328) 4096 5120 = true := by bl_cert

/-- The axis box test refuses boxes away from the axis: `axisOK` needs `n₁ > 0` and the
axis boxes are only used through `Cover.axis` (lower edge `s = 0`). -/
theorem axisOK_needs_positive : axisOK gdata (-4096) (-3840) 0 = false := by bl_cert

end PlasmaLean.Design.SolovevBallooning
