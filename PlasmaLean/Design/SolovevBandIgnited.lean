/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBandHighQ
public import PlasmaLean.Certificates.KernelFact

/-!
# An ignited two-sided transport band on the Solov'ev geometry: `solovev_one_plasma_ignited`

Labels: *geometry class* `IsSolovevGeometry` (reused unchanged from `Design.SolovevBand`;
**proved for the actual reactor Solov'ev field** by
`SolovevFluxGeometry.solovevFluxGeometry_isSolovev`, see the `_actual` theorem; the remaining
unformalized link is the coarea formula / change of variables stated in
`Design.SolovevFluxGeometry`), *synthetic reactor-scale data*, Bosch–Hale reactivity as
*supplied data*
(the fine class `Transport.BoschHaleFine`), quasilinear transport law *supplied* (rational
stand-in `χ₀ (1/10 + T²/100)`; only this stand-in is certified).

## Model

The generic machinery of `Design.SolovevBandHighQ` (`coeffsA`, `tsub_margin_gen`,
`tsup_margin_gen`, `pressure_gen`, `band_gen`) with **no auxiliary heating**
(`ignited_aux = 0`): the source is alpha heating minus bremsstrahlung only,
`R(s,T) = (n/10²⁰)(α ⟨σv⟩(T) − b √T)`. Density, geometry class, Kirchhoff transform, edge
temperature `[1, 3/2]` keV and the reactor Solov'ev field are those of `SolovevBand`.

Parameters that differ from `SolovevBandHighQ`:

* `P_aux = 0` (**ignited**, `Q = ∞`);
* transport window `χ₀ ∈ [63 / 100, 16 / 25]` m²/s (width `0.01`, ±0.8 %): near ignition
  the band is very sensitive to `χ₀`. With the worst geometry corner taken pointwise (as the
  four-corner certificate requires) the lower problem has no hot steady state at
  `χ₀ = 0.65`, so the window cannot extend much above `0.64`; below `0.63` the upper barrier
  is too hot for the pressure ceiling;
* pressure offset `Δ = 90000 Pa` (`2.25×` the 40 kPa of `SolovevBand`; ≈ 20 % of the axis
  pressure `p₀ ≈ 457 kPa`). With `Δ = 40 kPa` the ignited upper barrier violates the pressure
  ceiling (oracle ratio `1.11` at `χ₀ = 0.6`); at this window the oracle ratio is `0.983` for
  `Δ = 90 kPa`, so `Δ = 80 kPa` fails as well. `Δ` is an unmodelled edge pedestal: a pressure
  jump of the equilibrium at the boundary needs an **edge current sheet**, outside the
  kernel's pointwise `ForceBalance` (the layer and exterior are not modelled). At `s = 1` the
  MHD pressure is `p_eq(1) + Δ ≈ 38 + 90 ≈ 128 kPa`, whereas the plasma's kinetic pressure is
  only `n(1)(1 + r_i) T_edge keV ≈ 12 kPa`; the pressure ceiling is far from tight there.

## Results

* `ignited_band`: two-sided band for all time, `T ≥ 10 keV` on `s ≤ 3/10`, `T ≤ 20 keV`.
* `ignited_pressure`: `n(s)(1 + 53/60) T_sup(s) keV ≤ p_eq(s) + Δ` on `[0,1]`.
* `solovev_one_plasma_ignited`: same structure as `SolovevBand.solovev_one_plasma`.

## Oracle numbers (Python, untrusted; `/tmp/k4`)

Nominal steady states (`g = 0.51 s`, `h = 0.51`, Bosch–Hale fit, 200 cells,
`V' = 1599 (1 + s/20) m³`): `χ₀ = 0.63`: `T(0) = 17.8`, `T(3/10) = 15.7` keV,
`P_α ≈ 191 MW`; `χ₀ = 0.64`: `T(0) = 17.5`, `T(3/10) = 15.4` keV, `P_α ≈ 185 MW`;
`P_aux = 0`, fusion power `≈ 0.93–0.96 GW`, `max p/(p_eq + Δ) < 0.9`. Worst-case barrier
profiles: `T_sub(3/10) ≈ 11.5 keV`, `T_sup(0) ≈ 19.8 keV`.

## Honest limitations

As for `SolovevBand` and `SolovevBandHighQ`; in addition the transport window is narrow
(±0.8 %), and `Δ = 90 kPa` is a large offset.
-/

public section

noncomputable section

namespace PlasmaLean.Design.SolovevBandIgnited

open Set Filter Topology PlasmaLean.Transport PlasmaLean.Fusion PlasmaLean.Certificates
  PlasmaLean.Design.TransportBarrier PlasmaLean.Design.QuasilinearBarrier
  PlasmaLean.Design.SolovevOnePlasma PlasmaLean.Fields PlasmaLean.Kinetic
  PlasmaLean.Design.Solovev PlasmaLean.Design.SolovevAlpha PlasmaLean.Design.SolovevBand
  PlasmaLean.Design.SolovevBandHighQ PlasmaLean.Design.SolovevFluxGeometry WithLp

/-! ### ignited: barrier data (Python oracle `/tmp/k4/run2.py`, untrusted; checked below) -/

/-- No auxiliary heating: `q_aux = 0` (ignited). -/
@[expose] def ignited_aux : List ℚ := []

/-- Level function of the lower barrier, `F_sub = Φ(T_sub)`. -/
@[expose] def ignited_fs : List ℚ :=
  [6849517/750000, -1328027/125000, 3327301/1000000, -6191567/1000000, 22764141/500000,
   -233693309/1000000, 773171867/1000000, -1712759469/1000000, 2557560419/1000000,
   -634661771/250000, 801243119/500000, -580956633/1000000, 18353763/200000]

/-- Level function of the upper barrier, `F_sup = Φ(T_sup)`. -/
@[expose] def ignited_fu : List ℚ :=
  [27850611/1000000, -27067031/1000000, 351093/100000, -11556133/1000000, 18089877/200000,
   -485734907/1000000, 103803273/62500, -3773549911/1000000, 7172733/1250, -1441638957/250000,
   1832985109/500000, -26632737/20000, 104720999/500000]

/-- Pieces of the lower-barrier certificates (lower labels on the fine grid). -/
@[expose] def ignited_subP : List (ℚ × ℚ × ℚ) :=
  [(1/200, 53/4, 133/10), (243/5000, 13, 133/10), (229/2500, 51/4, 261/20), (1341/10000, 25/2,
   64/5), (1759/10000, 49/4, 251/20), (2171/10000, 12, 123/10), (103/400, 47/4, 241/20),
   (2971/10000, 23/2, 59/5), (3359/10000, 45/4, 231/20), (3737/10000, 11, 113/10), (2053/5000,
   43/4, 221/20), (279/625, 21/2, 54/5), (1203/2500, 41/4, 211/20), (5147/10000, 10, 103/10),
   (5471/10000, 39/4, 201/20), (2891/5000, 19/2, 49/5), (76/125, 37/4, 191/20), (1273/2000, 9,
   93/10), (1659/2500, 35/4, 181/20), (3447/5000, 17/2, 44/5), (3569/5000, 33/4, 171/20),
   (7369/10000, 8, 83/10), (3793/5000, 31/4, 161/20), (779/1000, 15/2, 39/5), (7981/10000, 29/4,
   151/20), (8159/10000, 7, 73/10), (4163/5000, 27/4, 141/20), (106/125, 13/2, 34/5), (539/625,
   25/4, 131/20), (8757/10000, 6, 63/10), (8881/10000, 23/4, 121/20), (4497/5000, 11/2, 29/5),
   (9099/10000, 21/4, 111/20), (2299/2500, 5, 53/10), (9509/10000, 4, 101/20), (973/1000, 3,
   81/20), (1977/2000, 2, 61/20), (1, 1, 41/20)]

/-- Pieces of the upper-barrier certificates (upper labels end supplied windows). -/
@[expose] def ignited_supP : List (ℚ × ℚ × ℚ) :=
  [(73/10000, 197/10, 20), (11/250, 389/20, 79/4), (801/10000, 96/5, 39/2), (231/2000, 379/20,
   77/4), (1503/10000, 187/10, 19), (1843/10000, 369/20, 75/4), (2177/10000, 91/5, 37/2),
   (2503/10000, 359/20, 73/4), (2821/10000, 177/10, 18), (3133/10000, 349/20, 71/4), (859/2500,
   86/5, 35/2), (933/2500, 339/20, 69/4), (201/500, 167/10, 17), (4299/10000, 329/20, 67/4),
   (4571/10000, 81/5, 33/2), (2417/5000, 319/20, 65/4), (509/1000, 157/10, 16), (667/1250, 309/20,
   63/4), (223/400, 76/5, 31/2), (1161/2000, 299/20, 61/4), (6027/10000, 147/10, 15), (78/125,
   289/20, 59/4), (3223/5000, 71/5, 29/2), (6643/10000, 279/20, 57/4), (427/625, 137/10, 14),
   (7013/10000, 269/20, 55/4), (7187/10000, 66/5, 27/2), (919/1250, 259/20, 53/4), (7511/10000,
   127/10, 13), (3831/5000, 249/20, 51/4), (1561/2000, 61/5, 25/2), (3971/5000, 239/20, 49/4),
   (8073/10000, 117/10, 12), (2049/2500, 229/20, 47/4), (4157/5000, 56/5, 23/2), (337/400, 219/20,
   45/4), (853/1000, 107/10, 11), (863/1000, 209/20, 43/4), (349/400, 51/5, 21/2), (4407/5000,
   199/20, 41/4), (4449/5000, 97/10, 10), (4489/5000, 189/20, 39/4), (9053/10000, 46/5, 19/2),
   (2281/2500, 179/20, 37/4), (919/1000, 87/10, 9), (9253/10000, 169/20, 35/4), (9311/10000, 41/5,
   17/2), (9367/10000, 159/20, 33/4), (4709/5000, 77/10, 8), (9467/10000, 149/20, 31/4),
   (1189/1250, 36/5, 15/2), (1911/2000, 139/20, 29/4), (1919/2000, 67/10, 7), (602/625, 129/20,
   27/4), (4833/5000, 31/5, 13/2), (9699/10000, 119/20, 25/4), (608/625, 57/10, 6), (2439/2500,
   109/20, 23/4), (4891/5000, 26/5, 11/2), (4903/5000, 99/20, 21/4), (1977/2000, 79/20, 5),
   (9943/10000, 59/20, 4), (624/625, 39/20, 3), (1, 3/2, 2)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- The literal list of rationals is long; its elaboration exceeds the default heartbeats.
/-- Pieces of the pressure certificate (upper labels in `1/8 keV`). -/
@[expose] def ignited_presP : List (ℚ × ℚ × ℚ) :=
  [(73/10000, 0, 159/8), (129/5000, 0, 79/4), (11/250, 0, 157/8), (311/5000, 0, 39/2), (801/10000,
   0, 155/8), (979/10000, 0, 77/4), (231/2000, 0, 153/8), (133/1000, 0, 19), (1503/10000, 0,
   151/8), (837/5000, 0, 75/4), (1843/10000, 0, 149/8), (2011/10000, 0, 37/2), (2177/10000, 0,
   147/8), (117/500, 0, 73/4), (2503/10000, 0, 145/8), (2663/10000, 0, 18), (2821/10000, 0,
   143/8), (1489/5000, 0, 71/4), (3133/10000, 0, 141/8), (657/2000, 0, 35/2), (859/2500, 0,
   139/8), (717/2000, 0, 69/4), (933/2500, 0, 137/8), (3877/10000, 0, 17), (201/500, 0, 135/8),
   (4161/10000, 0, 67/4), (4299/10000, 0, 133/8), (1109/2500, 0, 33/2), (4571/10000, 0, 131/8),
   (294/625, 0, 65/4), (2417/5000, 0, 129/8), (4963/10000, 0, 16), (509/1000, 0, 127/8),
   (2607/5000, 0, 63/4), (667/1250, 0, 125/8), (5457/10000, 0, 31/2), (223/400, 0, 123/8),
   (5691/10000, 0, 61/4), (1161/2000, 0, 121/8), (5917/10000, 0, 15), (6027/10000, 0, 119/8),
   (1227/2000, 0, 59/4), (78/125, 0, 117/8), (793/1250, 0, 29/2), (3223/5000, 0, 115/8),
   (1309/2000, 0, 57/4), (6643/10000, 0, 113/8), (3369/5000, 0, 14), (427/625, 0, 111/8),
   (1731/2500, 0, 55/4), (7013/10000, 0, 109/8), (7101/10000, 0, 27/2), (7187/10000, 0, 107/8),
   (727/1000, 0, 53/4), (919/1250, 0, 105/8), (929/1250, 0, 13), (7511/10000, 0, 103/8),
   (7587/10000, 0, 51/4), (3831/5000, 0, 101/8), (3867/5000, 0, 25/2), (1561/2000, 0, 99/8),
   (63/80, 0, 49/4), (3971/5000, 0, 97/8), (1001/1250, 0, 12), (8073/10000, 0, 95/8), (1627/2000,
   0, 47/4), (2049/2500, 0, 93/8), (516/625, 0, 23/2), (4157/5000, 0, 91/8), (837/1000, 0, 45/4),
   (337/400, 0, 89/8), (4239/5000, 0, 11), (853/1000, 0, 87/8), (8581/10000, 0, 43/4), (863/1000,
   0, 85/8), (4339/5000, 0, 21/2), (349/400, 0, 83/8), (877/1000, 0, 41/4), (4407/5000, 0, 81/8),
   (8857/10000, 0, 10), (4449/5000, 0, 79/8), (8939/10000, 0, 39/4), (4489/5000, 0, 77/8),
   (1127/1250, 0, 19/2), (9053/10000, 0, 75/8), (9089/10000, 0, 37/4), (2281/2500, 0, 73/8),
   (9157/10000, 0, 9), (919/1000, 0, 71/8), (4611/5000, 0, 35/4), (9253/10000, 0, 69/8),
   (9283/10000, 0, 17/2), (9311/10000, 0, 67/8), (467/500, 0, 33/4), (9367/10000, 0, 65/8),
   (9393/10000, 0, 8), (4709/5000, 0, 63/8), (9443/10000, 0, 31/4), (9467/10000, 0, 61/8),
   (949/1000, 0, 15/2), (1189/1250, 0, 59/8), (4767/5000, 0, 29/4), (1911/2000, 0, 57/8),
   (383/400, 0, 7), (1919/2000, 0, 55/8), (4807/5000, 0, 27/4), (602/625, 0, 53/8), (9649/10000,
   0, 13/2), (4833/5000, 0, 51/8), (9683/10000, 0, 25/4), (9699/10000, 0, 49/8), (4857/5000, 0,
   6), (608/625, 0, 47/8), (9743/10000, 0, 23/4), (2439/2500, 0, 45/8), (9769/10000, 0, 11/2),
   (4891/5000, 0, 43/8), (4897/5000, 0, 21/4), (4903/5000, 0, 41/8), (9817/10000, 0, 5),
   (2457/2500, 0, 39/8), (9839/10000, 0, 19/4), (9849/10000, 0, 37/8), (9859/10000, 0, 9/2),
   (2467/2500, 0, 35/8), (9877/10000, 0, 17/4), (1977/2000, 0, 33/8), (4947/5000, 0, 4),
   (9901/10000, 0, 31/8), (9909/10000, 0, 15/4), (2479/2500, 0, 29/8), (9923/10000, 0, 7/2),
   (993/1000, 0, 27/8), (621/625, 0, 13/4), (9943/10000, 0, 25/8), (9949/10000, 0, 3), (4977/5000,
   0, 23/8), (249/250, 0, 11/4), (1993/2000, 0, 21/8), (997/1000, 0, 5/2), (399/400, 0, 19/8),
   (499/500, 0, 9/4), (624/625, 0, 17/8), (2497/2500, 0, 2), (9993/10000, 0, 15/8), (9997/10000,
   0, 7/4), (1, 0, 13/8)]

/-- The lower barrier `T_sub = Φ⁻¹ ∘ F_sub`. -/
@[expose] def ignited_Tsub (s : ℝ) : ℝ := kProf ignited_fs s

/-- The upper barrier `T_sup = Φ⁻¹ ∘ F_sup`. -/
@[expose] def ignited_Tsup (s : ℝ) : ℝ := kProf ignited_fu s

/-! ### ignited: certificates (each evaluated once) -/

/-- Lower barrier, corner `χ₀ = 63 / 100`, `γ = 0.49`. -/
theorem ignited_sub_check_ll :
    pieceCheckL (lowA ignited_aux ignited_fs (63 / 100) (49 / 100)) ignited_fs
      kirchhoffQ (1 / 200) 0 ignited_subP = true := by
  kernel_fact
/-- Lower barrier, corner `χ₀ = 63 / 100`, `γ = 0.525`. -/
theorem ignited_sub_check_lu :
    pieceCheckL (lowA ignited_aux ignited_fs (63 / 100) (21 / 40)) ignited_fs
      kirchhoffQ (1 / 200) 0 ignited_subP = true := by
  kernel_fact
/-- Lower barrier, corner `χ₀ = 16 / 25`, `γ = 0.49`. -/
theorem ignited_sub_check_hl :
    pieceCheckL (lowA ignited_aux ignited_fs (16 / 25) (49 / 100)) ignited_fs
      kirchhoffQ (1 / 200) 0 ignited_subP = true := by
  kernel_fact
/-- Lower barrier, corner `χ₀ = 16 / 25`, `γ = 0.525`. -/
theorem ignited_sub_check_hu :
    pieceCheckL (lowA ignited_aux ignited_fs (16 / 25) (21 / 40)) ignited_fs
      kirchhoffQ (1 / 200) 0 ignited_subP = true := by
  kernel_fact
/-- Upper barrier, corner `χ₀ = 63 / 100`, `γ = 0.49`. -/
theorem ignited_sup_check_ll :
    pieceCheckL (upA ignited_aux ignited_fu (63 / 100) (49 / 100)) ignited_fu
      kirchhoffQ (1 / 200) 0 ignited_supP = true := by
  kernel_fact
/-- Upper barrier, corner `χ₀ = 63 / 100`, `γ = 0.525`. -/
theorem ignited_sup_check_lu :
    pieceCheckL (upA ignited_aux ignited_fu (63 / 100) (21 / 40)) ignited_fu
      kirchhoffQ (1 / 200) 0 ignited_supP = true := by
  kernel_fact
/-- Upper barrier, corner `χ₀ = 16 / 25`, `γ = 0.49`. -/
theorem ignited_sup_check_hl :
    pieceCheckL (upA ignited_aux ignited_fu (16 / 25) (49 / 100)) ignited_fu
      kirchhoffQ (1 / 200) 0 ignited_supP = true := by
  kernel_fact
/-- Upper barrier, corner `χ₀ = 16 / 25`, `γ = 0.525`. -/
theorem ignited_sup_check_hu :
    pieceCheckL (upA ignited_aux ignited_fu (16 / 25) (21 / 40)) ignited_fu
      kirchhoffQ (1 / 200) 0 ignited_supP = true := by
  kernel_fact
/-- Pressure certificate (`Δ = 90000 Pa`). -/
theorem ignited_pres_check :
    pieceCheckL (presD 90000) ignited_fu kirchhoffQ 0 0 ignited_presP = true := by
  kernel_fact

/-- Monotonicity: `−F_sub' ≥ 0` on `[0,1]`. -/
theorem ignited_fs_deriv_check :
    QPoly.checkOn (QPoly.scale (-1) (QPoly.deriv ignited_fs)) 0 0 1 (gridN 8) = true := by
  kernel_fact
/-- Monotonicity: `−F_sup' ≥ 0` on `[0,1]`. -/
theorem ignited_fu_deriv_check :
    QPoly.checkOn (QPoly.scale (-1) (QPoly.deriv ignited_fu)) 0 0 1 (gridN 8) = true := by
  kernel_fact
/-- Ordering: `F_sup − F_sub ≥ 0` on `[0,1]`. -/
theorem ignited_gap_check :
    QPoly.checkOn (QPoly.add ignited_fu (QPoly.scale (-1) ignited_fs)) 0 0 1 (gridN 8) = true := by
  kernel_fact

/-- Label and endpoint facts, checked once. -/
theorem ignited_labels_check :
    (ignited_subP.all (fun p => decide (0 ≤ p.2.1)) &&
      ignited_supP.all (fun p => ceilOK p.2.2 && decide (p.2.2 ≤ 60) && decide (0 ≤ p.2.1)) &&
      decide (pieceEnd2 0 ignited_subP = 1) && decide (pieceEnd2 0 ignited_supP = 1) &&
      decide (pieceEnd2 0 ignited_presP = 1) &&
      decide (QPoly.evalQ ignited_fs 1 = kirchhoffQ 1) &&
      decide (QPoly.evalQ ignited_fu 1 = kirchhoffQ (3 / 2)) &&
      decide (QPoly.evalQ ignited_fs 0 ≤ kirchhoffQ 60) &&
      decide (kirchhoffQ 10 ≤ QPoly.evalQ ignited_fs (3 / 10)) &&
      decide (QPoly.evalQ ignited_fu 0 ≤ kirchhoffQ 20)) = true := by
  kernel_fact

/-- Unpacked label and endpoint facts. -/
theorem ignited_labels_facts :
    (∀ p ∈ ignited_subP, 0 ≤ p.2.1) ∧
      (∀ p ∈ ignited_supP, ceilOK p.2.2 = true ∧ p.2.2 ≤ 60 ∧ 0 ≤ p.2.1) ∧
      pieceEnd2 0 ignited_subP = 1 ∧ pieceEnd2 0 ignited_supP = 1 ∧ pieceEnd2 0 ignited_presP = 1 ∧
      QPoly.evalQ ignited_fs 1 = kirchhoffQ 1 ∧ QPoly.evalQ ignited_fu 1 = kirchhoffQ (3 / 2) ∧
      QPoly.evalQ ignited_fs 0 ≤ kirchhoffQ 60 ∧ kirchhoffQ 10 ≤ QPoly.evalQ ignited_fs (3 / 10) ∧
      QPoly.evalQ ignited_fu 0 ≤ kirchhoffQ 20 := by
  have h := ignited_labels_check
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, fun p hp => ⟨(h2 p hp).1.1, (h2 p hp).1.2, (h2 p hp).2⟩, h3, h4, h5, h6, h7, h8,
    h9, h10⟩

/-! ### ignited: consequences -/

/-- `1 ≤ T_sub ≤ 60` on `[0,1]`. -/
theorem ignited_tsub_bounds {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    1 ≤ ignited_Tsub s ∧ ignited_Tsub s ≤ 60 := by
  obtain ⟨-, -, -, -, -, h6, -, h8, -⟩ := ignited_labels_facts
  have hF := antitone_of_deriv_check ignited_fs_deriv_check
  have a := le_kProf_of_edge hF h6 hs
  have b := kProf_le_of_axis hF h8 hs
  push_cast at a b
  exact ⟨a, b⟩

/-- `1 ≤ T_sup ≤ 20` on `[0,1]`. -/
theorem ignited_tsup_bounds {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    1 ≤ ignited_Tsup s ∧ ignited_Tsup s ≤ 20 := by
  obtain ⟨-, -, -, -, -, -, h7, -, -, h10⟩ := ignited_labels_facts
  have hF := antitone_of_deriv_check ignited_fu_deriv_check
  have a := le_kProf_of_edge hF h7 hs
  have b := kProf_le_of_axis hF h10 hs
  push_cast at a b
  exact ⟨le_trans (by norm_num) a, b⟩

/-- **Core temperature.** `T_sub ≥ 10 keV` on `s ≤ 3/10`. -/
theorem ignited_tsub_core {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 3 / 10) : 10 ≤ ignited_Tsub s := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := ignited_labels_facts
  have := le_kProf_of_core (antitone_of_deriv_check ignited_fs_deriv_check) (by norm_num) h9 h0
    (by push_cast; exact h1)
  push_cast at this
  exact this

/-- Edge values `T_sub(1) = 1`, `T_sup(1) = 3/2`. -/
theorem ignited_barrier_edges : ignited_Tsub 1 = 1 ∧ ignited_Tsup 1 = 3 / 2 := by
  obtain ⟨-, -, -, -, -, h6, h7, -⟩ := ignited_labels_facts
  have a := kProf_one h6
  have b := kProf_one h7
  push_cast at a b
  exact ⟨a, b⟩

/-- Sanity: the band is not empty, `T_sub ≤ T_sup` on `[0,1]`. -/
theorem ignited_band_nonempty {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ignited_Tsub s ≤ ignited_Tsup s := by
  have := QPoly.checkOn_sound ignited_gap_check s (by simpa using hs)
  simp only [QPoly.eval_add, QPoly.eval_scale] at this
  push_cast at this
  exact kirchhoffIso.symm.monotone (by linarith)

/-- **Lower-barrier margin.** For every geometry in `IsSolovevGeometry`, every fine supplied
reactivity and every `χ₀ ∈ [63 / 100, 16 / 25]`, `N[T_sub] ≥ 1/200 keV/s` on `[0,1]`. -/
theorem ignited_tsub_margin (G : FluxGeometry) [IsSolovevGeometry G] (sv : ℝ → ℝ)
    [BoschHaleFine sv] {χ₀ : ℝ} (h1 : 63 / 100 ≤ χ₀) (h2 : χ₀ ≤ 16 / 25) :
    ∀ s ∈ Icc (0 : ℝ) 1, (1 / 200 : ℝ) ≤ (coeffsA ignited_aux G sv χ₀).op s (ignited_Tsub s)
      (kProf' ignited_fs s) (kProf'' ignited_fs s) := by
  obtain ⟨hl, -, hend, -⟩ := ignited_labels_facts
  have := tsub_margin_gen ignited_aux ignited_fs ignited_subP (χL := 63 / 100) (χH := 16 / 25)
    (κ := 1 / 200) (by norm_num) (by norm_num) ignited_sub_check_ll ignited_sub_check_lu
    ignited_sub_check_hl ignited_sub_check_hu (by simp [ignited_subP]) hl hend
    ignited_fs_deriv_check
    (fun s hs => ignited_tsub_bounds hs) G sv (χ₀ := χ₀) (by push_cast; linarith)
    (by push_cast; linarith)
  push_cast at this
  exact this

/-- **Upper-barrier margin.** For every geometry in `IsSolovevGeometry`, every fine supplied
reactivity and every `χ₀ ∈ [63 / 100, 16 / 25]`, `N[T_sup] ≤ −1/200 keV/s` on `[0,1]`. -/
theorem ignited_tsup_margin (G : FluxGeometry) [IsSolovevGeometry G] (sv : ℝ → ℝ)
    [BoschHaleFine sv] {χ₀ : ℝ} (h1 : 63 / 100 ≤ χ₀) (h2 : χ₀ ≤ 16 / 25) :
    ∀ s ∈ Icc (0 : ℝ) 1, (coeffsA ignited_aux G sv χ₀).op s (ignited_Tsup s) (kProf' ignited_fu s)
      (kProf'' ignited_fu s) ≤ -(1 / 200) := by
  obtain ⟨-, hu, -, hend, -⟩ := ignited_labels_facts
  have := tsup_margin_gen ignited_aux ignited_fu ignited_supP (χL := 63 / 100) (χH := 16 / 25)
    (κ := 1 / 200) (by norm_num) (by norm_num) ignited_sup_check_ll ignited_sup_check_lu
    ignited_sup_check_hl ignited_sup_check_hu (by simp [ignited_supP]) hu hend
    ignited_fu_deriv_check
    (fun s hs => (ignited_tsup_bounds hs).1) G sv (χ₀ := χ₀) (by push_cast; linarith)
    (by push_cast; linarith)
  push_cast at this
  exact this

/-- **Pressure ceiling.** `n(s) (1 + 53/60) T_sup(s) keV ≤ p_eq(s) + Δ` on `[0,1]`,
`Δ = 90000 Pa`, for reactor `μ₀ ∈ [1.2566·10⁻⁶, 1.2567·10⁻⁶]`. -/
theorem ignited_pressure {μ₀ : ℝ} (hμ1 : 1.2566e-6 ≤ μ₀) (hμ2 : μ₀ ≤ 1.2567e-6) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      nProf s * (1 + 53 / 60) * ignited_Tsup s * keV ≤ peqLabel μ₀ 90000 s := by
  obtain ⟨-, -, -, -, hend, -⟩ := ignited_labels_facts
  have := pressure_gen 90000 ignited_fu ignited_presP ignited_pres_check
    (by simp [ignited_presP]) hend ignited_fu_deriv_check
    (fun s hs => le_trans (by norm_num) (ignited_tsup_bounds hs).1) hμ1 hμ2
  push_cast at this
  exact this

/-- **Two-sided band on the Solov'ev geometry (ignited).** For every geometry in
`IsSolovevGeometry`, every reactivity satisfying the fine supplied Bosch–Hale enclosures,
every `χ₀ ∈ [63 / 100, 16 / 25]` m²/s, and every kernel solution on all horizons of
`coeffsA ignited_aux G sv χ₀`
(no auxiliary heating (ignited))
with edge temperature in `[1, 3/2]` keV and initial profile in `[T_sub, T_sup]`: for all
`t ≥ 0`, `T_sub ≤ T ≤ T_sup`, `T ≥ 10 keV` on `s ≤ 3/10`, and `T ≤ 20 keV`. -/
theorem ignited_band (G : FluxGeometry) [IsSolovevGeometry G] (sv : ℝ → ℝ)
    [BoschHaleFine sv] {χ₀ : ℝ} (h1 : 63 / 100 ≤ χ₀) (h2 : χ₀ ≤ 16 / 25) {Tedge : ℝ → ℝ}
    {u : RadialField}
    (hu : ∀ τ, 0 ≤ τ → ClassicalRadialSolution (coeffsA ignited_aux G sv χ₀) Tedge τ u)
    (h0 : ∀ s ∈ Icc (0 : ℝ) 1, ignited_Tsub s ≤ u.T s 0 ∧ u.T s 0 ≤ ignited_Tsup s)
    (hedge : ∀ t, 0 ≤ t → 1 ≤ Tedge t ∧ Tedge t ≤ 3 / 2) :
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → ignited_Tsub s ≤ u.T s t ∧ u.T s t ≤ ignited_Tsup s) ∧
      (∀ s, 0 ≤ s → s ≤ 3 / 10 → ∀ t, 0 ≤ t → 10 ≤ u.T s t) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → u.T s t ≤ 20) := by
  have hb := band_gen ignited_aux ignited_fs ignited_fu (κ := 1 / 200) (by norm_num) G sv
    (by linarith : (0 : ℝ) ≤ χ₀)
    (fun s hs => lt_of_lt_of_le (by norm_num) (ignited_tsub_bounds hs).1)
    (fun s hs => lt_of_lt_of_le (by norm_num) (ignited_tsup_bounds hs).1)
    ignited_barrier_edges.1 ignited_barrier_edges.2 (ignited_tsub_margin G sv h1 h2)
    (ignited_tsup_margin G sv h1 h2) hu h0 hedge
  refine ⟨hb, fun s h0' h1' t ht => ?_, fun s hs t ht => (hb s hs t ht).2.trans
    (ignited_tsup_bounds hs).2⟩
  exact (ignited_tsub_core h0' h1').trans (hb s ⟨h0', h1'.trans (by norm_num)⟩ t ht).1

/-- **`solovev_one_plasma_ignited`** (rung C2, ignited). One field: the reactor Solov'ev field `B`
with Ampère current `J` and pressure `p_eq + Δ`, `Δ = 90000 Pa`.

1. *(equilibrium)* the kernel law `ForceBalance B J ∇(p_eq + Δ)` holds at every point of the
   transport domain `s ≤ 1`;
2. *(alphas)* every 3.5 MeV alpha born at `s ≤ 3/11` stays in `0 ≤ s ≤ 1` for all real time;
3. *(transport)* for every geometry in `IsSolovevGeometry` (instantiated for the actual
   field in `solovev_one_plasma_ignited_actual`),
   every reactivity in the fine supplied Bosch–Hale class, every
   `χ₀ ∈ [63 / 100, 16 / 25]` (stand-in `χ₀ (1/10 + T²/100)`),
   no auxiliary heating (ignited),
   and every supplied classical solution on all horizons with edge temperature in `[1, 3/2]`
   keV starting in the band: for all `t ≥ 0`, `T_sub ≤ T ≤ T_sup` on `[0,1]`, `T ≥ 10 keV`
   on `s ≤ 3/10`, and the plasma pressure `n(s)(1 + r_i) T keV` at every point of the
   transport domain is at most `p_eq(x) + Δ`.

Ignited: `P_aux = 0`, oracle `P_α ≈ 185–191 MW` over the window (not formalized).
Caveats as for `SolovevBand.solovev_one_plasma`. -/
theorem solovev_one_plasma_ignited {μ₀ : ℝ} (hμ1 : 1.2566e-6 ≤ μ₀) (hμ2 : μ₀ ≤ 1.2567e-6) :
    (∀ x : Space, label x ≤ 1 →
      ForceBalance (ofLp (reactorField x)) (ofLp (current μ₀ (7 / 4) 10 50 x))
        (ofLp (gradient (offsetPressure μ₀ 90000) x))) ∧
    (∀ {m e : ℝ} {x v : ℝ → Space}, 6.6446e-27 ≤ m → m ≤ 6.6448e-27 → 1.6021e-19 ≤ e →
      e ≤ 1.6023e-19 → LorentzOrbit m (2 * e) (fun _ => 0) reactorField x v →
      m * ‖v 0‖ ^ 2 ≤ 2 * (3.5e6 * e) → label (x 0) ≤ 3 / 11 →
      ∀ t, label (x t) ∈ Icc (0 : ℝ) 1) ∧
    (∀ (G : FluxGeometry) [IsSolovevGeometry G] (sv : ℝ → ℝ) [BoschHaleFine sv] {χ₀ : ℝ},
      63 / 100 ≤ χ₀ → χ₀ ≤ 16 / 25 → ∀ {Tedge : ℝ → ℝ} {u : RadialField},
      (∀ τ, 0 ≤ τ → ClassicalRadialSolution (coeffsA ignited_aux G sv χ₀) Tedge τ u) →
      (∀ s ∈ Icc (0 : ℝ) 1, ignited_Tsub s ≤ u.T s 0 ∧ u.T s 0 ≤ ignited_Tsup s) →
      (∀ t, 0 ≤ t → 1 ≤ Tedge t ∧ Tedge t ≤ 3 / 2) →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → ignited_Tsub s ≤ u.T s t ∧ u.T s t ≤ ignited_Tsup s) ∧
      (∀ s, 0 ≤ s → s ≤ 3 / 10 → ∀ t, 0 ≤ t → 10 ≤ u.T s t) ∧
      (∀ x : Space, label x ≤ 1 → ∀ t, 0 ≤ t →
        nProf (label x) * (1 + 53 / 60) * u.T (label x) t * keV ≤
          reactorPressure μ₀ x + 90000)) := by
  have hμ : μ₀ ≠ 0 := by intro h; rw [h] at hμ1; norm_num at hμ1
  refine ⟨fun x hx => offset_force_balance_domain hμ 90000 hx,
    fun hm1 hm2 he1 he2 h hK hs0 t =>
      (alpha_stays_in_transport_domain hm1 hm2 he1 he2 h hK hs0 t).1, ?_⟩
  intro G _ sv _ χ₀ h1 h2 Tedge u hu h0 hedge
  obtain ⟨hband, hcore, -⟩ := ignited_band G sv h1 h2 hu h0 hedge
  refine ⟨hband, hcore, fun x hx t ht => ?_⟩
  exact plasma_pressure_le_offset (c := 1 + 53 / 60) (n := nProf) (Tsup := ignited_Tsup)
    (T := u.T) hμ (by norm_num)
    (fun s hs => by unfold nProf; have := dens_pos hs; positivity)
    (fun s hs t ht => (hband s hs t ht).2) (ignited_pressure hμ1 hμ2) hx ht

/-- **`solovev_one_plasma_ignited` for the actual Solov'ev transport geometry**: the geometry
hypothesis is discharged by `SolovevFluxGeometry.solovevFluxGeometry_isSolovev`
(validated enclosures for the reactor Solov'ev field). Remaining unformalized link: the
coarea formula and the measure-theoretic change of variables identifying the flux-surface
averages, as stated in `Design.SolovevFluxGeometry`. -/
theorem solovev_one_plasma_ignited_actual {μ₀ : ℝ} (hμ1 : 1.2566e-6 ≤ μ₀) (hμ2 : μ₀ ≤ 1.2567e-6) :
    (∀ x : Space, label x ≤ 1 →
      ForceBalance (ofLp (reactorField x)) (ofLp (current μ₀ (7 / 4) 10 50 x))
        (ofLp (gradient (offsetPressure μ₀ 90000) x))) ∧
    (∀ {m e : ℝ} {x v : ℝ → Space}, 6.6446e-27 ≤ m → m ≤ 6.6448e-27 → 1.6021e-19 ≤ e →
      e ≤ 1.6023e-19 → LorentzOrbit m (2 * e) (fun _ => 0) reactorField x v →
      m * ‖v 0‖ ^ 2 ≤ 2 * (3.5e6 * e) → label (x 0) ≤ 3 / 11 →
      ∀ t, label (x t) ∈ Icc (0 : ℝ) 1) ∧
    (∀ (sv : ℝ → ℝ) [BoschHaleFine sv] {χ₀ : ℝ},
      63 / 100 ≤ χ₀ → χ₀ ≤ 16 / 25 → ∀ {Tedge : ℝ → ℝ} {u : RadialField},
      (∀ τ, 0 ≤ τ →
        ClassicalRadialSolution (coeffsA ignited_aux solovevFluxGeometry sv χ₀) Tedge τ u) →
      (∀ s ∈ Icc (0 : ℝ) 1, ignited_Tsub s ≤ u.T s 0 ∧ u.T s 0 ≤ ignited_Tsup s) →
      (∀ t, 0 ≤ t → 1 ≤ Tedge t ∧ Tedge t ≤ 3 / 2) →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → ignited_Tsub s ≤ u.T s t ∧ u.T s t ≤ ignited_Tsup s) ∧
      (∀ s, 0 ≤ s → s ≤ 3 / 10 → ∀ t, 0 ≤ t → 10 ≤ u.T s t) ∧
      (∀ x : Space, label x ≤ 1 → ∀ t, 0 ≤ t →
        nProf (label x) * (1 + 53 / 60) * u.T (label x) t * keV ≤
          reactorPressure μ₀ x + 90000)) :=
  ⟨(solovev_one_plasma_ignited hμ1 hμ2).1, (solovev_one_plasma_ignited hμ1 hμ2).2.1,
    fun sv _ _ h1 h2 _ _ => (solovev_one_plasma_ignited hμ1 hμ2).2.2 solovevFluxGeometry sv h1 h2⟩

/-- Sanity (degenerate case): with no auxiliary heating the source is alpha heating minus
bremsstrahlung only. -/
theorem srcA_ignited (sv : ℝ → ℝ) (s T : ℝ) :
    srcA ignited_aux sv s T = dens s * (alphaRate * sv T - bremsRate * Real.sqrt T) := by
  simp [srcA, ignited_aux]

end PlasmaLean.Design.SolovevBandIgnited
