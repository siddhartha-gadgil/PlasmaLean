"""UNTRUSTED: compose PlasmaLean/Design/RationalStellaratorGCFamMaj.lean from the parts written by
fam_maj.py (mirrors at rho = 65/16384) and the monotonicity in rho (hand-written text below)."""
p1 = open('/tmp/famw/maj_part1.lean').read()
p2 = open('/tmp/famw/maj_part2.lean').read()
s = p1 + p2
s = s.replace('(-1 / 256)', '(65 / 16384)').replace('(−1/256)', '(65/16384)').replace('−1/256', '65/16384')
s = s.replace('namespace PlasmaLean.Design.RationalStellaratorGCNeg', 'namespace PlasmaLean.Design.RationalStellaratorGCFamily')
s = s.replace('# Majorants of the `v∥ < 0` guiding-centre field: node validity and the Taylor constant',
              '# Majorants of the guiding-centre field family: node validity and the Taylor constant')
s = s.replace('`scripts/gc_kam/neg_maj.py`', '`scripts/gc_kam/fam_maj.py`')
s = s.replace('''`Design/RationalStellaratorGCTorusMaj` (which do not depend on `ρ`), with their embeddings
(`*_toS`), and the two numerical facts of the KAM theorem that need majorants, at the bounds of the
`ι_B` torus:''', '''`Design/RationalStellaratorGCTorusMaj` (which do not depend on `ρ`), with their embeddings
(`*_toS`), and the two numerical facts of the KAM theorem that need majorants, at the bounds of the
family tori (cell `ρ ∈ [63/16384, 65/16384]`); the majorants are monotone in `|ρ|`
(`majD2_resRp_mono`), so the constant at `ρ = 65/16384` is uniform over the cell (`gc_C2R_cell`):''')
s = s.replace('the guiding-centre field `gcFlow (65/16384)` (`ρ_s = 65/16384`)', 'the guiding-centre field `gcFlow (65/16384)` (`ρ_s = 65/16384`, the largest `ρ` of the cell)')
mono = r'''
/-! ## Monotonicity in `ρ` -/

/-- `‖ρ‖ ≤ ρ'` for `|ρ| ≤ ρ'`. -/
theorem norm_ofReal_le {ρ ρ' : ℝ} (h : |ρ| ≤ ρ') : ‖(ρ : ℂ)‖ ≤ ‖(ρ' : ℂ)‖ := by
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  exact h.trans (le_abs_self _)

/-- **The second-derivative majorant of the `R`-residual is monotone in `|ρ|`.** -/
theorem majD2_resRp_mono {a b : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) {ρ ρ' : ℝ}
    (h : |ρ| ≤ ρ') :
    PolyExprS.majD2 a b (gcFlow ρ).resRp ≤ PolyExprS.majD2 a b (gcFlow ρ').resRp := by
  have hρ := norm_ofReal_le h
  simp only [FlowFieldS.resRp, gcFlow, gcD, gcNR, PolyExprS.majD2, PolyExprS.majD, PolyExprS.maj]
  have m1 := PolyExprS.maj_nonneg ha (.mul (.const (1 / 2 : ℂ)) (.mul eW3 eKD))
  have m2 := PolyExprS.majD_nonneg ha hb (.mul (.const (1 / 2 : ℂ)) (.mul eW3 eKD))
  have m3 := PolyExprS.majD2_nonneg ha hb (.mul (.const (1 / 2 : ℂ)) (.mul eW3 eKD))
  have m4 := PolyExprS.majD2_nonneg ha hb (.mul (.const (1 / 2 : ℂ)) (.mul eW3 eKR))
  simp only [PolyExprS.majD2, PolyExprS.majD, PolyExprS.maj] at m1 m2 m3 m4
  have a4 := ha 4
  have b4 := hb 4
  gcongr

/-- **The second-derivative majorant of the `z`-residual is monotone in `|ρ|`.** -/
theorem majD2_resZp_mono {a b : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) {ρ ρ' : ℝ}
    (h : |ρ| ≤ ρ') :
    PolyExprS.majD2 a b (gcFlow ρ).resZp ≤ PolyExprS.majD2 a b (gcFlow ρ').resZp := by
  have hρ := norm_ofReal_le h
  simp only [FlowFieldS.resZp, gcFlow, gcD, gcNZ, PolyExprS.majD2, PolyExprS.majD, PolyExprS.maj]
  have m1 := PolyExprS.maj_nonneg ha (.mul (.const (1 / 2 : ℂ)) (.mul eW3 eKD))
  have m2 := PolyExprS.majD_nonneg ha hb (.mul (.const (1 / 2 : ℂ)) (.mul eW3 eKD))
  have m3 := PolyExprS.majD2_nonneg ha hb (.mul (.const (1 / 2 : ℂ)) (.mul eW3 eKD))
  have m4 := PolyExprS.majD2_nonneg ha hb (.mul (.const (1 / 2 : ℂ)) (.mul eW3 eKZ))
  simp only [PolyExprS.majD2, PolyExprS.majD, PolyExprS.maj] at m1 m2 m3 m4
  have a5 := ha 5
  have b5 := hb 5
  gcongr

/-- **The Taylor constant of the `R`-residual, uniform over the cell** `|ρ| ≤ 65/16384`. -/
theorem gc_C2R_cell {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i) (haa : ∀ i, a i ≤ aTQ i) {ρ : ℝ}
    (hρ : |ρ| ≤ 65 / 16384) :
    PolyExprS.majD2 a (fun i => (mvQ i : ℝ)) (gcFlow ρ).resRp / 2 ≤ (C2Q : ℝ) := by
  have hb : ∀ i, (0 : ℝ) ≤ (mvQ i : ℝ) := fun i => by
    have := (show ∀ i, (0 : ℚ) ≤ mvQ i by kernel_fact) i
    exact_mod_cast this
  have := majD2_resRp_mono ha hb hρ
  linarith [gc_C2R ha haa]

/-- **The Taylor constant of the `z`-residual, uniform over the cell** `|ρ| ≤ 65/16384`. -/
theorem gc_C2Z_cell {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i) (haa : ∀ i, a i ≤ aTQ i) {ρ : ℝ}
    (hρ : |ρ| ≤ 65 / 16384) :
    PolyExprS.majD2 a (fun i => (mvQ i : ℝ)) (gcFlow ρ).resZp / 2 ≤ (C2Q : ℝ) := by
  have hb : ∀ i, (0 : ℝ) ≤ (mvQ i : ℝ) := fun i => by
    have := (show ∀ i, (0 : ℚ) ≤ mvQ i by kernel_fact) i
    exact_mod_cast this
  have := majD2_resZp_mono ha hb hρ
  linarith [gc_C2Z ha haa]

/-- The residual expressions are valid at every bound below `aTQ`, for every `ρ`. -/
theorem gc_valid_res_cell {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i) (haa : ∀ i, a i ≤ aTQ i) (ρ : ℝ) :
    PolyExprS.Valid a (gcFlow ρ).resRp ∧ PolyExprS.Valid a (gcFlow ρ).resZp :=
  ⟨(gcFlow_valid _ a (gc_maj_E_lt ha haa)).2.1, (gcFlow_valid _ a (gc_maj_E_lt ha haa)).2.2⟩

end PlasmaLean.Design.RationalStellaratorGCFamily
'''
s = s.replace('] <;> norm_num\n', ']\n  norm_num\n')
s = s + mono
open('/Users/gadgil/code/PlasmaLean/PlasmaLean/Design/RationalStellaratorGCFamMaj.lean', 'w').write(s)
print('ok')
