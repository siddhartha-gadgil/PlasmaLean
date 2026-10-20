import pickle
from gen import d3_str, fpoly_str
d = pickle.load(open('final.pkl', 'rb'))
m = d['main']; I = d['I']; st = d['start']
HDR = '''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

'''
NS = 'PlasmaLean.Design.RationalStellarator.Confined'
def wrap(s, n=96):
    # wrap a long literal string body into lines (spaces only)
    out = []; line = ''
    for tok in s.split(' '):
        if len(line) + len(tok) + 1 > n:
            out.append(line); line = tok
        else:
            line = (line + ' ' + tok) if line else tok
    out.append(line)
    return '\n'.join(out)
def fpoly_lit(p):
    return '\n  fpoly% "' + wrap(fpoly_str(p).replace('\n', ' '), 90) + '"'
def d3_lit(A):
    return '\n  d3% "' + wrap(d3_str(A), 90) + '"'
def plan_lit(s):
    return '\n    plan% "' + '\n'.join(s[i:i+80] for i in range(0, len(s), 80)) + '"'

# ------------------------------------------------------------------ Data
data = HDR + '''public import PlasmaLean.Design.RationalStellaratorCover

/-!
# Data for the field-line confinement certificate of the rational stellarator

Literal data for `Design/RationalStellaratorConfined` (produced by an untrusted Python fit and
search; every use is checked by the kernel):

* `Pz`: the approximate first integral `I = 2⁴⁰ Î`, a polynomial in `(s, z, C, S)` with
  `s = (x² + y² - 1)/2`, `C = cos 2φ`, `S = sin 2φ` (integer coefficients, 363 monomials;
  least-squares fit of order `(10, 5)`, stellarator-symmetric basis).
* `G4 i`: `4 r₂²` times the rates of change of `s, z, C, S` along the field `field (1/4)`
  (proved in `RationalStellaratorConfined`).
* `J2`: twice the quadratic invariant `J = s² + z² + (z² - s²) S/2 + s z C` of the linearised
  field-line flow (the rotating ellipse of `notes/theory/first-stellarator-rung.md` §1.3).
* `Qroot`: the chart (`C ≥ 0`, `t = tan φ`) of the defect polynomial
  `∑ᵢ ∂ᵢP · G4ᵢ`, computed exactly by the kernel; `Alit` is its rescaling to the cube
  (`s = σ/10`, `z = ζ/10`), checked against the computation by `Alit_eq`.
-/

public section

namespace ''' + NS + '''
open PlasmaLean.Design.RationalStellarator.Cover PlasmaLean.Kinetic.LiePoly

/-- The approximate first integral (scaled by `2⁴⁰`), exponents `[s, z, C, S]`. -/
@[expose] def Pz : FPoly := ''' + fpoly_lit(d['P']) + '''

''' + ''.join(f'''/-- `4 r₂²` times the rate of change of variable `{i}` along the field (exponents
`[s, z, C, S]`). -/
@[expose] def G4_{i} : FPoly := {fpoly_lit(d['G'][i])}

''' for i in range(4)) + '''/-- The rate polynomials. -/
@[expose] def G4 : List FPoly := [G4_0, G4_1, G4_2, G4_3]

/-- Twice the quadratic invariant `J = s² + z² + (z² - s²) S/2 + s z C`. -/
@[expose] def J2 : FPoly := ''' + fpoly_lit([(2,[2,0,0,0]),(2,[0,2,0,0]),(1,[0,2,0,1]),(-1,[2,0,0,1]),(2,[1,1,1,0])]) + '''

/-- Chart of the defect polynomial `∑ᵢ ∂ᵢP · G4ᵢ` (`C ≥ 0` chart, weight `(1 + t²)⁶`). -/
@[expose] def Qroot : D3 :=
  add3 (add3 (mul3 (chartD 5 1 (pderivZ Pz 0)) (chartD 1 1 G4_0))
      (mul3 (chartD 5 1 (pderivZ Pz 1)) (chartD 1 1 G4_1)))
    (add3 (mul3 (chartD 4 1 (pderivZ Pz 2)) (chartD 2 1 G4_2))
      (mul3 (chartD 4 1 (pderivZ Pz 3)) (chartD 2 1 G4_3)))

/-- The defect chart rescaled to the cube: value `10²⁵ Qroot(σ/10, ζ/10, τ)`. -/
@[expose] def Alit : D3 := ''' + d3_lit(m['A']) + '''

set_option maxRecDepth 100000 in
/-- The literal `Alit` is the rescaled chart of the defect (kernel computation). -/
theorem Alit_eq : (lenOK 0 12 Qroot && lenOK 1 13 Qroot &&
    beq3 (scale0 10 12 (scale1 10 13 Qroot)) Alit) = true := by
  decide +kernel

end ''' + NS + '\n'
open('/Users/gadgil/code/PlasmaLean/PlasmaLean/Design/RationalStellaratorConfinedData.lean', 'w').write(data.replace(' := \n', ' :=\n'))

# ------------------------------------------------------------------ main cover
cps = m['cps']
cov = HDR + '''public import PlasmaLean.Design.RationalStellaratorConfinedData

/-!
# Kernel-checked cover for the defect of the rational stellarator

`mainGood`: on the cube `[-1, 1]³`, `|Alit| ≤ Dlit`, where `Alit` is the rescaled chart of the
field-line defect (`RationalStellaratorConfinedData`) and
`Dlit = δ' 10²⁵ (1 + 2σ/10)² (1 + τ²)⁶`, `δ' = 17592186`. The certificate is an adaptive
Taylor-shift cover (`Cover.check`, 65 leaves). It is split into a top part (`main_top`, which
ends in the four external nodes `mainCP`) and four subtrees (`main_sub_i`), each a separate
kernel evaluation of the checker; the external claims are discharged by the subtrees.
-/

public section

namespace ''' + NS + '''
open PlasmaLean.Design.RationalStellarator.Cover

/-- Degree bounds for the main cover. -/
@[expose] def mainDD : ℕ × ℕ × ℕ := (12, 13, 12)

/-- The bound `δ' 10²⁵ (1 + 2σ/10)² (1 + τ²)⁶` (`δ' = 17592186`). -/
@[expose] def Dlit : D3 :=
  [[smul1 (17592186 * 10 ^ 25) (onePlusSq 6)], [smul1 (17592186 * 4 * 10 ^ 24) (onePlusSq 6)],
    [smul1 (17592186 * 4 * 10 ^ 23) (onePlusSq 6)]]

''' + ''.join(f'''/-- Checkpoint polynomial {i} of the main cover. -/
@[expose] def cpA{i} : D3 := {d3_lit(A)}

/-- Checkpoint bound polynomial {i} of the main cover. -/
@[expose] def cpD{i} : D3 := {d3_lit(D)}

''' for i, (A, D, r, sp) in enumerate(cps)) + '''/-- The external claims of the main cover. -/
@[expose] def mainCP : List (D3 × D3 × ℕ) :=
  [''' + ',\n    '.join(f'(cpA{i}, cpD{i}, {r})' for i, (A, D, r, sp) in enumerate(cps)) + ''']

set_option maxRecDepth 100000 in
/-- Top part of the main cover (ends in the checkpoints). -/
theorem main_top :
    check true mainDD mainCP (''' + plan_lit(m['top']) + ''') Alit Dlit 0 = true := by
  decide +kernel

''' + ''.join(f'''set_option maxRecDepth 100000 in
/-- Subtree {i} of the main cover. -/
theorem main_sub_{i} : check true mainDD [] ({plan_lit(sp)})
    cpA{i} cpD{i} {r} = true := by
  decide +kernel

''' for i, (A, D, r, sp) in enumerate(cps)) + '''/-- The external claims hold. -/
theorem mainCP_good : ∀ x ∈ mainCP, Good true x.1 x.2.1 x.2.2 := by
  have h := fun (p : Plan) A D r (hc : check true mainDD [] p A D r = true) =>
    check_sound (absMode := true) (dd := mainDD) (lits := []) (by simp) p A D r hc
  intro x hx
  simp only [mainCP, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact h _ _ _ _ main_sub_0
  · exact h _ _ _ _ main_sub_1
  · exact h _ _ _ _ main_sub_2
  · exact h _ _ _ _ main_sub_3

/-- **The main cover**: `|Alit| ≤ Dlit` on the cube. -/
theorem mainGood : Good true Alit Dlit 0 :=
  check_sound mainCP_good _ _ _ _ main_top

end ''' + NS + '\n'
open('/Users/gadgil/code/PlasmaLean/PlasmaLean/Design/RationalStellaratorConfinedMain.lean', 'w').write(cov.replace(' := \n', ' :=\n'))

# ------------------------------------------------------------------ faces + start
fs = I['faces']
names = ['sPos', 'sNeg', 'zPos', 'zNeg']
def restr(f):
    return f"restrict{f['ax']} {'true' if f['pos'] else 'false'}"
fc = HDR + '''public import PlasmaLean.Design.RationalStellaratorConfinedData

/-!
# Kernel-checked covers for the boundary and the start set

* `faceGood_*`: on the four faces `s = ±1/10`, `z = ±1/10` of the tube (chart `C ≥ 0`), the
  first integral exceeds `I_b = 4398046511 ≈ 0.004 · 2⁴⁰`: the polynomial
  `I_b 10²⁰ (1 + τ²)⁵ - Ichart` is `≤ -1` on the cube.
* `startGood`: `20000 (I - I_a) - 10625 · 2⁴⁰ (2J - 2/1250) ≤ 0` on `|s|, |z| ≤ 1/25`
  (chart `C ≥ 0`), with `I_a = 1099511628 ≈ 0.001 · 2⁴⁰`; hence `I ≤ I_a` wherever
  `J ≤ 1/1250` (S-procedure with multiplier `17/16`).
-/

public section

namespace ''' + NS + '''
open PlasmaLean.Design.RationalStellarator.Cover PlasmaLean.Kinetic.LiePoly

/-- The chart of the first integral, rescaled: value `10²⁰ (1 + τ²)⁵ I(σ/10, ζ/10, C, S)`. -/
@[expose] def Ichart : D3 := scale0 10 10 (scale1 10 10 (chartD 5 1 Pz))

/-- The constant `I_b 10²⁰ (1 + τ²)⁵`. -/
@[expose] def IbPoly : D3 := [[smul1 (4398046511 * 10 ^ 20) (onePlusSq 5)]]

''' + ''.join(f'''set_option maxRecDepth 100000 in
/-- Face cover `{nm}`. -/
theorem face_{nm} :
    check false ({f['dd'][0]}, {f['dd'][1]}, {f['dd'][2]}) [] ({plan_lit(f['plan'])})
    (add3 IbPoly (neg3 ({restr(f)} Ichart))) [[[-1]]] 0 = true := by
  decide +kernel

''' for nm, f in zip(names, fs)) + '''/-- The start-set polynomial `20000 P - 10625 · 2⁴⁰ J2 + (17 · 2⁴⁰ - 20000 I_a)`. -/
@[expose] def Pstart : FPoly :=
  Pz.map (fun t => (20000 * t.1, t.2)) ++ J2.map (fun t => (-(10625 * 2 ^ 40) * t.1, t.2)) ++
    [(17 * 2 ^ 40 - 20000 * 1099511628, [0, 0, 0, 0])]

/-- Its chart rescaled to `|s|, |z| ≤ 1/25`. -/
@[expose] def Schart : D3 := scale0 25 10 (scale1 25 10 (chartD 5 1 Pstart))

set_option maxRecDepth 100000 in
/-- Start-set cover. -/
theorem start_cover :
    check false (''' + f"{st['dd'][0]}, {st['dd'][1]}, {st['dd'][2]}" + ''') [] (''' + plan_lit(st['plan']) + ''')
    Schart [[[0]]] 0 = true := by
  decide +kernel

end ''' + NS + '\n'
open('/Users/gadgil/code/PlasmaLean/PlasmaLean/Design/RationalStellaratorConfinedFaces.lean', 'w').write(fc.replace(' := \n', ' :=\n'))
print('ok')
