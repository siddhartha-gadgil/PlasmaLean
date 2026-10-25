"""UNTRUSTED (pitch cell [LAM_LO, LAM_HI], see lc.py): the KAM constants of the cell and the Lean
majorant module, with ONE BOUND PER INVERSE-SQUARE-ROOT NODE.  Replacement of maj.py for cells that
reach above lam ~ 0.156.

Why.  lam_maj.py (run by maj.py) evaluates all three nodes (1 + E)^{-1/2}, (1 + E4)^{-1/2} and
(1 - lam1|B|)^{-1/2} through one uniform bound g (Theory/KAM/PolyExprSMajQ).  Since |B| = QPP4 (1+E)^{-1/2}
(1+E4)^{-1/2} contains two nodes, the bound of the last node is lam1 mQQ g^2 and g must solve
g^2 (1 - lam1 mQQ g^2) >= 1, which is impossible once 4 lam1 mQQ > 1, i.e. lam1 > 1/(4 * 1.596) = 0.1566
(the 'node invalid' failure of the cell [1/8, 3/16]; the reported value 1.6 is where the divergent
fixed-point iteration first exceeds 1, not a property of the field).  With separate bounds
gE, gE4 of the inner nodes the last node only needs lam1 mQQ gE gE4 < 1 (0.47 at lam1 = 1/4).

What.  lam_maj.py is run with these patches (besides the paths of maj.py):
  * node bounds: gE, gE4 from mE, mE4; mB = mQQ gE gE4 (bound of |B|); mN = lam1 mB; gN from mN;
  * the Taylor constant C2 with the per-node majorants (node (1+E)^{-1/2} -> gE, (1+E4)^{-1/2} -> gE4,
    the pitch node -> gN), mirroring Theory/KAM/PolyExprSMajQG (PQG.mD2Q of PQG.ofPQS);
  * the Lean module RationalStellaratorGCMuMaj.lean is emitted from the template below (generic
    lemmas: Theory/KAM/PolyExprSMajQG).  It exports the same declarations used downstream as the
    lam_maj.py template (lam1, aTQ, aTQ_nonneg, mvQ, C2Q, mu_C2R, mu_C2Z, mu_C2_cell,
    mu_node_bounds, mu_valid_cell, constLe_eF, constLe_res, nodesOK_res (now about PQG trees)).
Output: $LAM_WORK/lam_const.pkl and $LAM_WORK/emit/RationalStellaratorGCMuMaj.lean (original names;
install.py renames).
Usage: python maj_g.py            (full: needs $LAM_WORK/lam_cert_{H,L}.pkl)
       python maj_g.py --check    (cheap: node bounds and C2 at the bounds aTQ, mvQ of the certified
                                   cell Mu2 for LAM_HI, and for comparison the uniform-g check)
"""
import os, sys, math
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lc


def gof(m, up):
    """a rational g >= (1 - m)^{-1/2} with an exact check."""
    assert m < 1, ('node invalid', float(m))
    g = up(Fr(1 / math.sqrt(1 - float(m))) * Fr(1000001, 1000000), 6)
    assert g * g * (1 - m) >= 1
    return g


def node_bounds_g(G, a):
    """(mE, mE4, mQQ, mB, mN, gE, gE4, gN) with one bound per node."""
    up, mQ = G['up'], G['mQ']
    mE = up(mQ(a, Fr(0), G['EpQ'], {}), 4)
    mE4 = up(mQ(a, Fr(0), G['E4Q'], {}), 4)
    mQQ = up(mQ(a, Fr(0), G['QQ'], {}), 4)
    gE, gE4 = gof(mE, up), gof(mE4, up)
    mB = up(mQQ * gE * gE4, 4)
    mN = up(G['LAM1'] * mB, 4)
    gN = gof(mN, up)
    return mE, mE4, mQQ, mB, mN, gE, gE4, gN


def gfun(G, gE, gE4, gN):
    """the bound of a node with argument d (the lookup of PQG.ofPQS [(E4PQ, gE4), (EpPQ, gE)] gN)."""
    E4Q, EpQ = G['E4Q'], G['EpQ']
    return lambda d: gE4 if d is E4Q else (gE if d is EpQ else gN)


def mQg(a, gf, t, memo):
    k = id(t)
    if k in memo:
        return memo[k]
    c = t[0]
    if c == 'c':
        r = abs(t[1])
    elif c == 'v':
        r = a[t[1]]
    elif c in ('a', 's'):
        r = mQg(a, gf, t[1], memo) + mQg(a, gf, t[2], memo)
    elif c == 'm':
        r = mQg(a, gf, t[1], memo) * mQg(a, gf, t[2], memo)
    else:
        r = gf(t[2])
    memo[k] = r
    return r


def mDg(a, b, gf, t, memo, mm):
    k = id(t)
    if k in memo:
        return memo[k]
    c = t[0]
    if c == 'c':
        r = Fr(0)
    elif c == 'v':
        r = b[t[1]]
    elif c in ('a', 's'):
        r = mDg(a, b, gf, t[1], memo, mm) + mDg(a, b, gf, t[2], memo, mm)
    elif c == 'm':
        r = mDg(a, b, gf, t[1], memo, mm) * mQg(a, gf, t[2], mm) + mQg(a, gf, t[1], mm) * mDg(a, b, gf, t[2], memo, mm)
    else:
        r = gf(t[2]) ** 3 / 2 * mDg(a, b, gf, t[2], memo, mm)
    memo[k] = r
    return r


def mD2g(a, b, gf, t, memo=None, md=None, mm=None):
    memo = {} if memo is None else memo
    md = {} if md is None else md
    mm = {} if mm is None else mm
    k = id(t)
    if k in memo:
        return memo[k]
    c = t[0]
    if c in ('c', 'v'):
        r = Fr(0)
    elif c in ('a', 's'):
        r = mD2g(a, b, gf, t[1], memo, md, mm) + mD2g(a, b, gf, t[2], memo, md, mm)
    elif c == 'm':
        p, q = t[1], t[2]
        r = (mD2g(a, b, gf, p, memo, md, mm) * mQg(a, gf, q, mm)
             + 2 * (mDg(a, b, gf, p, md, mm) * mDg(a, b, gf, q, md, mm))
             + mQg(a, gf, p, mm) * mD2g(a, b, gf, q, memo, md, mm))
    else:
        g = gf(t[2])
        r = 3 * g ** 5 / 4 * mDg(a, b, gf, t[2], md, mm) ** 2 + g ** 3 / 2 * mD2g(a, b, gf, t[2], memo, md, mm)
    memo[k] = r
    return r


def LAMG_NODE(G, a):
    mE, mE4, mQQ, mB, mN, gE, gE4, gN = node_bounds_g(G, a)
    G['LAMG_GF'] = gfun(G, gE, gE4, gN)
    print('per-node bounds: mE %.4f mE4 %.6f mQQ %.4f mB %.4f mN %.4f gE %s gE4 %s gN %s'
          % (mE, mE4, mQQ, mB, mN, float(gE), float(gE4), float(gN)))
    return mE, mE4, mQQ, mN, gN, gE, gE4, mB


def LAMG_MD2(G, a, b, t):
    return mD2g(a, b, G['LAMG_GF'], t)


# ----------------------------------------------------------------------------- the Lean template
TEMPLATE = '''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCTorusMaj
public import PlasmaLean.Design.RationalStellaratorGCMuInstance
public import PlasmaLean.Theory.KAM.PolyExprSConstMono
public import PlasmaLean.Theory.KAM.PolyExprSMajQG

/-!
# Majorants of the `μ > 0` passing guiding-centre field family: node validity and `C₂`

The computable mirrors (`Theory/KAM/PolyExprSMajQ`, `PQS`) of the expression trees of the
`μ > 0` passing field `gcFlowMu (1/256) λ₁` (`λ₁ = @LAM@`, the largest pitch parameter of the cell),
built from the leaf mirrors of `Design/RationalStellaratorGCTorusMaj` and of the leaves
`E₄`, `Q P P₄`, with their embeddings (`*_toS`), and the facts of the KAM theorem that need
majorants, at the bounds `aTQ` of the family tori. The nodes are evaluated with **one bound per
node** (`Theory/KAM/PolyExprSMajQG`, `PQG.ofPQS`): `gEQ` for `(1 + E)^{−1/2}`, `gE4Q` for
`(1 + E₄)^{−1/2}` and `gNQ` for `(1 − λ₁|B|)^{−1/2}`. (A uniform bound, as in
`Theory/KAM/PolyExprSMajQ`, would have to satisfy `g² (1 − λ₁ m g²) ≥ 1`, which has no solution
for `λ₁ > 0.156`.)

* **node validity** (`nodesOK_res`), checked by the computable `PQG.okQ`;
* **the bound of `|B|`** (`maj_eBm_le`): `maj |B| ≤ m_B = @MB@`, so `λ₁ m_B ≤ @MN@ < 1`;
* **the Taylor constant** (`mu_C2R`, `mu_C2Z`): `½ majD2(res) ≤ C₂ = @C2@`;
* **uniformity in the pitch parameter** (`mu_C2_cell`, `mu_valid_cell`): `λ` enters the trees only
  through constants of modulus `≤ λ₁` (`Theory/KAM/PolyExprSConstMono`, `ConstLe`), so the bounds at
  `λ₁` hold for every `λ ∈ [0, λ₁]`.

The rational majorants are evaluated by the kernel (`decide +kernel`). Generated by
`scripts/gc_kam/lamcell/maj_g.py`.

**Sanity.** `gcDMQ_toS`: the mirror embeds to the field expression `gcDM (1/256) λ₁`;
`resRG_toS`: attaching the node bounds does not change the tree.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGCMu

open PlasmaLean.Design.RationalStellaratorGC
open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Theory.KAM.PQS

/-- The largest pitch parameter of the cell. -/
def lam1 : ℝ := @LAMR@

set_option linter.style.longLine false in
/-- The (integer) monomials of `E₄`. -/
def E4PL : List (ℤ × List (Fin 6 × ℕ)) :=
  @E4L@

/-- The mirror of `E₄`. -/
def E4PQ : PQS (Fin 6) := polyQ (E4PL.map fun cm => ((cm.1 : ℚ), cm.2))

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
/-- The mirror of `E₄` embeds to it. -/
theorem E4PQ_toS : E4PQ.toS = PolyExprS.ofPoly E4P := by
  rw [E4PQ, toS_polyQ]
  simp only [E4PL, List.map, E4P, Rat.cast_intCast, Int.cast_ofNat, Int.cast_neg]
  norm_num

set_option linter.style.longLine false in
/-- The (integer) monomials of `@SQ@ Q P P₄`. -/
def QPP4PL : List (ℤ × List (Fin 6 × ℕ)) :=
  @QL@

/-- The mirror of `Q P P₄`. -/
def QPP4PQ : PQS (Fin 6) :=
  .mul (.const (1 / @SQ@)) (polyQ (QPP4PL.map fun cm => ((cm.1 : ℚ), cm.2)))

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- the expanded `Q P P₄` (106 monomials) is normalised by `norm_num`
/-- The mirror of `Q P P₄` embeds to it. -/
theorem QPP4PQ_toS : QPP4PQ.toS = PolyExprS.ofPoly QPP4P := by
  rw [QPP4PQ, toS, toS_polyQ]
  simp only [toS, QPP4PL, List.map, QPP4P, PolyExprS.ofPoly, Rat.cast_intCast, Int.cast_ofNat,
    Int.cast_neg]
  norm_num

/-- The mirror of the node `(1 + E₄)^{−1/2}`. -/
def eV4Q : PQS (Fin 6) := .isqrt 1 E4PQ

/-- The mirror of the node embeds to it. -/
theorem eV4Q_toS : eV4Q.toS = eV4 := by
  simp only [eV4Q, toS, E4PQ_toS, eV4, Rat.cast_one]

/-- The mirror of `|B|`. -/
def eBmQ : PQS (Fin 6) := .mul QPP4PQ (.mul eVQ eV4Q)

/-- The mirror of `|B|` embeds to it. -/
theorem eBmQ_toS : eBmQ.toS = eBm := by
  simp only [eBmQ, toS, QPP4PQ_toS, eVQ_toS, eV4Q_toS, eBm]

/-- The mirror of the node `(1 − λ₁|B|)^{−1/2}`. -/
def eNQ : PQS (Fin 6) := .isqrt 1 (.mul (.const (-@LAMQ@)) eBmQ)

/-- The mirror of the node embeds to it. -/
theorem eNQ_toS : eNQ.toS = RationalStellaratorGC.eN lam1 := by
  simp only [eNQ, toS, eBmQ_toS, RationalStellaratorGC.eN, lam1, Rat.cast_one]
  norm_num

/-- The mirror of `F`. -/
def eFQ : PQS (Fin 6) := .mul (.sub (.const 1) (.mul (.const (@LAMQ@ / 2)) eBmQ)) eNQ

/-- The mirror of `F` embeds to it. -/
theorem eFQ_toS : eFQ.toS = eF lam1 := by
  simp only [eFQ, toS, eBmQ_toS, eNQ_toS, eF, lam1]
  norm_num

/-- The mirror of `½ W³ κ_D`. -/
def eYDQ : PQS (Fin 6) := .mul (.const (1 / 2)) (.mul eW3Q eKDQ)
/-- The mirror of `½ W³ κ_R`. -/
def eYRQ : PQS (Fin 6) := .mul (.const (1 / 2)) (.mul eW3Q eKRQ)
/-- The mirror of `½ W³ κ_z`. -/
def eYZQ : PQS (Fin 6) := .mul (.const (1 / 2)) (.mul eW3Q eKZQ)

/-- The mirror of `½ W³ κ_D` embeds to it. -/
theorem eYDQ_toS : eYDQ.toS = eYD := by
  simp only [eYDQ, toS, eW3Q_toS, eKDQ_toS, eYD]; norm_num
/-- The mirror of `½ W³ κ_R` embeds to it. -/
theorem eYRQ_toS : eYRQ.toS = eYR := by
  simp only [eYRQ, toS, eW3Q_toS, eKRQ_toS, eYR]; norm_num
/-- The mirror of `½ W³ κ_z` embeds to it. -/
theorem eYZQ_toS : eYZQ.toS = eYZ := by
  simp only [eYZQ, toS, eW3Q_toS, eKZQ_toS, eYZ]; norm_num

/-- The mirror of `D̃` at `λ₁`. -/
def gcDMQ : PQS (Fin 6) := .add DpQ (.mul (.const (1 / 256)) (.mul eFQ eYDQ))
/-- The mirror of `ñ_R` at `λ₁`. -/
def gcNRMQ : PQS (Fin 6) := .add nRpQ (.mul (.const (1 / 256)) (.mul eFQ eYRQ))
/-- The mirror of `ñ_z` at `λ₁`. -/
def gcNZMQ : PQS (Fin 6) := .add nZpQ (.mul (.const (1 / 256)) (.mul eFQ eYZQ))

/-- The mirror of `D̃` embeds to it. -/
theorem gcDMQ_toS : gcDMQ.toS = gcDM (1 / 256) lam1 := by
  simp only [gcDMQ, toS, DpQ_toS, eFQ_toS, eYDQ_toS, gcDM]; norm_num
/-- The mirror of `ñ_R` embeds to it. -/
theorem gcNRMQ_toS : gcNRMQ.toS = gcNRM (1 / 256) lam1 := by
  simp only [gcNRMQ, toS, nRpQ_toS, eFQ_toS, eYRQ_toS, gcNRM]; norm_num
/-- The mirror of `ñ_z` embeds to it. -/
theorem gcNZMQ_toS : gcNZMQ.toS = gcNZM (1 / 256) lam1 := by
  simp only [gcNZMQ, toS, nZpQ_toS, eFQ_toS, eYZQ_toS, gcNZM]; norm_num

/-- The mirror of the `R`-residual expression. -/
def resRQ : PQS (Fin 6) := .sub (.mul gcDMQ (.var 4)) gcNRMQ

/-- The mirror of the `z`-residual expression. -/
def resZQ : PQS (Fin 6) := .sub (.mul gcDMQ (.var 5)) gcNZMQ

/-- The mirror of the `R`-residual embeds to it. -/
theorem resRQ_toS : resRQ.toS = (gcFlowMu (1 / 256) lam1).resRp := by
  simp only [resRQ, toS, gcDMQ_toS, gcNRMQ_toS]; rfl

/-- The mirror of the `z`-residual embeds to it. -/
theorem resZQ_toS : resZQ.toS = (gcFlowMu (1 / 256) lam1).resZp := by
  simp only [resZQ, toS, gcDMQ_toS, gcNZMQ_toS]; rfl

/-! ## The bounds -/

/-- Rational upper bounds of the torus variables on the Taylor segments and the admissible tori. -/
def aTQ : Fin 6 → ℚ := @ATQ@

/-- The perturbation profile `(c_K, c_K, 0, 0, c_L, c_L)`. -/
def mvQ : Fin 6 → ℚ := @MVQ@

/-- The bound of the majorant of `E`. -/
def mEQ : ℚ := @MEQ@
/-- The bound of the majorant of `E₄`. -/
def mE4Q : ℚ := @ME4Q@
/-- The bound of the majorant of `Q P P₄`. -/
def mQQ : ℚ := @MQQ@
/-- The bound of the majorant of `|B|`. -/
def mBQ : ℚ := @MBQ@
/-- The bound of the majorant under the node `(1 − λ₁|B|)^{−1/2}`. -/
def mNQ : ℚ := @MNQ@
/-- The bound of the node `(1 + E)^{−1/2}`. -/
def gEQ : ℚ := @GEQ@
/-- The bound of the node `(1 + E₄)^{−1/2}`. -/
def gE4Q : ℚ := @GE4Q@
/-- The bound of the node `(1 − λ₁|B|)^{−1/2}`. -/
def gNQ : ℚ := @GNQ@
/-- The Taylor constant. -/
def C2Q : ℚ := @C2Q@

/-- The node bounds by node argument (the pitch node takes the default `gNQ`). -/
def gsQ : List (PQS (Fin 6) × ℚ) := [(E4PQ, gE4Q), (EpPQ, gEQ)]

/-- The tree of `|B|` with its node bounds. -/
def eBmG : PQG (Fin 6) := PQG.ofPQS gsQ gNQ eBmQ
/-- The `R`-residual tree with its node bounds. -/
def resRG : PQG (Fin 6) := PQG.ofPQS gsQ gNQ resRQ
/-- The `z`-residual tree with its node bounds. -/
def resZG : PQG (Fin 6) := PQG.ofPQS gsQ gNQ resZQ

/-- The tree of `|B|` with bounds embeds to `|B|`. -/
theorem eBmG_toS : eBmG.toS = eBm := by rw [eBmG, PQG.toS_ofPQS, eBmQ_toS]
/-- **Sanity**: the `R`-residual with bounds embeds to the `R`-residual. -/
theorem resRG_toS : resRG.toS = (gcFlowMu (1 / 256) lam1).resRp := by
  rw [resRG, PQG.toS_ofPQS, resRQ_toS]
/-- The `z`-residual with bounds embeds to the `z`-residual. -/
theorem resZG_toS : resZG.toS = (gcFlowMu (1 / 256) lam1).resZp := by
  rw [resZG, PQG.toS_ofPQS, resZQ_toS]

/-- Expressions without nodes satisfy the node condition. -/
theorem nodesOK_ofPoly (a : Fin 6 → ℝ) (g : ℝ) (e : PolyExpr ℂ (Fin 6)) :
    NodesOK a g (PolyExprS.ofPoly e) := by
  induction e with
  | const _ => trivial
  | var _ => trivial
  | add p q hp hq => exact ⟨hp, hq⟩
  | sub p q hp hq => exact ⟨hp, hq⟩
  | mul p q hp hq => exact ⟨hp, hq⟩

/-- The bounds `aTQ` are nonnegative. -/
theorem aTQ_nonneg : ∀ i, (0 : ℝ) ≤ (aTQ i : ℝ) := fun i => by
  have := (show ∀ i, (0 : ℚ) ≤ aTQ i by decide +kernel) i
  exact_mod_cast this

set_option maxRecDepth 100000 in
/-- **The majorant of `E` at `aTQ`.** -/
theorem mu_maj_E : PolyExpr.maj (fun i => (aTQ i : ℝ)) EpP ≤ (mEQ : ℝ) := by
  rw [← PolyExprS.maj_ofPoly, ← EpPQ_toS]
  refine (maj_le (a := aTQ) (g := 0) (by decide +kernel) le_rfl EpPQ (nodesOK_EpPQ _ _)).trans ?_
  exact_mod_cast (show mQ aTQ 0 EpPQ ≤ mEQ by decide +kernel)

set_option maxRecDepth 100000 in
/-- **The majorant of `E₄` at `aTQ`.** -/
theorem mu_maj_E4 : PolyExpr.maj (fun i => (aTQ i : ℝ)) E4P ≤ (mE4Q : ℝ) := by
  rw [← PolyExprS.maj_ofPoly, ← E4PQ_toS]
  refine (maj_le (a := aTQ) (g := 0) (by decide +kernel) le_rfl E4PQ
    (nodesOK_polyQ _ _ _)).trans ?_
  exact_mod_cast (show mQ aTQ 0 E4PQ ≤ mE4Q by decide +kernel)

set_option maxRecDepth 100000 in
/-- **The node conditions of `|B|`** at `aTQ` (bounds `gEQ`, `gE4Q`). -/
theorem nodesOK_eBmG : PQG.NodesOK (fun i => (aTQ i : ℝ)) eBmG :=
  PQG.nodesOK_of_okQ (by decide +kernel) _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **`maj |B| ≤ m_B`** at `aTQ`. -/
theorem maj_eBm_le : PolyExprS.maj (fun i => (aTQ i : ℝ)) eBm ≤ (mBQ : ℝ) := by
  rw [← eBmG_toS]
  refine (PQG.maj_le (by decide +kernel) eBmG nodesOK_eBmG).trans ?_
  exact_mod_cast (show PQG.mQ aTQ eBmG ≤ mBQ by decide +kernel)

set_option maxRecDepth 100000 in
/-- **The node condition on the residual trees** at `aTQ`, `λ = λ₁` (one bound per node). -/
theorem nodesOK_res : PQG.NodesOK (fun i => (aTQ i : ℝ)) resRG ∧
    PQG.NodesOK (fun i => (aTQ i : ℝ)) resZG :=
  ⟨PQG.nodesOK_of_okQ (by decide +kernel) _ (by decide +kernel),
    PQG.nodesOK_of_okQ (by decide +kernel) _ (by decide +kernel)⟩

/-- The residual trees at `λ₁` are valid at `aTQ`. -/
theorem valid_res : PolyExprS.Valid (fun i => (aTQ i : ℝ)) (gcFlowMu (1 / 256) lam1).resRp ∧
    PolyExprS.Valid (fun i => (aTQ i : ℝ)) (gcFlowMu (1 / 256) lam1).resZp := by
  rw [← resRG_toS, ← resZG_toS]
  exact ⟨PQG.valid_of_nodesOK nodesOK_res.1, PQG.valid_of_nodesOK nodesOK_res.2⟩

set_option maxRecDepth 100000 in
/-- **The Taylor constant of the `R`-residual** at `aTQ`, `λ = λ₁`. -/
theorem mu_C2R : PolyExprS.majD2 (fun i => (aTQ i : ℝ)) (fun i => (mvQ i : ℝ))
    (gcFlowMu (1 / 256) lam1).resRp / 2 ≤ (C2Q : ℝ) := by
  rw [← resRG_toS]
  have h2 := PQG.majD2_le (a := aTQ) (b := mvQ) (by decide +kernel) (by decide +kernel)
    resRG nodesOK_res.1
  have h3 : (PQG.mD2Q aTQ mvQ resRG : ℝ) / 2 ≤ C2Q := by
    exact_mod_cast (show PQG.mD2Q aTQ mvQ resRG / 2 ≤ C2Q by decide +kernel)
  linarith

set_option maxRecDepth 100000 in
/-- **The Taylor constant of the `z`-residual** at `aTQ`, `λ = λ₁`. -/
theorem mu_C2Z : PolyExprS.majD2 (fun i => (aTQ i : ℝ)) (fun i => (mvQ i : ℝ))
    (gcFlowMu (1 / 256) lam1).resZp / 2 ≤ (C2Q : ℝ) := by
  rw [← resZG_toS]
  have h2 := PQG.majD2_le (a := aTQ) (b := mvQ) (by decide +kernel) (by decide +kernel)
    resZG nodesOK_res.2
  have h3 : (PQG.mD2Q aTQ mvQ resZG : ℝ) / 2 ≤ C2Q := by
    exact_mod_cast (show PQG.mD2Q aTQ mvQ resZG / 2 ≤ C2Q by decide +kernel)
  linarith

/-! ## Uniformity over the cell -/

/-- The pitch parameter enters `F` only through constants of modulus `≤ λ₁`. -/
theorem constLe_eF {lm : ℝ} (h : |lm| ≤ lam1) : PolyExprS.ConstLe (eF lm) (eF lam1) := by
  have h2 : ‖((lm : ℂ) / 2)‖ ≤ ‖((lam1 : ℂ) / 2)‖ := by
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
    rw [abs_of_pos (show (0 : ℝ) < lam1 by norm_num [lam1])]; linarith
  have h1 : ‖(-(lm : ℂ))‖ ≤ ‖(-(lam1 : ℂ))‖ := by
    simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (show (0 : ℝ) < lam1 by norm_num [lam1])]; exact h
  exact .mul (.sub (.const le_rfl) (.mul (.const h2) (PolyExprS.constLe_refl _)))
    (.isqrt 1 (.mul (.const h1) (PolyExprS.constLe_refl _)))

/-- The residual trees at `λ` are `ConstLe` those at `λ₁` for `|λ| ≤ λ₁`. -/
theorem constLe_res {lm : ℝ} (h : |lm| ≤ lam1) :
    PolyExprS.ConstLe (gcFlowMu (1 / 256) lm).resRp (gcFlowMu (1 / 256) lam1).resRp ∧
    PolyExprS.ConstLe (gcFlowMu (1 / 256) lm).resZp (gcFlowMu (1 / 256) lam1).resZp := by
  have hF := constLe_eF h
  have r := PolyExprS.constLe_refl (𝕜 := ℂ) (σ := Fin 6)
  exact ⟨.sub (.mul (.add (r _) (.mul (r _) (.mul hF (r _)))) (r _))
      (.add (r _) (.mul (r _) (.mul hF (r _)))),
    .sub (.mul (.add (r _) (.mul (r _) (.mul hF (r _)))) (r _))
      (.add (r _) (.mul (r _) (.mul hF (r _))))⟩

/-- **The Taylor constants, uniform over the cell** (`|λ| ≤ λ₁`, bounds `a ≤ aTQ`). -/
theorem mu_C2_cell {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i) (haa : ∀ i, a i ≤ aTQ i) {lm : ℝ}
    (hlm : |lm| ≤ lam1) :
    PolyExprS.majD2 a (fun i => (mvQ i : ℝ)) (gcFlowMu (1 / 256) lm).resRp / 2 ≤ (C2Q : ℝ) ∧
    PolyExprS.majD2 a (fun i => (mvQ i : ℝ)) (gcFlowMu (1 / 256) lm).resZp / 2 ≤ (C2Q : ℝ) := by
  have hb : ∀ i, (0 : ℝ) ≤ (mvQ i : ℝ) := fun i => by
    have := (show ∀ i, (0 : ℚ) ≤ mvQ i by decide +kernel) i
    exact_mod_cast this
  obtain ⟨cR, cZ⟩ := constLe_res hlm
  obtain ⟨vR, vZ⟩ := valid_res
  have mR := PolyExprS.majD2_mono (b := fun i => (mvQ i : ℝ)) (b' := fun i => (mvQ i : ℝ)) ha hb haa
    (fun _ => le_rfl) (cR.valid aTQ_nonneg vR)
  have mZ := PolyExprS.majD2_mono (b := fun i => (mvQ i : ℝ)) (b' := fun i => (mvQ i : ℝ)) ha hb haa
    (fun _ => le_rfl) (cZ.valid aTQ_nonneg vZ)
  have kR := cR.majD2_le aTQ_nonneg hb vR
  have kZ := cZ.majD2_le aTQ_nonneg hb vZ
  exact ⟨by linarith [mu_C2R], by linarith [mu_C2Z]⟩

/-- **The three node conditions over the cell** at every bound `0 ≤ a ≤ aTQ`, `|λ| ≤ λ₁`. -/
theorem mu_node_bounds {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i) (haa : ∀ i, a i ≤ aTQ i) {lm : ℝ}
    (hlm : |lm| ≤ lam1) : PolyExpr.maj a EpP < 1 ∧ PolyExpr.maj a E4P < 1 ∧
      |lm| * PolyExprS.maj a eBm < 1 := by
  have hE : PolyExpr.maj a EpP < 1 := ((PolyExpr.maj_mono ha haa EpP).trans mu_maj_E).trans_lt
    (by exact_mod_cast (show mEQ < 1 by decide +kernel))
  have hE4 : PolyExpr.maj a E4P < 1 := ((PolyExpr.maj_mono ha haa E4P).trans mu_maj_E4).trans_lt
    (by exact_mod_cast (show mE4Q < 1 by decide +kernel))
  have hBv : PolyExprS.Valid (fun i => (aTQ i : ℝ)) eBm := by
    rw [← eBmG_toS]; exact PQG.valid_of_nodesOK nodesOK_eBmG
  have hB : PolyExprS.maj a eBm ≤ (mBQ : ℝ) := (PolyExprS.maj_mono ha haa hBv).trans maj_eBm_le
  refine ⟨hE, hE4, ?_⟩
  have h := (show @LAMQ@ * mBQ ≤ mNQ by decide +kernel)
  have h' : ((@LAMQ@ * mBQ : ℚ) : ℝ) ≤ (mNQ : ℝ) := by exact_mod_cast h
  have h1 : (mNQ : ℝ) < 1 := by exact_mod_cast (show mNQ < 1 by decide +kernel)
  push_cast at h'
  have h0 := PolyExprS.maj_nonneg ha eBm
  have hl : |lm| ≤ @LAMR@ := hlm
  nlinarith [abs_nonneg lm]

/-- **Validity over the cell**: all expressions of `gcFlowMu (1/256) λ` and its residuals are valid
at every bound `0 ≤ a ≤ aTQ`, `|λ| ≤ λ₁`. -/
theorem mu_valid_cell {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i) (haa : ∀ i, a i ≤ aTQ i) {lm : ℝ}
    (hlm : |lm| ≤ lam1) :
    (gcFlowMu (1 / 256) lm).Valid6 a ∧ PolyExprS.Valid a (gcFlowMu (1 / 256) lm).resRp ∧
      PolyExprS.Valid a (gcFlowMu (1 / 256) lm).resZp := by
  obtain ⟨hE, hE4, hN⟩ := mu_node_bounds ha haa hlm
  exact gcFlowMu_valid _ lm a hE hE4 hN

end PlasmaLean.Design.RationalStellaratorGCMu
'''


def LAMG_EMIT(G, C, path=None):
    ql, leaf_int_list, LL = G['ql'], G['leaf_int_list'], G['LL']
    vec = lambda xs: '\n  ![' + ',\n    '.join(ql(x) for x in xs) + ']'
    lam = Fr(C['LAM1'])
    lamn, lamd = lam.numerator, lam.denominator
    sQ = LL['QPP4P'][0]
    assert LL['E4P'][0] == 1
    rep = {'@LAM@': '%d/%d' % (lamn, lamd), '@LAMR@': '%d / %d' % (lamn, lamd),
           '@LAMQ@': '(%d / %d : ℚ)' % (lamn, lamd), '@E4L@': leaf_int_list('E4P'),
           '@QL@': leaf_int_list('QPP4P'), '@SQ@': str(sQ), '@ATQ@': vec(C['aTQ']),
           '@MVQ@': vec(C['mvec']), '@MEQ@': ql(C['mE']), '@ME4Q@': ql(C['mE4']), '@MQQ@': ql(C['mQQ']),
           '@MBQ@': ql(C['mB']), '@MNQ@': ql(C['mN']), '@GEQ@': ql(C['gE']), '@GE4Q@': ql(C['gE4']),
           '@GNQ@': ql(C['gN']), '@C2Q@': ql(C['C2']), '@C2@': '%.4g' % float(C['C2']),
           '@MB@': '%.4g' % float(C['mB']), '@MN@': '%.4g' % float(C['mN'])}
    txt = TEMPLATE
    for k, v in rep.items():
        txt = txt.replace(k, v)
    assert '@' not in txt.replace('@[expose]', ''), 'unreplaced template field'
    open(path or (EMIT + 'RationalStellaratorGCMuMaj.lean'), 'w').write(txt)


W = lc.WORK
EMIT = os.path.join(W, 'emit') + '/'


def load_globals():
    """lam_maj.py's module-level definitions (trees, majorants, helpers) without its main part."""
    lc.setup_path()
    path = os.path.join(lc.GCK, 'lam_maj.py')
    src = open(path).read()
    src = lc.patch(src, [("ROOT = '/Users/gadgil/code/PlasmaLean/PlasmaLean/Design/'", "ROOT = LAMCELL_DESIGN"),
                         ("LAM1 = Fr(2, LAMDEN)", "LAM1 = LAMCELL_HI")], 'lam_maj.py')
    src = src.replace("if __name__ == '__main__':", "if False:")
    G = {'__name__': 'lam_maj_g', '__file__': path, '__builtins__': __builtins__,
         'LAMCELL_DESIGN': lc.DESIGN, 'LAMCELL_HI': lc.HI}
    exec(compile(src, path + ' (lamcell maj_g)', 'exec'), G)
    return G


def check():
    """Cheap check at the certified Mu2 bounds (no ball pipeline): node bounds and C2 for LAM_HI."""
    G = load_globals()
    import re
    s = open(lc.DESIGN + 'RationalStellaratorGCMu2Maj.lean').read()

    def vecq(name):
        body = re.search(r'def %s : Fin 6 → ℚ := \s*!\[(.*?)\]' % name, s, re.S).group(1)
        out = []
        for t in re.findall(r'\(([^():]*?) : ℚ\)', body):
            t = t.replace(' ', '').replace('^', '**')
            out.append(Fr(eval(t, {'__builtins__': {}})) if '**' in t else Fr(t))
        return out
    aTQ, mvQ = vecq('aTQ'), vecq('mvQ')
    up = G['up']
    print('cell [%s, %s], lam1 = %s; bounds aTQ, mvQ of RationalStellaratorGCMu2Maj (certified [1/16, 1/8])'
          % (lc.LO, lc.HI, lc.HI))
    try:
        u = G['node_bounds'](aTQ)
        print('  uniform g (lam_maj.py): OK  mN %.4f g %.4f' % (u[3], u[4]))
    except AssertionError as e:
        print('  uniform g (lam_maj.py): FAIL %s  (needs lam1 <= 1/(4 mQQ))' % (e,))
    mE, mE4, mQQ, mB, mN, gE, gE4, gN = node_bounds_g(G, aTQ)
    print('  per-node: mE %.4f mE4 %.6f mQQ %.4f  mB = mQQ gE gE4 = %.4f  mN = lam1 mB = %.4f < 1  '
          'gE %.5f gE4 %.5f gN %.5f' % (mE, mE4, mQQ, mB, mN, gE, gE4, gN))
    eN, resR, resZ = G['trees'](G['LAM1'])
    gf = gfun(G, gE, gE4, gN)
    C2 = up(max(mD2g(aTQ, mvQ, gf, resR), mD2g(aTQ, mvQ, gf, resZ)) / 2, 3)
    print('  per-node C2 = %.4g  (certified Mu2 cell, lam1 = 1/8, uniform g: 9.67e10)' % float(C2))
    print('node check PASSED')


if __name__ == '__main__':
    if '--check' in sys.argv:
        check()
        sys.exit(0)
    os.makedirs(EMIT, exist_ok=True)
    os.environ['LAM_DEN'] = str(lc.LAMDEN)
    os.environ['LAM_PKL_H'] = os.path.join(W, 'lam_cert_H.pkl')
    os.environ['LAM_PKL_L'] = os.path.join(W, 'lam_cert_L.pkl')
    lc.run_patched('lam_maj.py', [
        ("ROOT = '/Users/gadgil/code/PlasmaLean/PlasmaLean/Design/'", "ROOT = LAMCELL_DESIGN"),
        ("LAM1 = Fr(2, LAMDEN)", "LAM1 = LAMCELL_HI"),
        ("    mE, mE4, mQQ, mN, g = node_bounds(aTQ)\n",
         "    mE, mE4, mQQ, mN, g, gE, gE4, mB = LAMG_NODE(globals(), aTQ)\n"),
        ("    C2R = mD2Q(aTQ, mvec, g, resR, {}) / 2\n", "    C2R = LAMG_MD2(globals(), aTQ, mvec, resR) / 2\n"),
        ("    C2Z = mD2Q(aTQ, mvec, g, resZ, {}) / 2\n", "    C2Z = LAMG_MD2(globals(), aTQ, mvec, resZ) / 2\n"),
        ("                 LAM1=LAM1)", "                 LAM1=LAM1, gE=gE, gE4=gE4, gN=g, mB=mB)"),
        ("pickle.dump(CONST, open('/tmp/lamc/lam_const.pkl', 'wb'))",
         "pickle.dump(CONST, open(LAMCELL_WORK + '/lam_const.pkl', 'wb'))"),
        ("    emit_lean(CONST)\n", "    LAMG_EMIT(globals(), CONST)\n"),
    ], [], extra_globals=dict(LAMCELL_DESIGN=lc.DESIGN, LAMCELL_HI=lc.HI, LAMCELL_WORK=W,
                              LAMG_NODE=LAMG_NODE, LAMG_MD2=LAMG_MD2, LAMG_EMIT=LAMG_EMIT))
