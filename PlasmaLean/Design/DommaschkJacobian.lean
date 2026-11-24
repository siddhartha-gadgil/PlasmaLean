/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkBounceTaylor

/-! # Sparse spatial derivatives and the moving-frame quadratic form

The quotient rule is kept over its common denominator. Retaining the trace
and diagonal difference of the transformed numerator avoids independent
upper bounds on the two diagonal entries.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkJacobian

open DommaschkKam DommaschkKam.DkPoly

/-- Numerator of a spatial partial derivative of a field-line velocity. -/
def quotientNumerator (n : SP) (der : SP → SP) (u z c s : ℝ) : ℝ :=
  evR u z c s (der n) * evR u z c s dD - evR u z c s n * evR u z c s (der dD)

/-- Spatial partial derivative formula, in shifted radius or height coordinates. -/
def quotientEntry (n : SP) (der : SP → SP) (u z c s : ℝ) : ℝ :=
  quotientNumerator n der u z c s / (evR u z c s dD * evR u z c s dD)

/-- Four real matrix entries in physical coordinate order. -/
structure Entries where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

def Entries.product (x y : Entries) : Entries :=
  ⟨x.a*y.a+x.b*y.c, x.a*y.b+x.b*y.d, x.c*y.a+x.d*y.c, x.c*y.b+x.d*y.d⟩

def Entries.sub (x y : Entries) : Entries := ⟨x.a-y.a,x.b-y.b,x.c-y.c,x.d-y.d⟩
def Entries.scale (x : Entries) (q : ℝ) : Entries := ⟨q*x.a,q*x.b,q*x.c,q*x.d⟩
def Entries.adj (x : Entries) : Entries := ⟨x.d,-x.b,-x.c,x.a⟩
def Entries.det (x : Entries) : ℝ := x.a*x.d-x.b*x.c
def Entries.quad (x : Entries) (v w : ℝ) : ℝ := v*(x.a*v+x.b*w)+w*(x.c*v+x.d*w)

/-- The numerator of the physical spatial Jacobian, with denominator D². -/
def spatialNumerator (u z c s : ℝ) : Entries :=
  ⟨quotientNumerator dnR dU u z c s, quotientNumerator dnR dZ u z c s,
   quotientNumerator dnZ dU u z c s, quotientNumerator dnZ dZ u z c s⟩

/-- Numerator of M⁻¹(JM−M′), with denominator det(M) D². -/
def transformedNumerator (j m velocity : Entries) (denSq : ℝ) : Entries :=
  m.adj.product ((j.product m).sub (velocity.scale denSq))

/-- A trace bound and a disk enclosing the two independent traceless entries
give a logarithmic norm bound. The data may be scaled by any positive denominator. -/
theorem quadratic_le_of_trace (A : Entries) {den traceRadius diskRadius mu : ℝ}
    (hd : 0 < den) (htrace : A.a + A.d ≤ traceRadius)
    (hdisk : (A.a - A.d) ^ 2 + (A.b + A.c) ^ 2 ≤ diskRadius ^ 2)
    (hr : 0 ≤ diskRadius) (hmu : traceRadius + diskRadius ≤ 2 * den * mu) (x y : ℝ) :
    A.quad x y / den ≤ mu * (x^2+y^2) := by
  let p := x^2-y^2
  let q := 2*x*y
  let r := x^2+y^2
  let v := A.a-A.d
  let w := A.b+A.c
  have nr : 0 ≤ r := by dsimp [r]; positivity
  have id : p^2 + q^2 = r^2 := by dsimp [p,q,r]; ring
  have cs : (v*p+w*q)^2 ≤ (v^2+w^2)*r^2 := by
    rw [← id]
    nlinarith only [sq_nonneg (v*q-w*p)]
  have cs' : (v*p+w*q)^2 ≤ (diskRadius*r)^2 := by
    rw [mul_pow]
    exact cs.trans (mul_le_mul_of_nonneg_right hdisk (sq_nonneg r))
  have lin : v*p+w*q ≤ diskRadius*r :=
    (abs_le_of_sq_le_sq' cs' (mul_nonneg hr nr)).2
  have eq : 2 * A.quad x y = (A.a + A.d)*r + (v*p+w*q) := by
    dsimp [Entries.quad,v,w,p,q,r]
    ring
  apply (div_le_iff₀ hd).mpr
  change A.quad x y ≤ (mu*r)*den
  nlinarith only [eq, lin, mul_le_mul_of_nonneg_right htrace nr,
    mul_le_mul_of_nonneg_right hmu nr]

/-- On a subcell, nonnegative diagonal entries and determinant of the
symmetric matrix `mu * den * I − sym(A)` certify the same quadratic bound. -/
theorem quadratic_le_of_minors (A : Entries) {den mu : ℝ}
    (hd : 0 < den) (ha : A.a ≤ mu * den) (hb : A.d ≤ mu * den)
    (hm : (A.b + A.c) ^ 2 ≤ 4 * (mu * den - A.a) * (mu * den - A.d)) (x y : ℝ) :
    A.quad x y / den ≤ mu * (x^2+y^2) := by
  apply quadratic_le_of_trace A hd (le_refl _) (diskRadius := 2 * (mu * den) - (A.a + A.d))
  · nlinarith only [hm]
  · linarith only [ha, hb]
  · ring_nf
    exact le_rfl

end PlasmaLean.Design.DommaschkJacobian
