/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningDefs

/-!
# Ballooning certificate data for the reactor Solov'ev equilibrium

The Riccati certificate data `gdata` (one data set for ALL surfaces `0 < s ≤ 25`: the
coefficients are quadratic polynomials in `s`), proposed by the UNTRUSTED oracle
`scripts/solovev_ballooning_oracle.py` (convex SOCP, coefficients rounded to multiples of
`2⁻²⁴`). The `s⁰` coefficients are fixed exactly so that the certificate degenerates correctly
on the magnetic axis (`f₀ = (3√2/35) x + O(s)`, `f₁, f₂ = O(s)`).
-/

public section

namespace PlasmaLean.Design.SolovevBallooning

open Tm

/-- **The certificate data** (untrusted oracle output, checked by the kernel). -/
@[expose] def gdata : Data where
  dl := (add (c (9811) 4194304) (mul tS (add (c (-10505) 16777216) (mul tS (c (21) 16777216)))))
  A0 := [(add (mul (c (3) 35) tr) (mul tS (add (c (-607) 2097152) (mul tS (c (265) 8388608))))),
    (mul tS (add (c (-38247) 16777216) (mul tS (c (-63) 4194304)))),
    (mul tS (add (c (-4453) 16777216) (mul tS (c (2063) 16777216)))),
    (mul tS (add (c (1431) 16777216) (mul tS (c (-393) 8388608))))]
  A1 := [(mul tS (add (c (12095) 16777216) (mul tS (c (-349) 8388608)))),
    (mul tS (add (c (-12163) 4194304) (mul tS (c (61) 4194304)))),
    (mul tS (add (c (10341) 16777216) (mul tS (c (79) 16777216)))),
    (mul tS (add (c (-249) 16777216) (mul tS (c (-51) 16777216))))]
  A2 := [(mul tS (add (c (-5937) 8388608) (mul tS (c (-53) 4194304)))),
    (mul tS (add (c (-6015) 16777216) (mul tS (c (251) 8388608)))),
    (mul tS (add (c (12475) 4194304) (mul tS (c (-45) 16777216)))),
    (mul tS (add (c (-1091) 2097152) (mul tS (c (-153) 8388608))))]

end PlasmaLean.Design.SolovevBallooning
