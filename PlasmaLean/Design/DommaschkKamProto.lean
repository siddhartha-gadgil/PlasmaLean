/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronProof2D

/-!
# Cost prototype for the Dommaschk KAM residual certificate (not imported by `PlasmaLean.lean`)

Design study `notes/theory/dommaschk-kam-certificate.md` (N-33), §5. The residual certificate of
the Dommaschk torus would be a chain of ball-arithmetic product nodes in the strip algebra
(`Certificates/KronBall`, as for the guiding-centre torus `Design/RationalStellaratorGCTorus*`).
The kernel cost of one node is dominated by the Kronecker image of a product of two
trigonometric-polynomial centres and by the weighted digit reading of that image (`kron2_proof`,
`Certificates/KronProof2D`). This file measures exactly that core step at two sizes:

* `protoSmall`: two `40 × 30` grids (the size of the high-resolution guiding-centre chain),
  coefficients of `101` bits, `b = 219` bits per slot, product image `≈ 4.3` Mbit;
* `protoBig`: two `104 × 88` grids (the size proposed for the Dommaschk torus), coefficients of
  `130` bits, `b = 279` bits per slot, product image `≈ 41` Mbit.

The input images are closed forms (all digits equal), so the kernel builds them with a few GMP
operations; the product and the digit reading are the same work as for genuine data. Note that
the kernel refuses `Nat.pow` results above `2^25` bits (`LEAN_NAT_MAX_SIZE`), but not products
or shifts, so images are built with `<<<` (the `offs`/`rowOffs` of `wl1KronP` already are).
Measurements (laptop, `lake env lean`, `/usr/bin/time -l`) are recorded in the note.

**Sanity.** `protoSmall` and `protoBig` are accepted; a false bound on the small image is refused
(`fail_if_success`).
-/

@[expose] public section

namespace PlasmaLean.Design.DommaschkKamProto

open PlasmaLean.Certificates.Kron2

/-- `geoK b n = 1 + 2^b + ⋯ + 2^{b(n−1)}`: `n` base-`2^b` digits equal to `1`. -/
def geoK (b n : Nat) : Nat := ((1 <<< (b * n)) - 1) / ((1 <<< b) - 1)

/-- Input image of size `40 × 30` (all `(2N+1)(2M+1)` digits equal to `2^101 − 3`, row stride
`W = 161`, `b = 219` bits per slot; a closed form, so that the kernel computes it with a few GMP
operations). -/
def imgSmallA : Int := ((2 ^ 101 - 3 : Nat) : Int) * (geoK 219 81 * geoK (219 * 161) 61 : Nat)

/-- Second input image (digits `−(2^101 − 5)`). -/
def imgSmallB : Int := -((2 ^ 101 - 5 : Nat) : Int) * (geoK 219 81 * geoK (219 * 161) 61 : Nat)

/-- **Prototype check `Small`**: the separable weighted digit sum (weights of the strip
`e^r ≤ 74315/2^16`) of the Kronecker image of the product of two `40 × 30` grids, i.e. the core
kernel cost of one ball-arithmetic product node at this size. -/
theorem protoSmall :
    wl1KronP 219 161 8 7 121 (fun i => kwtS 74315 16 80 (ndist i 80))
      (fun j => kwtS 74315 16 60 (ndist j 60)) (imgSmallA * imgSmallB) ≤ 2 ^ 2703 := by
  kron2_proof

/-- Input image of size `104 × 88` (all `(2N+1)(2M+1)` digits equal to `2^130 − 3`, row stride
`W = 417`, `b = 280` bits per slot; a closed form, so that the kernel computes it with a few GMP
operations). -/
def imgBigA : Int := ((2 ^ 130 - 3 : Nat) : Int) * (geoK 280 209 * geoK (280 * 417) 177 : Nat)

/-- Second input image (digits `−(2^130 − 5)`). -/
def imgBigB : Int := -((2 ^ 130 - 5 : Nat) : Int) * (geoK 280 209 * geoK (280 * 417) 177 : Nat)

/-- **Prototype check `Big`**: the separable weighted digit sum (weights of the strip
`e^r ≤ 74315/2^16`) of the Kronecker image of the product of two `104 × 88` grids, i.e. the core
kernel cost of one ball-arithmetic product node at this size. -/
theorem protoBig :
    wl1KronP 280 417 9 9 353 (fun i => kwtS 74315 16 208 (ndist i 208))
      (fun j => kwtS 74315 16 176 (ndist j 176)) (imgBigA * imgBigB) ≤ 2 ^ 6912 := by
  kron2_proof

/-- **Sanity (rejected)**: `kron2_proof` refuses a false bound (`2^64`) on the small image. -/
example : True := by
  fail_if_success
    have : wl1KronP 219 161 8 7 121 (fun i => kwtS 74315 16 80 (ndist i 80))
      (fun j => kwtS 74315 16 60 (ndist j 60)) (imgSmallA * imgSmallB) ≤ 2 ^ 64 := by kron2_proof
  trivial

end PlasmaLean.Design.DommaschkKamProto
