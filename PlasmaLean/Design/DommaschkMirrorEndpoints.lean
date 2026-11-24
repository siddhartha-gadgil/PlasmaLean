/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PositionFrameSlabs

/-!
# Initial states of the eight local-action endpoint traces

Position uses units of 2⁻⁸⁰ and the initial frame is the identity in units of
2⁻⁴⁰. The generated scalar replay proves that both directions start at this
same state for each endpoint.
-/

@[expose] public section
namespace PlasmaLean.Design.DommaschkMirrorLaunch
noncomputable section

/-- The four radial endpoints on each symmetry section. -/
inductive MirrorEndpoint where
  | q0r470 | q0r478 | q0r523 | q0r531
  | q1r456 | q1r464 | q1r509 | q1r517

namespace MirrorEndpoint

/-- Symmetry section of the common angular clock. -/
def opposite : MirrorEndpoint → Bool
  | .q0r470 => false
  | .q0r478 => false
  | .q0r523 => false
  | .q0r531 => false
  | .q1r456 => true
  | .q1r464 => true
  | .q1r509 => true
  | .q1r517 => true

/-- Interpolation coordinate between the two true Q-16 profiles. -/
def radius : MirrorEndpoint → ℝ
  | .q0r470 => 470 / 1000
  | .q0r478 => 478 / 1000
  | .q0r523 => 523 / 1000
  | .q0r531 => 531 / 1000
  | .q1r456 => 456 / 1000
  | .q1r464 => 464 / 1000
  | .q1r509 => 509 / 1000
  | .q1r517 => 517 / 1000

/-- Transferred centre and Euclidean radius in the integer units of the frame witness. -/
def start : MirrorEndpoint → Certificates.PositionFrameSlabs.State
  | .q0r470 => ⟨⟨1203469614412823932174336, 0⟩, ⟨2^40, 0, 0, 2^40⟩, 1475196542527609990⟩
  | .q0r478 => ⟨⟨1203570775625936261873664, 0⟩, ⟨2^40, 0, 0, 2^40⟩, 1477643372418852310⟩
  | .q0r523 => ⟨⟨1204139807449693384867840, 0⟩, ⟨2^40, 0, 0, 2^40⟩, 1491350776919641843⟩
  | .q0r531 => ⟨⟨1204240968662805714567168, 0⟩, ⟨2^40, 0, 0, 2^40⟩, 1493737295514859369⟩
  | .q1r456 => ⟨⟨1081068480584480819511296, 0⟩, ⟨2^40, 0, 0, 2^40⟩, 1034284459323321581⟩
  | .q1r464 => ⟨⟨1081210970017597524803584, 0⟩, ⟨2^40, 0, 0, 2^40⟩, 1035624340981689527⟩
  | .q1r509 => ⟨⟨1082012473078879696715776, 0⟩, ⟨2^40, 0, 0, 2^40⟩, 1043748261584110630⟩
  | .q1r517 => ⟨⟨1082154962511996402008064, 0⟩, ⟨2^40, 0, 0, 2^40⟩, 1045315895699093361⟩

/-- Half-width in geometric radians of the physical birth sector. -/
def width (e : MirrorEndpoint) : ℝ := if e.opposite then 1 / 2^20 else 1 / 2^19

end MirrorEndpoint

end
end PlasmaLean.Design.DommaschkMirrorLaunch
