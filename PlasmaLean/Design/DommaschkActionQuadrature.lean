/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkActionBroad1Inner
public import PlasmaLean.Design.DommaschkActionBroad1Outer
public import PlasmaLean.Design.DommaschkActionBroad2Inner
public import PlasmaLean.Design.DommaschkActionBroad2Outer
public import PlasmaLean.Design.DommaschkActionChart0Inner
public import PlasmaLean.Design.DommaschkActionChart0Outer
public import PlasmaLean.Design.DommaschkActionChart1Inner
public import PlasmaLean.Design.DommaschkActionChart1Outer
public import PlasmaLean.Design.DommaschkActionChart2Inner
public import PlasmaLean.Design.DommaschkActionChart2Outer
public import PlasmaLean.Design.DommaschkActionChart3Inner
public import PlasmaLean.Design.DommaschkActionChart3Outer
public import PlasmaLean.Design.DommaschkActionMirrorBirthHigh
public import PlasmaLean.Design.DommaschkActionMirrorBirthLow
public import PlasmaLean.Design.DommaschkActionMirrorCommonHigh
public import PlasmaLean.Design.DommaschkActionMirrorCommonLow
public import PlasmaLean.Design.DommaschkActionQ0R470
public import PlasmaLean.Design.DommaschkActionQ0R478
public import PlasmaLean.Design.DommaschkActionQ0R523
public import PlasmaLean.Design.DommaschkActionQ0R531
public import PlasmaLean.Design.DommaschkActionQ1R456
public import PlasmaLean.Design.DommaschkActionQ1R464
public import PlasmaLean.Design.DommaschkActionQ1R509
public import PlasmaLean.Design.DommaschkActionQ1R517
public import PlasmaLean.Design.DommaschkActionSym0Inner
public import PlasmaLean.Design.DommaschkActionSym0Outer
public import PlasmaLean.Design.DommaschkActionSym1Inner
public import PlasmaLean.Design.DommaschkActionSym1Outer

/-!
# Exact quadrature checks for Dommaschk mirror and sector packets

Each imported namespace provides `checked` for its packed rectangle weights and
`endpoint` for the corresponding continuous weighted action when the trajectory
realizes its two primitive enclosures. The four broad-sector packets use the
declared forbidden-cap or accessible-core interval. All angular coordinates
are relative to the displayed origin.
-/
