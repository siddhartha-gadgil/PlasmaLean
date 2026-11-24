"""Recheck a compiled forward Jacobian's time panels against a signed partner's rate."""
from fractions import Fraction

from bounce_mirror_pilot import Model, ORDER, SCALE
from screen_sparse_jacobians import symmetric_models
from screen_sparse_reference_defects import bounds


def backward_rate(index, previous, step, forward_module, backward_budget, panels=8):
    if panels < 1 or panels & (panels - 1):
        raise ValueError('expected a power of two time panels')
    rate = Fraction(backward_budget)
    coordinates = (Model(p, step['physical_trial_radius']) for p in step['coefficients'])
    models = symmetric_models(0, 1, index, previous, step, *coordinates)
    name = f'DommaschkBackwardRate{index:03}'
    lines = [f'''module
public import PlasmaLean.Design.{forward_module}

/-! # Forward spatial Jacobian with the exact archived backward allowance -/
@[expose] public section
namespace PlasmaLean.Design.{name}
open DommaschkJacobian DommaschkKam DommaschkKam.DkPoly {forward_module}
open Certificates.PositionFrameSlabs
open scoped RealInnerProductSpace
set_option linter.style.longLine false
def rate : ℚ := {rate}
''']
    proofs = []
    scale = SCALE * panels**ORDER
    for i, (den, aa, dd, off) in enumerate(zip(*(bounds(m, panels) for m in models), strict=True)):
        dl, a, d, w = (Fraction(k, scale) for k in (den[0], aa[1], dd[1], max(map(abs, off))))
        ma, md = rate*dl-a, rate*dl-d
        if min(dl, rate) <= 0 or min(ma, md) < 0 or w*w > 4*ma*md:
            raise ValueError(f'backward row {index}, time panel {i} exceeds its archived allowance')
        left = Fraction(2*i-panels, panels)
        right = Fraction(2*i+2-panels, panels)
        label = f'panel{i}'
        lines.append(f'''private theorem {label} :
    MinorCover {forward_module}Panels.models rate ({left}) ({right}) := by
  apply MinorCover.panel
  refine ⟨{dl}, {a}, {d}, {w}, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_fact
''')
        proofs.append(label)
    while len(proofs) > 1:
        proofs = [f'(MinorCover.join {left} {right})' for left,right
                  in zip(proofs[::2],proofs[1::2],strict=True)]
    s = f'(128 * t - {2*index+1})'
    lines.append(f'''theorem accepted : MinorCover {forward_module}Panels.models rate (-1) 1 := {proofs[0]}

/-- The original forward spacetime tube satisfies the backward clock's recorded allowance. -/
theorem physical_clock_log_norm {{t R z : ℝ}} (ht : t ∈ Set.Icc ({index} / 64 : ℝ) ({index+1} / 64))
    (hu : trial.u.Mem {s} (R - dkR0)) (hz : trial.z.Mem {s} z) (x : Plane) :
    ⟪x, Fields.LogNormTrajectory.MovingFrame.jacobian
      (spatialMatrix (R - dkR0) z (Real.cos (2 * t)) (Real.sin (2 * t)))
      (frameEquiv leftFrame rightFrame {s}) (frameVelocity leftFrame rightFrame) x⟫ ≤
      (rate : ℝ) * ‖x‖ ^ 2 := by
  have hs : |128 * t - {2*index+1}| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact spatial_log_norm_of_cover accepted leftFrame rightFrame {s} (R - dkR0) z _ _ hs
    (models_mem hs (clock_inputs ht hu hz)) x

end PlasmaLean.Design.{name}
''')
    return name, '\n'.join(lines), ['physical_clock_log_norm']
