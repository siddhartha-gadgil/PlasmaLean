"""Compensated strength-gap evaluations for the rational Dommaschk field.

The toroidal field component D/R^7 is close to the mirror height. Subtract
h0*R^7 directly in D's spatial coefficients before evaluating the tube.
The resulting polynomial A gives R^16 (|B|²-h0²) =
R²*A*(D+h0*R^7) + nR²+nZ². Differentiate this same expression along the
line to check outward slopes. All arithmetic uses the pilot's dyadic models.
"""
from fractions import Fraction as F
from math import comb

import bounce_mirror_pilot as pilot
from bounce_launch_box import R0


def subtract_radial_power(poly, degree, scale):
    """Subtract scale*(R0+u)^degree from the z-independent constant harmonic."""
    result = dict(poly)
    rows = list(poly.get(0, [[pilot.ZERO]]))
    right = [pilot.Model.rational(scale*comb(degree,j)*R0**(degree-j))
             for j in range(degree,-1,-1)]
    left = rows[-1]
    size = max(len(left), len(right))
    left = [pilot.ZERO]*(size-len(left))+left
    right = [pilot.ZERO]*(size-len(right))+right
    rows[-1] = [a-b for a,b in zip(left,right,strict=True)]
    result[0] = rows
    return result


class ShiftedStrength:
    def __init__(self, data):
        self.reference = pilot.HEIGHTS[0]
        den, den_r, den_z = data[0]
        self.diff = [subtract_radial_power(den,7,self.reference),
                     subtract_radial_power(den_r,6,7*self.reference), den_z]

    def numerators(self, tube, angles, val, heights):
        """Return models of R^16*(|B|²-h²) for the requested h."""
        gaps, _ = self.calculate(tube, angles, val, heights)
        return gaps

    def calculate(self, tube, angles, val, heights):
        radius = tube[0]
        r2 = radius*radius
        r4 = r2*r2
        r8 = r4*r4
        r16 = r8*r8
        diff, phi_diff = pilot.evaluate(self.diff[0],tube,angles)
        den, nr, nz = val
        plus = den.integer(2)-diff
        base = r2*diff*plus+nr*nr+nz*nz
        gaps = [base + r16*pilot.Model.rational(self.reference**2-h**2) for h in heights]
        return gaps, (r16,base,plus,diff,phi_diff)

    def geometry(self, data, angles, tube, val, grad, sign, want_slope):
        gaps, (r16,base,plus,diff,phi_diff) = self.calculate(tube,angles,val,pilot.HEIGHTS)
        bounds = [pilot.quotient_range(gap,r16) for gap in gaps]
        if not want_slope:
            return bounds,None
        den,nr,nz = val
        radius = tube[0]
        # Along the line D*d/dphi = D*partial_phi + nr*partial_R + nz*partial_z.
        dr,dz = [pilot.evaluate(poly,tube,angles)[0] for poly in self.diff[1:]]
        d_diff = den*phi_diff+nr*dr+nz*dz
        phi = [pilot.evaluate(g[0],tube,angles)[1] for g in data]
        d_den,d_nr,d_nz = [den*p+nr*r+nz*z for p,(r,z) in zip(phi,grad,strict=True)]
        d_plus = d_den.integer(2)-d_diff
        d_base = ((radius*nr*diff*plus).integer(2)
                  + radius*radius*(d_diff*plus+diff*d_plus)
                  + (nr*d_nr+nz*d_nz).integer(2))
        slope = pilot.quotient_range((radius*d_base-(nr*base).integer(16)).integer(sign),
                                     radius*r16*den)
        return bounds,slope


def check_shifted_strength():
    """Compare to the analytic strength and derivative of a translating field."""
    den,nr,nz = [pilot.Model.rational(v) for v in (1,F(1,4),F(-1,8))]
    data = [[{0:[[v]]},{},{}] for v in (den,nr,nz)]
    val = [den,nr,nz]
    grad = [[pilot.ZERO,pilot.ZERO] for _ in val]
    shifted = ShiftedStrength(data)
    for r in (F(7,8), F(1), F(17,16)):
        tube = [pilot.Model.rational(r),pilot.ZERO]
        for sign in (-1,1):
            gaps,slope = shifted.geometry(data,[pilot.ONE],tube,val,grad,sign,True)
            b2 = r**(-14)+F(5,64)*r**(-16)
            derivative = sign*F(1,4)*(-14*r**(-15)-F(5,4)*r**(-17))
            if not slope[0]<=derivative<=slope[1] or any(
                    not low<=b2-h*h<=high for h,(low,high) in zip(pilot.HEIGHTS,gaps)):
                raise ArithmeticError('compensated strength sanity check failed')
