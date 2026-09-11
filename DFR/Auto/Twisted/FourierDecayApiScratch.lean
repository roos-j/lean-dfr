import Auto.Twisted.Twisted
import Mathlib.Analysis.Fourier.AddCircleMulti

namespace Auto.Twisted

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal Topology

#check ContDiff.contDiffAt
#check ContDiff.differentiable
#check DifferentiableAt.hasFDerivAt
#check HasFDerivAt.comp_hasDerivAt
#check HasFDerivAt.comp
#check HasDerivAt.comp
#check HasDerivAt.mul
#check fourierCoeffOn_of_hasDerivAt
#check UnitAddTorus.mFourierCoeff_eq_integral
#check UnitAddTorus.mFourierCoeff
#check intervalIntegral.integral_mul_deriv_eq_deriv_mul
#check MeasureTheory.integral_prod
#check Continuous.intervalIntegrable
#check iteratedFDeriv_one_apply
#check norm_iteratedFDeriv_comp_le
#check Complex.norm_real
#check Complex.norm_I

end Auto.Twisted
