import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open MeasureTheory Filter FourierTransform TopologicalSpace
open scoped FourierTransform RealInnerProductSpace

#check fourier_gaussian_pi
#check Complex.ofReal_exp
#check FourierTransform.fourier
#check Complex.ofRealCLM.hasDerivAt
#check @ContinuousLinearMap.hasDerivAt
#check @HasDerivAt.comp
#check @HasFDerivAt.comp
#check @HasFDerivAt.hasDerivAt
#check @HasDerivAt.hasFDerivAt
#check Complex.ofRealCLM.hasFDerivAt
#check @SchwartzMap.postcompCLM
#check Complex.norm_real
#check Complex.norm_real_of_nonneg
#check Integrable.ofReal

noncomputable def g (x : ℝ) : ℝ := Real.exp (-Real.pi * x ^ 2)

example :
    (𝓕 fun x : ℝ ↦ (g x : ℂ)) = fun t : ℝ ↦ (g t : ℂ) := by
  have h := fourier_gaussian_pi (b := (1 : ℂ)) (by norm_num)
  convert h using 1 <;> ext x <;> simp [g]
