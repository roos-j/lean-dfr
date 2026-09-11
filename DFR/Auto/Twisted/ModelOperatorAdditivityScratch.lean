/- Copyright (c) 2026. All rights reserved.
   SPDX-License-Identifier: Apache-2.0 -/

import Auto.Twisted.Twisted

namespace Auto
namespace Twisted

open MeasureTheory Filter
open scoped BigOperators ENNReal

noncomputable section

/-! ## Algebra of the literal coordinate convolution

The one-fiber decomposition needs to expand a selected input into its good
and bad parts inside the actual coordinate convolution.  Since Bochner
integration is totalized, additivity is stated with the precise two
integrability hypotheses which make the expansion sound. -/

/-- A literal coordinate convolution is additive in its input once the two
line integrands are integrable. -/
theorem scratch_ModelCoordinateConvolution_add
    (i : Fin 3) (f g : E3 → ℝ) (k : ℝ → ℝ) (s : ℝ) (x : E3)
    (hf : Integrable (fun r : ℝ ↦
      f (x - r • Anisotropy.coordinateDirection i) * kernelDilate k s r))
    (hg : Integrable (fun r : ℝ ↦
      g (x - r • Anisotropy.coordinateDirection i) * kernelDilate k s r)) :
    ModelCoordinateConvolution i (f + g) k s x =
      ModelCoordinateConvolution i f k s x +
        ModelCoordinateConvolution i g k s x := by
  unfold ModelCoordinateConvolution
  have hpoint : (fun r : ℝ ↦
      (f + g) (x - r • Anisotropy.coordinateDirection i) * kernelDilate k s r) =
      (fun r : ℝ ↦
        f (x - r • Anisotropy.coordinateDirection i) * kernelDilate k s r +
          g (x - r • Anisotropy.coordinateDirection i) * kernelDilate k s r) := by
    funext r
    simp only [Pi.add_apply]
    ring
  rw [hpoint, integral_add hf hg]

/-- A literal coordinate convolution is additive in its input after a
pointwise rewrite of the two summands.  This convenient form avoids forcing
the good--bad construction to use function addition definitionally. -/
theorem scratch_ModelCoordinateConvolution_add_of_eq
    (i : Fin 3) (f g h : E3 → ℝ) (k : ℝ → ℝ) (s : ℝ) (x : E3)
    (hfg : h = f + g)
    (hf : Integrable (fun r : ℝ ↦
      f (x - r • Anisotropy.coordinateDirection i) * kernelDilate k s r))
    (hg : Integrable (fun r : ℝ ↦
      g (x - r • Anisotropy.coordinateDirection i) * kernelDilate k s r)) :
    ModelCoordinateConvolution i h k s x =
      ModelCoordinateConvolution i f k s x +
        ModelCoordinateConvolution i g k s x := by
  rw [hfg]
  exact scratch_ModelCoordinateConvolution_add i f g k s x hf hg

/-- A merely Borel bounded input already gives an integrable literal line
integrand.  Continuity is not needed for this Young-type fact, which is
important because selected Calderón--Zygmund good and bad pieces are only
measurable. -/
theorem scratch_integrable_modelCoordinateConvolutionIntegrand_of_bounded_measurable
    (i : Fin 3) (f : E3 → ℝ) (k : ℝ → ℝ) (s : ℝ) (x : E3)
    (hf : Measurable f) (B : ℝ) (hfB : ∀ y : E3, |f y| ≤ B)
    (hk : Integrable k) (hs : 0 < s) :
    Integrable (fun r : ℝ ↦
      f (x - r • Anisotropy.coordinateDirection i) * kernelDilate k s r) := by
  let G : ℝ → ℝ := fun r ↦
    f (x - r • Anisotropy.coordinateDirection i) * kernelDilate k s r
  have hmap : Measurable (fun r : ℝ ↦
      x - r • Anisotropy.coordinateDirection i) :=
    (continuous_const.sub (continuous_id.smul continuous_const)).measurable
  have hkd : Integrable (kernelDilate k s) := by
    exact integrable_kernelDilate hk hs.ne'
  have hGmeas : AEStronglyMeasurable G volume := by
    dsimp only [G]
    exact ((hf.comp hmap).aestronglyMeasurable.mul hkd.aestronglyMeasurable)
  have hK : Integrable (fun r : ℝ ↦ |kernelDilate k s r|) :=
    integrable_abs_kernelDilate k hk hs
  have hupper : Integrable (fun r : ℝ ↦ B * |kernelDilate k s r|) :=
    hK.const_mul B
  apply hupper.mono' hGmeas
  filter_upwards [] with r
  dsimp only [G]
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right
    (hfB (x - r • Anisotropy.coordinateDirection i)) (abs_nonneg _)

/-- The `L∞` Young bound for a coordinate convolution needs only Borel
measurability of its bounded input. -/
theorem scratch_abs_ModelCoordinateConvolution_le_of_bounded_measurable
    (i : Fin 3) (f : E3 → ℝ) (k : ℝ → ℝ) (s : ℝ) (x : E3)
    (hf : Measurable f) (B : ℝ) (hfB : ∀ y : E3, |f y| ≤ B)
    (hk : Integrable k) (hs : 0 < s) :
    |ModelCoordinateConvolution i f k s x| ≤ B * ∫ r : ℝ, |k r| := by
  let G : ℝ → ℝ := fun r ↦
    f (x - r • Anisotropy.coordinateDirection i) * kernelDilate k s r
  have hG := scratch_integrable_modelCoordinateConvolutionIntegrand_of_bounded_measurable
    i f k s x hf B hfB hk hs
  have hK : Integrable (fun r : ℝ ↦ |kernelDilate k s r|) :=
    integrable_abs_kernelDilate k hk hs
  have hupper : Integrable (fun r : ℝ ↦ B * |kernelDilate k s r|) :=
    hK.const_mul B
  unfold ModelCoordinateConvolution
  change |∫ r : ℝ, G r| ≤ _
  calc
    |∫ r : ℝ, G r| ≤ ∫ r : ℝ, |G r| :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ r : ℝ, B * |kernelDilate k s r| := by
      apply integral_mono hG.norm hupper
      intro r
      dsimp only [G]
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (hfB (x - r • Anisotropy.coordinateDirection i)) (abs_nonneg _)
    _ = B * ∫ r : ℝ, |k r| := by
      rw [integral_const_mul, integral_abs_kernelDilate k hs]

/-- Replace one of the three inputs of the fixed truncated model operator.
This is the bookkeeping map used to insert one selected good or bad fiber
without changing the two untouched input slots. -/
noncomputable def scratch_modelOperatorReplace
    (f : ModelOperatorRealInput) (m : Fin 3) (g : E3 → ℝ) :
    ModelOperatorRealInput :=
  fun j => if j = m then g else f j

@[simp] theorem scratch_modelOperatorReplace_same
    (f : ModelOperatorRealInput) (m : Fin 3) (g : E3 → ℝ) :
    scratch_modelOperatorReplace f m g m = g := by
  simp [scratch_modelOperatorReplace]

@[simp] theorem scratch_modelOperatorReplace_ne
    (f : ModelOperatorRealInput) (m j : Fin 3) (g : E3 → ℝ) (hjm : j ≠ m) :
    scratch_modelOperatorReplace f m g j = f j := by
  simp [scratch_modelOperatorReplace, hjm]

/-- At a fixed scale and point, the actual truncated-model integrand is
additive in an explicitly replaced input slot.  The hypotheses are exactly
the two line-integrability facts used by Bochner additivity in that slot. -/
theorem scratch_modelTruncatedOperatorIntegrand_replace_add
    (α : Anisotropy) (u : E3) (c : ℝ → ℝ) (f : ModelOperatorRealInput)
    (m : Fin 3) (g h : E3 → ℝ) (t : ℝ) (x : E3)
    (hg : Integrable (fun r : ℝ ↦
      g (x - r • Anisotropy.coordinateDirection m) *
        kernelDilate (activeModelKernel 2 m u) (t ^ α.weight m) r))
    (hh : Integrable (fun r : ℝ ↦
      h (x - r • Anisotropy.coordinateDirection m) *
        kernelDilate (activeModelKernel 2 m u) (t ^ α.weight m) r)) :
    modelTruncatedOperatorIntegrand α u c
        (scratch_modelOperatorReplace f m (g + h)) t x =
      modelTruncatedOperatorIntegrand α u c
          (scratch_modelOperatorReplace f m g) t x +
        modelTruncatedOperatorIntegrand α u c
          (scratch_modelOperatorReplace f m h) t x := by
  fin_cases m
  · have hadd := scratch_ModelCoordinateConvolution_add
      0 g h (ModelLowKernel (u 0)) (t ^ α.weight 0) x (by
        simpa [activeModelKernel] using hg) (by
        simpa [activeModelKernel] using hh)
    change c t *
        ModelCoordinateConvolution 0 (g + h) (ModelLowKernel (u 0))
          (t ^ α.weight 0) x *
        ModelCoordinateConvolution 1 (f 1) (ModelLowKernel (u 1))
          (t ^ α.weight 1) x *
        ModelCoordinateConvolution 2 (f 2) (ModelThirdKernel (u 2))
          (t ^ α.weight 2) x =
      c t * ModelCoordinateConvolution 0 g (ModelLowKernel (u 0))
          (t ^ α.weight 0) x *
        ModelCoordinateConvolution 1 (f 1) (ModelLowKernel (u 1))
          (t ^ α.weight 1) x *
        ModelCoordinateConvolution 2 (f 2) (ModelThirdKernel (u 2))
          (t ^ α.weight 2) x +
      c t * ModelCoordinateConvolution 0 h (ModelLowKernel (u 0))
          (t ^ α.weight 0) x *
        ModelCoordinateConvolution 1 (f 1) (ModelLowKernel (u 1))
          (t ^ α.weight 1) x *
        ModelCoordinateConvolution 2 (f 2) (ModelThirdKernel (u 2))
          (t ^ α.weight 2) x
    rw [hadd]
    ring

  · have hadd := scratch_ModelCoordinateConvolution_add
      1 g h (ModelLowKernel (u 1)) (t ^ α.weight 1) x (by
        simpa [activeModelKernel] using hg) (by
        simpa [activeModelKernel] using hh)
    change c t *
        ModelCoordinateConvolution 0 (f 0) (ModelLowKernel (u 0))
          (t ^ α.weight 0) x *
        ModelCoordinateConvolution 1 (g + h) (ModelLowKernel (u 1))
          (t ^ α.weight 1) x *
        ModelCoordinateConvolution 2 (f 2) (ModelThirdKernel (u 2))
          (t ^ α.weight 2) x =
      c t * ModelCoordinateConvolution 0 (f 0) (ModelLowKernel (u 0))
          (t ^ α.weight 0) x *
        ModelCoordinateConvolution 1 g (ModelLowKernel (u 1))
          (t ^ α.weight 1) x *
        ModelCoordinateConvolution 2 (f 2) (ModelThirdKernel (u 2))
          (t ^ α.weight 2) x +
      c t * ModelCoordinateConvolution 0 (f 0) (ModelLowKernel (u 0))
          (t ^ α.weight 0) x *
        ModelCoordinateConvolution 1 h (ModelLowKernel (u 1))
          (t ^ α.weight 1) x *
        ModelCoordinateConvolution 2 (f 2) (ModelThirdKernel (u 2))
          (t ^ α.weight 2) x
    rw [hadd]
    ring
  · have hadd := scratch_ModelCoordinateConvolution_add
      2 g h (ModelThirdKernel (u 2)) (t ^ α.weight 2) x (by
        simpa [activeModelKernel] using hg) (by
        simpa [activeModelKernel] using hh)
    change c t *
        ModelCoordinateConvolution 0 (f 0) (ModelLowKernel (u 0))
          (t ^ α.weight 0) x *
        ModelCoordinateConvolution 1 (f 1) (ModelLowKernel (u 1))
          (t ^ α.weight 1) x *
        ModelCoordinateConvolution 2 (g + h) (ModelThirdKernel (u 2))
          (t ^ α.weight 2) x =
      c t * ModelCoordinateConvolution 0 (f 0) (ModelLowKernel (u 0))
          (t ^ α.weight 0) x *
        ModelCoordinateConvolution 1 (f 1) (ModelLowKernel (u 1))
          (t ^ α.weight 1) x *
        ModelCoordinateConvolution 2 g (ModelThirdKernel (u 2))
          (t ^ α.weight 2) x +
      c t * ModelCoordinateConvolution 0 (f 0) (ModelLowKernel (u 0))
          (t ^ α.weight 0) x *
        ModelCoordinateConvolution 1 (f 1) (ModelLowKernel (u 1))
          (t ^ α.weight 1) x *
        ModelCoordinateConvolution 2 h (ModelThirdKernel (u 2))
          (t ^ α.weight 2) x
    rw [hadd]
    ring

/-- The fixed scale truncation is additive in a replaced input slot when the
two output scale integrands and the underlying two line integrands are
integrable.  This is the exact good--bad splitting identity for the actual
operator, with all totalized-integral side conditions exposed. -/
theorem scratch_ModelTruncatedOperator_replace_add
    (α : Anisotropy) (u : E3) (c : ℝ → ℝ) (f : ModelOperatorRealInput)
    (m : Fin 3) (g h : E3 → ℝ) (a b : ℝ) (x : E3)
    (hlineg : ∀ t : ℝ, Integrable (fun r : ℝ ↦
      g (x - r • Anisotropy.coordinateDirection m) *
        kernelDilate (activeModelKernel 2 m u) (t ^ α.weight m) r))
    (hlineh : ∀ t : ℝ, Integrable (fun r : ℝ ↦
      h (x - r • Anisotropy.coordinateDirection m) *
        kernelDilate (activeModelKernel 2 m u) (t ^ α.weight m) r))
    (hg : IntegrableOn (fun t : ℝ ↦
      modelTruncatedOperatorIntegrand α u c
        (scratch_modelOperatorReplace f m g) t x) (Set.Ioc a b)
      ((volume : Measure ℝ).withDensity cubeScaleDensity))
    (hh : IntegrableOn (fun t : ℝ ↦
      modelTruncatedOperatorIntegrand α u c
        (scratch_modelOperatorReplace f m h) t x) (Set.Ioc a b)
      ((volume : Measure ℝ).withDensity cubeScaleDensity)) :
    ModelTruncatedOperator α u c
        (scratch_modelOperatorReplace f m (g + h)) a b x =
      ModelTruncatedOperator α u c (scratch_modelOperatorReplace f m g) a b x +
        ModelTruncatedOperator α u c (scratch_modelOperatorReplace f m h) a b x := by
  let ν : Measure ℝ := (volume : Measure ℝ).withDensity cubeScaleDensity
  let I : Set ℝ := Set.Ioc a b
  have hpoint (t : ℝ) :
      modelTruncatedOperatorIntegrand α u c
          (scratch_modelOperatorReplace f m (g + h)) t x =
        modelTruncatedOperatorIntegrand α u c
            (scratch_modelOperatorReplace f m g) t x +
          modelTruncatedOperatorIntegrand α u c
            (scratch_modelOperatorReplace f m h) t x :=
    scratch_modelTruncatedOperatorIntegrand_replace_add α u c f m g h t x
      (hlineg t) (hlineh t)
  unfold ModelTruncatedOperator
  change (∫ t in I,
      modelTruncatedOperatorIntegrand α u c
        (scratch_modelOperatorReplace f m (g + h)) t x ∂ν) = _
  rw [show (fun t : ℝ => modelTruncatedOperatorIntegrand α u c
      (scratch_modelOperatorReplace f m (g + h)) t x) =
      fun t => modelTruncatedOperatorIntegrand α u c
        (scratch_modelOperatorReplace f m g) t x +
          modelTruncatedOperatorIntegrand α u c
            (scratch_modelOperatorReplace f m h) t x by
      funext t
      exact hpoint t]
  rw [integral_add (by simpa only [IntegrableOn, ν, I] using hg)
    (by simpa only [IntegrableOn, ν, I] using hh)]

end
end Twisted
end Auto
