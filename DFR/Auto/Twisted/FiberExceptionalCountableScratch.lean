/- Copyright (c) 2026. All rights reserved.
   SPDX-License-Identifier: Apache-2.0 -/

import Auto.Twisted.Twisted

namespace Auto
namespace Twisted

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

noncomputable section

/-! ## Countable exceptional-set exhaustion

The maximal dyadic selection is globally pairwise disjoint.  Combining its
finite real-measure bound with `measure_iUnion` and the nonnegative real
series criterion upgrades the finite stopping estimate to the literal
countable exceptional set used by the one-fiber argument.
-/

theorem scratch_measureReal_fiberDyadicExceptionalSet_le_inv_mul_integral
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]
    (Zf : Set Z) (hZf : MeasurableSet Zf)
    (F : ℝ × Z → ℝ) (hF : Integrable F (volume.prod μ))
    (hF_nonneg : ∀ yz : ℝ × Z, 0 ≤ F yz)
    (hF_meas : Measurable F)
    (H : ℝ) (hH : 0 < H)
    (hfiber : ∀ z ∈ Zf, Integrable (fun y : ℝ => F (y, z)) volume) :
    (volume.prod μ).real
      (fiberDyadicExceptionalSet Zf (fiberDyadicIntervalAverage F) H) ≤
      H⁻¹ * ∫ yz, F yz ∂(volume.prod μ) := by
  classical
  let R : FiberDyadicInterval → Set (ℝ × Z) := fun I =>
    fiberDyadicInterval I ×ˢ
      fiberDyadicSelectionSet Zf (fiberDyadicIntervalAverage F) H I
  have hRmeas (I : FiberDyadicInterval) : MeasurableSet (R I) := by
    dsimp [R]
    exact (measurableSet_fiberDyadicInterval I).prod
      (measurableSet_fiberDyadicSelectionSet Zf hZf
        (fiberDyadicIntervalAverage F)
        (fun J => measurable_fiberDyadicIntervalAverage F hF_meas J) H I)
  have hRpair : Pairwise (Function.onFun Disjoint R) := by
    intro I J hIJ
    exact pairwiseDisjoint_fiberDyadicSelectedRectangles Zf
      (fiberDyadicIntervalAverage F) H (Set.mem_univ I) (Set.mem_univ J) hIJ
  have hRneTop (I : FiberDyadicInterval) :
      (volume.prod μ) (R I) ≠ ∞ := by
    dsimp [R]
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top
      (by rw [measure_fiberDyadicInterval]; exact ENNReal.ofReal_ne_top)
      (measure_ne_top μ _)
  have hrect (I : FiberDyadicInterval) :
      (volume.prod μ).real (R I) =
        fiberDyadicIntervalLength I *
          μ.real (fiberDyadicSelectionSet Zf
            (fiberDyadicIntervalAverage F) H I) := by
    change ((volume.prod μ) (R I)).toReal = _
    dsimp [R]
    rw [Measure.prod_prod, measure_fiberDyadicInterval, ENNReal.toReal_mul]
    simp only [ENNReal.toReal_ofReal (fiberDyadicIntervalLength_pos I).le]
    rfl
  have hfinite (T : Finset FiberDyadicInterval) :
      (∑ I ∈ T, (volume.prod μ).real (R I)) ≤
        H⁻¹ * ∫ yz, F yz ∂(volume.prod μ) := by
    calc
      (∑ I ∈ T, (volume.prod μ).real (R I)) =
          ∑ I ∈ T, fiberDyadicIntervalLength I *
            μ.real (fiberDyadicSelectionSet Zf
              (fiberDyadicIntervalAverage F) H I) := by
            apply Finset.sum_congr rfl
            intro I hI
            exact hrect I
      _ = ∫ z, fiberDyadicSelectedLengthDensity T Zf
          (fiberDyadicIntervalAverage F) H z ∂μ :=
        (integral_fiberDyadicSelectedLengthDensity_eq_sum μ T Zf hZf
          (fiberDyadicIntervalAverage F)
          (fun I => measurable_fiberDyadicIntervalAverage F hF_meas I) H).symm
      _ = (volume.prod μ).real
          (fiberDyadicExceptionalSetFinset T Zf
            (fiberDyadicIntervalAverage F) H) :=
        (measureReal_fiberDyadicExceptionalSetFinset_eq_integral μ T Zf hZf
          (fiberDyadicIntervalAverage F)
          (fun I => measurable_fiberDyadicIntervalAverage F hF_meas I) H).symm
      _ ≤ H⁻¹ * ∫ yz, F yz ∂(volume.prod μ) :=
        measureReal_fiberDyadicExceptionalSetFinset_le_inv_mul_integral μ Zf hZf
          F hF hF_nonneg hF_meas H hH T hfiber
  unfold fiberDyadicExceptionalSet
  change ((volume.prod μ) (⋃ I, R I)).toReal ≤ _
  rw [measure_iUnion hRpair hRmeas, ENNReal.tsum_toReal_eq hRneTop]
  apply Real.tsum_le_of_sum_le
  · intro I
    exact ENNReal.toReal_nonneg
  · intro T
    exact hfinite T

end

end Twisted
end Auto
