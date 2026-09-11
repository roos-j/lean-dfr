/- Copyright (c) 2026. All rights reserved.
   SPDX-License-Identifier: Apache-2.0 -/

import Auto.Twisted.Twisted

namespace Auto
namespace Twisted

open MeasureTheory Filter Set
open scoped BigOperators

noncomputable section

/-! ## Finite selected-fiber mass

This is the finite, fixed-fiber measure calculation in the Calderón--
Zygmund selection argument.  It deliberately precedes the countable
measurable selection/exhaustion layer: every selected interval has average
strictly above `H`, so disjointness alone controls the total selected length.
-/

/-- A finite pairwise-disjoint family of selected source fiber intervals has
total length at most its ambient nonnegative mass divided by the stopping
height. -/
theorem scratch_fiberDyadic_selected_length_sum_le_integral
    (F : ℝ → ℝ) (H : ℝ) (S : Finset FiberDyadicInterval)
    (_hH : 0 < H) (hF : Integrable F volume)
    (hF_nonneg : ∀ x : ℝ, 0 ≤ F x)
    (hdisj : (↑S : Set FiberDyadicInterval).PairwiseDisjoint
      fiberDyadicInterval)
    (hselected : ∀ I ∈ S,
      H < (fiberDyadicIntervalLength I)⁻¹ *
        ∫ x : ℝ in fiberDyadicInterval I, F x) :
    H * (∑ I ∈ S, fiberDyadicIntervalLength I) ≤ ∫ x : ℝ, F x := by
  have hpoint (I : FiberDyadicInterval) (hI : I ∈ S) :
      H * fiberDyadicIntervalLength I ≤
        ∫ x : ℝ in fiberDyadicInterval I, F x := by
    have hlen : 0 < fiberDyadicIntervalLength I :=
      fiberDyadicIntervalLength_pos I
    have hstrict := mul_lt_mul_of_pos_right (hselected I hI) hlen
    have hcancel :
        ((fiberDyadicIntervalLength I)⁻¹ *
          ∫ x : ℝ in fiberDyadicInterval I, F x) *
            fiberDyadicIntervalLength I =
          ∫ x : ℝ in fiberDyadicInterval I, F x := by
      field_simp
    rw [hcancel] at hstrict
    exact hstrict.le
  have hsum :
      H * (∑ I ∈ S, fiberDyadicIntervalLength I) ≤
        ∑ I ∈ S, ∫ x : ℝ in fiberDyadicInterval I, F x := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun I hI => hpoint I hI
  have hunion :
      (∑ I ∈ S, ∫ x : ℝ in fiberDyadicInterval I, F x) =
        ∫ x : ℝ in ⋃ I ∈ S, fiberDyadicInterval I, F x := by
    symm
    exact integral_biUnion_finset S
      (fun I _ => measurableSet_fiberDyadicInterval I) hdisj
      (fun _ _ => hF.integrableOn)
  have hglobal :
      (∫ x : ℝ in ⋃ I ∈ S, fiberDyadicInterval I, F x) ≤
        ∫ x : ℝ, F x :=
    setIntegral_le_integral hF
      (Filter.Eventually.of_forall hF_nonneg)
  calc
    H * (∑ I ∈ S, fiberDyadicIntervalLength I) ≤
        ∑ I ∈ S, ∫ x : ℝ in fiberDyadicInterval I, F x := hsum
    _ = ∫ x : ℝ in ⋃ I ∈ S, fiberDyadicInterval I, F x := hunion
    _ ≤ ∫ x : ℝ, F x := hglobal

/-- Division by the positive stopping height gives the form used to bound
the exceptional-set measure after a finite fiber selection. -/
theorem scratch_fiberDyadic_selected_length_sum_le_inv_mul_integral
    (F : ℝ → ℝ) (H : ℝ) (S : Finset FiberDyadicInterval)
    (hH : 0 < H) (hF : Integrable F volume)
    (hF_nonneg : ∀ x : ℝ, 0 ≤ F x)
    (hdisj : (↑S : Set FiberDyadicInterval).PairwiseDisjoint
      fiberDyadicInterval)
    (hselected : ∀ I ∈ S,
      H < (fiberDyadicIntervalLength I)⁻¹ *
        ∫ x : ℝ in fiberDyadicInterval I, F x) :
    (∑ I ∈ S, fiberDyadicIntervalLength I) ≤
      H⁻¹ * ∫ x : ℝ, F x := by
  have hmain := scratch_fiberDyadic_selected_length_sum_le_integral
    F H S hH hF hF_nonneg hdisj hselected
  have hHne : H ≠ 0 := hH.ne'
  calc
    (∑ I ∈ S, fiberDyadicIntervalLength I) =
        H⁻¹ * (H * (∑ I ∈ S, fiberDyadicIntervalLength I)) := by
          field_simp
    _ ≤ H⁻¹ * ∫ x : ℝ, F x :=
      mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr hH.le)

end
end Twisted
end Auto
