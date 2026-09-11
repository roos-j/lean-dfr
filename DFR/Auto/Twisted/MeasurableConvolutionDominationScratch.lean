/- Copyright (c) 2026. All rights reserved.
   SPDX-License-Identifier: Apache-2.0 -/

import Auto.Twisted.Twisted

namespace Auto
namespace Twisted

open MeasureTheory Filter
open scoped BigOperators ENNReal

noncomputable section

/-! ## Linewise bracket domination without continuity

The selected Calderón--Zygmund pieces are measurable rather than continuous.
For the actual model convolution, continuity is unnecessary once the two
literal line integrals occurring in the comparison are known to be
integrable.  Keeping those hypotheses explicit is also the right interface
for a later Fubini construction of the selected fibers. -/

/-- A pointwise bracket majorant controls a literal coordinate convolution
under exactly the two line-integrability facts used by the integral
comparison. -/
theorem scratch_abs_ModelCoordinateConvolution_le_displacementBracket_of_integrable
    (i : Fin 3) (f : E3 → ℝ) (k : ℝ → ℝ) (s : ℝ) (x : E3)
    (hG : Integrable (fun r : ℝ ↦
      f (x - r • Anisotropy.coordinateDirection i) * kernelDilate k s r))
    (C : ℝ)
    (hH : Integrable (fun r : ℝ ↦ C *
      (|f (x - r • Anisotropy.coordinateDirection i)| *
        bracketKernelAt s 0 r)))
    (hmajor : ∀ r : ℝ,
      |kernelDilate k s r| ≤ C * bracketKernelAt s 0 r) :
    |ModelCoordinateConvolution i f k s x| ≤ C *
      ∫ r : ℝ, |f (x - r • Anisotropy.coordinateDirection i)| *
        bracketKernelAt s 0 r := by
  let h : ℝ → E3 := fun r ↦ x - r • Anisotropy.coordinateDirection i
  let G : ℝ → ℝ := fun r ↦ f (h r) * kernelDilate k s r
  let H : ℝ → ℝ := fun r ↦
    C * (|f (h r)| * bracketKernelAt s 0 r)
  unfold ModelCoordinateConvolution
  change |∫ r : ℝ, G r| ≤ C * ∫ r : ℝ,
    |f (h r)| * bracketKernelAt s 0 r
  calc
    |∫ r : ℝ, G r| ≤ ∫ r : ℝ, |G r| :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ r : ℝ, H r := by
      apply integral_mono (by simpa [G, h, Real.norm_eq_abs] using hG.norm)
        (by simpa only [H, h] using hH)
      intro r
      dsimp only [G, H]
      rw [abs_mul]
      calc
        |f (h r)| * |kernelDilate k s r| ≤
            |f (h r)| * (C * bracketKernelAt s 0 r) :=
          mul_le_mul_of_nonneg_left (hmajor r) (abs_nonneg _)
        _ = C * (|f (h r)| * bracketKernelAt s 0 r) := by ring
    _ = C * ∫ r : ℝ, |f (h r)| * bracketKernelAt s 0 r := by
      rw [integral_const_mul]

/-- The preceding measurable-input linewise comparison in the source's
sampled-coordinate bracket convention. -/
theorem scratch_abs_ModelCoordinateConvolution_le_coordinateBracketConvolution_of_integrable
    (i : Fin 3) (f : E3 → ℝ) (k : ℝ → ℝ) (s : ℝ) (x : E3)
    (hG : Integrable (fun r : ℝ ↦
      f (x - r • Anisotropy.coordinateDirection i) * kernelDilate k s r))
    (C : ℝ)
    (hH : Integrable (fun r : ℝ ↦ C *
      (|f (x - r • Anisotropy.coordinateDirection i)| *
        bracketKernelAt s 0 r)))
    (hmajor : ∀ r : ℝ,
      |kernelDilate k s r| ≤ C * bracketKernelAt s 0 r) :
    |ModelCoordinateConvolution i f k s x| ≤ C *
      coordinateBracketConvolution i (fun y ↦ (f y : ℂ)) s x := by
  calc
    |ModelCoordinateConvolution i f k s x| ≤ C *
        ∫ r : ℝ, |f (x - r • Anisotropy.coordinateDirection i)| *
          bracketKernelAt s 0 r :=
      scratch_abs_ModelCoordinateConvolution_le_displacementBracket_of_integrable
        i f k s x hG C hH hmajor
    _ = C * coordinateBracketConvolution i (fun y ↦ (f y : ℂ)) s x := by
      rw [← displacementBracket_eq_coordinateBracketConvolution
        i (fun y ↦ (f y : ℂ)) s x]
      simp only [Complex.norm_real, Real.norm_eq_abs]

/-- Every active literal convolution has the measurable-input bracket bound
once its line convolution and weighted bracket line integrals are integrable. -/
theorem scratch_abs_activeModelCoordinateConvolution_le_coordinateBracketConvolution_of_integrable :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i j : Fin 3) (u : E3) (s : ℝ) (x : E3)
      (f : E3 → ℝ), 0 < s →
      Integrable (fun r : ℝ ↦
        f (x - r • Anisotropy.coordinateDirection j) *
          kernelDilate (activeModelKernel i j u) s r) →
      Integrable (fun r : ℝ ↦ C * sourceWeight u ^ 10 *
        (|f (x - r • Anisotropy.coordinateDirection j)| *
          bracketKernelAt s 0 r)) →
      |ModelCoordinateConvolution j f (activeModelKernel i j u) s x| ≤
        C * sourceWeight u ^ 10 *
          coordinateBracketConvolution j (fun y ↦ (f y : ℂ)) s x := by
  rcases kernelDilate_activeModelKernel_sourceWeight_bracket_majorant with
    ⟨C, hC, hmajor⟩
  refine ⟨C, hC, ?_⟩
  intro i j u s x f hs hG hH
  have hpoint : ∀ r : ℝ,
      |kernelDilate (activeModelKernel i j u) s r| ≤
        (C * sourceWeight u ^ 10) * bracketKernelAt s 0 r := by
    intro r
    calc
      |kernelDilate (activeModelKernel i j u) s r| ≤
          C * sourceWeight u ^ 10 * bracketKernelAt s 0 r :=
        hmajor i j u s r hs
      _ = (C * sourceWeight u ^ 10) * bracketKernelAt s 0 r := by ring
  exact scratch_abs_ModelCoordinateConvolution_le_coordinateBracketConvolution_of_integrable
    j f (activeModelKernel i j u) s x hG (C * sourceWeight u ^ 10)
    (by simpa only [mul_assoc] using hH) hpoint

end
end Twisted
end Auto
