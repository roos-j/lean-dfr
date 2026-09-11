import Auto.Twisted.Twisted

namespace Auto
namespace Twisted

open MeasureTheory Filter
open scoped BigOperators ENNReal

noncomputable section

/-- The strict real initial range can be stated with the source's larger
translation weight exponent. -/
theorem scratch_initialModelFullForm_bound_weight100
    (α : Anisotropy) (u : E3) (c : ℝ → ℝ) (F : InitialModelSchwartzInput)
    (q : Fin 4 → ℝ)
    (hq : ∀ j : Fin 4, 0 < q j)
    (hsum : ∑ j : Fin 4, (q j)⁻¹ = 1)
    (hqs : ∀ j : Fin 4, sourceStoppingExponent j < q j)
    (hcmeas : Measurable c) (hc : ∀ t : ℝ, |c t| ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      |ModelFullForm α u c F| ≤ C * sourceWeight u ^ 100 *
        ∏ j : Fin 4, lpNorm (F j : E3 → ℝ) (ENNReal.ofReal (q j)) volume := by
  obtain ⟨C, hC, hbound⟩ :=
    initialModelFullForm_bound α u c F q hq hsum hqs hcmeas hc
  refine ⟨C, hC, hbound.trans ?_⟩
  have hweight : 1 ≤ sourceWeight u := by
    unfold sourceWeight
    linarith [abs_nonneg (u 0), abs_nonneg (u 1), abs_nonneg (u 2)]
  have hpow : sourceWeight u ^ 75 ≤ sourceWeight u ^ 100 :=
    pow_le_pow_right₀ hweight (by norm_num)
  have hprod : 0 ≤ ∏ j : Fin 4,
      lpNorm (F j : E3 → ℝ) (ENNReal.ofReal (q j)) volume := by
    exact Finset.prod_nonneg fun j _ ↦ lpNorm_nonneg
  calc
    C * sourceWeight u ^ 75 *
        ∏ j : Fin 4, lpNorm (F j : E3 → ℝ) (ENNReal.ofReal (q j)) volume =
        (C * ∏ j : Fin 4,
          lpNorm (F j : E3 → ℝ) (ENNReal.ofReal (q j)) volume) *
          sourceWeight u ^ 75 := by ring
    _ ≤ (C * ∏ j : Fin 4,
          lpNorm (F j : E3 → ℝ) (ENNReal.ofReal (q j)) volume) *
          sourceWeight u ^ 100 :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hC hprod)
    _ = C * sourceWeight u ^ 100 *
        ∏ j : Fin 4, lpNorm (F j : E3 → ℝ) (ENNReal.ofReal (q j)) volume := by
      ring

end
end Twisted
end Auto
