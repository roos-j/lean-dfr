import Auto.Twisted.Twisted

namespace Auto.Twisted

open MeasureTheory Filter
open scoped BigOperators ENNReal

noncomputable section

/-- The literal active model is complex-linear in its scale coefficient. -/
theorem scratch_LiteralActiveModelFullForm_smul_coefficient
    (α : Anisotropy) (i : Fin 3) (u : E3) (r : ℂ) (c : ℝ → ℂ)
    (F : ModelComplexSchwartzInput) :
    LiteralActiveModelFullForm α i u (r • c) F =
      r * LiteralActiveModelFullForm α i u c F := by
  unfold LiteralActiveModelFullForm
    LiteralComplexActiveInternal.scratch_LiteralActiveModelFullForm
  rw [← MeasureTheory.integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change (r • c) t * _ = r * (c t * _)
  simp [smul_eq_mul]
  ring

/-- A scalar can equivalently be placed outside the coefficient function of
the literal active model. -/
theorem scratch_LiteralActiveModelFullForm_mul_coefficient
    (α : Anisotropy) (i : Fin 3) (u : E3) (r : ℂ) (c : ℝ → ℂ)
    (F : ModelComplexSchwartzInput) :
    LiteralActiveModelFullForm α i u (fun t ↦ r * c t) F =
      r * LiteralActiveModelFullForm α i u c F := by
  have hcoefficient : (fun t ↦ r * c t) = r • c := by
    funext t
    simp [smul_eq_mul]
  rw [hcoefficient]
  exact scratch_LiteralActiveModelFullForm_smul_coefficient α i u r c F

/-- The literal active form vanishes for the zero scale coefficient. -/
theorem scratch_LiteralActiveModelFullForm_zero_coefficient
    (α : Anisotropy) (i : Fin 3) (u : E3)
    (F : ModelComplexSchwartzInput) :
    LiteralActiveModelFullForm α i u (0 : ℝ → ℂ) F = 0 := by
  unfold LiteralActiveModelFullForm
    LiteralComplexActiveInternal.scratch_LiteralActiveModelFullForm
  simp

/-- A pointwise `B`-bounded complex coefficient can be divided by its positive
bound to obtain a measurable unit coefficient. -/
theorem scratch_normalized_coefficient_measurable_unit
    (B : ℝ) (hB : 0 < B) (c : ℝ → ℂ) (hc : Measurable c)
    (hcb : ∀ t : ℝ, ‖c t‖ ≤ B) :
    Measurable (fun t ↦ ((B : ℂ)⁻¹) * c t) ∧
      ∀ t : ℝ, ‖((B : ℂ)⁻¹) * c t‖ ≤ 1 := by
  constructor
  · exact measurable_const.mul hc
  · intro t
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hB]
    rw [inv_mul_le_iff₀ hB]
    simpa using hcb t

/-- Any estimate for measurable unit coefficients scales linearly to a
measurable coefficient uniformly bounded by a nonnegative real number. -/
theorem scratch_LiteralActiveModelFullForm_norm_le_of_coefficient_bound
    (α : Anisotropy) (i : Fin 3) (u : E3) (c : ℝ → ℂ)
    (F : ModelComplexSchwartzInput) (B K : ℝ)
    (hB : 0 ≤ B) (hc : Measurable c) (hcb : ∀ t : ℝ, ‖c t‖ ≤ B)
    (hunit : ∀ d : ℝ → ℂ, Measurable d → (∀ t : ℝ, ‖d t‖ ≤ 1) →
      ‖LiteralActiveModelFullForm α i u d F‖ ≤ K) :
    ‖LiteralActiveModelFullForm α i u c F‖ ≤ B * K := by
  by_cases hBzero : B = 0
  · have hczero : c = 0 := by
      funext t
      apply norm_eq_zero.mp
      simpa [hBzero] using hcb t
    rw [hczero, scratch_LiteralActiveModelFullForm_zero_coefficient]
    simp [hBzero]
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hBzero)
    let d : ℝ → ℂ := fun t ↦ ((B : ℂ)⁻¹) * c t
    have hd := scratch_normalized_coefficient_measurable_unit B hBpos c hc hcb
    have hdmeas : Measurable d := by simpa only [d] using hd.1
    have hdunit : ∀ t : ℝ, ‖d t‖ ≤ 1 := by simpa only [d] using hd.2
    have hscale : c = fun t ↦ (B : ℂ) * d t := by
      funext t
      dsimp only [d]
      rw [← mul_assoc, mul_inv_cancel₀]
      · simp
      · exact_mod_cast hBzero
    rw [hscale, scratch_LiteralActiveModelFullForm_mul_coefficient]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hBpos]
    exact mul_le_mul_of_nonneg_left (hunit d hdmeas hdunit) hB

/-- The strict active-model estimate accepts a Fourier coefficient with an
arbitrary explicit scalar envelope.  The coefficient is normalized before
using the unit-coefficient model estimate, so no untracked mode factor is
absorbed into its constant. -/
theorem scratch_exists_uniform_thirdModeFrequencyFullForm_bound_of_coefficient_bound
    (α : Anisotropy) (q : Fin 4 → ℝ)
    (hq : ∀ j : Fin 4, 0 < q j)
    (hsum : ∑ j : Fin 4, (q j)⁻¹ = 1)
    (hqs : ∀ j : Fin 4, activeSourceStoppingExponent 2 j < q j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν : standardModeLattice) (B : ℝ)
      (a : ℝ → ℂ) (F : ModelComplexSchwartzInput),
      0 ≤ B → Measurable a → (∀ t : ℝ, ‖a t‖ ≤ B) →
      ‖thirdModeFrequencyFullForm α ν a F‖ ≤
        B * (32 * C * sourceWeight (standardModeTranslate ν) ^ 100 *
          ∏ j : Fin 4, lpNorm (F j : E3 → ℂ)
            (ENNReal.ofReal (q j)) volume) := by
  rcases exists_uniform_LiteralActiveModelFullForm_bound_weight100
    α 2 q hq hsum hqs with ⟨C, hC, hmodel⟩
  refine ⟨C, hC, ?_⟩
  intro ν B a F hB hameas habound
  rw [thirdModeFrequencyFullForm_eq_LiteralActiveModelFullForm]
  apply scratch_LiteralActiveModelFullForm_norm_le_of_coefficient_bound
    α 2 (standardModeTranslate ν) (-a) F B
  · exact hB
  · exact hameas.neg
  · intro t
    simpa only [Pi.neg_apply, norm_neg] using habound t
  · intro d hdmeas hdunit
    exact hmodel (standardModeTranslate ν) d F hdmeas hdunit

/-- Degree-110 Fourier coefficient decay is summable after the degree-100
strict active-model growth, already at the literal complex frequency-mode
level.  This is the one-cone version of the final mode summation. -/
theorem scratch_summable_thirdModeFrequencyFullForm_of_decay
    (α : Anisotropy) (q : Fin 4 → ℝ)
    (hq : ∀ j : Fin 4, 0 < q j)
    (hsum : ∑ j : Fin 4, (q j)⁻¹ = 1)
    (hqs : ∀ j : Fin 4, activeSourceStoppingExponent 2 j < q j)
    (A : ℝ) (hA : 0 ≤ A)
    (a : standardModeLattice → ℝ → ℂ)
    (hameas : ∀ ν, Measurable (a ν))
    (hadecay : ∀ ν t, ‖a ν t‖ ≤
      A * (sourceWeight (ν : E3))⁻¹ ^ (110 : ℕ))
    (F : ModelComplexSchwartzInput) :
    Summable (fun ν : standardModeLattice ↦
      thirdModeFrequencyFullForm α ν (a ν) F) := by
  rcases scratch_exists_uniform_thirdModeFrequencyFullForm_bound_of_coefficient_bound
    α q hq hsum hqs with ⟨C, hC, hmode⟩
  let N : ℝ := ∏ j : Fin 4,
    lpNorm (F j : E3 → ℂ) (ENNReal.ofReal (q j)) volume
  let D : ℝ := 32 * C * N
  have hN : 0 ≤ N := Finset.prod_nonneg fun j _ ↦ lpNorm_nonneg
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  apply Summable.of_norm_bounded
    ((summable_standardMode_sourceWeight_inv).mul_left (A * D))
  intro ν
  let W : ℝ := sourceWeight (ν : E3)
  let B : ℝ := A * W⁻¹ ^ (110 : ℕ)
  have hWpos : 0 < W := by
    dsimp [W]
    exact sourceWeight_pos _
  have hWne : W ≠ 0 := hWpos.ne'
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hBpoint : ∀ t : ℝ, ‖a ν t‖ ≤ B := by
    intro t
    simpa only [B, W] using hadecay ν t
  have hraw := hmode ν B (a ν) F hB (hameas ν) hBpoint
  have htranslate : sourceWeight (standardModeTranslate ν) ^ (100 : ℕ) ≤
      W ^ (100 : ℕ) := by
    simpa only [W] using sourceWeight_standardModeTranslate_pow_le ν
  have hscale : B * (D * sourceWeight (standardModeTranslate ν) ^ (100 : ℕ)) ≤
      B * (D * W ^ (100 : ℕ)) := by
    apply mul_le_mul_of_nonneg_left
    · exact mul_le_mul_of_nonneg_left htranslate hD
    · exact hB
  have hident : B * (D * W ^ (100 : ℕ)) =
      (A * D) * W⁻¹ ^ (10 : ℕ) := by
    dsimp [B]
    field_simp [hWne]
  calc
    ‖thirdModeFrequencyFullForm α ν (a ν) F‖ ≤
        B * (32 * C * sourceWeight (standardModeTranslate ν) ^ 100 * N) := by
      simpa only [N] using hraw
    _ = B * (D * sourceWeight (standardModeTranslate ν) ^ (100 : ℕ)) := by
      dsimp [D]
      ring
    _ ≤ B * (D * W ^ (100 : ℕ)) := hscale
    _ = (A * D) * W⁻¹ ^ (10 : ℕ) := hident
    _ = (A * D) * (sourceWeight (ν : E3))⁻¹ ^ (10 : ℕ) := by rfl

end

end Auto.Twisted
