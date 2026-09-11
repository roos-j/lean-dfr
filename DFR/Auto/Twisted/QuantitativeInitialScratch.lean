import Auto.Twisted.QuantitativeDyadicScratch

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Auto
namespace Twisted

/-- The explicit three-coordinate strong factor is finite above the
strong-type endpoint. -/
theorem scratchDyadicStrongFactor_ne_top
    (K p : ℝ) (hp : 1 < p) :
    scratchDyadicStrongFactor K p ≠ ∞ := by
  unfold scratchDyadicStrongFactor
  apply ENNReal.mul_ne_top
  · apply ne_of_lt
    exact ENNReal.rpow_lt_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
  · apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
      · apply ne_of_lt
        exact ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (by linarith))
    · apply ne_of_lt
      exact ENNReal.rpow_lt_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top

/-- Convert the raw `lintegral` strong estimate to the ordinary nonnegative
real integral used by the stopping distribution. -/
theorem scratch_scaledIteratedCoordinateDyadicBallMaximal_integral_bound
    (K : ℝ) (hK : 0 ≤ K) (f : E3 → ℂ) (hf : Measurable f)
    (A : ℝ) (hA : 0 ≤ A) (hbound : ∀ x, ‖f x‖ ≤ A)
    {p : ℝ} (hp : 1 < p) (hfp : MemLp f (ENNReal.ofReal p) volume) :
    ∫ x : E3, ‖scaledIteratedCoordinateDyadicBallMaximal K f x‖ ^ p ≤
      (scratchDyadicStrongFactor K p ^ 3).toReal *
        ∫ x : E3, ‖f x‖ ^ p := by
  let G := scaledIteratedCoordinateDyadicBallMaximal K f
  have hp0 : 0 < p := by linarith
  have hGmem : MemLp G (ENNReal.ofReal p) volume := by
    dsimp only [G]
    exact scaledIteratedCoordinateDyadicBallMaximal_memLp
      K hK f hf A hA hbound hp hfp
  have hGin : Integrable (fun x : E3 ↦ ‖G x‖ ^ p) := by
    have h := hGmem.integrable_norm_rpow
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hp0.le] using h
  have hfin : Integrable (fun x : E3 ↦ ‖f x‖ ^ p) := by
    have h := hfp.integrable_norm_rpow
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hp0.le] using h
  have hG_eq :
      (∫⁻ x, (ENNReal.ofReal ‖G x‖) ^ p) =
        ENNReal.ofReal (∫ x : E3, ‖G x‖ ^ p) := by
    calc
      (∫⁻ x, (ENNReal.ofReal ‖G x‖) ^ p) =
          ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ p) := by
            apply lintegral_congr
            intro x
            exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le
      _ = ENNReal.ofReal (∫ x : E3, ‖G x‖ ^ p) := by
            exact (ofReal_integral_eq_lintegral_ofReal hGin
              (Filter.Eventually.of_forall fun x ↦
                Real.rpow_nonneg (norm_nonneg _) _)).symm
  have hfin_eq :
      (∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p) =
        ENNReal.ofReal (∫ x : E3, ‖f x‖ ^ p) := by
    calc
      (∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p) =
          ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p) := by
            apply lintegral_congr
            intro x
            exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le
      _ = ENNReal.ofReal (∫ x : E3, ‖f x‖ ^ p) := by
            exact (ofReal_integral_eq_lintegral_ofReal hfin
              (Filter.Eventually.of_forall fun x ↦
                Real.rpow_nonneg (norm_nonneg _) _)).symm
  have hraw := scratch_scaledIteratedCoordinateDyadicBallMaximal_lintegral_bound
    K hK f hf A hA hbound hp
  have hfactor : (scratchDyadicStrongFactor K p ^ 3 : ℝ≥0∞) ≠ ∞ := by
    exact ENNReal.pow_ne_top (scratchDyadicStrongFactor_ne_top K p hp)
  have hrighttop :
      (scratchDyadicStrongFactor K p ^ 3 : ℝ≥0∞) *
        ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ≠ ∞ := by
    apply ENNReal.mul_ne_top hfactor
    rw [hfin_eq]
    exact ENNReal.ofReal_ne_top
  have hlefttop : (∫⁻ x, (ENNReal.ofReal ‖G x‖) ^ p) ≠ ∞ :=
    ne_top_of_le_ne_top hrighttop hraw
  have htoReal :=
    (ENNReal.toReal_le_toReal hlefttop hrighttop).mpr hraw
  change ∫ x : E3, ‖G x‖ ^ p ≤ _
  rw [hG_eq, hfin_eq] at htoReal
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (integral_nonneg fun x ↦
      Real.rpow_nonneg (norm_nonneg (G x)) _),
    ENNReal.toReal_ofReal (integral_nonneg fun x ↦
      Real.rpow_nonneg (norm_nonneg (f x)) _)] at htoReal
  exact htoReal

end Twisted
end Auto
