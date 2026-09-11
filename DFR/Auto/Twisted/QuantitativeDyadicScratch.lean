import Auto.Twisted.Twisted

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace Auto
namespace Twisted

/-- The strong fiber maximal estimate transports to each literal coordinate
of `E3`, retaining its explicit `L^p` constant. -/
theorem scratch_coordinateDyadicBallMaximal_lintegral_bound
    (i : Fin 3) (f : E3 → ℂ) (hf : Measurable f)
    (A : ℝ) (hA : 0 ≤ A) (hbound : ∀ x, ‖f x‖ ≤ A)
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, ENNReal.ofReal (coordinateDyadicBallMaximal i f x ^ p)) ≤
      ENNReal.ofReal p *
        (2 * ENNReal.ofReal 4 * (ENNReal.ofReal (p - 1))⁻¹ *
          (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
          ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p) := by
  let e := e3ToFiberDyadicCoordinates i
  let G : FiberDyadicBase × FiberDyadicLine → ℂ := f ∘ e.symm
  have he : MeasurePreserving e volume fiberDyadicMeasure := by
    simpa only [e] using e3ToFiberDyadicCoordinates_measurePreserving i
  have hG : Measurable G := hf.comp e.symm.measurable
  have hGbound : ∀ z, ‖G z‖ ≤ A := by
    intro z
    exact hbound (e.symm z)
  have hfiber := fiberDyadicBallMaximal_lintegral_bound
    G hG ⟨A, hA, hGbound⟩ hp
  have hleft :
      (∫⁻ x, ENNReal.ofReal (coordinateDyadicBallMaximal i f x ^ p)) =
        ∫⁻ z, ENNReal.ofReal (fiberDyadicBallMaximal G z ^ p)
          ∂fiberDyadicMeasure := by
    change (∫⁻ x, ENNReal.ofReal (fiberDyadicBallMaximal G (e x) ^ p)) = _
    exact he.lintegral_comp
      ((fiberDyadicBallMaximal_measurable G hG).pow measurable_const).ennreal_ofReal
  have hright :
      (∫⁻ z, (ENNReal.ofReal ‖G z‖) ^ p ∂fiberDyadicMeasure) =
        ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p := by
    simpa only [G, Function.comp_apply, MeasurableEquiv.symm_apply_apply] using
      (he.lintegral_comp ((hG.norm.ennreal_ofReal).pow measurable_const)).symm
  calc
    (∫⁻ x, ENNReal.ofReal (coordinateDyadicBallMaximal i f x ^ p)) =
        ∫⁻ z, ENNReal.ofReal (fiberDyadicBallMaximal G z ^ p)
          ∂fiberDyadicMeasure := hleft
    _ ≤ ENNReal.ofReal p *
        (2 * ENNReal.ofReal 4 * (ENNReal.ofReal (p - 1))⁻¹ *
          (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
          ∫⁻ z, (ENNReal.ofReal ‖G z‖) ^ p ∂fiberDyadicMeasure) := hfiber
    _ = ENNReal.ofReal p *
        (2 * ENNReal.ofReal 4 * (ENNReal.ofReal (p - 1))⁻¹ *
          (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
          ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p) := by rw [hright]

/-- Complex packaging of the transported estimate preserves the literal
`L^p` integral, because the packaged maximal function is nonnegative real. -/
theorem scratch_coordinateDyadicBallMaximalComplex_lintegral_bound
    (i : Fin 3) (f : E3 → ℂ) (hf : Measurable f)
    (A : ℝ) (hA : 0 ≤ A) (hbound : ∀ x, ‖f x‖ ≤ A)
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, (ENNReal.ofReal ‖coordinateDyadicBallMaximalComplex i f x‖) ^ p) ≤
      ENNReal.ofReal p *
        (2 * ENNReal.ofReal 4 * (ENNReal.ofReal (p - 1))⁻¹ *
          (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
          ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p) := by
  have h := scratch_coordinateDyadicBallMaximal_lintegral_bound
    i f hf A hA hbound hp
  have hpoint (x : E3) :
      ENNReal.ofReal (coordinateDyadicBallMaximal i f x ^ p) =
        (ENNReal.ofReal ‖coordinateDyadicBallMaximalComplex i f x‖) ^ p := by
    have hnon : 0 ≤ coordinateDyadicBallMaximal i f x := ENNReal.toReal_nonneg
    rw [coordinateDyadicBallMaximalComplex, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hnon,
      ENNReal.ofReal_rpow_of_nonneg hnon (by linarith)]
  calc
    (∫⁻ x, (ENNReal.ofReal ‖coordinateDyadicBallMaximalComplex i f x‖) ^ p) =
        ∫⁻ x, ENNReal.ofReal (coordinateDyadicBallMaximal i f x ^ p) := by
          apply lintegral_congr
          intro x
          exact (hpoint x).symm
    _ ≤ _ := h

/-- Pulling a nonnegative real constant through a complex-valued `L^p`
integral costs exactly its `p`th power. -/
theorem scratch_lintegral_norm_const_smul_rpow
    (K : ℝ) (hK : 0 ≤ K) (g : E3 → ℂ) (hg : Measurable g)
    {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x, (ENNReal.ofReal ‖(K : ℂ) • g x‖) ^ p) =
      (ENNReal.ofReal K) ^ p *
        ∫⁻ x, (ENNReal.ofReal ‖g x‖) ^ p := by
  have hpoint (x : E3) :
      (ENNReal.ofReal ‖(K : ℂ) • g x‖) ^ p =
        (ENNReal.ofReal K) ^ p * (ENNReal.ofReal ‖g x‖) ^ p := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK,
      ENNReal.ofReal_mul hK, ENNReal.mul_rpow_of_nonneg _ _ hp]
  calc
    (∫⁻ x, (ENNReal.ofReal ‖(K : ℂ) • g x‖) ^ p) =
        ∫⁻ x, (ENNReal.ofReal K) ^ p * (ENNReal.ofReal ‖g x‖) ^ p := by
          apply lintegral_congr
          intro x
          exact hpoint x
    _ = (ENNReal.ofReal K) ^ p *
        ∫⁻ x, (ENNReal.ofReal ‖g x‖) ^ p := by
          rw [lintegral_const_mul]
          exact (hg.norm.ennreal_ofReal.pow measurable_const)

/-- The explicit one-coordinate strong-type factor, including one shell
constant from the bracket-to-dyadic comparison. -/
noncomputable def scratchDyadicStrongFactor (K p : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal K) ^ p *
    (ENNReal.ofReal p *
      (2 * ENNReal.ofReal 4 * (ENNReal.ofReal (p - 1))⁻¹ *
        (ENNReal.ofReal (2 : ℝ)) ^ (p - 1)))

/-- Three successive literal-coordinate dyadic maximal operations have an
explicit strong `L^p` bound.  This is the quantitative upgrade of the
earlier `MemLp`-only terminal. -/
theorem scratch_scaledIteratedCoordinateDyadicBallMaximal_lintegral_bound
    (K : ℝ) (hK : 0 ≤ K) (f : E3 → ℂ) (hf : Measurable f)
    (A : ℝ) (hA : 0 ≤ A) (hbound : ∀ x, ‖f x‖ ≤ A)
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, (ENNReal.ofReal
      ‖scaledIteratedCoordinateDyadicBallMaximal K f x‖) ^ p) ≤
      (scratchDyadicStrongFactor K p) ^ 3 *
        ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p := by
  let D : ℝ≥0∞ := ENNReal.ofReal p *
    (2 * ENNReal.ofReal 4 * (ENNReal.ofReal (p - 1))⁻¹ *
      (ENNReal.ofReal (2 : ℝ)) ^ (p - 1))
  let k : ℝ≥0∞ := (ENNReal.ofReal K) ^ p
  let f₀ : E3 → ℂ := coordinateDyadicBallMaximalComplex 0 f
  let g₀ : E3 → ℂ := (K : ℂ) • f₀
  let f₁ : E3 → ℂ := coordinateDyadicBallMaximalComplex 1 g₀
  let g₁ : E3 → ℂ := (K : ℂ) • f₁
  let f₂ : E3 → ℂ := coordinateDyadicBallMaximalComplex 2 g₁
  have hnormK : ‖(K : ℂ)‖ = K := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK]
  have hf₀ : Measurable f₀ := by
    dsimp only [f₀]
    exact coordinateDyadicBallMaximalComplex_measurable 0 f hf
  have hbound₀ : ∀ x, ‖f₀ x‖ ≤ A := by
    dsimp only [f₀]
    exact coordinateDyadicBallMaximalComplex_top_bound 0 f A hA hbound
  have hD₀ : (∫⁻ x, (ENNReal.ofReal ‖f₀ x‖) ^ p) ≤
      D * ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p := by
    simpa only [D, mul_assoc] using
      (scratch_coordinateDyadicBallMaximalComplex_lintegral_bound
        0 f hf A hA hbound hp)
  have hg₀ : Measurable g₀ := by
    dsimp only [g₀]
    exact hf₀.const_smul (K : ℂ)
  have hKA : 0 ≤ K * A := mul_nonneg hK hA
  have hboundg₀ : ∀ x, ‖g₀ x‖ ≤ K * A := by
    intro x
    change ‖(K : ℂ) • f₀ x‖ ≤ K * A
    rw [norm_smul, hnormK]
    exact mul_le_mul_of_nonneg_left (hbound₀ x) hK
  have hf₁ : Measurable f₁ := by
    dsimp only [f₁]
    exact coordinateDyadicBallMaximalComplex_measurable 1 g₀ hg₀
  have hbound₁ : ∀ x, ‖f₁ x‖ ≤ K * A := by
    dsimp only [f₁]
    exact coordinateDyadicBallMaximalComplex_top_bound 1 g₀
      (K * A) hKA hboundg₀
  have hD₁ : (∫⁻ x, (ENNReal.ofReal ‖f₁ x‖) ^ p) ≤
      D * ∫⁻ x, (ENNReal.ofReal ‖g₀ x‖) ^ p := by
    simpa only [D, mul_assoc] using
      (scratch_coordinateDyadicBallMaximalComplex_lintegral_bound
        1 g₀ hg₀ (K * A) hKA hboundg₀ hp)
  have hg₁ : Measurable g₁ := by
    dsimp only [g₁]
    exact hf₁.const_smul (K : ℂ)
  have hKKA : 0 ≤ K * (K * A) := mul_nonneg hK hKA
  have hboundg₁ : ∀ x, ‖g₁ x‖ ≤ K * (K * A) := by
    intro x
    change ‖(K : ℂ) • f₁ x‖ ≤ K * (K * A)
    rw [norm_smul, hnormK]
    exact mul_le_mul_of_nonneg_left (hbound₁ x) hK
  have hf₂ : Measurable f₂ := by
    dsimp only [f₂]
    exact coordinateDyadicBallMaximalComplex_measurable 2 g₁ hg₁
  have hD₂ : (∫⁻ x, (ENNReal.ofReal ‖f₂ x‖) ^ p) ≤
      D * ∫⁻ x, (ENNReal.ofReal ‖g₁ x‖) ^ p := by
    simpa only [D, mul_assoc] using
      (scratch_coordinateDyadicBallMaximalComplex_lintegral_bound
        2 g₁ hg₁ (K * (K * A)) hKKA hboundg₁ hp)
  have hk₀ : (∫⁻ x, (ENNReal.ofReal ‖g₀ x‖) ^ p) =
      k * ∫⁻ x, (ENNReal.ofReal ‖f₀ x‖) ^ p := by
    simpa only [g₀, Pi.smul_apply, k] using
      (scratch_lintegral_norm_const_smul_rpow K hK f₀ hf₀ (by linarith))
  have hk₁ : (∫⁻ x, (ENNReal.ofReal ‖g₁ x‖) ^ p) =
      k * ∫⁻ x, (ENNReal.ofReal ‖f₁ x‖) ^ p := by
    simpa only [g₁, Pi.smul_apply, k] using
      (scratch_lintegral_norm_const_smul_rpow K hK f₁ hf₁ (by linarith))
  have hG₀ : (∫⁻ x, (ENNReal.ofReal ‖g₀ x‖) ^ p) ≤
      (k * D) * ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p := by
    calc
      (∫⁻ x, (ENNReal.ofReal ‖g₀ x‖) ^ p) =
          k * ∫⁻ x, (ENNReal.ofReal ‖f₀ x‖) ^ p := hk₀
      _ ≤ k * (D * ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p) :=
        mul_le_mul_of_nonneg_left hD₀ bot_le
      _ = (k * D) * ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p := by ring
  have hG₁ : (∫⁻ x, (ENNReal.ofReal ‖g₁ x‖) ^ p) ≤
      (k * D) ^ 2 * ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p := by
    calc
      (∫⁻ x, (ENNReal.ofReal ‖g₁ x‖) ^ p) =
          k * ∫⁻ x, (ENNReal.ofReal ‖f₁ x‖) ^ p := hk₁
      _ ≤ k * (D * ∫⁻ x, (ENNReal.ofReal ‖g₀ x‖) ^ p) :=
        mul_le_mul_of_nonneg_left hD₁ bot_le
      _ ≤ k * (D * ((k * D) * ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hG₀ bot_le) bot_le
      _ = (k * D) ^ 2 * ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p := by ring
  have hk₂ : (∫⁻ x, (ENNReal.ofReal ‖(K : ℂ) • f₂ x‖) ^ p) =
      k * ∫⁻ x, (ENNReal.ofReal ‖f₂ x‖) ^ p := by
    simpa only [k] using
      (scratch_lintegral_norm_const_smul_rpow K hK f₂ hf₂ (by linarith))
  change (∫⁻ x, (ENNReal.ofReal ‖(K : ℂ) • f₂ x‖) ^ p) ≤ _
  calc
    (∫⁻ x, (ENNReal.ofReal ‖(K : ℂ) • f₂ x‖) ^ p) =
        k * ∫⁻ x, (ENNReal.ofReal ‖f₂ x‖) ^ p := hk₂
    _ ≤ k * (D * ∫⁻ x, (ENNReal.ofReal ‖g₁ x‖) ^ p) :=
      mul_le_mul_of_nonneg_left hD₂ bot_le
    _ ≤ k * (D * ((k * D) ^ 2 *
        ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hG₁ bot_le) bot_le
    _ = (scratchDyadicStrongFactor K p) ^ 3 *
        ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p := by
      dsimp only [scratchDyadicStrongFactor, k, D]
      ring

end Twisted
end Auto
