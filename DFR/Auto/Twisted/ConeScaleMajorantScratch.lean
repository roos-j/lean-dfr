/- Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
This file is a scratch investigation for the cone-scale Fubini majorant.
-/
import Auto.Twisted.Twisted

namespace Auto
namespace Twisted

open MeasureTheory Filter FourierTransform TopologicalSpace
open scoped BigOperators Convolution ENNReal FourierTransform NNReal Topology

noncomputable section

/-- The positive third-cone scalar factor left after summing Fourier modes.
It is the scale-dependent part that must dominate the joint mode/frequency
Fubini argument. -/
noncomputable def scratch_thirdConeScaleEnvelope
    (α : Anisotropy) (ξ : E3) (t : ℝ) : ℝ :=
  conePsi (t ^ α.weight 2 * ξ 2) *
    gaussianDeriv (t ^ α.weight 2 * ξ 2) ^ 2 *
      (conePhi (t ^ α.weight 0 * ξ 0) *
        conePhi (t ^ α.weight 1 * ξ 1))

/-- The active annular factor in the third cone. -/
noncomputable def scratch_thirdConeActiveDensity
    (α : Anisotropy) (ξ : E3) (t : ℝ) : ℝ :=
  conePsi (t ^ α.weight 2 * ξ 2) *
    gaussianDeriv (t ^ α.weight 2 * ξ 2) ^ 2

theorem scratch_thirdConeScaleEnvelope_nonneg
    (α : Anisotropy) (ξ : E3) (t : ℝ) :
    0 ≤ scratch_thirdConeScaleEnvelope α ξ t := by
  unfold scratch_thirdConeScaleEnvelope
  exact mul_nonneg
    (mul_nonneg (conePsi_nonneg _) (sq_nonneg _))
    (mul_nonneg (conePhi_nonneg _) (conePhi_nonneg _))

theorem scratch_thirdConeActiveDensity_nonneg
    (α : Anisotropy) (ξ : E3) (t : ℝ) :
    0 ≤ scratch_thirdConeActiveDensity α ξ t := by
  unfold scratch_thirdConeActiveDensity
  exact mul_nonneg (conePsi_nonneg _) (sq_nonneg _)

/-- Passive low-frequency factors are bounded by two copies of the
Calderón mass, leaving a one-dimensional active scale density. -/
theorem scratch_thirdConeScaleEnvelope_le
    (α : Anisotropy) (ξ : E3) (t : ℝ) :
    scratch_thirdConeScaleEnvelope α ξ t ≤
      cPsi ^ 2 * scratch_thirdConeActiveDensity α ξ t := by
  have hpass :
      conePhi (t ^ α.weight 0 * ξ 0) *
          conePhi (t ^ α.weight 1 * ξ 1) ≤ cPsi * cPsi := by
    exact mul_le_mul
      (conePhi_le_cPsi _) (conePhi_le_cPsi _)
      (conePhi_nonneg _) cPsi_pos.le
  have hactive : 0 ≤ scratch_thirdConeActiveDensity α ξ t :=
    scratch_thirdConeActiveDensity_nonneg α ξ t
  unfold scratch_thirdConeScaleEnvelope scratch_thirdConeActiveDensity
  calc
    conePsi (t ^ α.weight 2 * ξ 2) *
          gaussianDeriv (t ^ α.weight 2 * ξ 2) ^ 2 *
        (conePhi (t ^ α.weight 0 * ξ 0) *
          conePhi (t ^ α.weight 1 * ξ 1)) ≤
        (conePsi (t ^ α.weight 2 * ξ 2) *
          gaussianDeriv (t ^ α.weight 2 * ξ 2) ^ 2) * (cPsi * cPsi) :=
      mul_le_mul_of_nonneg_left hpass hactive
    _ = cPsi ^ 2 *
        (conePsi (t ^ α.weight 2 * ξ 2) *
          gaussianDeriv (t ^ α.weight 2 * ξ 2) ^ 2) := by ring

theorem scratch_continuous_thirdConeScaleEnvelope
    (α : Anisotropy) (ξ : E3) :
    Continuous (scratch_thirdConeScaleEnvelope α ξ) := by
  have harg (j : Fin 3) : Continuous (fun t : ℝ ↦
      t ^ α.weight j * ξ j) :=
    (continuous_pow _).mul continuous_const
  unfold scratch_thirdConeScaleEnvelope
  exact ((conePsi_contDiff.continuous.comp (harg 2)).mul
      ((continuous_gaussianDeriv.comp (harg 2)).pow 2)).mul
    ((conePhi_contDiff.continuous.comp (harg 0)).mul
      (conePhi_contDiff.continuous.comp (harg 1)))

theorem scratch_continuous_thirdConeActiveDensity
    (α : Anisotropy) (ξ : E3) :
    Continuous (scratch_thirdConeActiveDensity α ξ) := by
  have harg : Continuous (fun t : ℝ ↦
      t ^ α.weight 2 * ξ 2) :=
    (continuous_pow _).mul continuous_const
  unfold scratch_thirdConeActiveDensity
  exact (conePsi_contDiff.continuous.comp harg).mul
    ((continuous_gaussianDeriv.comp harg).pow 2)

/-- On every positive finite scale interval, the third cone has the exact
uniform scalar majorant needed for the mode/Fourier interchange.  It is the
one-coordinate Calderón identity times two passive cutoff bounds. -/
theorem scratch_integral_thirdConeScaleEnvelope_Ioc_le
    (α : Anisotropy) (ξ : E3) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hξ : ξ 2 ≠ 0) :
    ∫ t in Set.Ioc a b, scratch_thirdConeScaleEnvelope α ξ t
      ∂((volume : Measure ℝ).withDensity cubeScaleDensity) ≤
      cPsi ^ 3 / (α.weight 2 : ℝ) := by
  rw [integral_modelScaleInterval_withDensity_eq_intervalIntegral ha hab]
  have hden (t : ℝ) (ht : t ∈ Set.Icc a b) : t ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le ha ht.1)
  have hleftcont : ContinuousOn (fun t : ℝ ↦
      scratch_thirdConeScaleEnvelope α ξ t / t) (Set.Icc a b) :=
    (scratch_continuous_thirdConeScaleEnvelope α ξ).continuousOn.div
      continuousOn_id hden
  have hrightcont : ContinuousOn (fun t : ℝ ↦
      (cPsi ^ 2 * scratch_thirdConeActiveDensity α ξ t) / t)
        (Set.Icc a b) :=
    (continuous_const.mul (scratch_continuous_thirdConeActiveDensity α ξ)).continuousOn.div
      continuousOn_id hden
  have hmono :
      (∫ t in a..b, scratch_thirdConeScaleEnvelope α ξ t / t) ≤
        ∫ t in a..b, (cPsi ^ 2 * scratch_thirdConeActiveDensity α ξ t) / t := by
    apply intervalIntegral.integral_mono_on hab
      (hleftcont.intervalIntegrable_of_Icc hab)
      (hrightcont.intervalIntegrable_of_Icc hab)
    intro t ht
    exact div_le_div_of_nonneg_right
      (scratch_thirdConeScaleEnvelope_le α ξ t)
      (le_of_lt (lt_of_lt_of_le ha ht.1))
  have hn : 0 < α.weight 2 := α.weight_pos 2
  have hnR : (α.weight 2 : ℝ) ≠ 0 := by positivity
  have hscale : (fun t : ℝ ↦
      (cPsi ^ 2 * scratch_thirdConeActiveDensity α ξ t) / t) =
      (fun t ↦ (cPsi ^ 2 / (α.weight 2 : ℝ)) *
        ((α.weight 2 : ℝ) *
          conePsi (t ^ α.weight 2 * ξ 2) *
            gaussianDeriv (t ^ α.weight 2 * ξ 2) ^ 2 / t)) := by
    funext t
    by_cases ht : t = 0
    · simp [ht]
    · unfold scratch_thirdConeActiveDensity
      field_simp [hnR, ht]
  have hactive :
      (∫ t in a..b,
        (cPsi ^ 2 * scratch_thirdConeActiveDensity α ξ t) / t) =
        (cPsi ^ 2 / (α.weight 2 : ℝ)) *
          (conePhi (a ^ α.weight 2 * ξ 2) -
            conePhi (b ^ α.weight 2 * ξ 2)) := by
    rw [hscale, intervalIntegral.integral_const_mul,
      calderon_interval_nat_scale (α.weight 2) hn (ξ 2) a b hξ ha hab]
  have hdiff :
      conePhi (a ^ α.weight 2 * ξ 2) -
          conePhi (b ^ α.weight 2 * ξ 2) ≤ cPsi := by
    linarith [conePhi_le_cPsi (a ^ α.weight 2 * ξ 2),
      conePhi_nonneg (b ^ α.weight 2 * ξ 2)]
  have hfac : 0 ≤ cPsi ^ 2 / (α.weight 2 : ℝ) := by positivity
  calc
    (∫ t in a..b, scratch_thirdConeScaleEnvelope α ξ t / t) ≤
        ∫ t in a..b, (cPsi ^ 2 * scratch_thirdConeActiveDensity α ξ t) / t := hmono
    _ = (cPsi ^ 2 / (α.weight 2 : ℝ)) *
          (conePhi (a ^ α.weight 2 * ξ 2) -
            conePhi (b ^ α.weight 2 * ξ 2)) := hactive
    _ ≤ (cPsi ^ 2 / (α.weight 2 : ℝ)) * cPsi :=
      mul_le_mul_of_nonneg_left hdiff hfac
    _ = cPsi ^ 3 / (α.weight 2 : ℝ) := by ring

/-- The active annular cutoff vanishes at all sufficiently small positive
scales when the active frequency is nonzero. -/
theorem scratch_exists_small_scale_zero_thirdConeScaleEnvelope
    (α : Anisotropy) (ξ : E3) (hξ : ξ 2 ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ t : ℝ, 0 < t → t ≤ a →
      scratch_thirdConeScaleEnvelope α ξ t = 0 := by
  let R : ℝ := |ξ 2|
  let a : ℝ := 1 / (1 + R)
  have hR : 0 < R := by
    dsimp [R]
    exact abs_pos.mpr hξ
  have hden : 0 < 1 + R := by linarith
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos zero_lt_one hden
  have haone : a ≤ 1 := by
    dsimp [a]
    apply (div_le_iff₀ hden).mpr
    linarith
  have haR : a * R ≤ 1 := by
    calc
      a * R = R / (1 + R) := by
        dsimp [a]
        ring
      _ ≤ 1 := (div_le_iff₀ hden).mpr (by linarith)
  refine ⟨a, ha, ?_⟩
  intro t ht hta
  have htone : t ≤ 1 := hta.trans haone
  have hn : α.weight 2 ≠ 0 := Nat.ne_zero_of_lt (α.weight_pos 2)
  have hpow : t ^ α.weight 2 ≤ t :=
    pow_le_of_le_one ht.le htone hn
  have hsmall : |t ^ α.weight 2 * ξ 2| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg ht.le _)]
    calc
      t ^ α.weight 2 * |ξ 2| ≤ t * |ξ 2| :=
        mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
      _ ≤ a * |ξ 2| :=
        mul_le_mul_of_nonneg_right hta (abs_nonneg _)
      _ = a * R := by rfl
      _ ≤ 1 := haR
  unfold scratch_thirdConeScaleEnvelope
  rw [conePsi_eq_zero_of_abs_le_one hsmall]
  ring

/-- The positive third-cone scalar envelope is integrable on all source
scales as soon as its active frequency is nonzero.  The proof uses its
small-scale annular vanishing and the finite-scale Calderón bound. -/
theorem scratch_integrableOn_thirdConeScaleEnvelope_Ioi
    (α : Anisotropy) (ξ : E3) (hξ : ξ 2 ≠ 0) :
    IntegrableOn (scratch_thirdConeScaleEnvelope α ξ) (Set.Ioi (0 : ℝ))
      ((volume : Measure ℝ).withDensity cubeScaleDensity) := by
  rcases scratch_exists_small_scale_zero_thirdConeScaleEnvelope α ξ hξ
    with ⟨a, ha, hzero⟩
  let μ : Measure ℝ := (volume : Measure ℝ).withDensity cubeScaleDensity
  let b : ℕ → ℝ := fun n ↦ a + n
  have hb (n : ℕ) : a ≤ b n := by
    dsimp [b]
    positivity
  have hbpos (n : ℕ) : 0 < b n := lt_of_lt_of_le ha (hb n)
  have hfinite (n : ℕ) : IntegrableOn (scratch_thirdConeScaleEnvelope α ξ)
      (Set.Ioc (0 : ℝ) (b n)) μ := by
    have hinner : IntegrableOn (scratch_thirdConeScaleEnvelope α ξ)
        (Set.Ioc a (b n)) μ := by
      dsimp [μ]
      exact integrableOn_modelScaleInterval_of_continuous ha
        (scratch_thirdConeScaleEnvelope α ξ)
        (scratch_continuous_thirdConeScaleEnvelope α ξ)
    apply hinner.of_forall_sdiff_eq_zero measurableSet_Ioc
    intro t ht
    have htpos : 0 < t := ht.1.1
    have htba : t ≤ b n := ht.1.2
    have hnot : ¬ (a < t ∧ t ≤ b n) := by
      simpa only [Set.mem_Ioc] using ht.2
    have hta : t ≤ a := le_of_not_gt (fun hta ↦ hnot ⟨hta, htba⟩)
    exact hzero t htpos hta
  have hbound : ∀ n : ℕ,
      (∫ t in 0..b n, ‖scratch_thirdConeScaleEnvelope α ξ t‖ ∂μ) ≤
        cPsi ^ 3 / (α.weight 2 : ℝ) := by
    intro n
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ b n by positivity)]
    change (∫ t in Set.Ioc (0 : ℝ) (b n),
      ‖scratch_thirdConeScaleEnvelope α ξ t‖ ∂μ) ≤ _
    rw [show (fun t : ℝ ↦ ‖scratch_thirdConeScaleEnvelope α ξ t‖) =
        scratch_thirdConeScaleEnvelope α ξ by
      funext t
      exact Real.norm_of_nonneg (scratch_thirdConeScaleEnvelope_nonneg α ξ t)]
    have hzeroOn : IntegrableOn (scratch_thirdConeScaleEnvelope α ξ)
        (Set.Ioc (0 : ℝ) a) μ := by
      apply integrableOn_zero.congr_fun
        (fun t ht ↦ (hzero t ht.1 ht.2).symm) measurableSet_Ioc
    have hzeroInterval :
        (∫ t in 0..a, scratch_thirdConeScaleEnvelope α ξ t ∂μ) = 0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards [] with t ht
      rw [Set.uIcc_of_le ha.le] at ht
      by_cases ht0 : t = 0
      · subst t
        have hpsi : conePsi ((0 : ℝ) ^ α.weight 2 * ξ 2) = 0 := by
          apply conePsi_eq_zero_of_abs_le_one
          simp
        unfold scratch_thirdConeScaleEnvelope
        rw [hpsi]
        ring
      · exact hzero t (lt_of_le_of_ne ht.1 (Ne.symm ht0)) ht.2
    have hsplit :
        (∫ t in Set.Ioc (0 : ℝ) (b n), scratch_thirdConeScaleEnvelope α ξ t ∂μ) =
          ∫ t in Set.Ioc a (b n), scratch_thirdConeScaleEnvelope α ξ t ∂μ := by
      have hinter : IntervalIntegrable (scratch_thirdConeScaleEnvelope α ξ) μ a (b n) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (hb n)).mpr
          (integrableOn_modelScaleInterval_of_continuous ha
            (scratch_thirdConeScaleEnvelope α ξ)
            (scratch_continuous_thirdConeScaleEnvelope α ξ))
      calc
        (∫ t in Set.Ioc (0 : ℝ) (b n), scratch_thirdConeScaleEnvelope α ξ t ∂μ) =
            ∫ t in 0..b n, scratch_thirdConeScaleEnvelope α ξ t ∂μ :=
          (intervalIntegral.integral_of_le (show (0 : ℝ) ≤ b n by positivity)).symm
        _ = (∫ t in 0..a, scratch_thirdConeScaleEnvelope α ξ t ∂μ) +
            ∫ t in a..b n, scratch_thirdConeScaleEnvelope α ξ t ∂μ :=
          (intervalIntegral.integral_add_adjacent_intervals
            ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mpr hzeroOn)
            hinter).symm
        _ = ∫ t in a..b n, scratch_thirdConeScaleEnvelope α ξ t ∂μ := by
          rw [hzeroInterval, zero_add]
        _ = ∫ t in Set.Ioc a (b n), scratch_thirdConeScaleEnvelope α ξ t ∂μ :=
          intervalIntegral.integral_of_le (hb n)
    rw [hsplit]
    dsimp [μ]
    exact scratch_integral_thirdConeScaleEnvelope_Ioc_le α ξ a (b n)
      ha (hb n) hξ

end
end Twisted
end Auto

end
end Twisted
end Auto
