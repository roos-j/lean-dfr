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
noncomputable def thirdConeScaleEnvelope
    (α : Anisotropy) (ξ : E3) (t : ℝ) : ℝ :=
  conePsi (t ^ α.weight 2 * ξ 2) *
    gaussianDeriv (t ^ α.weight 2 * ξ 2) ^ 2 *
      (conePhi (t ^ α.weight 0 * ξ 0) *
        conePhi (t ^ α.weight 1 * ξ 1))

/-- The active annular factor in the third cone. -/
noncomputable def thirdConeActiveDensity
    (α : Anisotropy) (ξ : E3) (t : ℝ) : ℝ :=
  conePsi (t ^ α.weight 2 * ξ 2) *
    gaussianDeriv (t ^ α.weight 2 * ξ 2) ^ 2

/-- The scale majorant after the two passive low-frequency factors have been
bounded by `cPsi`.  This is the scalar integrand used for the joint
mode/scale Fubini domination. -/
noncomputable def thirdConeScaleMajorant
    (α : Anisotropy) (ξ : E3) (t : ℝ) : ℝ :=
  cPsi ^ 2 * thirdConeActiveDensity α ξ t

theorem thirdConeScaleEnvelope_nonneg
    (α : Anisotropy) (ξ : E3) (t : ℝ) :
    0 ≤ thirdConeScaleEnvelope α ξ t := by
  unfold thirdConeScaleEnvelope
  exact mul_nonneg
    (mul_nonneg (conePsi_nonneg _) (sq_nonneg _))
    (mul_nonneg (conePhi_nonneg _) (conePhi_nonneg _))

theorem thirdConeActiveDensity_nonneg
    (α : Anisotropy) (ξ : E3) (t : ℝ) :
    0 ≤ thirdConeActiveDensity α ξ t := by
  unfold thirdConeActiveDensity
  exact mul_nonneg (conePsi_nonneg _) (sq_nonneg _)

theorem thirdConeScaleMajorant_nonneg
    (α : Anisotropy) (ξ : E3) (t : ℝ) :
    0 ≤ thirdConeScaleMajorant α ξ t := by
  unfold thirdConeScaleMajorant
  exact mul_nonneg (sq_nonneg cPsi)
    (thirdConeActiveDensity_nonneg α ξ t)

/-- Passive low-frequency factors are bounded by two copies of the
Calderón mass, leaving a one-dimensional active scale density. -/
theorem thirdConeScaleEnvelope_le
    (α : Anisotropy) (ξ : E3) (t : ℝ) :
    thirdConeScaleEnvelope α ξ t ≤
      cPsi ^ 2 * thirdConeActiveDensity α ξ t := by
  have hpass :
      conePhi (t ^ α.weight 0 * ξ 0) *
          conePhi (t ^ α.weight 1 * ξ 1) ≤ cPsi * cPsi := by
    exact mul_le_mul
      (conePhi_le_cPsi _) (conePhi_le_cPsi _)
      (conePhi_nonneg _) cPsi_pos.le
  have hactive : 0 ≤ thirdConeActiveDensity α ξ t :=
    thirdConeActiveDensity_nonneg α ξ t
  unfold thirdConeScaleEnvelope thirdConeActiveDensity
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

theorem continuous_thirdConeScaleEnvelope
    (α : Anisotropy) (ξ : E3) :
    Continuous (thirdConeScaleEnvelope α ξ) := by
  have harg (j : Fin 3) : Continuous (fun t : ℝ ↦
      t ^ α.weight j * ξ j) :=
    (continuous_pow _).mul continuous_const
  unfold thirdConeScaleEnvelope
  exact ((conePsi_contDiff.continuous.comp (harg 2)).mul
      ((continuous_gaussianDeriv.comp (harg 2)).pow 2)).mul
    ((conePhi_contDiff.continuous.comp (harg 0)).mul
      (conePhi_contDiff.continuous.comp (harg 1)))

theorem continuous_thirdConeActiveDensity
    (α : Anisotropy) (ξ : E3) :
    Continuous (thirdConeActiveDensity α ξ) := by
  have harg : Continuous (fun t : ℝ ↦
      t ^ α.weight 2 * ξ 2) :=
    (continuous_pow _).mul continuous_const
  unfold thirdConeActiveDensity
  exact (conePsi_contDiff.continuous.comp harg).mul
    ((continuous_gaussianDeriv.comp harg).pow 2)

theorem continuous_thirdConeScaleMajorant
    (α : Anisotropy) (ξ : E3) :
    Continuous (thirdConeScaleMajorant α ξ) := by
  unfold thirdConeScaleMajorant
  exact continuous_const.mul (continuous_thirdConeActiveDensity α ξ)

theorem continuous_thirdConeScaleMajorant_joint
    (α : Anisotropy) :
    Continuous (fun p : ℝ × E3 ↦ thirdConeScaleMajorant α p.2 p.1) := by
  have harg (j : Fin 3) : Continuous (fun p : ℝ × E3 ↦
      p.1 ^ α.weight j * p.2 j) := by
    have hcoord : Continuous (fun p : ℝ × E3 ↦ p.2 j) := by
      convert (coordinateProjection j).continuous.comp continuous_snd using 1
      ext p
      simp [coordinateProjection_apply]
    exact (continuous_fst.pow _).mul hcoord
  unfold thirdConeScaleMajorant thirdConeActiveDensity
  exact continuous_const.mul
    ((conePsi_contDiff.continuous.comp (harg 2)).mul
      ((continuous_gaussianDeriv.comp (harg 2)).pow 2))

/-- On every positive finite scale interval, the third cone has the exact
uniform scalar majorant needed for the mode/Fourier interchange.  It is the
one-coordinate Calderón identity times two passive cutoff bounds. -/
theorem integral_thirdConeScaleEnvelope_Ioc_le
    (α : Anisotropy) (ξ : E3) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hξ : ξ 2 ≠ 0) :
    ∫ t in Set.Ioc a b, thirdConeScaleEnvelope α ξ t
      ∂((volume : Measure ℝ).withDensity cubeScaleDensity) ≤
      cPsi ^ 3 / (α.weight 2 : ℝ) := by
  rw [integral_modelScaleInterval_withDensity_eq_intervalIntegral ha hab]
  have hden (t : ℝ) (ht : t ∈ Set.Icc a b) : t ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le ha ht.1)
  have hleftcont : ContinuousOn (fun t : ℝ ↦
      thirdConeScaleEnvelope α ξ t / t) (Set.Icc a b) :=
    (continuous_thirdConeScaleEnvelope α ξ).continuousOn.div
      continuousOn_id hden
  have hrightcont : ContinuousOn (fun t : ℝ ↦
      (cPsi ^ 2 * thirdConeActiveDensity α ξ t) / t)
        (Set.Icc a b) :=
    (continuous_const.mul (continuous_thirdConeActiveDensity α ξ)).continuousOn.div
      continuousOn_id hden
  have hmono :
      (∫ t in a..b, thirdConeScaleEnvelope α ξ t / t) ≤
        ∫ t in a..b, (cPsi ^ 2 * thirdConeActiveDensity α ξ t) / t := by
    apply intervalIntegral.integral_mono_on hab
      (hleftcont.intervalIntegrable_of_Icc hab)
      (hrightcont.intervalIntegrable_of_Icc hab)
    intro t ht
    exact div_le_div_of_nonneg_right
      (thirdConeScaleEnvelope_le α ξ t)
      (le_of_lt (lt_of_lt_of_le ha ht.1))
  have hn : 0 < α.weight 2 := α.weight_pos 2
  have hnR : (α.weight 2 : ℝ) ≠ 0 := by positivity
  have hscale : (fun t : ℝ ↦
      (cPsi ^ 2 * thirdConeActiveDensity α ξ t) / t) =
      (fun t ↦ (cPsi ^ 2 / (α.weight 2 : ℝ)) *
        ((α.weight 2 : ℝ) *
          conePsi (t ^ α.weight 2 * ξ 2) *
            gaussianDeriv (t ^ α.weight 2 * ξ 2) ^ 2 / t)) := by
    funext t
    by_cases ht : t = 0
    · simp [ht]
    · unfold thirdConeActiveDensity
      field_simp [hnR, ht]
  have hactive :
      (∫ t in a..b,
        (cPsi ^ 2 * thirdConeActiveDensity α ξ t) / t) =
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
    (∫ t in a..b, thirdConeScaleEnvelope α ξ t / t) ≤
        ∫ t in a..b, (cPsi ^ 2 * thirdConeActiveDensity α ξ t) / t := hmono
    _ = (cPsi ^ 2 / (α.weight 2 : ℝ)) *
          (conePhi (a ^ α.weight 2 * ξ 2) -
            conePhi (b ^ α.weight 2 * ξ 2)) := hactive
    _ ≤ (cPsi ^ 2 / (α.weight 2 : ℝ)) * cPsi :=
      mul_le_mul_of_nonneg_left hdiff hfac
    _ = cPsi ^ 3 / (α.weight 2 : ℝ) := by ring

/-- The positive scale integral of the post-summation active majorant is
uniformly bounded on every finite interval by the one-dimensional Calderón
identity. -/
theorem integral_thirdConeScaleMajorant_Ioc_le
    (α : Anisotropy) (ξ : E3) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hξ : ξ 2 ≠ 0) :
    ∫ t in Set.Ioc a b, thirdConeScaleMajorant α ξ t
      ∂((volume : Measure ℝ).withDensity cubeScaleDensity) ≤
      cPsi ^ 3 / (α.weight 2 : ℝ) := by
  rw [integral_modelScaleInterval_withDensity_eq_intervalIntegral ha hab]
  have hn : 0 < α.weight 2 := α.weight_pos 2
  have hnR : (α.weight 2 : ℝ) ≠ 0 := by positivity
  have hscale : (fun t : ℝ ↦ thirdConeScaleMajorant α ξ t / t) =
      (fun t ↦ (cPsi ^ 2 / (α.weight 2 : ℝ)) *
        ((α.weight 2 : ℝ) *
          conePsi (t ^ α.weight 2 * ξ 2) *
            gaussianDeriv (t ^ α.weight 2 * ξ 2) ^ 2 / t)) := by
    funext t
    by_cases ht : t = 0
    · simp [thirdConeScaleMajorant, ht]
    · unfold thirdConeScaleMajorant thirdConeActiveDensity
      field_simp [hnR, ht]
  have hactive :
      (∫ t in a..b, thirdConeScaleMajorant α ξ t / t) =
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
    (∫ t in a..b, thirdConeScaleMajorant α ξ t / t) =
        (cPsi ^ 2 / (α.weight 2 : ℝ)) *
          (conePhi (a ^ α.weight 2 * ξ 2) -
            conePhi (b ^ α.weight 2 * ξ 2)) := hactive
    _ ≤ (cPsi ^ 2 / (α.weight 2 : ℝ)) * cPsi :=
      mul_le_mul_of_nonneg_left hdiff hfac
    _ = cPsi ^ 3 / (α.weight 2 : ℝ) := by ring

/-- The active annular cutoff vanishes at all sufficiently small positive
scales when the active frequency is nonzero. -/
theorem exists_small_scale_zero_thirdConeScaleEnvelope
    (α : Anisotropy) (ξ : E3) (hξ : ξ 2 ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ t : ℝ, 0 < t → t ≤ a →
      thirdConeScaleEnvelope α ξ t = 0 := by
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
  unfold thirdConeScaleEnvelope
  rw [conePsi_eq_zero_of_abs_le_one hsmall]
  ring

/-- The active annular factor itself vanishes below a positive scale depending
only on the nonzero active frequency. -/
theorem exists_small_scale_zero_thirdConeActiveDensity
    (α : Anisotropy) (ξ : E3) (hξ : ξ 2 ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ t : ℝ, 0 < t → t ≤ a →
      thirdConeActiveDensity α ξ t = 0 := by
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
  unfold thirdConeActiveDensity
  rw [conePsi_eq_zero_of_abs_le_one hsmall]
  ring

theorem exists_small_scale_zero_thirdConeScaleMajorant
    (α : Anisotropy) (ξ : E3) (hξ : ξ 2 ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ t : ℝ, 0 < t → t ≤ a →
      thirdConeScaleMajorant α ξ t = 0 := by
  rcases exists_small_scale_zero_thirdConeActiveDensity α ξ hξ
    with ⟨a, ha, hzero⟩
  refine ⟨a, ha, ?_⟩
  intro t ht hta
  unfold thirdConeScaleMajorant
  rw [hzero t ht hta]
  ring

/-- The positive third-cone scalar envelope is integrable on all source
scales as soon as its active frequency is nonzero.  The proof uses its
small-scale annular vanishing and the finite-scale Calderón bound. -/
theorem integrableOn_thirdConeScaleEnvelope_Ioi
    (α : Anisotropy) (ξ : E3) (hξ : ξ 2 ≠ 0) :
    IntegrableOn (thirdConeScaleEnvelope α ξ) (Set.Ioi (0 : ℝ))
      ((volume : Measure ℝ).withDensity cubeScaleDensity) := by
  rcases exists_small_scale_zero_thirdConeScaleEnvelope α ξ hξ
    with ⟨a, ha, hzero⟩
  let μ : Measure ℝ := (volume : Measure ℝ).withDensity cubeScaleDensity
  let b : ℕ → ℝ := fun n ↦ a + n
  have hb (n : ℕ) : a ≤ b n := by
    dsimp [b]
    exact le_add_of_nonneg_right (Nat.cast_nonneg n)
  have hbpos (n : ℕ) : 0 < b n := lt_of_lt_of_le ha (hb n)
  have hfinite (n : ℕ) : IntegrableOn (thirdConeScaleEnvelope α ξ)
      (Set.Ioc (0 : ℝ) (b n)) μ := by
    have hinner : IntegrableOn (thirdConeScaleEnvelope α ξ)
        (Set.Ioc a (b n)) μ := by
      dsimp [μ]
      exact integrableOn_modelScaleInterval_of_continuous ha
        (thirdConeScaleEnvelope α ξ)
        (continuous_thirdConeScaleEnvelope α ξ)
    apply hinner.of_forall_sdiff_eq_zero measurableSet_Ioc
    intro t ht
    have htpos : 0 < t := ht.1.1
    have htba : t ≤ b n := ht.1.2
    have hnot : ¬ (a < t ∧ t ≤ b n) := by
      simpa only [Set.mem_Ioc] using ht.2
    have hta : t ≤ a := le_of_not_gt (fun hta ↦ hnot ⟨hta, htba⟩)
    exact hzero t htpos hta
  have hbound : ∀ n : ℕ,
      (∫ t in 0..b n, ‖thirdConeScaleEnvelope α ξ t‖ ∂μ) ≤
        cPsi ^ 3 / (α.weight 2 : ℝ) := by
    intro n
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ b n by positivity)]
    change (∫ t in Set.Ioc (0 : ℝ) (b n),
      ‖thirdConeScaleEnvelope α ξ t‖ ∂μ) ≤ _
    rw [show (fun t : ℝ ↦ ‖thirdConeScaleEnvelope α ξ t‖) =
        thirdConeScaleEnvelope α ξ by
      funext t
      exact Real.norm_of_nonneg (thirdConeScaleEnvelope_nonneg α ξ t)]
    have hzeroOn : IntegrableOn (thirdConeScaleEnvelope α ξ)
        (Set.Ioc (0 : ℝ) a) μ := by
      apply integrableOn_zero.congr_fun
        (fun t ht ↦ (hzero t ht.1 ht.2).symm) measurableSet_Ioc
    have hzeroInterval :
        (∫ t in 0..a, thirdConeScaleEnvelope α ξ t ∂μ) = 0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards [] with t ht
      rw [Set.uIoc_of_le ha.le] at ht
      exact hzero t ht.1 ht.2
    have hsplit :
        (∫ t in Set.Ioc (0 : ℝ) (b n), thirdConeScaleEnvelope α ξ t ∂μ) =
          ∫ t in Set.Ioc a (b n), thirdConeScaleEnvelope α ξ t ∂μ := by
      have hinter : IntervalIntegrable (thirdConeScaleEnvelope α ξ) μ a (b n) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (hb n)).mpr
          (integrableOn_modelScaleInterval_of_continuous ha
            (thirdConeScaleEnvelope α ξ)
            (continuous_thirdConeScaleEnvelope α ξ))
      calc
        (∫ t in Set.Ioc (0 : ℝ) (b n), thirdConeScaleEnvelope α ξ t ∂μ) =
            ∫ t in 0..b n, thirdConeScaleEnvelope α ξ t ∂μ :=
          (intervalIntegral.integral_of_le (show (0 : ℝ) ≤ b n by positivity)).symm
        _ = (∫ t in 0..a, thirdConeScaleEnvelope α ξ t ∂μ) +
            ∫ t in a..b n, thirdConeScaleEnvelope α ξ t ∂μ :=
          (intervalIntegral.integral_add_adjacent_intervals
            ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mpr hzeroOn)
            hinter).symm
        _ = ∫ t in a..b n, thirdConeScaleEnvelope α ξ t ∂μ := by
          rw [hzeroInterval, zero_add]
        _ = ∫ t in Set.Ioc a (b n), thirdConeScaleEnvelope α ξ t ∂μ :=
          intervalIntegral.integral_of_le (hb n)
    rw [hsplit]
    dsimp [μ]
    exact integral_thirdConeScaleEnvelope_Ioc_le α ξ a (b n)
      ha (hb n) hξ
  have hbTendsto : Tendsto b atTop atTop := by
    dsimp [b]
    exact tendsto_atTop_add_const_left _ a tendsto_natCast_atTop_atTop
  change IntegrableOn (thirdConeScaleEnvelope α ξ) (Set.Ioi (0 : ℝ)) μ
  exact integrableOn_Ioi_of_intervalIntegral_norm_bounded
    (cPsi ^ 3 / (α.weight 2 : ℝ)) 0 hfinite hbTendsto
    (Filter.Eventually.of_forall hbound)

/-- A source-scale exhaustion principle.  A continuous nonnegative density
that vanishes below one positive scale and has a uniform finite-interval
bound is integrable on all positive scales, with the same global bound. -/
theorem integrableOn_and_integral_Ioi_of_small_zero_Ioc_bound
    (f : ℝ → ℝ) (a C : ℝ) (ha : 0 < a)
    (hfcont : Continuous f) (hfnonneg : ∀ t : ℝ, 0 ≤ f t)
    (hzero : ∀ t : ℝ, 0 < t → t ≤ a → f t = 0)
    (hboundIoc : ∀ b : ℝ, a ≤ b →
      ∫ t in Set.Ioc a b, f t
        ∂((volume : Measure ℝ).withDensity cubeScaleDensity) ≤ C) :
    IntegrableOn f (Set.Ioi (0 : ℝ))
        ((volume : Measure ℝ).withDensity cubeScaleDensity) ∧
      ∫ t in Set.Ioi (0 : ℝ), f t
        ∂((volume : Measure ℝ).withDensity cubeScaleDensity) ≤ C := by
  let μ : Measure ℝ := (volume : Measure ℝ).withDensity cubeScaleDensity
  let b : ℕ → ℝ := fun n ↦ a + n
  have hb (n : ℕ) : a ≤ b n := by
    dsimp [b]
    exact le_add_of_nonneg_right (Nat.cast_nonneg n)
  have hfinite (n : ℕ) : IntegrableOn f (Set.Ioc (0 : ℝ) (b n)) μ := by
    have hinner : IntegrableOn f (Set.Ioc a (b n)) μ := by
      dsimp [μ]
      exact integrableOn_modelScaleInterval_of_continuous ha f hfcont
    apply hinner.of_forall_sdiff_eq_zero measurableSet_Ioc
    intro t ht
    have htpos : 0 < t := ht.1.1
    have htba : t ≤ b n := ht.1.2
    have hnot : ¬ (a < t ∧ t ≤ b n) := by
      simpa only [Set.mem_Ioc] using ht.2
    have hta : t ≤ a := le_of_not_gt (fun hta ↦ hnot ⟨hta, htba⟩)
    exact hzero t htpos hta
  have hzeroOn : IntegrableOn f (Set.Ioc (0 : ℝ) a) μ := by
    apply integrableOn_zero.congr_fun
      (fun t ht ↦ (hzero t ht.1 ht.2).symm) measurableSet_Ioc
  have hzeroInterval : (∫ t in 0..a, f t ∂μ) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with t ht
    rw [Set.uIoc_of_le ha.le] at ht
    exact hzero t ht.1 ht.2
  have hsplit (n : ℕ) :
      (∫ t in Set.Ioc (0 : ℝ) (b n), f t ∂μ) =
        ∫ t in Set.Ioc a (b n), f t ∂μ := by
    have hinter : IntervalIntegrable f μ a (b n) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (hb n)).mpr
        (by
          dsimp [μ]
          exact integrableOn_modelScaleInterval_of_continuous ha f hfcont)
    calc
      (∫ t in Set.Ioc (0 : ℝ) (b n), f t ∂μ) =
          ∫ t in 0..b n, f t ∂μ :=
        (intervalIntegral.integral_of_le
          (show (0 : ℝ) ≤ b n by
            exact le_trans ha.le (hb n))).symm
      _ = (∫ t in 0..a, f t ∂μ) + ∫ t in a..b n, f t ∂μ :=
        (intervalIntegral.integral_add_adjacent_intervals
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mpr hzeroOn)
          hinter).symm
      _ = ∫ t in a..b n, f t ∂μ := by rw [hzeroInterval, zero_add]
      _ = ∫ t in Set.Ioc a (b n), f t ∂μ :=
        intervalIntegral.integral_of_le (hb n)
  have hboundNorm : ∀ n : ℕ, (∫ t in 0..b n, ‖f t‖ ∂μ) ≤ C := by
    intro n
    rw [intervalIntegral.integral_of_le
      (show (0 : ℝ) ≤ b n by exact le_trans ha.le (hb n))]
    change (∫ t in Set.Ioc (0 : ℝ) (b n), ‖f t‖ ∂μ) ≤ C
    rw [show (fun t : ℝ ↦ ‖f t‖) = f by
      funext t
      exact Real.norm_of_nonneg (hfnonneg t), hsplit n]
    dsimp [μ]
    exact hboundIoc (b n) (hb n)
  have hbTendsto : Tendsto b atTop atTop := by
    dsimp [b]
    exact tendsto_atTop_add_const_left _ a tendsto_natCast_atTop_atTop
  have hintegrable : IntegrableOn f (Set.Ioi (0 : ℝ)) μ :=
    integrableOn_Ioi_of_intervalIntegral_norm_bounded C 0 hfinite hbTendsto
      (Filter.Eventually.of_forall hboundNorm)
  have hboundActual : ∀ n : ℕ, (∫ t in 0..b n, f t ∂μ) ≤ C := by
    intro n
    calc
      (∫ t in 0..b n, f t ∂μ) = ∫ t in 0..b n, ‖f t‖ ∂μ := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [] with t ht
        exact (Real.norm_of_nonneg (hfnonneg t)).symm
      _ ≤ C := hboundNorm n
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hintegrable hbTendsto
  refine ⟨?_, ?_⟩
  · simpa only [μ] using hintegrable
  · change (∫ t in Set.Ioi (0 : ℝ), f t ∂μ) ≤ C
    exact le_of_tendsto hlim (Filter.Eventually.of_forall hboundActual)

/-- The scale majorant which remains after summing Fourier modes is globally
integrable, with the same Calderón constant as on finite scale intervals. -/
theorem integrableOn_and_integral_thirdConeScaleMajorant_Ioi
    (α : Anisotropy) (ξ : E3) (hξ : ξ 2 ≠ 0) :
    IntegrableOn (thirdConeScaleMajorant α ξ) (Set.Ioi (0 : ℝ))
        ((volume : Measure ℝ).withDensity cubeScaleDensity) ∧
      ∫ t in Set.Ioi (0 : ℝ), thirdConeScaleMajorant α ξ t
        ∂((volume : Measure ℝ).withDensity cubeScaleDensity) ≤
        cPsi ^ 3 / (α.weight 2 : ℝ) := by
  rcases exists_small_scale_zero_thirdConeScaleMajorant α ξ hξ
    with ⟨a, ha, hzero⟩
  exact integrableOn_and_integral_Ioi_of_small_zero_Ioc_bound
    (thirdConeScaleMajorant α ξ) a
    (cPsi ^ 3 / (α.weight 2 : ℝ)) ha
    (continuous_thirdConeScaleMajorant α ξ)
    (thirdConeScaleMajorant_nonneg α ξ)
    hzero
    (fun b hab ↦ integral_thirdConeScaleMajorant_Ioc_le
      α ξ a b ha hab hξ)

/-- The preceding all-positive-scale majorant bound also holds at zero active
frequency, where the annular cutoff makes the density identically zero. -/
theorem integrableOn_and_integral_thirdConeScaleMajorant_Ioi_all
    (α : Anisotropy) (ξ : E3) :
    IntegrableOn (thirdConeScaleMajorant α ξ) (Set.Ioi (0 : ℝ))
        ((volume : Measure ℝ).withDensity cubeScaleDensity) ∧
      ∫ t in Set.Ioi (0 : ℝ), thirdConeScaleMajorant α ξ t
        ∂((volume : Measure ℝ).withDensity cubeScaleDensity) ≤
        cPsi ^ 3 / (α.weight 2 : ℝ) := by
  by_cases hξ : ξ 2 = 0
  · have hzero : ∀ t : ℝ, thirdConeScaleMajorant α ξ t = 0 := by
      intro t
      have hpsi : conePsi (t ^ α.weight 2 * ξ 2) = 0 := by
        apply conePsi_eq_zero_of_abs_le_one
        simp [hξ]
      unfold thirdConeScaleMajorant thirdConeActiveDensity
      rw [hpsi]
      ring
    have hfun : thirdConeScaleMajorant α ξ = 0 := funext hzero
    rw [hfun]
    constructor
    · exact integrableOn_zero
    · simp
      exact div_nonneg (pow_nonneg cPsi_pos.le _)
        (Nat.cast_nonneg _)
  · exact integrableOn_and_integral_thirdConeScaleMajorant_Ioi α ξ hξ

/-- The degree-110 coefficient estimate has a scale-uniform absolutely
summable norm envelope.  The displayed constant is independent of the scale
and is the coefficient factor in the joint Fubini majorant. -/
theorem exists_uniform_tsum_norm_mFourierCoeff
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 < t →
      Summable (fun ν : Fin 3 → ℤ ↦
        ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν‖) ∧
      ∑' ν : Fin 3 → ℤ,
        ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν‖ ≤ B := by
  rcases exists_uniform_mFourierCoeff_unitTorusLocalizedSymbol_sourceWeight_110_decay
    α M m hm i with ⟨A, hA, hcoeff⟩
  let g : (Fin 3 → ℤ) → ℝ := fun ν ↦
    (A * M) *
      (sourceWeight ((standardModeOfInt ν : standardModeLattice) : E3))⁻¹ ^
        (10 : ℕ)
  have hAM : 0 ≤ A * M := mul_nonneg hA hm.nonneg
  have hg : Summable g := by
    change Summable ((fun z : standardModeLattice ↦
      (A * M) * (sourceWeight (z : E3))⁻¹ ^ (10 : ℕ)) ∘ standardModeOfInt)
    exact ((summable_standardMode_sourceWeight_inv).mul_left (A * M)).comp_injective
      standardModeOfInt_injective
  let B : ℝ := ∑' ν : Fin 3 → ℤ, g ν
  refine ⟨B, ?_, ?_⟩
  · dsimp [B]
    exact tsum_nonneg fun ν ↦
      mul_nonneg hAM (pow_nonneg (inv_nonneg.mpr (sourceWeight_pos _).le) _)
  · intro t ht
    have hpoint : ∀ ν : Fin 3 → ℤ,
        ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν‖ ≤
          g ν := by
      intro ν
      have h110 := hcoeff t ht ν
      have htail := scratch_sourceWeight_inv_pow_110_le_pow_10
        (standardModeOfInt ν)
      exact h110.trans (by
        simpa only [g] using mul_le_mul_of_nonneg_left htail hAM)
    have hnorm : Summable (fun ν : Fin 3 → ℤ ↦
        ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν‖) :=
      hg.of_nonneg_of_le (fun ν ↦ norm_nonneg _) hpoint
    refine ⟨hnorm, ?_⟩
    simpa only [B] using hnorm.tsum_le_tsum hpoint hg

/-- Each literal third-coordinate Fourier mode is bounded by the common
active Calderón density; importantly, the bound is independent of its mode. -/
theorem norm_thirdModeFrequencySymbol_le_scaleMajorant
    (α : Anisotropy) (ν : Fin 3 → ℤ) (t : ℝ) (ξ : E3) :
    ‖thirdModeFrequencySymbol α (standardModeOfInt ν) t ξ‖ ≤
      thirdConeScaleMajorant α ξ t := by
  have hgaussian (x : ℝ) : ‖(gaussian x : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (gaussian_nonneg x)]
    exact gaussian_le_one x
  have hphi (x : ℝ) : ‖(conePhi x : ℂ)‖ ≤ cPsi := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (conePhi_nonneg x)]
    exact conePhi_le_cPsi x
  have hpass (x : ℝ) :
      ‖(gaussian x : ℂ)‖ * ‖(conePhi x : ℂ)‖ ≤ cPsi := by
    calc
      ‖(gaussian x : ℂ)‖ * ‖(conePhi x : ℂ)‖ ≤ 1 * cPsi :=
        mul_le_mul (hgaussian x) (hphi x) (norm_nonneg _) (by norm_num)
      _ = cPsi := by ring
  have hchar (x : ℝ) : ‖(Real.fourierChar x : ℂ)‖ = 1 := Circle.norm_coe _
  have hactive (x : ℝ) :
      ‖(gaussianDeriv x : ℂ)‖ ^ 2 * ‖(conePsi x : ℂ)‖ =
        conePsi x * gaussianDeriv x ^ 2 := by
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (conePsi_nonneg x), sq_abs]
    ring
  have hactiveNonneg (x : ℝ) :
      0 ≤ ‖(gaussianDeriv x : ℂ)‖ ^ 2 * ‖(conePsi x : ℂ)‖ := by
    positivity
  have hchain :
      (‖(gaussian (t ^ α.weight 0 * ξ 0) : ℂ)‖ *
          ‖(conePhi (t ^ α.weight 0 * ξ 0) : ℂ)‖) *
        ((‖(gaussian (t ^ α.weight 1 * ξ 1) : ℂ)‖ *
            ‖(conePhi (t ^ α.weight 1 * ξ 1) : ℂ)‖) *
          (‖(gaussianDeriv (t ^ α.weight 2 * ξ 2) : ℂ)‖ ^ 2 *
            ‖(conePsi (t ^ α.weight 2 * ξ 2) : ℂ)‖)) ≤
        cPsi ^ 2 *
          (conePsi (t ^ α.weight 2 * ξ 2) *
            gaussianDeriv (t ^ α.weight 2 * ξ 2) ^ 2) := by
    have hsecond :
        (‖(gaussian (t ^ α.weight 1 * ξ 1) : ℂ)‖ *
            ‖(conePhi (t ^ α.weight 1 * ξ 1) : ℂ)‖) *
          (‖(gaussianDeriv (t ^ α.weight 2 * ξ 2) : ℂ)‖ ^ 2 *
            ‖(conePsi (t ^ α.weight 2 * ξ 2) : ℂ)‖) ≤
          cPsi *
            (‖(gaussianDeriv (t ^ α.weight 2 * ξ 2) : ℂ)‖ ^ 2 *
              ‖(conePsi (t ^ α.weight 2 * ξ 2) : ℂ)‖) :=
      mul_le_mul_of_nonneg_right
        (hpass (t ^ α.weight 1 * ξ 1))
        (hactiveNonneg (t ^ α.weight 2 * ξ 2))
    have hfirst :
        (‖(gaussian (t ^ α.weight 0 * ξ 0) : ℂ)‖ *
            ‖(conePhi (t ^ α.weight 0 * ξ 0) : ℂ)‖) *
          ((‖(gaussian (t ^ α.weight 1 * ξ 1) : ℂ)‖ *
              ‖(conePhi (t ^ α.weight 1 * ξ 1) : ℂ)‖) *
            (‖(gaussianDeriv (t ^ α.weight 2 * ξ 2) : ℂ)‖ ^ 2 *
              ‖(conePsi (t ^ α.weight 2 * ξ 2) : ℂ)‖)) ≤
          cPsi *
            (cPsi *
              (‖(gaussianDeriv (t ^ α.weight 2 * ξ 2) : ℂ)‖ ^ 2 *
                ‖(conePsi (t ^ α.weight 2 * ξ 2) : ℂ)‖)) :=
      mul_le_mul (hpass (t ^ α.weight 0 * ξ 0)) hsecond
        (mul_nonneg
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (hactiveNonneg (t ^ α.weight 2 * ξ 2)))
        cPsi_pos.le
    calc
      (‖(gaussian (t ^ α.weight 0 * ξ 0) : ℂ)‖ *
          ‖(conePhi (t ^ α.weight 0 * ξ 0) : ℂ)‖) *
        ((‖(gaussian (t ^ α.weight 1 * ξ 1) : ℂ)‖ *
            ‖(conePhi (t ^ α.weight 1 * ξ 1) : ℂ)‖) *
          (‖(gaussianDeriv (t ^ α.weight 2 * ξ 2) : ℂ)‖ ^ 2 *
            ‖(conePsi (t ^ α.weight 2 * ξ 2) : ℂ)‖)) ≤
          cPsi *
            (cPsi *
              (‖(gaussianDeriv (t ^ α.weight 2 * ξ 2) : ℂ)‖ ^ 2 *
                ‖(conePsi (t ^ α.weight 2 * ξ 2) : ℂ)‖)) := hfirst
      _ = cPsi ^ 2 *
          (conePsi (t ^ α.weight 2 * ξ 2) *
            gaussianDeriv (t ^ α.weight 2 * ξ 2) ^ 2) := by
          rw [hactive]
          ring
  unfold thirdModeFrequencySymbol thirdConeScaleMajorant
    thirdConeActiveDensity
  simp only [norm_mul, norm_pow, hchar, mul_one]
  simpa only [mul_assoc] using hchain

theorem continuous_thirdModeFrequencySymbol_frequency_joint
    (α : Anisotropy) (ν : Fin 3 → ℤ) :
    Continuous (fun p : ℝ × Frequency9 ↦
      thirdModeFrequencySymbol α (standardModeOfInt ν) p.1
        (-frequencyDiagonal p.2)) := by
  have hdiag : Continuous (fun p : ℝ × Frequency9 ↦ -frequencyDiagonal p.2) :=
    frequencyDiagonal.continuous.neg.comp continuous_snd
  have hcoord (j : Fin 3) : Continuous (fun p : ℝ × Frequency9 ↦
      (-frequencyDiagonal p.2) j) := by
    convert (coordinateProjection j).continuous.comp hdiag using 1
    ext p
    simp [coordinateProjection_apply]
  have harg (j : Fin 3) : Continuous (fun p : ℝ × Frequency9 ↦
      p.1 ^ α.weight j * (-frequencyDiagonal p.2) j) :=
    (continuous_fst.pow _).mul (hcoord j)
  have hg0 : Continuous (fun p : ℝ × Frequency9 ↦
      (gaussian (p.1 ^ α.weight 0 * (-frequencyDiagonal p.2) 0) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (gaussian_contDiff.continuous.comp (harg 0))
  have hp0 : Continuous (fun p : ℝ × Frequency9 ↦
      (conePhi (p.1 ^ α.weight 0 * (-frequencyDiagonal p.2) 0) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (conePhi_contDiff.continuous.comp (harg 0))
  have hg1 : Continuous (fun p : ℝ × Frequency9 ↦
      (gaussian (p.1 ^ α.weight 1 * (-frequencyDiagonal p.2) 1) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (gaussian_contDiff.continuous.comp (harg 1))
  have hp1 : Continuous (fun p : ℝ × Frequency9 ↦
      (conePhi (p.1 ^ α.weight 1 * (-frequencyDiagonal p.2) 1) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (conePhi_contDiff.continuous.comp (harg 1))
  have hd2 : Continuous (fun p : ℝ × Frequency9 ↦
      (gaussianDeriv (p.1 ^ α.weight 2 * (-frequencyDiagonal p.2) 2) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (continuous_gaussianDeriv.comp (harg 2))
  have hp2 : Continuous (fun p : ℝ × Frequency9 ↦
      (conePsi (p.1 ^ α.weight 2 * (-frequencyDiagonal p.2) 2) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (conePsi_contDiff.continuous.comp (harg 2))
  have hphasearg : Continuous (fun p : ℝ × Frequency9 ↦
      (8 : ℝ)⁻¹ * ((standardModeOfInt ν : E3) 0) *
          (p.1 ^ α.weight 0 * (-frequencyDiagonal p.2) 0) +
        (8 : ℝ)⁻¹ * ((standardModeOfInt ν : E3) 1) *
          (p.1 ^ α.weight 1 * (-frequencyDiagonal p.2) 1) +
        (8 : ℝ)⁻¹ * ((standardModeOfInt ν : E3) 2) *
          (p.1 ^ α.weight 2 * (-frequencyDiagonal p.2) 2)) :=
    ((continuous_const.mul (harg 0)).add
      (continuous_const.mul (harg 1))).add
        (continuous_const.mul (harg 2))
  have hphase : Continuous (fun p : ℝ × Frequency9 ↦
      (Real.fourierChar
        ((8 : ℝ)⁻¹ * ((standardModeOfInt ν : E3) 0) *
            (p.1 ^ α.weight 0 * (-frequencyDiagonal p.2) 0) +
          (8 : ℝ)⁻¹ * ((standardModeOfInt ν : E3) 1) *
            (p.1 ^ α.weight 1 * (-frequencyDiagonal p.2) 1) +
          (8 : ℝ)⁻¹ * ((standardModeOfInt ν : E3) 2) *
            (p.1 ^ α.weight 2 * (-frequencyDiagonal p.2) 2) : ℝ) : ℂ)) :=
    continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp hphasearg)
  unfold thirdModeFrequencySymbol
  exact (((hg0.mul hp0).mul (hg1.mul hp1)).mul
    ((hd2.pow 2).mul hp2)).mul hphase

/-- One literal localized third-cone Fourier mode, now as a function of both
positive scale and the nine frequency variables. -/
noncomputable def thirdModeFrequencyJointIntegrand
    (α : Anisotropy) (m : E3 → ℂ) (ν : Fin 3 → ℤ)
    (F : ModelComplexSchwartzInput) (p : ℝ × Frequency9) : ℂ :=
  (if 0 < p.1 then
    UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 p.1) ν else 0) *
      thirdModeFrequencySymbol α (standardModeOfInt ν) p.1
        (-frequencyDiagonal p.2) *
          frequencyKernel (F 0) (F 1) (F 2) (F 3) p.2

theorem measurable_thirdModeFrequencyJointIntegrand
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (ν : Fin 3 → ℤ) (F : ModelComplexSchwartzInput) :
    Measurable (thirdModeFrequencyJointIntegrand α m ν F) := by
  have hcoeff : Measurable (fun p : ℝ × Frequency9 ↦
      if 0 < p.1 then
        UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 p.1) ν else 0) :=
    (measurable_zeroExtended_mFourierCoeff_unitTorusLocalizedSymbol
      α M m hm 2 ν).comp measurable_fst
  have hsymbol : Measurable (fun p : ℝ × Frequency9 ↦
      thirdModeFrequencySymbol α (standardModeOfInt ν) p.1
        (-frequencyDiagonal p.2)) :=
    (continuous_thirdModeFrequencySymbol_frequency_joint α ν).measurable
  have hkernel : Measurable (fun p : ℝ × Frequency9 ↦
      frequencyKernel (F 0) (F 1) (F 2) (F 3) p.2) :=
    (frequencyKernel (F 0) (F 1) (F 2) (F 3)).continuous.measurable.comp
      measurable_snd
  exact (hcoeff.mul hsymbol).mul hkernel

/-- Uniform pointwise domination of the entire Fourier-mode family by the
integrable active scale majorant.  This is the exact coefficient-sum input
for the remaining joint scale/frequency Fubini step. -/
theorem exists_uniform_tsum_norm_coefficient_mul_thirdModeFrequencySymbol
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 < t → ∀ ξ : E3,
      Summable (fun ν : Fin 3 → ℤ ↦
        ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν *
          thirdModeFrequencySymbol α (standardModeOfInt ν) t ξ‖) ∧
      ∑' ν : Fin 3 → ℤ,
        ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν *
          thirdModeFrequencySymbol α (standardModeOfInt ν) t ξ‖ ≤
        B * thirdConeScaleMajorant α ξ t := by
  rcases exists_uniform_tsum_norm_mFourierCoeff α M m hm 2
    with ⟨B, hB, hcoeff⟩
  refine ⟨B, hB, ?_⟩
  intro t ht ξ
  rcases hcoeff t ht with ⟨hsum, htsum⟩
  let D : ℝ := thirdConeScaleMajorant α ξ t
  have hD : 0 ≤ D := thirdConeScaleMajorant_nonneg α ξ t
  have hproduct : Summable (fun ν : Fin 3 → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν‖ * D) :=
    hsum.mul_right D
  have hpoint : ∀ ν : Fin 3 → ℤ,
      ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν *
          thirdModeFrequencySymbol α (standardModeOfInt ν) t ξ‖ ≤
        ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν‖ * D := by
    intro ν
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (by
        simpa only [D] using
          norm_thirdModeFrequencySymbol_le_scaleMajorant α ν t ξ)
      (norm_nonneg _)
  have hsumModes : Summable (fun ν : Fin 3 → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν *
        thirdModeFrequencySymbol α (standardModeOfInt ν) t ξ‖) :=
    hproduct.of_nonneg_of_le (fun ν ↦ norm_nonneg _) hpoint
  refine ⟨hsumModes, ?_⟩
  calc
    ∑' ν : Fin 3 → ℤ,
        ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν *
          thirdModeFrequencySymbol α (standardModeOfInt ν) t ξ‖ ≤
        ∑' ν : Fin 3 → ℤ,
          ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν‖ * D :=
      hsumModes.tsum_le_tsum hpoint hproduct
    _ = (∑' ν : Fin 3 → ℤ,
          ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν‖) * D :=
      hsum.tsum_mul_right D
    _ ≤ B * D := mul_le_mul_of_nonneg_right htsum hD
    _ = B * thirdConeScaleMajorant α ξ t := by rfl

/-- The post-summation cone majorant times the Schwartz frequency kernel is
integrable jointly in positive scale and the nine frequency variables.  The
proof uses Fubini in the scale variable and the uniform Calderón mass bound. -/
theorem integrable_thirdConeScaleMajorant_times_frequencyKernel
    (α : Anisotropy) (F : ModelComplexSchwartzInput) :
    Integrable (fun p : ℝ × Frequency9 ↦
      thirdConeScaleMajorant α (-frequencyDiagonal p.2) p.1 *
        ‖frequencyKernel (F 0) (F 1) (F 2) (F 3) p.2‖)
      ((((volume : Measure ℝ).withDensity cubeScaleDensity).restrict
        (Set.Ioi (0 : ℝ))).prod frequencyMeasure) := by
  let μ : Measure ℝ := ((volume : Measure ℝ).withDensity cubeScaleDensity).restrict
    (Set.Ioi (0 : ℝ))
  let K : Frequency9 → ℂ := frequencyKernel (F 0) (F 1) (F 2) (F 3)
  let D : ℝ × Frequency9 → ℝ := fun p ↦
    thirdConeScaleMajorant α (-frequencyDiagonal p.2) p.1
  let H : ℝ × Frequency9 → ℝ := fun p ↦ D p * ‖K p.2‖
  let C : ℝ := cPsi ^ 3 / (α.weight 2 : ℝ)
  letI : (volume : Measure (E3 × E3)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  letI : (volume : Measure Frequency9).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (E3 × E3)) volume
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (pow_nonneg cPsi_pos.le _) (Nat.cast_nonneg _)
  have hK : Integrable K frequencyMeasure := by
    dsimp [K]
    rw [frequencyMeasure_eq_volume]
    exact (frequencyKernel (F 0) (F 1) (F 2) (F 3)).integrable
  have hDcont : Continuous D := by
    dsimp [D]
    have hdiag : Continuous (fun p : ℝ × Frequency9 ↦ -frequencyDiagonal p.2) :=
      frequencyDiagonal.continuous.neg.comp continuous_snd
    have hinput : Continuous (fun p : ℝ × Frequency9 ↦
        (p.1, -frequencyDiagonal p.2)) :=
      continuous_fst.prodMk hdiag
    change Continuous ((fun q : ℝ × E3 ↦
      thirdConeScaleMajorant α q.2 q.1) ∘
        fun p : ℝ × Frequency9 ↦ (p.1, -frequencyDiagonal p.2))
    exact (continuous_thirdConeScaleMajorant_joint α).comp hinput
  have hHmeas : AEStronglyMeasurable H (μ.prod frequencyMeasure) := by
    have hHcont : Continuous H := by
      dsimp [H]
      exact hDcont.mul
        (((frequencyKernel (F 0) (F 1) (F 2) (F 3)).continuous.norm).comp
          continuous_snd)
    exact hHcont.aestronglyMeasurable
  have hDint (ζ : Frequency9) :
      Integrable (fun t : ℝ ↦
        thirdConeScaleMajorant α (-frequencyDiagonal ζ) t) μ := by
    simpa only [μ, IntegrableOn] using
      (integrableOn_and_integral_thirdConeScaleMajorant_Ioi_all
        α (-frequencyDiagonal ζ)).1
  have hDle (ζ : Frequency9) :
      (∫ t : ℝ, thirdConeScaleMajorant α (-frequencyDiagonal ζ) t ∂μ) ≤ C := by
    simpa only [μ, C, IntegrableOn] using
      (integrableOn_and_integral_thirdConeScaleMajorant_Ioi_all
        α (-frequencyDiagonal ζ)).2
  have hHsection (ζ : Frequency9) : Integrable (fun t : ℝ ↦ H (t, ζ)) μ := by
    simpa only [H, D] using (hDint ζ).mul_const ‖K ζ‖
  have hJbound (ζ : Frequency9) :
      (∫ t : ℝ, ‖H (t, ζ)‖ ∂μ) ≤ C * ‖K ζ‖ := by
    have hnonneg (t : ℝ) : 0 ≤ H (t, ζ) := by
      dsimp [H, D]
      exact mul_nonneg
        (thirdConeScaleMajorant_nonneg α (-frequencyDiagonal ζ) t)
        (norm_nonneg _)
    rw [show (fun t : ℝ ↦ ‖H (t, ζ)‖) =
        (fun t ↦ thirdConeScaleMajorant α (-frequencyDiagonal ζ) t *
          ‖K ζ‖) by
      funext t
      exact Real.norm_of_nonneg (hnonneg t),
      integral_mul_const]
    exact mul_le_mul_of_nonneg_right (hDle ζ) (norm_nonneg _)
  have hJmeas : AEStronglyMeasurable
      (fun ζ : Frequency9 ↦ ∫ t : ℝ, ‖H (t, ζ)‖ ∂μ) frequencyMeasure := by
    simpa only [Prod.swap_prod_mk] using hHmeas.norm.prod_swap.integral_prod_right'
  have hJ : Integrable
      (fun ζ : Frequency9 ↦ ∫ t : ℝ, ‖H (t, ζ)‖ ∂μ) frequencyMeasure := by
    apply Integrable.mono' (hK.norm.const_mul C) hJmeas
    filter_upwards [] with ζ
    rw [Real.norm_of_nonneg (integral_nonneg fun t ↦ norm_nonneg (H (t, ζ)))]
    exact hJbound ζ
  change Integrable H (μ.prod frequencyMeasure)
  exact (integrable_prod_iff' hHmeas).mpr
    ⟨Filter.Eventually.of_forall hHsection, hJ⟩

/-- The literal joint scale--frequency integrals of the individual Fourier
modes have summable norms.  This is the precise Fubini hypothesis required
to exchange the mode series with both scale and frequency integration. -/
theorem summable_integral_norm_thirdModeFrequencyJointIntegrand
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (F : ModelComplexSchwartzInput) :
    Summable (fun ν : Fin 3 → ℤ ↦
      ∫ p : ℝ × Frequency9,
        ‖thirdModeFrequencyJointIntegrand α m ν F p‖
        ∂((((volume : Measure ℝ).withDensity cubeScaleDensity).restrict
          (Set.Ioi (0 : ℝ))).prod frequencyMeasure)) := by
  let μ : Measure ℝ := ((volume : Measure ℝ).withDensity cubeScaleDensity).restrict
    (Set.Ioi (0 : ℝ))
  let K : Frequency9 → ℂ := frequencyKernel (F 0) (F 1) (F 2) (F 3)
  let H : ℝ × Frequency9 → ℝ := fun p ↦
    thirdConeScaleMajorant α (-frequencyDiagonal p.2) p.1 * ‖K p.2‖
  rcases exists_uniform_mFourierCoeff_unitTorusLocalizedSymbol_sourceWeight_110_decay
    α M m hm 2 with ⟨A, hA, hcoeff⟩
  let g : (Fin 3 → ℤ) → ℝ := fun ν ↦
    (A * M) *
      (sourceWeight ((standardModeOfInt ν : standardModeLattice) : E3))⁻¹ ^
        (10 : ℕ)
  have hAM : 0 ≤ A * M := mul_nonneg hA hm.nonneg
  have hg_nonneg (ν : Fin 3 → ℤ) : 0 ≤ g ν := by
    dsimp [g]
    exact mul_nonneg hAM
      (pow_nonneg (inv_nonneg.mpr (sourceWeight_pos _).le) _)
  have hmajor : Summable g := by
    change Summable ((fun z : standardModeLattice ↦
      (A * M) * (sourceWeight (z : E3))⁻¹ ^ (10 : ℕ)) ∘ standardModeOfInt)
    exact ((summable_standardMode_sourceWeight_inv).mul_left (A * M)).comp_injective
      standardModeOfInt_injective
  have hHint : Integrable H (μ.prod frequencyMeasure) := by
    simpa only [H, μ, K] using
      integrable_thirdConeScaleMajorant_times_frequencyKernel α F
  have hHnonneg (p : ℝ × Frequency9) : 0 ≤ H p := by
    dsimp [H]
    exact mul_nonneg
      (thirdConeScaleMajorant_nonneg α (-frequencyDiagonal p.2) p.1)
      (norm_nonneg _)
  have hpoint (ν : Fin 3 → ℤ) (p : ℝ × Frequency9) :
      ‖thirdModeFrequencyJointIntegrand α m ν F p‖ ≤ g ν * H p := by
    by_cases ht : 0 < p.1
    · have h110 := hcoeff p.1 ht ν
      have htail := scratch_sourceWeight_inv_pow_110_le_pow_10
        (standardModeOfInt ν)
      have hcoef :
          ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 p.1) ν‖ ≤
            g ν :=
        h110.trans (by
          simpa only [g] using mul_le_mul_of_nonneg_left htail hAM)
      have hsymbol :=
        norm_thirdModeFrequencySymbol_le_scaleMajorant α ν p.1
          (-frequencyDiagonal p.2)
      unfold thirdModeFrequencyJointIntegrand
      rw [if_pos ht, norm_mul, norm_mul]
      calc
        ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 p.1) ν‖ *
            ‖thirdModeFrequencySymbol α (standardModeOfInt ν) p.1
              (-frequencyDiagonal p.2)‖ * ‖K p.2‖ ≤
            (g ν * thirdConeScaleMajorant α (-frequencyDiagonal p.2) p.1) *
              ‖K p.2‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hcoef hsymbol
              (norm_nonneg _) (hg_nonneg ν))
            (norm_nonneg _)
        _ = g ν * H p := by
          dsimp [H]
          ring
    · unfold thirdModeFrequencyJointIntegrand
      rw [if_neg ht]
      simp only [zero_mul, norm_zero]
      exact mul_nonneg (hg_nonneg ν) (hHnonneg p)
  have hGint (ν : Fin 3 → ℤ) :
      Integrable (thirdModeFrequencyJointIntegrand α m ν F)
        (μ.prod frequencyMeasure) := by
    apply Integrable.mono' (hHint.const_mul (g ν))
      (measurable_thirdModeFrequencyJointIntegrand α M m hm ν F).aestronglyMeasurable
    filter_upwards [] with p
    simpa only [mul_comm] using hpoint ν p
  let I : ℝ := ∫ p : ℝ × Frequency9, H p ∂(μ.prod frequencyMeasure)
  have hmajorI : Summable (fun ν : Fin 3 → ℤ ↦ g ν * I) := hmajor.mul_right I
  apply hmajorI.of_nonneg_of_le
  · intro ν
    exact integral_nonneg fun p ↦ norm_nonneg _
  · intro ν
    have hmajorInt : Integrable (fun p : ℝ × Frequency9 ↦ g ν * H p)
        (μ.prod frequencyMeasure) := hHint.const_mul (g ν)
    calc
      (∫ p : ℝ × Frequency9,
          ‖thirdModeFrequencyJointIntegrand α m ν F p‖
          ∂(μ.prod frequencyMeasure)) ≤
          ∫ p : ℝ × Frequency9, g ν * H p ∂(μ.prod frequencyMeasure) :=
        integral_mono (hGint ν).norm hmajorInt (hpoint ν)
      _ = g ν * ∫ p : ℝ × Frequency9, H p ∂(μ.prod frequencyMeasure) :=
        by rw [integral_const_mul]
      _ = g ν * I := by rfl

theorem integrable_thirdModeFrequencyJointIntegrand
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (ν : Fin 3 → ℤ) (F : ModelComplexSchwartzInput) :
    Integrable (thirdModeFrequencyJointIntegrand α m ν F)
      ((((volume : Measure ℝ).withDensity cubeScaleDensity).restrict
        (Set.Ioi (0 : ℝ))).prod frequencyMeasure) := by
  let μ : Measure ℝ := ((volume : Measure ℝ).withDensity cubeScaleDensity).restrict
    (Set.Ioi (0 : ℝ))
  let K : Frequency9 → ℂ := frequencyKernel (F 0) (F 1) (F 2) (F 3)
  let H : ℝ × Frequency9 → ℝ := fun p ↦
    thirdConeScaleMajorant α (-frequencyDiagonal p.2) p.1 * ‖K p.2‖
  rcases exists_uniform_mFourierCoeff_unitTorusLocalizedSymbol_sourceWeight_110_decay
    α M m hm 2 with ⟨A, hA, hcoeff⟩
  let g : ℝ := (A * M) *
    (sourceWeight ((standardModeOfInt ν : standardModeLattice) : E3))⁻¹ ^
      (10 : ℕ)
  have hAM : 0 ≤ A * M := mul_nonneg hA hm.nonneg
  have hg : 0 ≤ g := by
    dsimp [g]
    exact mul_nonneg hAM
      (pow_nonneg (inv_nonneg.mpr (sourceWeight_pos _).le) _)
  have hHint : Integrable H (μ.prod frequencyMeasure) := by
    simpa only [H, μ, K] using
      integrable_thirdConeScaleMajorant_times_frequencyKernel α F
  apply Integrable.mono' (hHint.const_mul g)
    (measurable_thirdModeFrequencyJointIntegrand α M m hm ν F).aestronglyMeasurable
  filter_upwards [] with p
  by_cases ht : 0 < p.1
  · have h110 := hcoeff p.1 ht ν
    have htail := scratch_sourceWeight_inv_pow_110_le_pow_10
      (standardModeOfInt ν)
    have hcoef :
        ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 p.1) ν‖ ≤ g :=
      h110.trans (by
        simpa only [g] using mul_le_mul_of_nonneg_left htail hAM)
    have hsymbol :=
      norm_thirdModeFrequencySymbol_le_scaleMajorant α ν p.1
        (-frequencyDiagonal p.2)
    unfold thirdModeFrequencyJointIntegrand
    rw [if_pos ht, norm_mul, norm_mul]
    calc
      ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 p.1) ν‖ *
          ‖thirdModeFrequencySymbol α (standardModeOfInt ν) p.1
            (-frequencyDiagonal p.2)‖ * ‖K p.2‖ ≤
          (g * thirdConeScaleMajorant α (-frequencyDiagonal p.2) p.1) *
            ‖K p.2‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hcoef hsymbol (norm_nonneg _) hg)
          (norm_nonneg _)
      _ = g * H p := by
        dsimp [H]
        ring
  · unfold thirdModeFrequencyJointIntegrand
    rw [if_neg ht]
    simp only [zero_mul, norm_zero]
    exact mul_nonneg hg
      (mul_nonneg
        (thirdConeScaleMajorant_nonneg α (-frequencyDiagonal p.2) p.1)
        (norm_nonneg _))

/-- Fubini for the fully literal joint third-cone Fourier modes.  The theorem
does not yet identify the pointwise sum with the cone integrand; that exact
identification is supplied by the following reconstruction bridge. -/
theorem hasSum_integral_thirdModeFrequencyJointIntegrand
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (F : ModelComplexSchwartzInput) :
    HasSum (fun ν : Fin 3 → ℤ ↦
      ∫ p : ℝ × Frequency9,
        thirdModeFrequencyJointIntegrand α m ν F p
        ∂((((volume : Measure ℝ).withDensity cubeScaleDensity).restrict
          (Set.Ioi (0 : ℝ))).prod frequencyMeasure))
      (∫ p : ℝ × Frequency9,
        ∑' ν : Fin 3 → ℤ,
          thirdModeFrequencyJointIntegrand α m ν F p
        ∂((((volume : Measure ℝ).withDensity cubeScaleDensity).restrict
          (Set.Ioi (0 : ℝ))).prod frequencyMeasure)) := by
  apply MeasureTheory.hasSum_integral_of_summable_integral_norm
  · intro ν
    exact integrable_thirdModeFrequencyJointIntegrand α M m hm ν F
  · exact summable_integral_norm_thirdModeFrequencyJointIntegrand
      α M m hm F

/-- A single literal joint mode integral is exactly the existing
scale-integrated `thirdModeFrequencyFullForm`. -/
theorem integral_thirdModeFrequencyJointIntegrand_eq_fullForm
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (ν : Fin 3 → ℤ) (F : ModelComplexSchwartzInput) :
    (∫ p : ℝ × Frequency9,
      thirdModeFrequencyJointIntegrand α m ν F p
      ∂((((volume : Measure ℝ).withDensity cubeScaleDensity).restrict
        (Set.Ioi (0 : ℝ))).prod frequencyMeasure)) =
      thirdModeFrequencyFullForm α (standardModeOfInt ν)
        (fun t ↦ if 0 < t then
          UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν else 0) F := by
  let μ : Measure ℝ := ((volume : Measure ℝ).withDensity cubeScaleDensity).restrict
    (Set.Ioi (0 : ℝ))
  have hG := integrable_thirdModeFrequencyJointIntegrand
    α M m hm ν F
  unfold thirdModeFrequencyFullForm
  change (∫ p : ℝ × Frequency9,
      thirdModeFrequencyJointIntegrand α m ν F p
      ∂(μ.prod frequencyMeasure)) =
      ∫ t : ℝ,
        (if 0 < t then
          UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν else 0) *
          thirdModeFrequencyForm α (standardModeOfInt ν) t F ∂μ
  rw [MeasureTheory.integral_prod _ hG]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := ht
  have hinner :
      (∫ ζ : Frequency9,
        thirdModeFrequencyJointIntegrand α m ν F (t, ζ)
        ∂frequencyMeasure) =
        (if 0 < t then
          UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν else 0) *
          thirdModeFrequencyForm α (standardModeOfInt ν) t F := by
    rw [show (∫ ζ : Frequency9,
        thirdModeFrequencyJointIntegrand α m ν F (t, ζ)
        ∂frequencyMeasure) =
        ∫ ζ : Frequency9,
          UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν *
            (thirdModeFrequencySymbol α (standardModeOfInt ν) t
              (-frequencyDiagonal ζ) *
              frequencyKernel (F 0) (F 1) (F 2) (F 3) ζ)
          ∂frequencyMeasure by
          apply integral_congr_ae
          filter_upwards [] with ζ
          unfold thirdModeFrequencyJointIntegrand
          simp only [if_pos htpos]
          ring,
      integral_const_mul]
    rw [if_pos htpos]
    unfold thirdModeFrequencyForm frequencyForm
    rfl
  exact hinner

/-- The literal third-cone frequency integrand after the Fourier modes have
been reconstructed, with the same zero extension in the scale variable. -/
noncomputable def thirdConeFrequencyJointIntegrand
    (α : Anisotropy) (m : E3 → ℂ)
    (F : ModelComplexSchwartzInput) (p : ℝ × Frequency9) : ℂ :=
  (if 0 < p.1 then
    thirdConeFrequencySymbol α m p.1 (-frequencyDiagonal p.2) else 0) *
      frequencyKernel (F 0) (F 1) (F 2) (F 3) p.2

/-- Pointwise reconstruction of the entire localized third cone from its
literal Fourier modes, now simultaneously in scale and frequency. -/
theorem hasSum_thirdModeFrequencyJointIntegrand
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (F : ModelComplexSchwartzInput) (p : ℝ × Frequency9) :
    HasSum (fun ν : Fin 3 → ℤ ↦
      thirdModeFrequencyJointIntegrand α m ν F p)
      (thirdConeFrequencyJointIntegrand α m F p) := by
  by_cases ht : 0 < p.1
  · have hmode := hasSum_thirdModeFrequencySymbols_eq_thirdConeTerm_global
      α M m hm p.1 ht (-frequencyDiagonal p.2)
    have hmode' : HasSum (fun ν : Fin 3 → ℤ ↦
        UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 p.1) ν *
          thirdModeFrequencySymbol α (standardModeOfInt ν) p.1
            (-frequencyDiagonal p.2))
        (thirdConeFrequencySymbol α m p.1 (-frequencyDiagonal p.2)) := by
      simpa only [thirdConeFrequencySymbol] using hmode
    simpa only [thirdModeFrequencyJointIntegrand,
      thirdConeFrequencyJointIntegrand, if_pos ht] using
      hmode'.mul_right (frequencyKernel (F 0) (F 1) (F 2) (F 3) p.2)
  · simp only [thirdModeFrequencyJointIntegrand,
      thirdConeFrequencyJointIntegrand, if_neg ht, zero_mul]
    exact hasSum_zero

/-- Joint scale--frequency Fubini plus pointwise Fourier reconstruction gives
the exact localized third-cone integral as a sum of literal modes. -/
theorem hasSum_integral_thirdModeFrequencyJointIntegrand_eq_thirdCone
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (F : ModelComplexSchwartzInput) :
    HasSum (fun ν : Fin 3 → ℤ ↦
      ∫ p : ℝ × Frequency9,
        thirdModeFrequencyJointIntegrand α m ν F p
        ∂((((volume : Measure ℝ).withDensity cubeScaleDensity).restrict
          (Set.Ioi (0 : ℝ))).prod frequencyMeasure))
      (∫ p : ℝ × Frequency9,
        thirdConeFrequencyJointIntegrand α m F p
        ∂((((volume : Measure ℝ).withDensity cubeScaleDensity).restrict
          (Set.Ioi (0 : ℝ))).prod frequencyMeasure)) := by
  have hFubini := hasSum_integral_thirdModeFrequencyJointIntegrand
    α M m hm F
  have htsum : (fun p : ℝ × Frequency9 ↦
      ∑' ν : Fin 3 → ℤ,
        thirdModeFrequencyJointIntegrand α m ν F p) =
      thirdConeFrequencyJointIntegrand α m F := by
    funext p
    exact (hasSum_thirdModeFrequencyJointIntegrand α M m hm F p).tsum_eq
  rw [htsum] at hFubini
  exact hFubini

/-- The exact all-scale third-cone reconstruction in the existing
`thirdModeFrequencyFullForm` interface.  This is the direct bridge from the
summable model forms to the literal localized cone integral. -/
theorem hasSum_thirdModeFrequencyFullForms_eq_thirdConeJointIntegral
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (F : ModelComplexSchwartzInput) :
    HasSum (fun ν : Fin 3 → ℤ ↦
      thirdModeFrequencyFullForm α (standardModeOfInt ν)
        (fun t ↦ if 0 < t then
          UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν else 0) F)
      (∫ p : ℝ × Frequency9,
        thirdConeFrequencyJointIntegrand α m F p
        ∂((((volume : Measure ℝ).withDensity cubeScaleDensity).restrict
          (Set.Ioi (0 : ℝ))).prod frequencyMeasure)) := by
  have h := hasSum_integral_thirdModeFrequencyJointIntegrand_eq_thirdCone
    α M m hm F
  have hleft : (fun ν : Fin 3 → ℤ ↦
      ∫ p : ℝ × Frequency9,
        thirdModeFrequencyJointIntegrand α m ν F p
        ∂((((volume : Measure ℝ).withDensity cubeScaleDensity).restrict
          (Set.Ioi (0 : ℝ))).prod frequencyMeasure)) =
      (fun ν : Fin 3 → ℤ ↦
        thirdModeFrequencyFullForm α (standardModeOfInt ν)
          (fun t ↦ if 0 < t then
            UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν else 0) F) := by
    funext ν
    exact integral_thirdModeFrequencyJointIntegrand_eq_fullForm
      α M m hm ν F
  rw [hleft] at h
  exact h

/-- The reconstructed third-cone multiplier itself is bounded by the same
active Calderón density, with the original multiplier constant as the only
extra factor. -/
theorem norm_thirdConeFrequencySymbol_le_scaleMajorant
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (t : ℝ) (ξ : E3) :
    ‖thirdConeFrequencySymbol α m t ξ‖ ≤
      M * thirdConeScaleMajorant α ξ t := by
  have hpass (x y : ℝ) : ‖(conePhi x : ℂ) * (conePhi y : ℂ)‖ ≤ cPsi ^ 2 := by
    rw [norm_mul]
    have hx : ‖(conePhi x : ℂ)‖ ≤ cPsi := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (conePhi_nonneg x)]
      exact conePhi_le_cPsi x
    have hy : ‖(conePhi y : ℂ)‖ ≤ cPsi := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (conePhi_nonneg y)]
      exact conePhi_le_cPsi y
    calc
      ‖(conePhi x : ℂ)‖ * ‖(conePhi y : ℂ)‖ ≤ cPsi * cPsi :=
        mul_le_mul hx hy (norm_nonneg _) cPsi_pos.le
      _ = cPsi ^ 2 := by ring
  have hactive (x : ℝ) :
      ‖(conePsi x * gaussianDeriv x ^ 2 : ℂ)‖ =
        conePsi x * gaussianDeriv x ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (conePsi_nonneg x), sq_abs]
  have hactive_nonneg (x : ℝ) : 0 ≤ conePsi x * gaussianDeriv x ^ 2 :=
    mul_nonneg (conePsi_nonneg x) (sq_nonneg _)
  unfold thirdConeFrequencySymbol thirdConeScaleMajorant
    thirdConeActiveDensity
  rw [norm_mul, norm_mul, hactive]
  have hleft : ‖m ξ‖ *
      (conePsi (t ^ α.weight 2 * ξ 2) *
        gaussianDeriv (t ^ α.weight 2 * ξ 2) ^ 2) ≤
      M * (conePsi (t ^ α.weight 2 * ξ 2) *
        gaussianDeriv (t ^ α.weight 2 * ξ 2) ^ 2) :=
    mul_le_mul_of_nonneg_right (hm.norm_le_all ξ)
      (hactive_nonneg (t ^ α.weight 2 * ξ 2))
  have hprod := mul_le_mul hleft
    (hpass (t ^ α.weight 0 * ξ 0) (t ^ α.weight 1 * ξ 1))
    (norm_nonneg ((conePhi (t ^ α.weight 0 * ξ 0) : ℂ) *
      (conePhi (t ^ α.weight 1 * ξ 1) : ℂ)))
    (mul_nonneg hm.nonneg
      (hactive_nonneg (t ^ α.weight 2 * ξ 2)))
  calc
    ‖m ξ‖ *
        (conePsi (t ^ α.weight 2 * ξ 2) *
          gaussianDeriv (t ^ α.weight 2 * ξ 2) ^ 2) *
        ‖(conePhi (t ^ α.weight 0 * ξ 0) : ℂ) *
          (conePhi (t ^ α.weight 1 * ξ 1) : ℂ)‖ ≤
        (M * (conePsi (t ^ α.weight 2 * ξ 2) *
          gaussianDeriv (t ^ α.weight 2 * ξ 2) ^ 2)) * cPsi ^ 2 := hprod
    _ = M * (cPsi ^ 2 *
        (conePsi (t ^ α.weight 2 * ξ 2) *
          gaussianDeriv (t ^ α.weight 2 * ξ 2) ^ 2)) := by ring

/-- Measurability of the literal reconstructed third-cone scale--frequency
integrand.  Unlike the mode integrands, this uses only measurability of the
original multiplier and continuity of the fixed cutoff factors. -/
theorem measurable_thirdConeFrequencyJointIntegrand
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (F : ModelComplexSchwartzInput) :
    Measurable (thirdConeFrequencyJointIntegrand α m F) := by
  have hdiag : Continuous (fun p : ℝ × Frequency9 ↦ -frequencyDiagonal p.2) :=
    frequencyDiagonal.continuous.neg.comp continuous_snd
  have hcoord (j : Fin 3) : Continuous (fun p : ℝ × Frequency9 ↦
      (-frequencyDiagonal p.2) j) := by
    convert (coordinateProjection j).continuous.comp hdiag using 1
    ext p
    simp [coordinateProjection_apply]
  have harg (j : Fin 3) : Continuous (fun p : ℝ × Frequency9 ↦
      p.1 ^ α.weight j * (-frequencyDiagonal p.2) j) :=
    (continuous_fst.pow _).mul (hcoord j)
  have hm' : Measurable (fun p : ℝ × Frequency9 ↦
      m (-frequencyDiagonal p.2)) :=
    hm.measurable.comp hdiag.measurable
  have hphi (j : Fin 3) : Measurable (fun p : ℝ × Frequency9 ↦
      (conePhi (p.1 ^ α.weight j * (-frequencyDiagonal p.2) j) : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (conePhi_contDiff.continuous.comp (harg j))).measurable
  have hpsi : Measurable (fun p : ℝ × Frequency9 ↦
      (conePsi (p.1 ^ α.weight 2 * (-frequencyDiagonal p.2) 2) : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (conePsi_contDiff.continuous.comp (harg 2))).measurable
  have hderiv : Measurable (fun p : ℝ × Frequency9 ↦
      (gaussianDeriv (p.1 ^ α.weight 2 * (-frequencyDiagonal p.2) 2) : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (continuous_gaussianDeriv.comp (harg 2))).measurable
  have hbase : Measurable (fun p : ℝ × Frequency9 ↦
      thirdConeFrequencySymbol α m p.1 (-frequencyDiagonal p.2)) := by
    unfold thirdConeFrequencySymbol
    exact (hm'.mul (hpsi.mul (hderiv.pow_const 2))).mul ((hphi 0).mul (hphi 1))
  have hzero : Measurable (fun p : ℝ × Frequency9 ↦
      if 0 < p.1 then
        thirdConeFrequencySymbol α m p.1 (-frequencyDiagonal p.2) else 0) :=
    hbase.ite (measurableSet_Ioi.preimage measurable_fst) measurable_const
  have hkernel : Measurable (fun p : ℝ × Frequency9 ↦
      frequencyKernel (F 0) (F 1) (F 2) (F 3) p.2) :=
    (frequencyKernel (F 0) (F 1) (F 2) (F 3)).continuous.measurable.comp
      measurable_snd
  exact hzero.mul hkernel

/-- Absolute integrability of the reconstructed third-cone joint integrand.
This is the scale--frequency version of the source majorant: the original
multiplier bound contributes `M`, while the integrable scalar factor is the
all-scale Calderón envelope times the Schwartz frequency kernel. -/
theorem integrable_thirdConeFrequencyJointIntegrand
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (F : ModelComplexSchwartzInput) :
    Integrable (thirdConeFrequencyJointIntegrand α m F)
      ((((volume : Measure ℝ).withDensity cubeScaleDensity).restrict
        (Set.Ioi (0 : ℝ))).prod frequencyMeasure) := by
  let μ : Measure ℝ := ((volume : Measure ℝ).withDensity cubeScaleDensity).restrict
    (Set.Ioi (0 : ℝ))
  let K : Frequency9 → ℂ := frequencyKernel (F 0) (F 1) (F 2) (F 3)
  let H : ℝ × Frequency9 → ℝ := fun p ↦
    thirdConeScaleMajorant α (-frequencyDiagonal p.2) p.1 * ‖K p.2‖
  have hH : Integrable H (μ.prod frequencyMeasure) := by
    simpa only [H, μ, K] using
      integrable_thirdConeScaleMajorant_times_frequencyKernel α F
  have hHnonneg (p : ℝ × Frequency9) : 0 ≤ H p := by
    dsimp [H]
    exact mul_nonneg
      (thirdConeScaleMajorant_nonneg α (-frequencyDiagonal p.2) p.1)
      (norm_nonneg _)
  apply Integrable.mono' (hH.norm.const_mul M)
    (measurable_thirdConeFrequencyJointIntegrand α M m hm F).aestronglyMeasurable
  filter_upwards [] with p
  by_cases ht : 0 < p.1
  · unfold thirdConeFrequencyJointIntegrand
    rw [if_pos ht, norm_mul]
    calc
      ‖thirdConeFrequencySymbol α m p.1 (-frequencyDiagonal p.2)‖ * ‖K p.2‖ ≤
          (M * thirdConeScaleMajorant α (-frequencyDiagonal p.2) p.1) *
            ‖K p.2‖ :=
        mul_le_mul_of_nonneg_right
          (norm_thirdConeFrequencySymbol_le_scaleMajorant α M m hm p.1
            (-frequencyDiagonal p.2))
          (norm_nonneg _)
      _ = M * ‖H p‖ := by
        rw [Real.norm_of_nonneg (hHnonneg p)]
        dsimp [H]
        ring
  · unfold thirdConeFrequencyJointIntegrand
    rw [if_neg ht]
    simp only [zero_mul, norm_zero]
    exact mul_nonneg hm.nonneg (norm_nonneg _)

/-- The literal third cone, expressed as the source's scale integral of its
fixed-scale `frequencyForm`. -/
noncomputable def thirdConeFrequencyFullForm
    (α : Anisotropy) (m : E3 → ℂ)
    (F : ModelComplexSchwartzInput) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ),
    frequencyForm (thirdConeFrequencySymbol α m t)
      (F 0) (F 1) (F 2) (F 3)
    ∂((volume : Measure ℝ).withDensity cubeScaleDensity)

/-- The joint integral is exactly the literal scale integral of the third
cone's `frequencyForm`; this is the final scale--frequency Fubini step. -/
theorem thirdConeJointIntegral_eq_frequencyFullForm
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (F : ModelComplexSchwartzInput) :
    (∫ p : ℝ × Frequency9,
      thirdConeFrequencyJointIntegrand α m F p
      ∂((((volume : Measure ℝ).withDensity cubeScaleDensity).restrict
        (Set.Ioi (0 : ℝ))).prod frequencyMeasure)) =
      thirdConeFrequencyFullForm α m F := by
  let μ : Measure ℝ := ((volume : Measure ℝ).withDensity cubeScaleDensity).restrict
    (Set.Ioi (0 : ℝ))
  have hG := integrable_thirdConeFrequencyJointIntegrand α M m hm F
  unfold thirdConeFrequencyFullForm
  change (∫ p : ℝ × Frequency9,
      thirdConeFrequencyJointIntegrand α m F p
      ∂(μ.prod frequencyMeasure)) =
      ∫ t : ℝ,
        frequencyForm (thirdConeFrequencySymbol α m t)
          (F 0) (F 1) (F 2) (F 3) ∂μ
  rw [MeasureTheory.integral_prod _ hG]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change (∫ ζ : Frequency9,
      thirdConeFrequencyJointIntegrand α m F (t, ζ)
      ∂frequencyMeasure) =
      frequencyForm (thirdConeFrequencySymbol α m t)
        (F 0) (F 1) (F 2) (F 3)
  have htpos : 0 < t := ht
  unfold thirdConeFrequencyJointIntegrand frequencyForm
  simp only [if_pos htpos]

/-- Full all-scale reconstruction of the third localized cone as the
absolutely summable series of literal Fourier-mode full forms. -/
theorem hasSum_thirdModeFrequencyFullForms_eq_thirdConeFrequencyFullForm
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (F : ModelComplexSchwartzInput) :
    HasSum (fun ν : Fin 3 → ℤ ↦
      thirdModeFrequencyFullForm α (standardModeOfInt ν)
        (fun t ↦ if 0 < t then
          UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν else 0) F)
      (thirdConeFrequencyFullForm α m F) := by
  rw [← thirdConeJointIntegral_eq_frequencyFullForm α M m hm F]
  exact hasSum_thirdModeFrequencyFullForms_eq_thirdConeJointIntegral
    α M m hm F

/-- The same literal third cone written in the source's physical
`multiplierForm` notation.  This definition is deliberately separate from
the Fourier-side one: identifying them requires a multiplier certificate for
the scale-dependent cone symbol. -/
noncomputable def thirdConeMultiplierFullForm
    (α : Anisotropy) (m : E3 → ℂ)
    (F : ModelComplexSchwartzInput) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ),
    multiplierForm (thirdConeFrequencySymbol α m t)
      (F 0) (F 1) (F 2) (F 3)
    ∂((volume : Measure ℝ).withDensity cubeScaleDensity)

/-- Conditional source-facing conversion of the reconstructed cone from its
frequency representation to `multiplierForm`.  The displayed hypothesis is
the exact missing infrastructure: a uniform anisotropic multiplier
certificate for the scale-dependent cone symbol at every positive scale. -/
theorem thirdConeFrequencyFullForm_eq_multiplierFullForm
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (F : ModelComplexSchwartzInput)
    (hcone : ∀ t : ℝ, 0 < t →
      Anisotropy.IsAnisotropicMultiplier α M
        (thirdConeFrequencySymbol α m t)) :
    thirdConeFrequencyFullForm α m F =
      thirdConeMultiplierFullForm α m F := by
  unfold thirdConeFrequencyFullForm thirdConeMultiplierFullForm
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact (multiplierForm_eq_frequencyForm α M
    (thirdConeFrequencySymbol α m t) (hcone t ht)
    (F 0) (F 1) (F 2) (F 3)).symm

end
end Twisted
end Auto
