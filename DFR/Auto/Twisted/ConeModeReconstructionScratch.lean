/- Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
This file is a scratch investigation for the final cone/form decomposition.
-/
import Auto.Twisted.Twisted

namespace Auto
namespace Twisted

open MeasureTheory Filter FourierTransform TopologicalSpace
open scoped BigOperators Convolution ENNReal FourierTransform NNReal Topology

noncomputable section

#check UnitAddTorus.mFourier
#check UnitAddTorus.mFourierCoeff
#check HasSum.mul_left
#check HasSum.mul_right
#check hasSum_mFourier_series_localizedSymbol
#check UnitAddTorus.hasSum_mFourier_series_apply_of_summable
#check unitTorusPoint
#check standardModeOfInt_apply
#check thirdModeFrequencySymbol
#check localizedSymbol_dilate_cone_factor_identity

/-- Multiplication of the reconstructed localized symbol by a fixed cone
factor preserves its exact Fourier-series sum on the period-eight cube. -/
theorem scratch_hasSum_localizedSymbol_mode_times
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) (t : ℝ) (ht : 0 < t) (η : E3)
    (hη : ∀ j : Fin 3, η j ∈ Set.Ico (-4 : ℝ) 4)
    (B : ℂ) :
    HasSum (fun ν : Fin 3 → ℤ ↦
      UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν *
        (UnitAddTorus.mFourier ν (unitTorusPoint (η 0) (η 1) (η 2)) * B))
      (localizedSymbol α m i t η * B) := by
  have h := hasSum_mFourier_series_localizedSymbol α M m hm i t ht
    (η 0) (η 1) (η 2) (hη 0) (hη 1) (hη 2)
  have h' := h.mul_right B
  have hassemble : frequencyAssemble3 (η 0) (η 1) (η 2) = η := by
    ext j
    fin_cases j <;> simp [frequencyAssemble3_apply]
  rw [localizedSymbolRaw_apply, hassemble] at h'
  simpa only [mul_assoc] using h'

/-- The unit-torus character at a period-eight point is the source product
of the three real Fourier characters. -/
theorem scratch_unitTorus_mFourier_unitTorusPoint
    (ν : Fin 3 → ℤ) (x y z : ℝ) :
    UnitAddTorus.mFourier ν (unitTorusPoint x y z) =
      (Real.fourierChar ((ν 0 : ℝ) * x / 8) : ℂ) *
        ((Real.fourierChar ((ν 1 : ℝ) * y / 8) : ℂ) *
          (Real.fourierChar ((ν 2 : ℝ) * z / 8) : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, unitTorusPoint,
    Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  have h₁ : (Fin.succ 0 : Fin 3) = 1 := rfl
  have h₂ : (Fin.succ (Fin.succ 0) : Fin 3) = 2 := rfl
  rw [h₁, h₂]
  rw [fourier_coe_apply, fourier_coe_apply, fourier_coe_apply,
    Real.fourierChar_apply, Real.fourierChar_apply,
    Real.fourierChar_apply]
  congr 1 <;> push_cast <;> ring

/-- The source's third-coordinate Fourier-mode symbol is the torus Fourier
character times its fixed cone/Gaussian base factor. -/
theorem scratch_thirdModeFrequencySymbol_eq_torus_phase_mul_base
    (α : Anisotropy) (t : ℝ) (ξ : E3) (ν : Fin 3 → ℤ) :
    thirdModeFrequencySymbol α (standardModeOfInt ν) t ξ =
      (UnitAddTorus.mFourier ν
        (unitTorusPoint ((α.dilate t ξ) 0) ((α.dilate t ξ) 1)
          ((α.dilate t ξ) 2))) *
        (((gaussian (α.dilate t ξ 0) : ℂ) *
            (conePhi (α.dilate t ξ 0) : ℂ)) *
          ((gaussian (α.dilate t ξ 1) : ℂ) *
            (conePhi (α.dilate t ξ 1) : ℂ)) *
          ((gaussianDeriv (α.dilate t ξ 2) : ℂ) ^ 2 *
            (conePsi (α.dilate t ξ 2) : ℂ))) := by
  unfold thirdModeFrequencySymbol
  have h0 : (8 : ℝ)⁻¹ * ((standardModeOfInt ν : E3) 0) *
      (t ^ α.weight 0 * ξ 0) =
      (ν 0 : ℝ) * (α.dilate t ξ 0) / 8 := by
    simp [Anisotropy.dilate, standardModeOfInt_apply]
    ring
  have h1 : (8 : ℝ)⁻¹ * ((standardModeOfInt ν : E3) 1) *
      (t ^ α.weight 1 * ξ 1) =
      (ν 1 : ℝ) * (α.dilate t ξ 1) / 8 := by
    simp [Anisotropy.dilate, standardModeOfInt_apply]
    ring
  have h2 : (8 : ℝ)⁻¹ * ((standardModeOfInt ν : E3) 2) *
      (t ^ α.weight 2 * ξ 2) =
      (ν 2 : ℝ) * (α.dilate t ξ 2) / 8 := by
    simp [Anisotropy.dilate, standardModeOfInt_apply]
    ring
  have hd0 : α.dilate t ξ 0 = t ^ α.weight 0 * ξ 0 := by
    simp [Anisotropy.dilate]
  have hd1 : α.dilate t ξ 1 = t ^ α.weight 1 * ξ 1 := by
    simp [Anisotropy.dilate]
  have hd2 : α.dilate t ξ 2 = t ^ α.weight 2 * ξ 2 := by
    simp [Anisotropy.dilate]
  rw [h0, h1, h2, scratch_unitTorus_mFourier_unitTorusPoint,
    hd0, hd1, hd2]
  rw [← fourierChar_three]
  ring

/-- On the period-eight fundamental cube, Fourier reconstruction of the
localized third cone is already an exact sum of the literal source mode
symbols, before any frequency/scale Fubini interchange. -/
theorem scratch_hasSum_thirdModeFrequencySymbols_of_localized_reconstruction
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (t : ℝ) (ht : 0 < t) (ξ : E3)
    (hξcube : ∀ j : Fin 3, (α.dilate t ξ) j ∈ Set.Ico (-4 : ℝ) 4) :
    HasSum (fun ν : Fin 3 → ℤ ↦
      UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν *
        thirdModeFrequencySymbol α (standardModeOfInt ν) t ξ)
      (localizedSymbol α m 2 t (α.dilate t ξ) *
        (((gaussian (α.dilate t ξ 0) : ℂ) *
            (conePhi (α.dilate t ξ 0) : ℂ)) *
          ((gaussian (α.dilate t ξ 1) : ℂ) *
            (conePhi (α.dilate t ξ 1) : ℂ)) *
          ((gaussianDeriv (α.dilate t ξ 2) : ℂ) ^ 2 *
            (conePsi (α.dilate t ξ 2) : ℂ)))) := by
  let B : ℂ :=
    (((gaussian (α.dilate t ξ 0) : ℂ) *
        (conePhi (α.dilate t ξ 0) : ℂ)) *
      ((gaussian (α.dilate t ξ 1) : ℂ) *
        (conePhi (α.dilate t ξ 1) : ℂ)) *
      ((gaussianDeriv (α.dilate t ξ 2) : ℂ) ^ 2 *
        (conePsi (α.dilate t ξ 2) : ℂ)))
  have hsum := scratch_hasSum_localizedSymbol_mode_times
    α M m hm 2 t ht (α.dilate t ξ) hξcube B
  have hrewrite : (fun ν : Fin 3 → ℤ ↦
      UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν *
        ((UnitAddTorus.mFourier ν
          (unitTorusPoint ((α.dilate t ξ) 0) ((α.dilate t ξ) 1)
            ((α.dilate t ξ) 2))) * B)) =
      (fun ν : Fin 3 → ℤ ↦
        UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν *
          thirdModeFrequencySymbol α (standardModeOfInt ν) t ξ) := by
    funext ν
    rw [scratch_thirdModeFrequencySymbol_eq_torus_phase_mul_base]
  rw [hrewrite] at hsum
  simpa only [B] using hsum

/-- On the fundamental cube, the reconstructed third-coordinate Fourier modes
sum to the literal third cone summand of the Calderón decomposition.  This
is the pointwise algebraic step immediately before a mode/scale Fubini
interchange. -/
theorem scratch_hasSum_thirdModeFrequencySymbols_eq_thirdConeTerm
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (t : ℝ) (ht : 0 < t) (ξ : E3)
    (hξcube : ∀ j : Fin 3, (α.dilate t ξ) j ∈ Set.Ico (-4 : ℝ) 4) :
    HasSum (fun ν : Fin 3 → ℤ ↦
      UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν *
        thirdModeFrequencySymbol α (standardModeOfInt ν) t ξ)
      (m ξ *
        (conePsi (α.dilate t ξ 2) *
          gaussianDeriv (α.dilate t ξ 2) ^ 2 : ℂ) *
        ((conePhi (α.dilate t ξ 0) : ℂ) *
          (conePhi (α.dilate t ξ 1) : ℂ))) := by
  have hsum := scratch_hasSum_thirdModeFrequencySymbols_of_localized_reconstruction
    α M m hm t ht ξ hξcube
  have hcone := localizedSymbol_dilate_cone_factor_identity α m 2 ht ξ
  have hrewrite :
      localizedSymbol α m 2 t (α.dilate t ξ) *
          (((gaussian (α.dilate t ξ 0) : ℂ) *
              (conePhi (α.dilate t ξ 0) : ℂ)) *
            ((gaussian (α.dilate t ξ 1) : ℂ) *
              (conePhi (α.dilate t ξ 1) : ℂ)) *
            ((gaussianDeriv (α.dilate t ξ 2) : ℂ) ^ 2 *
              (conePsi (α.dilate t ξ 2) : ℂ))) =
        m ξ *
          (conePsi (α.dilate t ξ 2) *
            gaussianDeriv (α.dilate t ξ 2) ^ 2 : ℂ) *
          ((conePhi (α.dilate t ξ 0) : ℂ) *
            (conePhi (α.dilate t ξ 1) : ℂ)) := by
    convert hcone using 1 <;>
      simp [Fin.prod_univ_succ] <;>
      ring
  rw [hrewrite] at hsum
  exact hsum

/-- The fundamental-cube qualification in Fourier reconstruction is harmless
for the cone summand: outside that cube one of the compact frequency cutoffs
vanishes, and hence every Fourier mode vanishes as well. -/
theorem scratch_hasSum_thirdModeFrequencySymbols_eq_thirdConeTerm_global
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (t : ℝ) (ht : 0 < t) (ξ : E3) :
    HasSum (fun ν : Fin 3 → ℤ ↦
      UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν *
        thirdModeFrequencySymbol α (standardModeOfInt ν) t ξ)
      (m ξ *
        (conePsi (α.dilate t ξ 2) *
          gaussianDeriv (α.dilate t ξ 2) ^ 2 : ℂ) *
        ((conePhi (α.dilate t ξ 0) : ℂ) *
          (conePhi (α.dilate t ξ 1) : ℂ))) := by
  by_cases hcube : ∀ j : Fin 3, (α.dilate t ξ) j ∈ Set.Ico (-4 : ℝ) 4
  · exact scratch_hasSum_thirdModeFrequencySymbols_eq_thirdConeTerm
      α M m hm t ht ξ hcube
  · obtain ⟨j, hj⟩ : ∃ j : Fin 3,
        (α.dilate t ξ) j ∉ Set.Ico (-4 : ℝ) 4 := by
      by_contra h
      push_neg at h
      exact hcube h
    have hjlarge : 2 ≤ |(α.dilate t ξ) j| := by
      by_cases hneg : (α.dilate t ξ) j < -4
      · rw [abs_of_neg (by linarith)]
        linarith
      · have hlow : -4 ≤ (α.dilate t ξ) j := le_of_not_gt hneg
        have hhigh : 4 ≤ (α.dilate t ξ) j := by
          by_contra hnot
          have hlt : (α.dilate t ξ) j < 4 := lt_of_not_ge hnot
          exact hj ⟨hlow, hlt⟩
        rw [abs_of_nonneg (by linarith)]
        linarith
    have htermzero : ∀ ν : Fin 3 → ℤ,
        UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν *
          thirdModeFrequencySymbol α (standardModeOfInt ν) t ξ = 0 := by
      intro ν
      rw [scratch_thirdModeFrequencySymbol_eq_torus_phase_mul_base]
      fin_cases j
      · have h0 : 2 ≤ |(α.dilate t ξ) 0| := by simpa using hjlarge
        rw [conePhi_eq_zero_of_two_le_abs h0]
        simp
      · have h1 : 2 ≤ |(α.dilate t ξ) 1| := by simpa using hjlarge
        rw [conePhi_eq_zero_of_two_le_abs h1]
        simp
      · have h2 : 2 ≤ |(α.dilate t ξ) 2| := by simpa using hjlarge
        rw [conePsi_eq_zero_of_two_le_abs h2]
        simp
    have htargetzero :
        m ξ *
          (conePsi (α.dilate t ξ 2) *
            gaussianDeriv (α.dilate t ξ 2) ^ 2 : ℂ) *
          ((conePhi (α.dilate t ξ 0) : ℂ) *
            (conePhi (α.dilate t ξ 1) : ℂ)) = 0 := by
      fin_cases j
      · have h0 : 2 ≤ |(α.dilate t ξ) 0| := by simpa using hjlarge
        rw [conePhi_eq_zero_of_two_le_abs h0]
        simp
      · have h1 : 2 ≤ |(α.dilate t ξ) 1| := by simpa using hjlarge
        rw [conePhi_eq_zero_of_two_le_abs h1]
        simp
      · have h2 : 2 ≤ |(α.dilate t ξ) 2| := by simpa using hjlarge
        rw [conePsi_eq_zero_of_two_le_abs h2]
        simp
    rw [htargetzero]
    simpa only [htermzero] using
      (hasSum_zero : HasSum (fun _ : Fin 3 → ℤ ↦ (0 : ℂ)) 0)

/-- The third summand in the source's three-cone Calderón multiplier after
the Gaussian factors have been cancelled by the localized symbol. -/
noncomputable def scratch_thirdConeFrequencySymbol
    (α : Anisotropy) (m : E3 → ℂ) (t : ℝ) : E3 → ℂ :=
  fun ξ ↦ m ξ *
    (conePsi (α.dilate t ξ 2) *
      gaussianDeriv (α.dilate t ξ 2) ^ 2 : ℂ) *
    ((conePhi (α.dilate t ξ 0) : ℂ) *
      (conePhi (α.dilate t ξ 1) : ℂ))

/-- The literal fixed-scale mode multiplier is continuous, independently of
the multiplier being decomposed. -/
theorem scratch_continuous_thirdModeFrequencySymbol
    (α : Anisotropy) (ν : Fin 3 → ℤ) (t : ℝ) :
    Continuous (thirdModeFrequencySymbol α (standardModeOfInt ν) t) := by
  unfold thirdModeFrequencySymbol
  have harg (j : Fin 3) : Continuous (fun ξ : E3 ↦
      t ^ α.weight j * ξ j) :=
    by
      convert ((t ^ α.weight j) • coordinateProjection j).continuous using 1
      ext ξ
      simp [coordinateProjection_apply, smul_apply, smul_eq_mul]
  have hg0 : Continuous (fun ξ : E3 ↦
      (gaussian (t ^ α.weight 0 * ξ 0) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (gaussian_contDiff.continuous.comp (harg 0))
  have hp0 : Continuous (fun ξ : E3 ↦
      (conePhi (t ^ α.weight 0 * ξ 0) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (conePhi_contDiff.continuous.comp (harg 0))
  have hg1 : Continuous (fun ξ : E3 ↦
      (gaussian (t ^ α.weight 1 * ξ 1) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (gaussian_contDiff.continuous.comp (harg 1))
  have hp1 : Continuous (fun ξ : E3 ↦
      (conePhi (t ^ α.weight 1 * ξ 1) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (conePhi_contDiff.continuous.comp (harg 1))
  have hd2 : Continuous (fun ξ : E3 ↦
      (gaussianDeriv (t ^ α.weight 2 * ξ 2) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (continuous_gaussianDeriv.comp (harg 2))
  have hp2 : Continuous (fun ξ : E3 ↦
      (conePsi (t ^ α.weight 2 * ξ 2) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (conePsi_contDiff.continuous.comp (harg 2))
  have hphasearg : Continuous (fun ξ : E3 ↦
      (8 : ℝ)⁻¹ * (standardModeOfInt ν : E3) 0 *
          (t ^ α.weight 0 * ξ 0) +
        (8 : ℝ)⁻¹ * (standardModeOfInt ν : E3) 1 *
          (t ^ α.weight 1 * ξ 1) +
        (8 : ℝ)⁻¹ * (standardModeOfInt ν : E3) 2 *
          (t ^ α.weight 2 * ξ 2)) :=
    ((continuous_const.mul (harg 0)).add
      (continuous_const.mul (harg 1))).add
        (continuous_const.mul (harg 2))
  have hphase : Continuous (fun ξ : E3 ↦
      (Real.fourierChar
        ((8 : ℝ)⁻¹ * (standardModeOfInt ν : E3) 0 *
            (t ^ α.weight 0 * ξ 0) +
          (8 : ℝ)⁻¹ * (standardModeOfInt ν : E3) 1 *
            (t ^ α.weight 1 * ξ 1) +
          (8 : ℝ)⁻¹ * (standardModeOfInt ν : E3) 2 *
            (t ^ α.weight 2 * ξ 2) : ℝ) : ℂ)) :=
    continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp hphasearg)
  exact (((hg0.mul hp0).mul (hg1.mul hp1)).mul ((hd2.pow 2).mul hp2)).mul hphase

/-- Every literal third-coordinate mode symbol has a common bounded
frequency envelope, independent of its lattice mode and its scale. -/
theorem scratch_exists_bound_thirdModeFrequencySymbol :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (α : Anisotropy) (ν : Fin 3 → ℤ)
      (t : ℝ) (ξ : E3),
      ‖thirdModeFrequencySymbol α (standardModeOfInt ν) t ξ‖ ≤ B := by
  rcases exists_bound_gaussianDeriv with ⟨D, hD, hderiv⟩
  refine ⟨2 * cPsi ^ 2 * D ^ 2, by positivity, ?_⟩
  intro α ν t ξ
  have hgaussian (x : ℝ) : ‖(gaussian x : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (gaussian_nonneg x)]
    exact gaussian_le_one x
  have hphi (x : ℝ) : ‖(conePhi x : ℂ)‖ ≤ cPsi := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (conePhi_nonneg x)]
    exact conePhi_le_cPsi x
  have hpsi (x : ℝ) : ‖(conePsi x : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (conePsi_nonneg x)]
    unfold conePsi
    linarith [standardFrequencyBump_le_one (4 * (x - 3 / 2)),
      standardFrequencyBump_le_one (4 * (x + 3 / 2))]
  have hderivC (x : ℝ) : ‖(gaussianDeriv x : ℂ)‖ ≤ D := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hderiv x
  have hchar (x : ℝ) : ‖(Real.fourierChar x : ℂ)‖ = 1 := Circle.norm_coe _
  let η : E3 := α.dilate t ξ
  have h0 : ‖(gaussian (η 0) : ℂ)‖ * ‖(conePhi (η 0) : ℂ)‖ ≤ 1 * cPsi :=
    mul_le_mul (hgaussian (η 0)) (hphi (η 0)) (norm_nonneg _)
      (by norm_num)
  have h1 : ‖(gaussian (η 1) : ℂ)‖ * ‖(conePhi (η 1) : ℂ)‖ ≤ 1 * cPsi :=
    mul_le_mul (hgaussian (η 1)) (hphi (η 1)) (norm_nonneg _)
      (by norm_num)
  have hd : ‖(gaussianDeriv (η 2) : ℂ)‖ ^ 2 ≤ D ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hderivC (η 2)) 2
  have h2 : ‖(gaussianDeriv (η 2) : ℂ)‖ ^ 2 * ‖(conePsi (η 2) : ℂ)‖ ≤
      D ^ 2 * 2 :=
    mul_le_mul hd (hpsi (η 2)) (norm_nonneg _) (pow_nonneg hD _)
  have h12 :
      (‖(gaussian (η 1) : ℂ)‖ * ‖(conePhi (η 1) : ℂ)‖) *
        (‖(gaussianDeriv (η 2) : ℂ)‖ ^ 2 * ‖(conePsi (η 2) : ℂ)‖) ≤
      (1 * cPsi) * (D ^ 2 * 2) :=
    mul_le_mul h1 h2
      (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))
      (mul_nonneg (by norm_num) cPsi_pos.le)
  have hall :
      (‖(gaussian (η 0) : ℂ)‖ * ‖(conePhi (η 0) : ℂ)‖) *
        ((‖(gaussian (η 1) : ℂ)‖ * ‖(conePhi (η 1) : ℂ)‖) *
          (‖(gaussianDeriv (η 2) : ℂ)‖ ^ 2 * ‖(conePsi (η 2) : ℂ)‖)) ≤
      (1 * cPsi) * ((1 * cPsi) * (D ^ 2 * 2)) :=
    mul_le_mul h0 h12
      (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)))
      (mul_nonneg (by norm_num) cPsi_pos.le)
  have hη0 : t ^ α.weight 0 * ξ 0 = η 0 := by
    simp only [η, Anisotropy.dilate]
  have hη1 : t ^ α.weight 1 * ξ 1 = η 1 := by
    simp only [η, Anisotropy.dilate]
  have hη2 : t ^ α.weight 2 * ξ 2 = η 2 := by
    simp only [η, Anisotropy.dilate]
  unfold thirdModeFrequencySymbol
  rw [hη0, hη1, hη2]
  simp only [norm_mul, norm_pow, hchar, mul_one]
  calc
    _ ≤ (1 * cPsi) * ((1 * cPsi) * (D ^ 2 * 2)) := by
      convert hall using 1 <;> ring
    _ = 2 * cPsi ^ 2 * D ^ 2 := by ring

/-- Conditional frequency-side Fubini bridge for one localized third cone.
The hypotheses are exactly absolute summability of the mode-frequency
integrands; the conclusion has no hidden interchange of a sum and an
integral. -/
theorem scratch_hasSum_thirdModeFrequencyForms_eq_thirdConeFrequencyForm
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (t : ℝ) (ht : 0 < t) (F : ModelComplexSchwartzInput)
    (hintegrable : ∀ ν : Fin 3 → ℤ, Integrable
      (fun ζ : Frequency9 ↦
        (UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν *
          thirdModeFrequencySymbol α (standardModeOfInt ν) t
            (-frequencyDiagonal ζ)) *
          frequencyKernel (F 0) (F 1) (F 2) (F 3) ζ)
      frequencyMeasure)
    (hsummable : Summable (fun ν : Fin 3 → ℤ ↦
      ∫ ζ : Frequency9,
        ‖(UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν *
            thirdModeFrequencySymbol α (standardModeOfInt ν) t
              (-frequencyDiagonal ζ)) *
            frequencyKernel (F 0) (F 1) (F 2) (F 3) ζ‖
        ∂frequencyMeasure)) :
    HasSum (fun ν : Fin 3 → ℤ ↦
      UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν *
        thirdModeFrequencyForm α (standardModeOfInt ν) t F)
      (frequencyForm (scratch_thirdConeFrequencySymbol α m t)
        (F 0) (F 1) (F 2) (F 3)) := by
  let G : (Fin 3 → ℤ) → Frequency9 → ℂ := fun ν ζ ↦
    (UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν *
      thirdModeFrequencySymbol α (standardModeOfInt ν) t
        (-frequencyDiagonal ζ)) *
      frequencyKernel (F 0) (F 1) (F 2) (F 3) ζ
  have hGintegrable : ∀ ν : Fin 3 → ℤ, Integrable (G ν) frequencyMeasure := by
    intro ν
    simpa only [G] using hintegrable ν
  have hGsummable : Summable (fun ν : Fin 3 → ℤ ↦
      ∫ ζ : Frequency9, ‖G ν ζ‖ ∂frequencyMeasure) := by
    simpa only [G] using hsummable
  have hFubini := MeasureTheory.hasSum_integral_of_summable_integral_norm
    hGintegrable hGsummable
  have hleft : (fun ν : Fin 3 → ℤ ↦ ∫ ζ : Frequency9, G ν ζ ∂frequencyMeasure) =
      (fun ν : Fin 3 → ℤ ↦
        UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν *
          thirdModeFrequencyForm α (standardModeOfInt ν) t F) := by
    funext ν
    unfold G thirdModeFrequencyForm frequencyForm
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ζ
    ring
  have hright :
      (∫ ζ : Frequency9, ∑' ν : Fin 3 → ℤ, G ν ζ ∂frequencyMeasure) =
        frequencyForm (scratch_thirdConeFrequencySymbol α m t)
          (F 0) (F 1) (F 2) (F 3) := by
    unfold frequencyForm
    apply integral_congr_ae
    filter_upwards [] with ζ
    have hsum := scratch_hasSum_thirdModeFrequencySymbols_eq_thirdConeTerm_global
      α M m hm t ht (-frequencyDiagonal ζ)
    have hsum' := hsum.mul_right
      (frequencyKernel (F 0) (F 1) (F 2) (F 3) ζ)
    have hsum'' : HasSum (fun ν : Fin 3 → ℤ ↦ G ν ζ)
        (scratch_thirdConeFrequencySymbol α m t (-frequencyDiagonal ζ) *
          frequencyKernel (F 0) (F 1) (F 2) (F 3) ζ) := by
      simpa only [G, scratch_thirdConeFrequencySymbol, mul_assoc] using hsum'
    exact hsum''.tsum_eq
  rw [hleft, hright] at hFubini
  exact hFubini

/-- The fixed-scale third-cone Fourier series may be interchanged with the
`Frequency9` integral without any extra analytic premise.  Its domination is
the product of the absolutely summable torus coefficients, the uniform mode
symbol envelope, and the integrable Schwartz frequency kernel. -/
theorem scratch_hasSum_thirdModeFrequencyForms_eq_thirdConeFrequencyForm_of_multiplier
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (t : ℝ) (ht : 0 < t) (F : ModelComplexSchwartzInput) :
    HasSum (fun ν : Fin 3 → ℤ ↦
      UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν *
        thirdModeFrequencyForm α (standardModeOfInt ν) t F)
      (frequencyForm (scratch_thirdConeFrequencySymbol α m t)
        (F 0) (F 1) (F 2) (F 3)) := by
  rcases scratch_exists_bound_thirdModeFrequencySymbol with ⟨B, hB, hBbound⟩
  letI : (volume : Measure (E3 × E3)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  letI : (volume : Measure Frequency9).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (E3 × E3)) volume
  let a : (Fin 3 → ℤ) → ℂ := fun ν ↦
    UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m 2 t) ν
  let K : Frequency9 → ℂ := frequencyKernel (F 0) (F 1) (F 2) (F 3)
  let S : (Fin 3 → ℤ) → Frequency9 → ℂ := fun ν ζ ↦
    thirdModeFrequencySymbol α (standardModeOfInt ν) t (-frequencyDiagonal ζ)
  let G : (Fin 3 → ℤ) → Frequency9 → ℂ := fun ν ζ ↦
    (a ν * S ν ζ) * K ζ
  have hKint : Integrable K frequencyMeasure := by
    dsimp [K]
    rw [frequencyMeasure_eq_volume]
    exact (frequencyKernel (F 0) (F 1) (F 2) (F 3)).integrable
  have hSint : ∀ ν : Fin 3 → ℤ, Integrable (fun ζ : Frequency9 ↦
      S ν ζ * K ζ) frequencyMeasure := by
    intro ν
    have hcont : Continuous (S ν) := by
      dsimp [S]
      exact (scratch_continuous_thirdModeFrequencySymbol α ν t).comp
        (continuous_neg.comp frequencyDiagonal.continuous)
    have hKS : Integrable (fun ζ : Frequency9 ↦ K ζ * S ν ζ)
        frequencyMeasure :=
      hKint.mul_bdd hcont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ζ ↦ hBbound α ν t
          (-frequencyDiagonal ζ))
    exact hKS.congr (Filter.Eventually.of_forall fun ζ ↦ by
      dsimp [K, S]
      ring)
  have hGint : ∀ ν : Fin 3 → ℤ, Integrable (G ν) frequencyMeasure := by
    intro ν
    have h := (hSint ν).const_mul (a ν)
    exact h.congr (Filter.Eventually.of_forall fun ζ ↦ by
      dsimp [G]
      ring)
  have haSummable : Summable a := by
    dsimp [a]
    exact summable_mFourierCoeff_unitTorusLocalizedSymbol α M m hm 2 t ht
  have hmajor : Summable (fun ν : Fin 3 → ℤ ↦
      ‖a ν‖ * (B * ∫ ζ : Frequency9, ‖K ζ‖ ∂frequencyMeasure)) :=
    haSummable.norm.mul_right _
  have hGnormSummable : Summable (fun ν : Fin 3 → ℤ ↦
      ∫ ζ : Frequency9, ‖G ν ζ‖ ∂frequencyMeasure) := by
    apply hmajor.of_nonneg_of_le
    · intro ν
      exact integral_nonneg fun ζ ↦ norm_nonneg (G ν ζ)
    · intro ν
      have hrightint : Integrable (fun ζ : Frequency9 ↦
          ‖a ν‖ * (B * ‖K ζ‖)) frequencyMeasure := by
        have h := (hKint.norm.const_mul (‖a ν‖ * B))
        exact h.congr (Filter.Eventually.of_forall fun ζ ↦ by ring)
      calc
        (∫ ζ : Frequency9, ‖G ν ζ‖ ∂frequencyMeasure) ≤
            ∫ ζ : Frequency9, ‖a ν‖ * (B * ‖K ζ‖) ∂frequencyMeasure := by
          apply integral_mono (hGint ν).norm hrightint
          intro ζ
          dsimp [G]
          rw [norm_mul, norm_mul]
          calc
            ‖a ν‖ * ‖S ν ζ‖ * ‖K ζ‖ ≤
                (‖a ν‖ * B) * ‖K ζ‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left
                  (hBbound α ν t (-frequencyDiagonal ζ)) (norm_nonneg _))
                (norm_nonneg _)
            _ = ‖a ν‖ * (B * ‖K ζ‖) := by ring
        _ = ‖a ν‖ * (B * ∫ ζ : Frequency9, ‖K ζ‖ ∂frequencyMeasure) := by
          rw [show (fun ζ : Frequency9 ↦ ‖a ν‖ * (B * ‖K ζ‖)) =
              (fun ζ : Frequency9 ↦ (‖a ν‖ * B) * ‖K ζ‖) by
                funext ζ
                ring,
            integral_const_mul]
          ring
  apply scratch_hasSum_thirdModeFrequencyForms_eq_thirdConeFrequencyForm
    α M m hm t ht F
  · intro ν
    simpa only [a, S, K, G] using hGint ν
  · simpa only [a, S, K, G] using hGnormSummable

end
end Twisted
end Auto
