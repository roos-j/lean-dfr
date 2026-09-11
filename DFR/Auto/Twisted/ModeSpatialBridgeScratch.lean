/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Auto.Twisted.FourierModeKernelScratch
import Auto.Twisted.SpatialFubiniScratch

/-!
# Scratch bridge from one localized Fourier mode to the literal active spatial model

This file deliberately remains scratch-only.  It combines the checked finite-scale
Fourier-mode kernel package with the checked spatial/Fubini package, and records the
coefficient sign which the source absorbs into the model coefficient.
-/

namespace Auto
namespace Twisted

open MeasureTheory Filter FourierTransform
open scoped BigOperators Convolution ENNReal FourierTransform NNReal

noncomputable section

/-- At active coordinate three, the public literal active spatial profile is
the base literal spatial profile. -/
theorem scratch_LiteralActiveModelSpatialProfile_two
    (α : Anisotropy) (u : E3) (F : ModelComplexSchwartzInput)
    (t : ℝ) :
    LiteralActiveModelSpatialProfile α 2 u F t =
      LiteralModelSpatialProfile α u F t := by
  unfold LiteralActiveModelSpatialProfile
    LiteralComplexActiveInternal.scratch_LiteralActiveModelSpatialProfile
    LiteralModelSpatialProfile
    LiteralComplexInternal.scratch_LiteralModelSpatialProfile
  apply integral_congr_ae
  filter_upwards [] with x
  exact LiteralActiveModelSpatialIntegrand_two α u F t x

/-- The public active-coordinate spatial profile obeys the existing
coordinate-permutation transport. -/
theorem scratch_LiteralActiveModelSpatialProfile_permute_to_two
    (α : Anisotropy) (σ : Equiv.Perm (Fin 3)) (i : Fin 3)
    (u : E3) (F : ModelComplexSchwartzInput) (hσ : σ 2 = i)
    (t : ℝ) :
    LiteralActiveModelSpatialProfile α i u F t =
      LiteralActiveModelSpatialProfile (permutedAnisotropy α σ) 2
        (coordinatePermutation σ u) (complexPermutedModelInput σ F) t := by
  simpa only [LiteralActiveModelSpatialProfile, complexPermutedModelInput] using
    LiteralComplexActiveInternal.scratch_LiteralActiveModelSpatialProfile_permute_to_two
      α σ i u F hσ t

/-- Negating a multiplier negates its four-linear frequency form. -/
theorem scratch_frequencyForm_neg
    (m : E3 → ℂ) (f₀ f₁ f₂ f₃ : SchwartzMap E3 ℂ) :
    frequencyForm (fun ξ ↦ -m ξ) f₀ f₁ f₂ f₃ =
      -frequencyForm m f₀ f₁ f₂ f₃ := by
  unfold frequencyForm
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with ζ
  ring

/-- For the source translation `ν / 8`, the literal spatial kernel symbol
is the negative of the positive localized third-coordinate Fourier-mode
symbol.  The one physical minus sign comes from the third kernel. -/
theorem scratch_literalModelScaleKernelSymbol_standardMode_eq_neg_thirdModeFrequencySymbol
    (α : Anisotropy) (ν : standardModeLattice) (t : ℝ) (ht : 0 < t) :
    scratch_literalModelScaleKernelSymbol α (standardModeTranslate ν) t =
      fun ξ ↦ -scratch_thirdModeFrequencySymbol α ν t ξ := by
  funext ξ
  unfold scratch_literalModelScaleKernelSymbol scratch_thirdModeFrequencySymbol
    scratch_complexDilatedModelLowKernel scratch_complexDilatedModelThirdKernel
  have h₀ := scratch_fourier_kernelDilate_ModelLowKernel_standardMode_neg
    ν 0 (t ^ α.weight 0) (ξ 0) (pow_pos ht _)
  have h₁ := scratch_fourier_kernelDilate_ModelLowKernel_standardMode_neg
    ν 1 (t ^ α.weight 1) (ξ 1) (pow_pos ht _)
  have h₂ := scratch_fourier_kernelDilate_ModelThirdKernel_standardMode_neg
    ν 2 (t ^ α.weight 2) (ξ 2) (pow_pos ht _)
  rw [h₀, h₁, h₂]
  rw [← scratch_fourierChar_three]
  ring

/-- The positive source Fourier-mode form equals the negative of the literal
third-active spatial profile. -/
theorem scratch_thirdModeFrequencyForm_eq_neg_LiteralActiveModelSpatialProfile
    (α : Anisotropy) (ν : standardModeLattice) (t : ℝ) (ht : 0 < t)
    (F : ModelComplexSchwartzInput) :
    scratch_thirdModeFrequencyForm α ν t F =
      -LiteralActiveModelSpatialProfile α 2 (standardModeTranslate ν) F t := by
  calc
    scratch_thirdModeFrequencyForm α ν t F =
        frequencyForm (scratch_thirdModeFrequencySymbol α ν t)
          (F 0) (F 1) (F 2) (F 3) := rfl
    _ = -frequencyForm
        (fun ξ ↦ -scratch_thirdModeFrequencySymbol α ν t ξ)
        (F 0) (F 1) (F 2) (F 3) := by
      rw [scratch_frequencyForm_neg]
      ring
    _ = -frequencyForm
        (scratch_literalModelScaleKernelSymbol α (standardModeTranslate ν) t)
        (F 0) (F 1) (F 2) (F 3) := by
      rw [scratch_literalModelScaleKernelSymbol_standardMode_eq_neg_thirdModeFrequencySymbol
        α ν t ht]
    _ = -LiteralModelSpatialProfile α (standardModeTranslate ν) F t := by
      rw [← scratch_LiteralModelSpatialProfile_eq_frequencyForm α
        (standardModeTranslate ν) F t ht]
    _ = -LiteralActiveModelSpatialProfile α 2 (standardModeTranslate ν) F t := by
      rw [scratch_LiteralActiveModelSpatialProfile_two]

/-- The one-mode spatial/Fourier sign bridge in any active coordinate, after
the standard source permutation has moved that coordinate to the third slot. -/
theorem scratch_thirdModeFrequencyForm_eq_neg_LiteralActiveModelSpatialProfile_permuted
    (α : Anisotropy) (σ : Equiv.Perm (Fin 3)) (i : Fin 3)
    (hσ : σ 2 = i) (ν : standardModeLattice) (t : ℝ) (ht : 0 < t)
    (F : ModelComplexSchwartzInput) :
    scratch_thirdModeFrequencyForm (permutedAnisotropy α σ) ν t
      (complexPermutedModelInput σ F) =
      -LiteralActiveModelSpatialProfile α i
        ((coordinatePermutation σ).symm (standardModeTranslate ν)) F t := by
  calc
    scratch_thirdModeFrequencyForm (permutedAnisotropy α σ) ν t
        (complexPermutedModelInput σ F) =
        -LiteralActiveModelSpatialProfile (permutedAnisotropy α σ) 2
          (standardModeTranslate ν) (complexPermutedModelInput σ F) t :=
      scratch_thirdModeFrequencyForm_eq_neg_LiteralActiveModelSpatialProfile
        (permutedAnisotropy α σ) ν t ht (complexPermutedModelInput σ F)
    _ = -LiteralActiveModelSpatialProfile α i
        ((coordinatePermutation σ).symm (standardModeTranslate ν)) F t := by
      rw [scratch_LiteralActiveModelSpatialProfile_permute_to_two α σ i
        ((coordinatePermutation σ).symm (standardModeTranslate ν)) F hσ]
      simp

/-- One localized positive Fourier mode with coefficient `a` is exactly the
literal third-active spatial mode with coefficient `-a`.  This is the sign
absorption in the coefficient `c_{i,ν}` of the source proof. -/
theorem scratch_thirdModeFrequencyMode_eq_LiteralActiveSpatialMode
    (α : Anisotropy) (ν : standardModeLattice) (t : ℝ) (ht : 0 < t)
    (a : ℂ) (F : ModelComplexSchwartzInput) :
    a * scratch_thirdModeFrequencyForm α ν t F =
      (-a) * LiteralActiveModelSpatialProfile α 2 (standardModeTranslate ν) F t := by
  rw [scratch_thirdModeFrequencyForm_eq_neg_LiteralActiveModelSpatialProfile
    α ν t ht F]
  ring

/-- The scale-integrated positive Fourier mode before passing through the
anisotropic-multiplier API. -/
noncomputable def scratch_thirdModeFrequencyFullForm
    (α : Anisotropy) (ν : standardModeLattice) (a : ℝ → ℂ)
    (F : ModelComplexSchwartzInput) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), a t * scratch_thirdModeFrequencyForm α ν t F
    ∂((volume : Measure ℝ).withDensity cubeScaleDensity)

/-- A complete localized positive Fourier mode is exactly a literal
third-active model form with the negated coefficient.  Thus the source
coefficient `c_{i,ν}` is obtained from a Fourier coefficient by precisely
this sign change (and its stated positive normalization). -/
theorem scratch_thirdModeFrequencyFullForm_eq_LiteralActiveModelFullForm
    (α : Anisotropy) (ν : standardModeLattice) (a : ℝ → ℂ)
    (F : ModelComplexSchwartzInput) :
    scratch_thirdModeFrequencyFullForm α ν a F =
      LiteralActiveModelFullForm α 2 (standardModeTranslate ν) (-a) F := by
  unfold scratch_thirdModeFrequencyFullForm LiteralActiveModelFullForm
    LiteralComplexActiveInternal.scratch_LiteralActiveModelFullForm
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change a t * scratch_thirdModeFrequencyForm α ν t F =
    (-a) t * LiteralActiveModelSpatialProfile α 2 (standardModeTranslate ν) F t
  simpa only [Pi.neg_apply] using
    scratch_thirdModeFrequencyMode_eq_LiteralActiveSpatialMode α ν t ht (a t) F

/-- The scale-integrated one-mode bridge in any active coordinate.  The mode
is written in the permuted coordinates in which that active coordinate is
the third coordinate. -/
theorem scratch_thirdModeFrequencyFullForm_eq_LiteralActiveModelFullForm_permuted
    (α : Anisotropy) (σ : Equiv.Perm (Fin 3)) (i : Fin 3)
    (hσ : σ 2 = i) (ν : standardModeLattice) (a : ℝ → ℂ)
    (F : ModelComplexSchwartzInput) :
    scratch_thirdModeFrequencyFullForm (permutedAnisotropy α σ) ν a
      (complexPermutedModelInput σ F) =
      LiteralActiveModelFullForm α i
        ((coordinatePermutation σ).symm (standardModeTranslate ν)) (-a) F := by
  calc
    scratch_thirdModeFrequencyFullForm (permutedAnisotropy α σ) ν a
        (complexPermutedModelInput σ F) =
        LiteralActiveModelFullForm (permutedAnisotropy α σ) 2
          (standardModeTranslate ν) (-a) (complexPermutedModelInput σ F) :=
      scratch_thirdModeFrequencyFullForm_eq_LiteralActiveModelFullForm
        (permutedAnisotropy α σ) ν a (complexPermutedModelInput σ F)
    _ = LiteralModelFullForm (permutedAnisotropy α σ)
        (standardModeTranslate ν) (-a) (complexPermutedModelInput σ F) :=
      LiteralActiveModelFullForm_two (permutedAnisotropy α σ)
        (standardModeTranslate ν) (-a) (complexPermutedModelInput σ F)
    _ = LiteralActiveModelFullForm α i
        ((coordinatePermutation σ).symm (standardModeTranslate ν)) (-a) F := by
      simpa using
        (LiteralActiveModelFullForm_permute_to_third α σ i
          ((coordinatePermutation σ).symm (standardModeTranslate ν)) (-a) F hσ).symm

/-- Conditional `multiplierForm` version of the one-mode spatial bridge.
The sole additional premise is the standard anisotropic multiplier certificate
for the localized mode symbol; Section 8's derivative package is intended to
supply this certificate. -/
theorem scratch_thirdModeMultiplier_eq_LiteralActiveSpatialMode
    (α : Anisotropy) (M : ℝ) (ν : standardModeLattice) (t : ℝ) (ht : 0 < t)
    (hm : Anisotropy.IsAnisotropicMultiplier α M
      (scratch_thirdModeFrequencySymbol α ν t))
    (a : ℂ) (F : ModelComplexSchwartzInput) :
    a * multiplierForm (scratch_thirdModeFrequencySymbol α ν t)
      (F 0) (F 1) (F 2) (F 3) =
      (-a) * LiteralActiveModelSpatialProfile α 2 (standardModeTranslate ν) F t := by
  rw [multiplierForm_eq_frequencyForm α M
    (scratch_thirdModeFrequencySymbol α ν t) hm (F 0) (F 1) (F 2) (F 3)]
  exact scratch_thirdModeFrequencyMode_eq_LiteralActiveSpatialMode α ν t ht a F

/-- The scale-integrated localized mode expressed via the existing
`multiplierForm` interface. -/
noncomputable def scratch_thirdModeMultiplierFullForm
    (α : Anisotropy) (ν : standardModeLattice) (a : ℝ → ℂ)
    (F : ModelComplexSchwartzInput) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), a t *
      multiplierForm (scratch_thirdModeFrequencySymbol α ν t)
        (F 0) (F 1) (F 2) (F 3)
    ∂((volume : Measure ℝ).withDensity cubeScaleDensity)

/-- Conditional source-facing one-mode bridge through `multiplierForm`.
The only premise is a uniform localized multiplier certificate at positive
scales; no spatial/Fourier interchange remains. -/
theorem scratch_thirdModeMultiplierFullForm_eq_LiteralActiveModelFullForm
    (α : Anisotropy) (M : ℝ) (ν : standardModeLattice) (a : ℝ → ℂ)
    (F : ModelComplexSchwartzInput)
    (hm : ∀ t : ℝ, 0 < t → Anisotropy.IsAnisotropicMultiplier α M
      (scratch_thirdModeFrequencySymbol α ν t)) :
    scratch_thirdModeMultiplierFullForm α ν a F =
      LiteralActiveModelFullForm α 2 (standardModeTranslate ν) (-a) F := by
  unfold scratch_thirdModeMultiplierFullForm LiteralActiveModelFullForm
    LiteralComplexActiveInternal.scratch_LiteralActiveModelFullForm
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change a t * multiplierForm (scratch_thirdModeFrequencySymbol α ν t)
      (F 0) (F 1) (F 2) (F 3) =
    (-a) t * LiteralActiveModelSpatialProfile α 2 (standardModeTranslate ν) F t
  simpa only [Pi.neg_apply] using
    scratch_thirdModeMultiplier_eq_LiteralActiveSpatialMode α M ν t ht (hm t ht) (a t) F

/-- Conditional any-active-coordinate version of the source-facing
one-mode `multiplierForm` bridge. -/
theorem scratch_thirdModeMultiplierFullForm_eq_LiteralActiveModelFullForm_permuted
    (α : Anisotropy) (M : ℝ) (σ : Equiv.Perm (Fin 3)) (i : Fin 3)
    (hσ : σ 2 = i) (ν : standardModeLattice) (a : ℝ → ℂ)
    (F : ModelComplexSchwartzInput)
    (hm : ∀ t : ℝ, 0 < t → Anisotropy.IsAnisotropicMultiplier
      (permutedAnisotropy α σ) M
      (scratch_thirdModeFrequencySymbol (permutedAnisotropy α σ) ν t)) :
    scratch_thirdModeMultiplierFullForm (permutedAnisotropy α σ) ν a
      (complexPermutedModelInput σ F) =
      LiteralActiveModelFullForm α i
        ((coordinatePermutation σ).symm (standardModeTranslate ν)) (-a) F := by
  calc
    scratch_thirdModeMultiplierFullForm (permutedAnisotropy α σ) ν a
        (complexPermutedModelInput σ F) =
        LiteralActiveModelFullForm (permutedAnisotropy α σ) 2
          (standardModeTranslate ν) (-a) (complexPermutedModelInput σ F) :=
      scratch_thirdModeMultiplierFullForm_eq_LiteralActiveModelFullForm
        (permutedAnisotropy α σ) M ν a (complexPermutedModelInput σ F) hm
    _ = LiteralModelFullForm (permutedAnisotropy α σ)
        (standardModeTranslate ν) (-a) (complexPermutedModelInput σ F) :=
      LiteralActiveModelFullForm_two (permutedAnisotropy α σ)
        (standardModeTranslate ν) (-a) (complexPermutedModelInput σ F)
    _ = LiteralActiveModelFullForm α i
        ((coordinatePermutation σ).symm (standardModeTranslate ν)) (-a) F := by
      simpa using
        (LiteralActiveModelFullForm_permute_to_third α σ i
          ((coordinatePermutation σ).symm (standardModeTranslate ν)) (-a) F hσ).symm

end
end Twisted
end Auto
