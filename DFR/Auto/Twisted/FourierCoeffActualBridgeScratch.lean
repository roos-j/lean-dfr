/- Copyright (c) 2026. All rights reserved. -/
import Auto.Twisted.FourierCoeffBridgeScratch
import Auto.Twisted.FourierCoeffFubiniScratch

namespace Auto
namespace Twisted

open MeasureTheory Filter FourierTransform TopologicalSpace
open scoped BigOperators Convolution ENNReal FourierTransform NNReal Topology

noncomputable section

/-- The raw Fourier integrand is continuous on Euclidean unit coordinates;
this supplies the compact-cube integrability required by literal Fubini. -/
theorem scratch_continuous_rawUnitFourierIntegrand
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (ν : Fin 3 → ℤ) :
    Continuous (fun u : Fin 3 → ℝ ↦
      UnitAddTorus.mFourier (-ν) (fun j ↦ (u j : UnitAddCircle)) *
        localizedSymbolRaw α m i t (8 * u 0) (8 * u 1) (8 * u 2)) := by
  have hlift : Continuous (fun u : Fin 3 → ℝ ↦
      fun j ↦ (u j : UnitAddCircle)) := by
    apply continuous_pi
    intro j
    exact (AddCircle.continuous_mk' 1).comp (continuous_apply j)
  have hchar : Continuous (fun u : Fin 3 → ℝ ↦
      UnitAddTorus.mFourier (-ν) (fun j ↦ (u j : UnitAddCircle))) :=
    (UnitAddTorus.mFourier (-ν)).continuous.comp hlift
  have hcoord : Continuous (fun u : Fin 3 → ℝ ↦
      (8 * u 0, (8 * u 1, 8 * u 2))) := by fun_prop
  have hraw : Continuous (fun u : Fin 3 → ℝ ↦
      localizedSymbolRaw α m i t (8 * u 0) (8 * u 1) (8 * u 2)) :=
    (continuous_localizedSymbolRaw α M m hm i ht).comp hcoord
  exact hchar.mul hraw

/-- The raw Fourier integrand is integrable on the literal half-open unit
cube. -/
theorem scratch_integrableOn_rawUnitFourierIntegrand
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (ν : Fin 3 → ℤ) :
    IntegrableOn (fun u : Fin 3 → ℝ ↦
      UnitAddTorus.mFourier (-ν) (fun j ↦ (u j : UnitAddCircle)) *
        localizedSymbolRaw α m i t (8 * u 0) (8 * u 1) (8 * u 2))
      fubini_unitIocCube := by
  have hcont := scratch_continuous_rawUnitFourierIntegrand α M m hm i ht ν
  have hlarge : IntegrableOn (fun u : Fin 3 → ℝ ↦
      UnitAddTorus.mFourier (-ν) (fun j ↦ (u j : UnitAddCircle)) *
        localizedSymbolRaw α m i t (8 * u 0) (8 * u 1) (8 * u 2))
      (Set.Icc (fun _ : Fin 3 ↦ -(1 / 2 : ℝ)) (fun _ : Fin 3 ↦ 1 / 2)) :=
    hcont.integrableOn_Icc
  apply hlarge.mono_set
  intro u hu
  simp only [Set.mem_Icc, Pi.le_def]
  constructor <;> intro j
  · exact (hu j (Set.mem_univ j)).1.le
  · exact (hu j (Set.mem_univ j)).2

theorem scratch_rawUnitFourierIntegrand_apply
    (α : Anisotropy) (m : E3 → ℂ) (i : Fin 3) (t : ℝ)
    (ν : Fin 3 → ℤ) (x y z : ℝ) :
    UnitAddTorus.mFourier (-ν) (fun j ↦ (![x, y, z] j : UnitAddCircle)) *
        localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z) =
      fourier (-ν 0) (x : UnitAddCircle) *
        fourier (-ν 1) (y : UnitAddCircle) *
          fourier (-ν 2) (z : UnitAddCircle) *
            localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply,
    Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  have h₁ : (Fin.succ 0 : Fin 3) = 1 := rfl
  have h₂ : (Fin.succ (Fin.succ 0) : Fin 3) = 2 := rfl
  rw [h₁, h₂]
  ring

/-- The `(1,2,0)` Fubini integral of the raw Fourier integrand is precisely
the nested coefficient whose innermost factor is `fourierCoeffOn`. -/
theorem scratch_iteratedRawUnitFourierIntegral_eq_nested
    (α : Anisotropy) (m : E3 → ℂ) (i : Fin 3) (t : ℝ)
    (ν : Fin 3 → ℤ) :
    (∫ y in fubini_unitIoc,
      ∫ z in fubini_unitIoc,
        ∫ x in fubini_unitIoc,
          UnitAddTorus.mFourier (-ν) (fun j ↦ (![x, y, z] j : UnitAddCircle)) *
            localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z)) =
      scratch_nestedRawUnitFourierCoeff α m i t ν := by
  have hab : -(1 / 2 : ℝ) < 1 / 2 := by norm_num
  have hcoeff (y z : ℝ) :
      fourierCoeffOn hab
          (fun x : ℝ ↦ localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z)) (ν 0) =
        ∫ x in fubini_unitIoc,
          fourier (-ν 0) (x : UnitAddCircle) *
            localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z) := by
    rw [fourierCoeffOn_eq_integral]
    rw [intervalIntegral.integral_of_le hab.le]
    norm_num [fubini_unitIoc, smul_eq_mul]
  unfold scratch_nestedRawUnitFourierCoeff
  simp_rw [hcoeff]
  simp only [intervalIntegral.integral_of_le hab.le]
  conv_rhs =>
    enter [2, y]
    rw [← MeasureTheory.integral_const_mul]
  conv_rhs =>
    enter [2, y, 2, z]
    rw [← MeasureTheory.integral_const_mul]
  conv_rhs =>
    enter [2, y, 2, z]
    rw [← MeasureTheory.integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro y hy
  change (∫ z in fubini_unitIoc, _) =
    ∫ z in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2), _
  apply setIntegral_congr_fun measurableSet_Ioc
  intro z hz
  change (∫ x in fubini_unitIoc, _) = ∫ x in fubini_unitIoc, _
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  change UnitAddTorus.mFourier (-ν) (fun j ↦ (![x, y, z] j : UnitAddCircle)) *
      localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z) =
    fourier (-ν 1) (y : UnitAddCircle) *
      (fourier (-ν 2) (z : UnitAddCircle) *
        (fourier (-ν 0) (x : UnitAddCircle) *
          localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z)))
  rw [scratch_rawUnitFourierIntegrand_apply]
  ring

/-- The actual torus Fourier coefficient is the ordered raw-cube coefficient.
The scale-eight change of variables stays literal in the raw symbol. -/
theorem scratch_mFourierCoeff_unitTorusLocalizedSymbol_eq_nestedRaw
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (ν : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν =
      scratch_nestedRawUnitFourierCoeff α m i t ν := by
  rw [scratch_mFourierCoeff_unitTorusLocalizedSymbol_eq_raw_unitCube]
  simp only [smul_eq_mul]
  have hcube : scratch_unitIocCube = fubini_unitIocCube := by
    rfl
  rw [hcube]
  rw [scratch_integral_fin3_unitIocCube_eq_iterated_120]
  · exact scratch_iteratedRawUnitFourierIntegral_eq_nested α m i t ν
  · exact scratch_integrableOn_rawUnitFourierIntegrand α M m hm i ht ν

/-- Four integrations by parts in the first unit-torus coordinate yield the
literal coefficient decay bound, conditional only on the corresponding raw
fourth-derivative envelope. -/
theorem scratch_norm_mFourierCoeff_unitTorusLocalizedSymbol_le_of_first_fourth_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t)
    (ν : Fin 3 → ℤ) (hν : ν 0 ≠ 0) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
      ∀ y ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
      ∀ z ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        ‖iteratedDeriv 4 (fun r : ℝ ↦ localizedSymbolRaw α m i t
          (8 * r) (8 * y) (8 * z)) x‖ ≤ C) :
    ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν‖ ≤
      (2 * Real.pi * |((ν 0 : ℤ) : ℝ)|)⁻¹ ^ 4 * C := by
  rw [scratch_mFourierCoeff_unitTorusLocalizedSymbol_eq_nestedRaw α M m hm i ht ν]
  exact scratch_norm_nestedRawUnitFourierCoeff_le_of_first_fourth_bound
    α M m hm i ht ν hν C hC hbound

end
end Twisted
end Auto
