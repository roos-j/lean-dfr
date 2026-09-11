/- Copyright (c) 2026. All rights reserved. -/
import Auto.Twisted.FourierCoeffDegree110Scratch

namespace Auto
namespace Twisted

open MeasureTheory Filter FourierTransform TopologicalSpace
open scoped BigOperators Convolution ENNReal FourierTransform NNReal Topology

noncomputable section

/-! ## Coordinate 2 (the default Fubini order) -/

/-- The raw cube coefficient with coordinate `2` integrated innermost. -/
noncomputable def scratch_nestedRawUnitFourierCoeff_last
    (α : Anisotropy) (m : E3 → ℂ) (i : Fin 3) (t : ℝ)
    (ν : Fin 3 → ℤ) : ℂ :=
  ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
    fourier (-ν 0) (x : UnitAddCircle) *
      ∫ y in (-(1 / 2 : ℝ))..(1 / 2),
        fourier (-ν 1) (y : UnitAddCircle) *
          fourierCoeffOn (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
            (fun z : ℝ ↦ localizedSymbolRaw α m i t
              (8 * x) (8 * y) (8 * z)) (ν 2)

/-- The default `(0,1,2)` Fubini ordering identifies the raw integral with
the last-coordinate nested coefficient. -/
theorem scratch_iteratedRawUnitFourierIntegral_eq_nestedLast
    (α : Anisotropy) (m : E3 → ℂ) (i : Fin 3) (t : ℝ)
    (ν : Fin 3 → ℤ) :
    (∫ x in fubini_unitIoc,
      ∫ y in fubini_unitIoc,
        ∫ z in fubini_unitIoc,
          UnitAddTorus.mFourier (-ν) (fun j ↦ (![x, y, z] j : UnitAddCircle)) *
            localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z)) =
      scratch_nestedRawUnitFourierCoeff_last α m i t ν := by
  have hab : -(1 / 2 : ℝ) < 1 / 2 := by norm_num
  have hcoeff (x y : ℝ) :
      fourierCoeffOn hab
          (fun z : ℝ ↦ localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z)) (ν 2) =
        ∫ z in fubini_unitIoc,
          fourier (-ν 2) (z : UnitAddCircle) *
            localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z) := by
    rw [fourierCoeffOn_eq_integral]
    rw [intervalIntegral.integral_of_le hab.le]
    norm_num [fubini_unitIoc, smul_eq_mul]
  unfold scratch_nestedRawUnitFourierCoeff_last
  simp_rw [hcoeff]
  simp only [intervalIntegral.integral_of_le hab.le]
  conv_rhs =>
    enter [2, x]
    rw [← MeasureTheory.integral_const_mul]
  conv_rhs =>
    enter [2, x, 2, y]
    rw [← MeasureTheory.integral_const_mul]
  conv_rhs =>
    enter [2, x, 2, y]
    rw [← MeasureTheory.integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  change (∫ y in fubini_unitIoc, _) =
    ∫ y in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2), _
  apply setIntegral_congr_fun measurableSet_Ioc
  intro y hy
  change (∫ z in fubini_unitIoc, _) = ∫ z in fubini_unitIoc, _
  apply setIntegral_congr_fun measurableSet_Ioc
  intro z hz
  change UnitAddTorus.mFourier (-ν) (fun j ↦ (![x, y, z] j : UnitAddCircle)) *
      localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z) =
    fourier (-ν 0) (x : UnitAddCircle) *
      (fourier (-ν 1) (y : UnitAddCircle) *
        (fourier (-ν 2) (z : UnitAddCircle) *
          localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z)))
  rw [scratch_rawUnitFourierIntegrand_apply]
  ring

/-- Exact reconstruction with coordinate `2` innermost. -/
theorem scratch_mFourierCoeff_unitTorusLocalizedSymbol_eq_nestedLast
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (ν : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν =
      scratch_nestedRawUnitFourierCoeff_last α m i t ν := by
  rw [scratch_mFourierCoeff_unitTorusLocalizedSymbol_eq_raw_unitCube]
  simp only [smul_eq_mul]
  have hcube : scratch_unitIocCube = fubini_unitIocCube := by rfl
  rw [hcube]
  rw [scratch_integral_fin3_unitIocCube_eq_iterated]
  · exact scratch_iteratedRawUnitFourierIntegral_eq_nestedLast α m i t ν
  · exact scratch_integrableOn_rawUnitFourierIntegrand α M m hm i ht ν

/-- The scale-eight last-coordinate raw slice is smooth through order 110. -/
theorem scratch_contDiff_raw_last_scaled
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    ContDiff ℝ 110 (fun z : ℝ ↦
      localizedSymbolRaw α m i t x y (8 * z)) := by
  change ContDiff ℝ 110
    (localizedSymbol α m i t ∘ fun z : ℝ ↦ frequencyAssemble3 x y (8 * z))
  let L : ℝ →L[ℝ] E3 :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (Anisotropy.coordinateDirection 2)
  have hslice : (fun z : ℝ ↦ frequencyAssemble3 x y (8 * z)) =
      fun z : ℝ ↦ L (8 * z) + frequencyAssemble3 x y 0 := by
    funext z
    ext j
    fin_cases j <;>
      simp [L, frequencyAssemble3_apply, coordinateDirection_apply]
  rw [hslice]
  apply (localizedSymbol_contDiff α M m hm i ht).comp
  fun_prop

/-- Compact support of the localized symbol gives zero boundary values for
every derivative of the last raw coordinate slice. -/
theorem scratch_iteratedDeriv_raw_last_scaled_unitBoundary
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (x y : ℝ) (k : ℕ) (hk : k ≤ 110) :
    iteratedDeriv k (fun z : ℝ ↦
      localizedSymbolRaw α m i t x y (8 * z)) (-(1 / 2 : ℝ)) = 0 ∧
      iteratedDeriv k (fun z : ℝ ↦
        localizedSymbolRaw α m i t x y (8 * z)) (1 / 2 : ℝ) = 0 := by
  apply scratch_iteratedDeriv_eq_zero_unitBoundary_of_contDiff 110 k
  · exact scratch_contDiff_raw_last_scaled α M m hm i ht x y
  · exact hk
  · intro z hz
    apply localizedSymbolRaw_eq_zero_of_coordinate_large α m i 2 t
    change 3 ≤ |8 * z|
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
    nlinarith

/-- Exact order-`k` chain rule for the last raw coordinate. -/
theorem scratch_iteratedDeriv_raw_last_scaled_eq_iteratedFDeriv_at_order
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (k : ℕ) (hk : k ≤ 110)
    (x y z : ℝ) :
    iteratedDeriv k (fun r : ℝ ↦
      localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * r)) z =
      (iteratedFDeriv ℝ k (localizedSymbol α m i t)
        (frequencyAssemble3 (8 * x) (8 * y) (8 * z)))
        (fun _ : Fin k ↦ (8 : ℝ) • Anisotropy.coordinateDirection 2) := by
  let L : ℝ →L[ℝ] E3 :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight ((8 : ℝ) • Anisotropy.coordinateDirection 2)
  let b : E3 := frequencyAssemble3 (8 * x) (8 * y) 0
  have hshift : ContDiff ℝ 110 (fun η : E3 ↦ localizedSymbol α m i t (η + b)) := by
    apply (localizedSymbol_contDiff α M m hm i ht).comp
    fun_prop
  have hslice : (fun r : ℝ ↦ localizedSymbolRaw α m i t
      (8 * x) (8 * y) (8 * r)) =
      (fun η : E3 ↦ localizedSymbol α m i t (η + b)) ∘ L := by
    funext r
    simp only [Function.comp_apply]
    change localizedSymbol α m i t (frequencyAssemble3 (8 * x) (8 * y) (8 * r)) =
      localizedSymbol α m i t (L r + b)
    congr 1
    ext j
    fin_cases j <;>
      simp [L, b, frequencyAssemble3_apply, coordinateDirection_apply] <;> ring
  rw [hslice, iteratedDeriv_eq_iteratedFDeriv]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right L hshift z
    (by exact_mod_cast hk)]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_comp_add_right]
  have hpoint : L z + b = frequencyAssemble3 (8 * x) (8 * y) (8 * z) := by
    ext j
    fin_cases j <;>
      simp [L, b, frequencyAssemble3_apply, coordinateDirection_apply] <;> ring
  have hdir : (fun _ : Fin k ↦ L (1 : ℝ)) =
      (fun _ : Fin k ↦ (8 : ℝ) • Anisotropy.coordinateDirection 2) := by
    funext j
    simp [L]
  rw [hpoint, hdir]

/-- Uniform 110-th derivative envelope in the last raw coordinate. -/
theorem scratch_exists_raw_last_scaled_110_deriv_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y z : ℝ,
      ‖iteratedDeriv 110 (fun r : ℝ ↦ localizedSymbolRaw α m i t
        (8 * x) (8 * y) (8 * r)) z‖ ≤ C * M := by
  rcases exists_localizedSymbol_derivative_bound α M m hm i ht 110 (by norm_num) with
    ⟨D, hD, hDbound⟩
  refine ⟨(8 : ℝ) ^ 110 * D, mul_nonneg (by positivity) hD, ?_⟩
  intro x y z
  rw [scratch_iteratedDeriv_raw_last_scaled_eq_iteratedFDeriv_at_order
    α M m hm i ht 110 (by norm_num) x y z]
  let F : ContinuousMultilinearMap ℝ (fun _ : Fin 110 ↦ E3) ℂ :=
    iteratedFDeriv ℝ 110 (localizedSymbol α m i t)
      (frequencyAssemble3 (8 * x) (8 * y) (8 * z))
  let v : Fin 110 → E3 := fun _ ↦ Anisotropy.coordinateDirection 2
  have hvnorm : ‖Anisotropy.coordinateDirection 2‖ = 1 := by
    simpa [Anisotropy.coordinateDirection] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one 2
  have hbase : ‖F v‖ ≤ D * M := by
    calc
      ‖F v‖ ≤ ‖F‖ * ∏ j, ‖v j‖ := F.le_opNorm v
      _ = ‖F‖ := by simp [v, hvnorm]
      _ ≤ D * M := hDbound _
  change ‖F (fun _ : Fin 110 ↦ (8 : ℝ) • Anisotropy.coordinateDirection 2)‖ ≤
    ((8 : ℝ) ^ 110 * D) * M
  calc
    ‖F (fun _ : Fin 110 ↦ (8 : ℝ) • Anisotropy.coordinateDirection 2)‖ =
        (8 : ℝ) ^ 110 * ‖F v‖ := by
      rw [show (fun _ : Fin 110 ↦ (8 : ℝ) • Anisotropy.coordinateDirection 2) =
          fun j ↦ (8 : ℝ) • v j by
        funext j
        rfl]
      rw [ContinuousMultilinearMap.map_smul_univ]
      norm_num
    _ ≤ (8 : ℝ) ^ 110 * (D * M) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = ((8 : ℝ) ^ 110 * D) * M := by ring

/-- 110-fold integration by parts in the last scaled raw coordinate. -/
theorem scratch_norm_fourierCoeffOn_raw_last_scaled_le_of_110_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (x y C : ℝ)
    (n : ℤ) (hn : n ≠ 0)
    (hbound : ∀ z ∈ Set.uIoc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
      ‖iteratedDeriv 110 (fun r : ℝ ↦
        localizedSymbolRaw α m i t x y (8 * r)) z‖ ≤ C) :
    ‖fourierCoeffOn (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
      (fun z : ℝ ↦ localizedSymbolRaw α m i t x y (8 * z)) n‖ ≤
      (2 * Real.pi * |(n : ℝ)|)⁻¹ ^ 110 * C := by
  let f : ℝ → ℂ := fun z ↦ localizedSymbolRaw α m i t x y (8 * z)
  have hf : ContDiff ℝ 110 f :=
    scratch_contDiff_raw_last_scaled α M m hm i ht x y
  have hboundary (r : ℕ) (hr : r < 110) :
      iteratedDeriv r f (1 / 2 : ℝ) = iteratedDeriv r f (-(1 / 2 : ℝ)) := by
    rcases scratch_iteratedDeriv_raw_last_scaled_unitBoundary
      α M m hm i ht x y r (le_of_lt hr) with ⟨hleft, hright⟩
    rw [hleft, hright]
  have hmain := scratch_norm_fourierCoeffOn_le_of_iteratedDeriv_bound
    (a := -(1 / 2 : ℝ)) (b := 1 / 2) (C := C)
    (by norm_num) hn 110 hf hboundary hbound
  convert hmain using 1 <;> norm_num

/-- The passive integrations preserve the last-coordinate inner bound. -/
theorem scratch_norm_nestedRawUnitFourierCoeff_last_le_of_last_bound
    (α : Anisotropy) (m : E3 → ℂ) (i : Fin 3) (t : ℝ)
    (ν : Fin 3 → ℤ) (B : ℝ)
    (hcoeff : ∀ x y : ℝ,
      ‖fourierCoeffOn (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
        (fun z : ℝ ↦ localizedSymbolRaw α m i t
          (8 * x) (8 * y) (8 * z)) (ν 2)‖ ≤ B) :
    ‖scratch_nestedRawUnitFourierCoeff_last α m i t ν‖ ≤ B := by
  unfold scratch_nestedRawUnitFourierCoeff_last
  calc
    ‖∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        fourier (-ν 0) (x : UnitAddCircle) *
          ∫ y in (-(1 / 2 : ℝ))..(1 / 2),
            fourier (-ν 1) (y : UnitAddCircle) *
              fourierCoeffOn (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
                (fun z : ℝ ↦ localizedSymbolRaw α m i t
                  (8 * x) (8 * y) (8 * z)) (ν 2)‖ ≤
        B * |(1 / 2 : ℝ) - (-(1 / 2 : ℝ))| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hxfourier : ‖fourier (-ν 0) (x : UnitAddCircle)‖ = 1 := Circle.norm_coe _
      rw [norm_mul, hxfourier, one_mul]
      calc
        ‖∫ y in (-(1 / 2 : ℝ))..(1 / 2),
            fourier (-ν 1) (y : UnitAddCircle) *
              fourierCoeffOn (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
                (fun z : ℝ ↦ localizedSymbolRaw α m i t
                  (8 * x) (8 * y) (8 * z)) (ν 2)‖ ≤
            B * |(1 / 2 : ℝ) - (-(1 / 2 : ℝ))| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro y hy
          have hyfourier : ‖fourier (-ν 1) (y : UnitAddCircle)‖ = 1 := Circle.norm_coe _
          rw [norm_mul, hyfourier, one_mul]
          exact hcoeff x y
        _ = B := by norm_num
    _ = B := by norm_num

/-- Degree-110 decay in lattice coordinate `2`, conditional on the raw
last-coordinate derivative envelope. -/
theorem scratch_norm_mFourierCoeff_unitTorusLocalizedSymbol_le_of_last_110_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t)
    (ν : Fin 3 → ℤ) (hν : ν 2 ≠ 0) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x y z : ℝ,
      ‖iteratedDeriv 110 (fun r : ℝ ↦ localizedSymbolRaw α m i t
        (8 * x) (8 * y) (8 * r)) z‖ ≤ C) :
    ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν‖ ≤
      (2 * Real.pi * |((ν 2 : ℤ) : ℝ)|)⁻¹ ^ 110 * C := by
  rw [scratch_mFourierCoeff_unitTorusLocalizedSymbol_eq_nestedLast α M m hm i ht ν]
  let B : ℝ := (2 * Real.pi * |((ν 2 : ℤ) : ℝ)|)⁻¹ ^ 110 * C
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity) hC
  apply scratch_norm_nestedRawUnitFourierCoeff_last_le_of_last_bound
    α m i t ν B
  intro x y
  exact scratch_norm_fourierCoeffOn_raw_last_scaled_le_of_110_bound
    α M m hm i ht (8 * x) (8 * y) C (ν 2) hν
    (fun z _ ↦ hbound x y z)

/-- Uniform degree-110 actual coefficient decay in coordinate `2`. -/
theorem scratch_exists_mFourierCoeff_unitTorusLocalizedSymbol_last_110_decay
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : Fin 3 → ℤ, ν 2 ≠ 0 →
      ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν‖ ≤
        (2 * Real.pi * |((ν 2 : ℤ) : ℝ)|)⁻¹ ^ 110 * (C * M) := by
  rcases scratch_exists_raw_last_scaled_110_deriv_bound α M m hm i ht with
    ⟨C, hC, hraw⟩
  refine ⟨C, hC, ?_⟩
  intro ν hν
  apply scratch_norm_mFourierCoeff_unitTorusLocalizedSymbol_le_of_last_110_bound
    α M m hm i ht ν hν (C * M) (mul_nonneg hC hm.nonneg)
  intro x y z
  exact hraw x y z

end

end Twisted
end Auto
