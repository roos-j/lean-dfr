/- Copyright (c) 2026. All rights reserved. -/
import Auto.Twisted.FourierCoeffAllCoordinateScratch

namespace Auto
namespace Twisted

open MeasureTheory Filter FourierTransform TopologicalSpace
open scoped BigOperators Convolution ENNReal FourierTransform NNReal Topology

noncomputable section

/-! ## Coordinate 1 via the unit-cube coordinate swap -/

/-- The measure-preserving coordinate swap which turns the standard Fubini
order `(0,1,2)` into `(0,2,1)`. -/
noncomputable def scratch_fubini_swap12 :
    (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin 3 ↦ ℝ) (Equiv.swap 1 2)

theorem scratch_fubini_swap12_apply (x y z : ℝ) :
    scratch_fubini_swap12 ![x, y, z] = ![x, z, y] := by
  ext j
  fin_cases j <;> rfl

/-- The `0,2,1` Fubini ordering follows from the coordinate swap, avoiding a
second product-measure construction. -/
theorem scratch_integral_fin3_unitIocCube_eq_iterated_021
    (F : (Fin 3 → ℝ) → ℂ) (hF : IntegrableOn F fubini_unitIocCube) :
    ∫ u in fubini_unitIocCube, F u =
      ∫ x in fubini_unitIoc,
        ∫ z in fubini_unitIoc,
          ∫ y in fubini_unitIoc, F ![x, y, z] := by
  let μ : Fin 3 → Measure ℝ := fun _ ↦ volume.restrict fubini_unitIoc
  have hμ : volume.restrict fubini_unitIocCube = Measure.pi μ := by
    unfold fubini_unitIocCube μ
    rw [volume_pi, Measure.restrict_pi_pi]
  let e := scratch_fubini_swap12
  have hmp : MeasurePreserving e (Measure.pi μ) (Measure.pi μ) := by
    exact measurePreserving_piCongrLeft μ (Equiv.swap 1 2)
  have hFcomp : Integrable (F ∘ e) (Measure.pi μ) :=
    hmp.integrable_comp_of_integrable (by simpa only [IntegrableOn, hμ] using hF)
  have hFcompOn : IntegrableOn (F ∘ e) fubini_unitIocCube := by
    simpa only [IntegrableOn, hμ] using hFcomp
  calc
    ∫ u in fubini_unitIocCube, F u = ∫ u in fubini_unitIocCube, F (e u) := by
      change ∫ u, F u ∂volume.restrict fubini_unitIocCube =
        ∫ u, F (e u) ∂volume.restrict fubini_unitIocCube
      rw [hμ]
      symm
      exact hmp.integral_comp' F
    _ = ∫ x in fubini_unitIoc,
          ∫ y in fubini_unitIoc,
            ∫ z in fubini_unitIoc, (F ∘ e) ![x, y, z] :=
      scratch_integral_fin3_unitIocCube_eq_iterated (F ∘ e) hFcompOn
    _ = ∫ x in fubini_unitIoc,
          ∫ z in fubini_unitIoc,
            ∫ y in fubini_unitIoc, F ![x, y, z] := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with z
      apply integral_congr_ae
      filter_upwards [] with y
      rw [Function.comp_apply, scratch_fubini_swap12_apply]

/-- The raw cube coefficient with coordinate `1` integrated innermost. -/
noncomputable def scratch_nestedRawUnitFourierCoeff_middle
    (α : Anisotropy) (m : E3 → ℂ) (i : Fin 3) (t : ℝ)
    (ν : Fin 3 → ℤ) : ℂ :=
  ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
    fourier (-ν 0) (x : UnitAddCircle) *
      ∫ z in (-(1 / 2 : ℝ))..(1 / 2),
        fourier (-ν 2) (z : UnitAddCircle) *
          fourierCoeffOn (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
            (fun y : ℝ ↦ localizedSymbolRaw α m i t
              (8 * x) (8 * y) (8 * z)) (ν 1)

/-- The swapped Fubini order identifies the raw integral with the
middle-coordinate nested Fourier coefficient. -/
theorem scratch_iteratedRawUnitFourierIntegral_eq_nestedMiddle
    (α : Anisotropy) (m : E3 → ℂ) (i : Fin 3) (t : ℝ)
    (ν : Fin 3 → ℤ) :
    (∫ x in fubini_unitIoc,
      ∫ z in fubini_unitIoc,
        ∫ y in fubini_unitIoc,
          UnitAddTorus.mFourier (-ν) (fun j ↦ (![x, y, z] j : UnitAddCircle)) *
            localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z)) =
      scratch_nestedRawUnitFourierCoeff_middle α m i t ν := by
  have hab : -(1 / 2 : ℝ) < 1 / 2 := by norm_num
  have hcoeff (x z : ℝ) :
      fourierCoeffOn hab
          (fun y : ℝ ↦ localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z)) (ν 1) =
        ∫ y in fubini_unitIoc,
          fourier (-ν 1) (y : UnitAddCircle) *
            localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z) := by
    rw [fourierCoeffOn_eq_integral]
    rw [intervalIntegral.integral_of_le hab.le]
    norm_num [fubini_unitIoc, smul_eq_mul]
  unfold scratch_nestedRawUnitFourierCoeff_middle
  simp_rw [hcoeff]
  simp only [intervalIntegral.integral_of_le hab.le]
  conv_rhs =>
    enter [2, x]
    rw [← MeasureTheory.integral_const_mul]
  conv_rhs =>
    enter [2, x, 2, z]
    rw [← MeasureTheory.integral_const_mul]
  conv_rhs =>
    enter [2, x, 2, z]
    rw [← MeasureTheory.integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  change (∫ z in fubini_unitIoc, _) =
    ∫ z in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ), _
  apply setIntegral_congr_fun measurableSet_Ioc
  intro z hz
  change (∫ y in fubini_unitIoc, _) = ∫ y in fubini_unitIoc, _
  apply setIntegral_congr_fun measurableSet_Ioc
  intro y hy
  change UnitAddTorus.mFourier (-ν) (fun j ↦ (![x, y, z] j : UnitAddCircle)) *
      localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z) =
    fourier (-ν 0) (x : UnitAddCircle) *
      (fourier (-ν 2) (z : UnitAddCircle) *
        (fourier (-ν 1) (y : UnitAddCircle) *
          localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z)))
  rw [scratch_rawUnitFourierIntegrand_apply]
  ring

/-- Exact reconstruction with coordinate `1` innermost. -/
theorem scratch_mFourierCoeff_unitTorusLocalizedSymbol_eq_nestedMiddle
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (ν : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν =
      scratch_nestedRawUnitFourierCoeff_middle α m i t ν := by
  rw [scratch_mFourierCoeff_unitTorusLocalizedSymbol_eq_raw_unitCube]
  simp only [smul_eq_mul]
  have hcube : scratch_unitIocCube = fubini_unitIocCube := by rfl
  rw [hcube]
  rw [scratch_integral_fin3_unitIocCube_eq_iterated_021]
  · exact scratch_iteratedRawUnitFourierIntegral_eq_nestedMiddle α m i t ν
  · exact scratch_integrableOn_rawUnitFourierIntegrand α M m hm i ht ν

/-- Smoothness of the scale-eight middle-coordinate raw slice. -/
theorem scratch_contDiff_raw_middle_scaled
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (x z : ℝ) :
    ContDiff ℝ 110 (fun y : ℝ ↦
      localizedSymbolRaw α m i t x (8 * y) z) := by
  change ContDiff ℝ 110
    (localizedSymbol α m i t ∘ fun y : ℝ ↦ frequencyAssemble3 x (8 * y) z)
  let L : ℝ →L[ℝ] E3 :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (Anisotropy.coordinateDirection 1)
  have hslice : (fun y : ℝ ↦ frequencyAssemble3 x (8 * y) z) =
      fun y : ℝ ↦ L (8 * y) + frequencyAssemble3 x 0 z := by
    funext y
    ext j
    fin_cases j <;>
      simp [L, frequencyAssemble3_apply, coordinateDirection_apply]
  rw [hslice]
  apply (localizedSymbol_contDiff α M m hm i ht).comp
  fun_prop

/-- The compact raw support gives all middle-coordinate derivative boundary
values through order 110. -/
theorem scratch_iteratedDeriv_raw_middle_scaled_unitBoundary
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (x z : ℝ) (k : ℕ) (hk : k ≤ 110) :
    iteratedDeriv k (fun y : ℝ ↦
      localizedSymbolRaw α m i t x (8 * y) z) (-(1 / 2 : ℝ)) = 0 ∧
      iteratedDeriv k (fun y : ℝ ↦
        localizedSymbolRaw α m i t x (8 * y) z) (1 / 2 : ℝ) = 0 := by
  apply scratch_iteratedDeriv_eq_zero_unitBoundary_of_contDiff 110 k
  · exact scratch_contDiff_raw_middle_scaled α M m hm i ht x z
  · exact hk
  · intro y hy
    apply localizedSymbolRaw_eq_zero_of_coordinate_large α m i 1 t
    change 3 ≤ |8 * y|
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
    nlinarith

/-- Exact arbitrary-order chain rule for the middle raw coordinate. -/
theorem scratch_iteratedDeriv_raw_middle_scaled_eq_iteratedFDeriv_at_order
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (k : ℕ) (hk : k ≤ 110)
    (x z y : ℝ) :
    iteratedDeriv k (fun r : ℝ ↦
      localizedSymbolRaw α m i t (8 * x) (8 * r) (8 * z)) y =
      (iteratedFDeriv ℝ k (localizedSymbol α m i t)
        (frequencyAssemble3 (8 * x) (8 * y) (8 * z)))
        (fun _ : Fin k ↦ (8 : ℝ) • Anisotropy.coordinateDirection 1) := by
  let L : ℝ →L[ℝ] E3 :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight ((8 : ℝ) • Anisotropy.coordinateDirection 1)
  let b : E3 := frequencyAssemble3 (8 * x) 0 (8 * z)
  have hshift : ContDiff ℝ 110 (fun η : E3 ↦ localizedSymbol α m i t (η + b)) := by
    apply (localizedSymbol_contDiff α M m hm i ht).comp
    fun_prop
  have hslice : (fun r : ℝ ↦ localizedSymbolRaw α m i t
      (8 * x) (8 * r) (8 * z)) =
      (fun η : E3 ↦ localizedSymbol α m i t (η + b)) ∘ L := by
    funext r
    simp only [Function.comp_apply]
    change localizedSymbol α m i t (frequencyAssemble3 (8 * x) (8 * r) (8 * z)) =
      localizedSymbol α m i t (L r + b)
    congr 1
    ext j
    fin_cases j <;>
      simp [L, b, frequencyAssemble3_apply, coordinateDirection_apply] <;> ring
  rw [hslice, iteratedDeriv_eq_iteratedFDeriv]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right L hshift y
    (by exact_mod_cast hk)]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_comp_add_right]
  have hpoint : L y + b = frequencyAssemble3 (8 * x) (8 * y) (8 * z) := by
    ext j
    fin_cases j <;>
      simp [L, b, frequencyAssemble3_apply, coordinateDirection_apply] <;> ring
  have hdir : (fun _ : Fin k ↦ L (1 : ℝ)) =
      (fun _ : Fin k ↦ (8 : ℝ) • Anisotropy.coordinateDirection 1) := by
    funext j
    simp [L]
  rw [hpoint, hdir]

/-- Uniform 110-th derivative envelope in the middle raw coordinate. -/
theorem scratch_exists_raw_middle_scaled_110_deriv_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y z : ℝ,
      ‖iteratedDeriv 110 (fun r : ℝ ↦ localizedSymbolRaw α m i t
        (8 * x) (8 * r) (8 * z)) y‖ ≤ C * M := by
  rcases exists_localizedSymbol_derivative_bound α M m hm i ht 110 (by norm_num) with
    ⟨D, hD, hDbound⟩
  refine ⟨(8 : ℝ) ^ 110 * D, mul_nonneg (by positivity) hD, ?_⟩
  intro x y z
  rw [scratch_iteratedDeriv_raw_middle_scaled_eq_iteratedFDeriv_at_order
    α M m hm i ht 110 (by norm_num) x z y]
  let F : ContinuousMultilinearMap ℝ (fun _ : Fin 110 ↦ E3) ℂ :=
    iteratedFDeriv ℝ 110 (localizedSymbol α m i t)
      (frequencyAssemble3 (8 * x) (8 * y) (8 * z))
  let v : Fin 110 → E3 := fun _ ↦ Anisotropy.coordinateDirection 1
  have hvnorm : ‖Anisotropy.coordinateDirection 1‖ = 1 := by
    simpa [Anisotropy.coordinateDirection] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one 1
  have hbase : ‖F v‖ ≤ D * M := by
    calc
      ‖F v‖ ≤ ‖F‖ * ∏ j, ‖v j‖ := F.le_opNorm v
      _ = ‖F‖ := by simp [v, hvnorm]
      _ ≤ D * M := hDbound _
  change ‖F (fun _ : Fin 110 ↦ (8 : ℝ) • Anisotropy.coordinateDirection 1)‖ ≤
    ((8 : ℝ) ^ 110 * D) * M
  calc
    ‖F (fun _ : Fin 110 ↦ (8 : ℝ) • Anisotropy.coordinateDirection 1)‖ =
        (8 : ℝ) ^ 110 * ‖F v‖ := by
      rw [show (fun _ : Fin 110 ↦ (8 : ℝ) • Anisotropy.coordinateDirection 1) =
          fun j ↦ (8 : ℝ) • v j by
        funext j
        rfl]
      rw [ContinuousMultilinearMap.map_smul_univ]
      norm_num
    _ ≤ (8 : ℝ) ^ 110 * (D * M) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = ((8 : ℝ) ^ 110 * D) * M := by ring

/-- 110-fold integration by parts in the middle scaled raw coordinate. -/
theorem scratch_norm_fourierCoeffOn_raw_middle_scaled_le_of_110_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (x z C : ℝ)
    (n : ℤ) (hn : n ≠ 0)
    (hbound : ∀ y ∈ Set.uIoc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
      ‖iteratedDeriv 110 (fun r : ℝ ↦
        localizedSymbolRaw α m i t x (8 * r) z) y‖ ≤ C) :
    ‖fourierCoeffOn (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
      (fun y : ℝ ↦ localizedSymbolRaw α m i t x (8 * y) z) n‖ ≤
      (2 * Real.pi * |(n : ℝ)|)⁻¹ ^ 110 * C := by
  let f : ℝ → ℂ := fun y ↦ localizedSymbolRaw α m i t x (8 * y) z
  have hf : ContDiff ℝ 110 f :=
    scratch_contDiff_raw_middle_scaled α M m hm i ht x z
  have hboundary (r : ℕ) (hr : r < 110) :
      iteratedDeriv r f (1 / 2 : ℝ) = iteratedDeriv r f (-(1 / 2 : ℝ)) := by
    rcases scratch_iteratedDeriv_raw_middle_scaled_unitBoundary
      α M m hm i ht x z r (le_of_lt hr) with ⟨hleft, hright⟩
    rw [hleft, hright]
  have hmain := scratch_norm_fourierCoeffOn_le_of_iteratedDeriv_bound
    (a := -(1 / 2 : ℝ)) (b := 1 / 2) (C := C)
    (by norm_num) hn 110 hf hboundary hbound
  convert hmain using 1 <;> norm_num

/-- The two passive integrations preserve a uniform middle-coordinate bound. -/
theorem scratch_norm_nestedRawUnitFourierCoeff_middle_le_of_middle_bound
    (α : Anisotropy) (m : E3 → ℂ) (i : Fin 3) (t : ℝ)
    (ν : Fin 3 → ℤ) (B : ℝ)
    (hcoeff : ∀ x z : ℝ,
      ‖fourierCoeffOn (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
        (fun y : ℝ ↦ localizedSymbolRaw α m i t
          (8 * x) (8 * y) (8 * z)) (ν 1)‖ ≤ B) :
    ‖scratch_nestedRawUnitFourierCoeff_middle α m i t ν‖ ≤ B := by
  unfold scratch_nestedRawUnitFourierCoeff_middle
  calc
    ‖∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        fourier (-ν 0) (x : UnitAddCircle) *
          ∫ z in (-(1 / 2 : ℝ))..(1 / 2),
            fourier (-ν 2) (z : UnitAddCircle) *
              fourierCoeffOn (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
                (fun y : ℝ ↦ localizedSymbolRaw α m i t
                  (8 * x) (8 * y) (8 * z)) (ν 1)‖ ≤
        B * |(1 / 2 : ℝ) - (-(1 / 2 : ℝ))| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hxfourier : ‖fourier (-ν 0) (x : UnitAddCircle)‖ = 1 := Circle.norm_coe _
      rw [norm_mul, hxfourier, one_mul]
      calc
        ‖∫ z in (-(1 / 2 : ℝ))..(1 / 2),
            fourier (-ν 2) (z : UnitAddCircle) *
              fourierCoeffOn (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
                (fun y : ℝ ↦ localizedSymbolRaw α m i t
                  (8 * x) (8 * y) (8 * z)) (ν 1)‖ ≤
            B * |(1 / 2 : ℝ) - (-(1 / 2 : ℝ))| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro z hz
          have hzfourier : ‖fourier (-ν 2) (z : UnitAddCircle)‖ = 1 := Circle.norm_coe _
          rw [norm_mul, hzfourier, one_mul]
          exact hcoeff x z
        _ = B := by norm_num
    _ = B := by norm_num

/-- Degree-110 actual coefficient decay in lattice coordinate `1`. -/
theorem scratch_norm_mFourierCoeff_unitTorusLocalizedSymbol_le_of_middle_110_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t)
    (ν : Fin 3 → ℤ) (hν : ν 1 ≠ 0) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x y z : ℝ,
      ‖iteratedDeriv 110 (fun r : ℝ ↦ localizedSymbolRaw α m i t
        (8 * x) (8 * r) (8 * z)) y‖ ≤ C) :
    ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν‖ ≤
      (2 * Real.pi * |((ν 1 : ℤ) : ℝ)|)⁻¹ ^ 110 * C := by
  rw [scratch_mFourierCoeff_unitTorusLocalizedSymbol_eq_nestedMiddle α M m hm i ht ν]
  let B : ℝ := (2 * Real.pi * |((ν 1 : ℤ) : ℝ)|)⁻¹ ^ 110 * C
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity) hC
  apply scratch_norm_nestedRawUnitFourierCoeff_middle_le_of_middle_bound
    α m i t ν B
  intro x z
  exact scratch_norm_fourierCoeffOn_raw_middle_scaled_le_of_110_bound
    α M m hm i ht (8 * x) (8 * z) C (ν 1) hν
    (fun y _ ↦ hbound x y z)

/-- Uniform degree-110 actual coefficient decay in coordinate `1`. -/
theorem scratch_exists_mFourierCoeff_unitTorusLocalizedSymbol_middle_110_decay
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : Fin 3 → ℤ, ν 1 ≠ 0 →
      ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν‖ ≤
        (2 * Real.pi * |((ν 1 : ℤ) : ℝ)|)⁻¹ ^ 110 * (C * M) := by
  rcases scratch_exists_raw_middle_scaled_110_deriv_bound α M m hm i ht with
    ⟨C, hC, hraw⟩
  refine ⟨C, hC, ?_⟩
  intro ν hν
  apply scratch_norm_mFourierCoeff_unitTorusLocalizedSymbol_le_of_middle_110_bound
    α M m hm i ht ν hν (C * M) (mul_nonneg hC hm.nonneg)
  intro x y z
  exact hraw x y z

end

end Twisted
end Auto
