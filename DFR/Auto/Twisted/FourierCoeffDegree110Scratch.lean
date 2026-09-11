/- Copyright (c) 2026. All rights reserved. -/
import Auto.Twisted.FourierCoeffDegreeScratch

namespace Auto
namespace Twisted

open MeasureTheory Filter FourierTransform TopologicalSpace
open scoped BigOperators Convolution ENNReal FourierTransform NNReal Topology

noncomputable section

/-- The scale-eight first-coordinate raw slice has the exact `k`-th
derivative obtained by feeding `8 e₀` into every slot of the Fréchet
derivative. -/
theorem scratch_iteratedDeriv_raw_first_scaled_eq_iteratedFDeriv_at_order
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (k : ℕ) (hk : k ≤ 110)
    (y z r : ℝ) :
    iteratedDeriv k (fun x : ℝ ↦
      localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z)) r =
      (iteratedFDeriv ℝ k (localizedSymbol α m i t)
        (frequencyAssemble3 (8 * r) (8 * y) (8 * z)))
        (fun _ : Fin k ↦ (8 : ℝ) • Anisotropy.coordinateDirection 0) := by
  let L : ℝ →L[ℝ] E3 :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight ((8 : ℝ) • Anisotropy.coordinateDirection 0)
  let b : E3 := frequencyAssemble3 0 (8 * y) (8 * z)
  have hshift : ContDiff ℝ 110 (fun η : E3 ↦ localizedSymbol α m i t (η + b)) := by
    apply (localizedSymbol_contDiff α M m hm i ht).comp
    fun_prop
  have hslice : (fun x : ℝ ↦ localizedSymbolRaw α m i t
      (8 * x) (8 * y) (8 * z)) =
      (fun η : E3 ↦ localizedSymbol α m i t (η + b)) ∘ L := by
    funext x
    simp only [Function.comp_apply]
    change localizedSymbol α m i t (frequencyAssemble3 (8 * x) (8 * y) (8 * z)) =
      localizedSymbol α m i t (L x + b)
    congr 1
    ext j
    fin_cases j <;>
      simp [L, b, frequencyAssemble3_apply, coordinateDirection_apply] <;> ring
  rw [hslice, iteratedDeriv_eq_iteratedFDeriv]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right L hshift r
    (by exact_mod_cast hk)]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_comp_add_right]
  have hpoint : L r + b = frequencyAssemble3 (8 * r) (8 * y) (8 * z) := by
    ext j
    fin_cases j <;>
      simp [L, b, frequencyAssemble3_apply, coordinateDirection_apply] <;> ring
  have hdir : (fun _ : Fin k ↦ L (1 : ℝ)) =
      (fun _ : Fin k ↦ (8 : ℝ) • Anisotropy.coordinateDirection 0) := by
    funext j
    simp [L]
  rw [hpoint, hdir]

/-- The global 110-th Fréchet derivative envelope gives a uniform 110-th
one-dimensional raw derivative envelope in the first torus coordinate. -/
theorem scratch_exists_raw_first_scaled_110_deriv_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y z : ℝ,
      ‖iteratedDeriv 110 (fun r : ℝ ↦ localizedSymbolRaw α m i t
        (8 * r) (8 * y) (8 * z)) x‖ ≤ C * M := by
  rcases exists_localizedSymbol_derivative_bound α M m hm i ht 110 (by norm_num) with
    ⟨D, hD, hDbound⟩
  refine ⟨(8 : ℝ) ^ 110 * D, mul_nonneg (by positivity) hD, ?_⟩
  intro x y z
  rw [scratch_iteratedDeriv_raw_first_scaled_eq_iteratedFDeriv_at_order
    α M m hm i ht 110 (by norm_num) y z x]
  let F : ContinuousMultilinearMap ℝ (fun _ : Fin 110 ↦ E3) ℂ :=
    iteratedFDeriv ℝ 110 (localizedSymbol α m i t)
      (frequencyAssemble3 (8 * x) (8 * y) (8 * z))
  let v : Fin 110 → E3 := fun _ ↦ Anisotropy.coordinateDirection 0
  have hvnorm : ‖Anisotropy.coordinateDirection 0‖ = 1 := by
    simpa [Anisotropy.coordinateDirection] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one 0
  have hbase : ‖F v‖ ≤ D * M := by
    calc
      ‖F v‖ ≤ ‖F‖ * ∏ j, ‖v j‖ := F.le_opNorm v
      _ = ‖F‖ := by simp [v, hvnorm]
      _ ≤ D * M := hDbound _
  change ‖F (fun _ : Fin 110 ↦ (8 : ℝ) • Anisotropy.coordinateDirection 0)‖ ≤
    ((8 : ℝ) ^ 110 * D) * M
  calc
    ‖F (fun _ : Fin 110 ↦ (8 : ℝ) • Anisotropy.coordinateDirection 0)‖ =
        (8 : ℝ) ^ 110 * ‖F v‖ := by
      rw [show (fun _ : Fin 110 ↦ (8 : ℝ) • Anisotropy.coordinateDirection 0) =
          fun j ↦ (8 : ℝ) • v j by
        funext j
        rfl]
      rw [ContinuousMultilinearMap.map_smul_univ]
      norm_num
    _ ≤ (8 : ℝ) ^ 110 * (D * M) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = ((8 : ℝ) ^ 110 * D) * M := by ring

/-- The 110-fold one-dimensional integration-by-parts consequence for the
first scaled raw coordinate. -/
theorem scratch_norm_fourierCoeffOn_raw_first_scaled_le_of_110_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (y z C : ℝ)
    (n : ℤ) (hn : n ≠ 0)
    (hbound : ∀ x ∈ Set.uIoc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
      ‖iteratedDeriv 110 (fun r : ℝ ↦
        localizedSymbolRaw α m i t (8 * r) y z) x‖ ≤ C) :
    ‖fourierCoeffOn (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
      (fun r : ℝ ↦ localizedSymbolRaw α m i t (8 * r) y z) n‖ ≤
      (2 * Real.pi * |(n : ℝ)|)⁻¹ ^ 110 * C := by
  let f : ℝ → ℂ := fun r ↦ localizedSymbolRaw α m i t (8 * r) y z
  have hf : ContDiff ℝ 110 f :=
    scratch_contDiff_raw_first_scaled α M m hm i ht y z
  have hboundary (r : ℕ) (hr : r < 110) :
      iteratedDeriv r f (1 / 2 : ℝ) = iteratedDeriv r f (-(1 / 2 : ℝ)) := by
    rcases scratch_iteratedDeriv_raw_first_scaled_unitBoundary
      α M m hm i ht y z r (le_of_lt hr) with ⟨hleft, hright⟩
    change iteratedDeriv r f (1 / 2 : ℝ) = iteratedDeriv r f (-(1 / 2 : ℝ))
    rw [hleft, hright]
  have hmain := scratch_norm_fourierCoeffOn_le_of_iteratedDeriv_bound
    (a := -(1 / 2 : ℝ)) (b := 1 / 2) (C := C)
    (by norm_num) hn 110 hf hboundary hbound
  convert hmain using 1 <;> norm_num

/-- The two passive raw integrations preserve a uniform bound for the inner
first-coordinate Fourier coefficient, since each integration interval has
length one and the characters have norm one. -/
theorem scratch_norm_nestedRawUnitFourierCoeff_le_of_first_bound
    (α : Anisotropy) (m : E3 → ℂ) (i : Fin 3) (t : ℝ)
    (ν : Fin 3 → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hcoeff : ∀ y z : ℝ,
      ‖fourierCoeffOn (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
        (fun x : ℝ ↦ localizedSymbolRaw α m i t
          (8 * x) (8 * y) (8 * z)) (ν 0)‖ ≤ B) :
    ‖scratch_nestedRawUnitFourierCoeff α m i t ν‖ ≤ B := by
  unfold scratch_nestedRawUnitFourierCoeff
  calc
    ‖∫ y in (-(1 / 2 : ℝ))..(1 / 2),
        fourier (-ν 1) (y : UnitAddCircle) *
          ∫ z in (-(1 / 2 : ℝ))..(1 / 2),
            fourier (-ν 2) (z : UnitAddCircle) *
              fourierCoeffOn (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
                (fun x : ℝ ↦ localizedSymbolRaw α m i t
                  (8 * x) (8 * y) (8 * z)) (ν 0)‖ ≤
        B * |(1 / 2 : ℝ) - (-(1 / 2 : ℝ))| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      have hyfourier : ‖fourier (-ν 1) (y : UnitAddCircle)‖ = 1 := Circle.norm_coe _
      rw [norm_mul, hyfourier, one_mul]
      calc
        ‖∫ z in (-(1 / 2 : ℝ))..(1 / 2),
            fourier (-ν 2) (z : UnitAddCircle) *
              fourierCoeffOn (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
                (fun x : ℝ ↦ localizedSymbolRaw α m i t
                  (8 * x) (8 * y) (8 * z)) (ν 0)‖ ≤
            B * |(1 / 2 : ℝ) - (-(1 / 2 : ℝ))| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro z hz
          have hzfourier : ‖fourier (-ν 2) (z : UnitAddCircle)‖ = 1 := Circle.norm_coe _
          rw [norm_mul, hzfourier, one_mul]
          exact hcoeff y z
        _ = B := by norm_num
    _ = B := by norm_num

/-- Degree-110 decay of the actual torus coefficient in its first lattice
coordinate, conditional on the displayed scale-eight raw derivative bound. -/
theorem scratch_norm_mFourierCoeff_unitTorusLocalizedSymbol_le_of_first_110_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t)
    (ν : Fin 3 → ℤ) (hν : ν 0 ≠ 0) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x y z : ℝ,
      ‖iteratedDeriv 110 (fun r : ℝ ↦ localizedSymbolRaw α m i t
        (8 * r) (8 * y) (8 * z)) x‖ ≤ C) :
    ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν‖ ≤
      (2 * Real.pi * |((ν 0 : ℤ) : ℝ)|)⁻¹ ^ 110 * C := by
  rw [scratch_mFourierCoeff_unitTorusLocalizedSymbol_eq_nestedRaw α M m hm i ht ν]
  let B : ℝ := (2 * Real.pi * |((ν 0 : ℤ) : ℝ)|)⁻¹ ^ 110 * C
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity) hC
  apply scratch_norm_nestedRawUnitFourierCoeff_le_of_first_bound
    α m i t ν B hB
  intro y z
  exact scratch_norm_fourierCoeffOn_raw_first_scaled_le_of_110_bound
    α M m hm i ht (8 * y) (8 * z) C (ν 0) hν
    (fun x _ ↦ hbound x y z)

/-- A uniform degree-110 first-coordinate decay estimate for the actual
localized torus symbol. -/
theorem scratch_exists_mFourierCoeff_unitTorusLocalizedSymbol_first_110_decay
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : Fin 3 → ℤ, ν 0 ≠ 0 →
      ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν‖ ≤
        (2 * Real.pi * |((ν 0 : ℤ) : ℝ)|)⁻¹ ^ 110 * (C * M) := by
  rcases scratch_exists_raw_first_scaled_110_deriv_bound α M m hm i ht with
    ⟨C, hC, hraw⟩
  refine ⟨C, hC, ?_⟩
  intro ν hν
  apply scratch_norm_mFourierCoeff_unitTorusLocalizedSymbol_le_of_first_110_bound
    α M m hm i ht ν hν (C * M) (mul_nonneg hC hm.nonneg)
  intro x y z
  exact hraw x y z

end

end Twisted
end Auto
