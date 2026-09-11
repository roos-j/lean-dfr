/- Copyright (c) 2026. All rights reserved. -/
import Auto.Twisted.FourierCoeffActualBridgeScratch

namespace Auto
namespace Twisted

open MeasureTheory Filter FourierTransform TopologicalSpace
open scoped BigOperators Convolution ENNReal FourierTransform NNReal Topology

noncomputable section

/-- Exact fourth-derivative chain rule for the scale-eight first-coordinate
raw slice.  The right side keeps the four copies of `8 e₀` explicit. -/
theorem scratch_iteratedDeriv_raw_first_scaled_eq_iteratedFDeriv
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (y z r : ℝ) :
    iteratedDeriv 4 (fun x : ℝ ↦
      localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z)) r =
      (iteratedFDeriv ℝ 4 (localizedSymbol α m i t)
        (frequencyAssemble3 (8 * r) (8 * y) (8 * z)))
        (fun _ : Fin 4 ↦ (8 : ℝ) • Anisotropy.coordinateDirection 0) := by
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
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right L hshift r (by norm_num)]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_comp_add_right]
  have hpoint : L r + b = frequencyAssemble3 (8 * r) (8 * y) (8 * z) := by
    ext j
    fin_cases j <;>
      simp [L, b, frequencyAssemble3_apply, coordinateDirection_apply] <;> ring
  have hdir : (fun _ : Fin 4 ↦ L (1 : ℝ)) =
      (fun _ : Fin 4 ↦ (8 : ℝ) • Anisotropy.coordinateDirection 0) := by
    funext j
    simp [L]
  rw [hpoint, hdir]

/-- The source's uniform localized-symbol derivative bound controls the
fourth derivative of every scale-eight first-coordinate raw slice. -/
theorem scratch_exists_raw_first_scaled_fourth_deriv_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y z : ℝ,
      ‖iteratedDeriv 4 (fun r : ℝ ↦ localizedSymbolRaw α m i t
        (8 * r) (8 * y) (8 * z)) x‖ ≤ C * M := by
  rcases exists_localizedSymbol_derivative_bound α M m hm i ht 4 (by norm_num) with
    ⟨D, hD, hDbound⟩
  refine ⟨(8 : ℝ) ^ 4 * D, mul_nonneg (by positivity) hD, ?_⟩
  intro x y z
  rw [scratch_iteratedDeriv_raw_first_scaled_eq_iteratedFDeriv α M m hm i ht y z x]
  let F : ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ E3) ℂ :=
    iteratedFDeriv ℝ 4 (localizedSymbol α m i t)
      (frequencyAssemble3 (8 * x) (8 * y) (8 * z))
  let v : Fin 4 → E3 := fun _ ↦ Anisotropy.coordinateDirection 0
  have hvnorm : ‖Anisotropy.coordinateDirection 0‖ = 1 := by
    simpa [Anisotropy.coordinateDirection] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one 0
  have hbase : ‖F v‖ ≤ D * M := by
    calc
      ‖F v‖ ≤ ‖F‖ * ∏ j, ‖v j‖ := F.le_opNorm v
      _ = ‖F‖ := by simp [v, hvnorm]
      _ ≤ D * M := hDbound _
  change ‖F (fun _ : Fin 4 ↦ (8 : ℝ) • Anisotropy.coordinateDirection 0)‖ ≤
    ((8 : ℝ) ^ 4 * D) * M
  calc
    ‖F (fun _ : Fin 4 ↦ (8 : ℝ) • Anisotropy.coordinateDirection 0)‖ =
        (8 : ℝ) ^ 4 * ‖F v‖ := by
      rw [show (fun _ : Fin 4 ↦ (8 : ℝ) • Anisotropy.coordinateDirection 0) =
          fun j ↦ (8 : ℝ) • v j by
        funext j
        rfl]
      rw [ContinuousMultilinearMap.map_smul_univ]
      norm_num
    _ ≤ (8 : ℝ) ^ 4 * (D * M) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = ((8 : ℝ) ^ 4 * D) * M := by ring

/-- A uniform literal Fourier-coefficient decay estimate in the first
lattice coordinate.  Its constant is independent of the scale, multiplier
coefficient, and lattice mode. -/
theorem scratch_exists_mFourierCoeff_unitTorusLocalizedSymbol_first_fourth_decay
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : Fin 3 → ℤ, ν 0 ≠ 0 →
      ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν‖ ≤
        (2 * Real.pi * |((ν 0 : ℤ) : ℝ)|)⁻¹ ^ 4 * (C * M) := by
  rcases scratch_exists_raw_first_scaled_fourth_deriv_bound α M m hm i ht with
    ⟨C, hC, hraw⟩
  refine ⟨C, hC, ?_⟩
  intro ν hν
  apply scratch_norm_mFourierCoeff_unitTorusLocalizedSymbol_le_of_first_fourth_bound
    α M m hm i ht ν hν (C * M) (mul_nonneg hC hm.nonneg)
  intro x hx y hy z hz
  exact hraw x y z

end
end Twisted
end Auto
