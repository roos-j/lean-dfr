/- Copyright (c) 2026. All rights reserved. -/
import Auto.Twisted.FourierCoeffMiddleCoordinateScratch
import Auto.Twisted.CoefficientScalingScratch

namespace Auto
namespace Twisted

open MeasureTheory Filter FourierTransform TopologicalSpace
open scoped BigOperators Convolution ENNReal FourierTransform NNReal Topology

noncomputable section

/-- The source Fourier-mode index embedded in the lattice used by the spatial
model package.  Its coercion is the coordinatewise real cast. -/
noncomputable def scratch_standardModeOfInt (ν : Fin 3 → ℤ) :
    standardModeLattice :=
  ⟨WithLp.toLp 2 (fun j ↦ (ν j : ℝ)), by
    rw [show WithLp.toLp 2 (fun j ↦ (ν j : ℝ)) =
        ∑ j : Fin 3, (ν j) • PiLp.basisFun 2 ℝ (Fin 3) j by
      apply PiLp.ext
      intro k
      change (ν k : ℝ) =
        (∑ j : Fin 3, (ν j) • PiLp.basisFun 2 ℝ (Fin 3) j) k
      classical
      fin_cases k <;> simp [PiLp.basisFun_apply, Fin.sum_univ_three]
    ]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨j, rfl⟩⟩

@[simp] theorem scratch_standardModeOfInt_apply (ν : Fin 3 → ℤ) (j : Fin 3) :
    ((scratch_standardModeOfInt ν : standardModeLattice) : E3) j = ν j := by
  change (WithLp.toLp 2 (fun j ↦ (ν j : ℝ)) : E3) j = ν j
  rfl

theorem scratch_standardModeOfInt_injective :
    Function.Injective scratch_standardModeOfInt := by
  intro ν μ h
  funext j
  have hcoord : ((scratch_standardModeOfInt ν : standardModeLattice) : E3) j =
      ((scratch_standardModeOfInt μ : standardModeLattice) : E3) j :=
    congrArg (fun z : E3 ↦ z j)
      (congrArg (fun z : standardModeLattice ↦ (z : E3)) h)
  have hcoord' : (ν j : ℝ) = (μ j : ℝ) := by
    simpa only [scratch_standardModeOfInt_apply] using hcoord
  exact_mod_cast hcoord'

/-- The localized-symbol derivative constant can be chosen before the positive
scale.  This is the quantifier order required by the Fourier coefficient
family in the cone expansion. -/
theorem scratch_exists_uniform_localizedSymbol_derivative_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) :
    ∀ k : ℕ, k ≤ 110 → ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ η : E3,
      ‖iteratedFDeriv ℝ k (localizedSymbol α m i t) η‖ ≤ C * M := by
  rcases exists_complexLocalizedCutoff_derivative_bound i 110 with
    ⟨D, hD, hcut⟩
  intro k hk
  let Ck : ℝ := ∑ n ∈ Finset.range (k + 1),
    (k.choose n : ℝ) *
      ((3 : ℝ) ^ n * ∑ σ : Fin n → Fin 3,
        (6 : ℝ) ^ (α.derivativeWeight σ)) * D
  have hDnonneg : 0 ≤ D := le_trans (by norm_num) hD
  have hCknonneg : 0 ≤ Ck := by
    dsimp [Ck]
    apply Finset.sum_nonneg
    intro n hn
    apply mul_nonneg
    · apply mul_nonneg
      · positivity
      · apply mul_nonneg
        · positivity
        · apply Finset.sum_nonneg
          intro σ _
          positivity
    · exact hDnonneg
  refine ⟨Ck, hCknonneg, ?_⟩
  intro t ht η
  by_cases hη : ‖η‖ < 1 / 2
  · rw [iteratedFDeriv_localizedSymbol_eq_zero_of_norm_lt_half
      α m i t η hη k]
    simp only [norm_zero]
    exact mul_nonneg hCknonneg hm.nonneg
  · have hhalf : 1 / 2 ≤ ‖η‖ := le_of_not_gt hη
    have hbound := norm_iteratedFDeriv_localizedSymbol_le_half_compl
      α M m hm i ht D hcut η k hk hhalf
    refine hbound.trans ?_
    have hfactor :
        (∑ n ∈ Finset.range (k + 1),
          (k.choose n : ℝ) *
            ((3 : ℝ) ^ n * ∑ σ : Fin n → Fin 3,
              M * (6 : ℝ) ^ (α.derivativeWeight σ)) * D) = Ck * M := by
      dsimp [Ck]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      rw [← Finset.mul_sum]
      ring
    exact le_of_eq hfactor

/-- The order-zero localized-symbol derivative envelope is a uniform raw
cube bound after the visible scale-eight coordinate map. -/
theorem scratch_exists_raw_scaled_uniform_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y z : ℝ,
      ‖localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z)‖ ≤ C * M := by
  rcases exists_localizedSymbol_derivative_bound α M m hm i ht 0 (by norm_num) with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro x y z
  rw [localizedSymbolRaw_apply]
  simpa only [norm_iteratedFDeriv_zero] using
    (hbound (frequencyAssemble3 (8 * x) (8 * y) (8 * z)))

/-- A uniform bound for every actual unit-torus coefficient, including the
zero mode, obtained directly from the compact raw cube. -/
theorem scratch_exists_mFourierCoeff_unitTorusLocalizedSymbol_uniform_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : Fin 3 → ℤ,
      ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν‖ ≤
        C * M := by
  rcases scratch_exists_raw_scaled_uniform_bound α M m hm i ht with
    ⟨C, hC, hraw⟩
  refine ⟨C, hC, ?_⟩
  intro ν
  rw [scratch_mFourierCoeff_unitTorusLocalizedSymbol_eq_nestedRaw
    α M m hm i ht ν]
  apply scratch_norm_nestedRawUnitFourierCoeff_le_of_first_bound
    α m i t ν (C * M) (mul_nonneg hC hm.nonneg)
  intro y z
  apply scratch_norm_fourierCoeffOn_le_of_norm_le
    (by norm_num : -(1 / 2 : ℝ) < 1 / 2) (ν 0)
  intro x hx
  exact hraw x y z

/-- The raw order-zero envelope is uniform over all positive scales. -/
theorem scratch_exists_uniform_raw_scaled_uniform_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ x y z : ℝ,
      ‖localizedSymbolRaw α m i t (8 * x) (8 * y) (8 * z)‖ ≤ C * M := by
  rcases scratch_exists_uniform_localizedSymbol_derivative_bound
    α M m hm i 0 (by norm_num) with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro t ht x y z
  rw [localizedSymbolRaw_apply]
  simpa only [norm_iteratedFDeriv_zero] using
    (hbound t ht (frequencyAssemble3 (8 * x) (8 * y) (8 * z)))

/-- A single order-zero constant bounds every torus coefficient at every
positive scale, including the zero Fourier mode. -/
theorem scratch_exists_uniform_mFourierCoeff_unitTorusLocalizedSymbol_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ ν : Fin 3 → ℤ,
      ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν‖ ≤
        C * M := by
  rcases scratch_exists_uniform_raw_scaled_uniform_bound α M m hm i with
    ⟨C, hC, hraw⟩
  refine ⟨C, hC, ?_⟩
  intro t ht ν
  rw [scratch_mFourierCoeff_unitTorusLocalizedSymbol_eq_nestedRaw
    α M m hm i ht ν]
  apply scratch_norm_nestedRawUnitFourierCoeff_le_of_first_bound
    α m i t ν (C * M) (mul_nonneg hC hm.nonneg)
  intro y z
  apply scratch_norm_fourierCoeffOn_le_of_norm_le
    (by norm_num : -(1 / 2 : ℝ) < 1 / 2) (ν 0)
  intro x hx
  exact hraw t ht x y z

/-- The order-110 Fréchet derivative bound applied repeatedly in any one
coordinate direction, with the scale-eight factor made explicit. -/
theorem scratch_norm_iteratedFDeriv_repeated_coordinate110_le
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (i j : Fin 3) (t : ℝ) (η : E3) (D : ℝ)
    (hbound : ∀ s : ℝ, 0 < s → ∀ ξ : E3,
      ‖iteratedFDeriv ℝ 110 (localizedSymbol α m i s) ξ‖ ≤ D * M)
    (ht : 0 < t) :
    ‖(iteratedFDeriv ℝ 110 (localizedSymbol α m i t) η)
      (fun _ : Fin 110 ↦ (8 : ℝ) • Anisotropy.coordinateDirection j)‖ ≤
      ((8 : ℝ) ^ 110 * D) * M := by
  let F : ContinuousMultilinearMap ℝ (fun _ : Fin 110 ↦ E3) ℂ :=
    iteratedFDeriv ℝ 110 (localizedSymbol α m i t) η
  let v : Fin 110 → E3 := fun _ ↦ Anisotropy.coordinateDirection j
  have hvnorm : ‖Anisotropy.coordinateDirection j‖ = 1 := by
    simp [Anisotropy.coordinateDirection]
  have hbase : ‖F v‖ ≤ D * M := by
    calc
      ‖F v‖ ≤ ‖F‖ * ∏ q, ‖v q‖ := F.le_opNorm v
      _ = ‖F‖ := by simp [v, hvnorm]
      _ ≤ D * M := hbound t ht η
  change ‖F (fun _ : Fin 110 ↦ (8 : ℝ) • Anisotropy.coordinateDirection j)‖ ≤
    ((8 : ℝ) ^ 110 * D) * M
  calc
    ‖F (fun _ : Fin 110 ↦ (8 : ℝ) • Anisotropy.coordinateDirection j)‖ =
        (8 : ℝ) ^ 110 * ‖F v‖ := by
      rw [show (fun _ : Fin 110 ↦ (8 : ℝ) • Anisotropy.coordinateDirection j) =
          fun q ↦ (8 : ℝ) • v q by
        funext q
        rfl]
      rw [ContinuousMultilinearMap.map_smul_univ]
      norm_num
    _ ≤ (8 : ℝ) ^ 110 * (D * M) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = ((8 : ℝ) ^ 110 * D) * M := by ring

/-- Uniform order-110 raw derivative envelope in the first Fourier
coordinate. -/
theorem scratch_exists_uniform_raw_first_scaled_110_deriv_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ x y z : ℝ,
      ‖iteratedDeriv 110 (fun r : ℝ ↦ localizedSymbolRaw α m i t
        (8 * r) (8 * y) (8 * z)) x‖ ≤ C * M := by
  rcases scratch_exists_uniform_localizedSymbol_derivative_bound
    α M m hm i 110 (by norm_num) with ⟨D, hD, hbound⟩
  refine ⟨(8 : ℝ) ^ 110 * D, mul_nonneg (by positivity) hD, ?_⟩
  intro t ht x y z
  rw [scratch_iteratedDeriv_raw_first_scaled_eq_iteratedFDeriv_at_order
    α M m hm i ht 110 (by norm_num) y z x]
  exact scratch_norm_iteratedFDeriv_repeated_coordinate110_le
    α M m i 0 t (frequencyAssemble3 (8 * x) (8 * y) (8 * z)) D hbound ht

/-- Uniform order-110 raw derivative envelope in the middle Fourier
coordinate. -/
theorem scratch_exists_uniform_raw_middle_scaled_110_deriv_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ x y z : ℝ,
      ‖iteratedDeriv 110 (fun r : ℝ ↦ localizedSymbolRaw α m i t
        (8 * x) (8 * r) (8 * z)) y‖ ≤ C * M := by
  rcases scratch_exists_uniform_localizedSymbol_derivative_bound
    α M m hm i 110 (by norm_num) with ⟨D, hD, hbound⟩
  refine ⟨(8 : ℝ) ^ 110 * D, mul_nonneg (by positivity) hD, ?_⟩
  intro t ht x y z
  rw [scratch_iteratedDeriv_raw_middle_scaled_eq_iteratedFDeriv_at_order
    α M m hm i ht 110 (by norm_num) x z y]
  exact scratch_norm_iteratedFDeriv_repeated_coordinate110_le
    α M m i 1 t (frequencyAssemble3 (8 * x) (8 * y) (8 * z)) D hbound ht

/-- Uniform order-110 raw derivative envelope in the last Fourier
coordinate. -/
theorem scratch_exists_uniform_raw_last_scaled_110_deriv_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ x y z : ℝ,
      ‖iteratedDeriv 110 (fun r : ℝ ↦ localizedSymbolRaw α m i t
        (8 * x) (8 * y) (8 * r)) z‖ ≤ C * M := by
  rcases scratch_exists_uniform_localizedSymbol_derivative_bound
    α M m hm i 110 (by norm_num) with ⟨D, hD, hbound⟩
  refine ⟨(8 : ℝ) ^ 110 * D, mul_nonneg (by positivity) hD, ?_⟩
  intro t ht x y z
  rw [scratch_iteratedDeriv_raw_last_scaled_eq_iteratedFDeriv_at_order
    α M m hm i ht 110 (by norm_num) x y z]
  exact scratch_norm_iteratedFDeriv_repeated_coordinate110_le
    α M m i 2 t (frequencyAssemble3 (8 * x) (8 * y) (8 * z)) D hbound ht

/-- Uniform degree-110 decay in the first integer Fourier coordinate. -/
theorem scratch_exists_uniform_mFourierCoeff_unitTorusLocalizedSymbol_first_110_decay
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ ν : Fin 3 → ℤ, ν 0 ≠ 0 →
      ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν‖ ≤
        (2 * Real.pi * |((ν 0 : ℤ) : ℝ)|)⁻¹ ^ 110 * (C * M) := by
  rcases scratch_exists_uniform_raw_first_scaled_110_deriv_bound α M m hm i with
    ⟨C, hC, hraw⟩
  refine ⟨C, hC, ?_⟩
  intro t ht ν hν
  apply scratch_norm_mFourierCoeff_unitTorusLocalizedSymbol_le_of_first_110_bound
    α M m hm i ht ν hν (C * M) (mul_nonneg hC hm.nonneg)
  intro x y z
  exact hraw t ht x y z

/-- Uniform degree-110 decay in the middle integer Fourier coordinate. -/
theorem scratch_exists_uniform_mFourierCoeff_unitTorusLocalizedSymbol_middle_110_decay
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ ν : Fin 3 → ℤ, ν 1 ≠ 0 →
      ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν‖ ≤
        (2 * Real.pi * |((ν 1 : ℤ) : ℝ)|)⁻¹ ^ 110 * (C * M) := by
  rcases scratch_exists_uniform_raw_middle_scaled_110_deriv_bound α M m hm i with
    ⟨C, hC, hraw⟩
  refine ⟨C, hC, ?_⟩
  intro t ht ν hν
  apply scratch_norm_mFourierCoeff_unitTorusLocalizedSymbol_le_of_middle_110_bound
    α M m hm i ht ν hν (C * M) (mul_nonneg hC hm.nonneg)
  intro x y z
  exact hraw t ht x y z

/-- Uniform degree-110 decay in the last integer Fourier coordinate. -/
theorem scratch_exists_uniform_mFourierCoeff_unitTorusLocalizedSymbol_last_110_decay
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ ν : Fin 3 → ℤ, ν 2 ≠ 0 →
      ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν‖ ≤
        (2 * Real.pi * |((ν 2 : ℤ) : ℝ)|)⁻¹ ^ 110 * (C * M) := by
  rcases scratch_exists_uniform_raw_last_scaled_110_deriv_bound α M m hm i with
    ⟨C, hC, hraw⟩
  refine ⟨C, hC, ?_⟩
  intro t ht ν hν
  apply scratch_norm_mFourierCoeff_unitTorusLocalizedSymbol_le_of_last_110_bound
    α M m hm i ht ν hν (C * M) (mul_nonneg hC hm.nonneg)
  intro x y z
  exact hraw t ht x y z

/-- Absolute real coordinate size of a literal integer Fourier mode. -/
noncomputable def scratch_intModeAbs (ν : Fin 3 → ℤ) (j : Fin 3) : ℝ :=
  |((ν j : ℤ) : ℝ)|

@[simp] theorem scratch_intModeAbs_apply (ν : Fin 3 → ℤ) (j : Fin 3) :
    scratch_intModeAbs ν j = |((ν j : ℤ) : ℝ)| := rfl

/-- The source lattice weight of the embedded integer Fourier mode is its
literal coordinatewise `ℓ¹` weight. -/
theorem scratch_sourceWeight_standardModeOfInt (ν : Fin 3 → ℤ) :
    sourceWeight ((scratch_standardModeOfInt ν : standardModeLattice) : E3) =
      1 + scratch_intModeAbs ν 0 + scratch_intModeAbs ν 1 + scratch_intModeAbs ν 2 := by
  unfold sourceWeight scratch_intModeAbs
  simp only [scratch_standardModeOfInt_apply]

/-- A coordinate attaining the largest absolute real integer coordinate is
nonzero whenever the mode itself is nonzero. -/
theorem scratch_intMode_coordinate_max_ne_zero
    (ν : Fin 3 → ℤ) (j : Fin 3) (hν : ν ≠ 0)
    (hmax : ∀ k : Fin 3, scratch_intModeAbs ν k ≤ scratch_intModeAbs ν j) :
    ν j ≠ 0 := by
  intro hj
  apply hν
  funext k
  have hle : scratch_intModeAbs ν k ≤ 0 := by
    simpa [scratch_intModeAbs, hj] using hmax k
  have habs : scratch_intModeAbs ν k = 0 :=
    le_antisymm hle (abs_nonneg _)
  have hcast : ((ν k : ℤ) : ℝ) = 0 := by
    exact abs_eq_zero.mp habs
  exact_mod_cast hcast

/-- The source weight is at most four times any nonzero largest integer
coordinate. -/
theorem scratch_sourceWeight_le_four_mul_intModeAbs_of_max
    (ν : Fin 3 → ℤ) (j : Fin 3) (hj : ν j ≠ 0)
    (hmax : ∀ k : Fin 3, scratch_intModeAbs ν k ≤ scratch_intModeAbs ν j) :
    sourceWeight ((scratch_standardModeOfInt ν : standardModeLattice) : E3) ≤
      4 * scratch_intModeAbs ν j := by
  have honeZ : (1 : ℤ) ≤ |ν j| := Int.one_le_abs hj
  have hone : (1 : ℝ) ≤ scratch_intModeAbs ν j := by
    rw [scratch_intModeAbs, ← Int.cast_one, ← Int.cast_abs]
    exact_mod_cast honeZ
  rw [scratch_sourceWeight_standardModeOfInt]
  have h0 := hmax 0
  have h1 := hmax 1
  have h2 := hmax 2
  linarith

/-- A one-coordinate degree-110 Fourier factor is controlled by the common
source-weight tail once that coordinate dominates the other two. -/
theorem scratch_frequencyFactor110_le_sourceWeight_decay
    (W a : ℝ) (hW : 0 < W) (ha : 0 < a) (hWa : W ≤ 4 * a) :
    (2 * Real.pi * a)⁻¹ ^ (110 : ℕ) ≤
      (1 + 4 * (2 * Real.pi)⁻¹) ^ (110 : ℕ) * W⁻¹ ^ (110 : ℕ) := by
  have hfoura : 0 < 4 * a := by positivity
  have hinv : (4 * a)⁻¹ ≤ W⁻¹ :=
    (inv_le_inv₀ hfoura hW).mpr hWa
  have hscale : a⁻¹ ≤ 4 * W⁻¹ := by
    calc
      a⁻¹ = 4 * (4 * a)⁻¹ := by field_simp [ha.ne']
      _ ≤ 4 * W⁻¹ := mul_le_mul_of_nonneg_left hinv (by norm_num)
  have hpiinv : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have hbase : (2 * Real.pi * a)⁻¹ ≤
      (4 * (2 * Real.pi)⁻¹) * W⁻¹ := by
    calc
      (2 * Real.pi * a)⁻¹ = (2 * Real.pi)⁻¹ * a⁻¹ := by
        rw [mul_inv_rev]
        ring
      _ ≤ (2 * Real.pi)⁻¹ * (4 * W⁻¹) :=
        mul_le_mul_of_nonneg_left hscale hpiinv
      _ = (4 * (2 * Real.pi)⁻¹) * W⁻¹ := by ring
  have hK : 4 * (2 * Real.pi)⁻¹ ≤ 1 + 4 * (2 * Real.pi)⁻¹ := by linarith
  have hWinv : 0 ≤ W⁻¹ := inv_nonneg.mpr hW.le
  have hbase' : (2 * Real.pi * a)⁻¹ ≤
      (1 + 4 * (2 * Real.pi)⁻¹) * W⁻¹ := by
    exact hbase.trans (mul_le_mul_of_nonneg_right hK hWinv)
  calc
    (2 * Real.pi * a)⁻¹ ^ (110 : ℕ) ≤
        ((1 + 4 * (2 * Real.pi)⁻¹) * W⁻¹) ^ (110 : ℕ) :=
      pow_le_pow_left₀ (inv_nonneg.mpr (by positivity)) hbase' _
    _ = (1 + 4 * (2 * Real.pi)⁻¹) ^ (110 : ℕ) * W⁻¹ ^ (110 : ℕ) := by
      rw [mul_pow]

/-- Combine a largest-coordinate degree-110 coefficient estimate with the
common source-weight decay.  The constant `D` may dominate the coordinate
constant `C`. -/
theorem scratch_le_sourceWeight_decay_of_coordinate_bound
    {X a W C D M : ℝ}
    (hW : 0 < W) (ha : 0 < a) (hWa : W ≤ 4 * a)
    (hC : 0 ≤ C) (hCD : C ≤ D) (hM : 0 ≤ M)
    (hX : X ≤ (2 * Real.pi * a)⁻¹ ^ (110 : ℕ) * (C * M)) :
    X ≤ ((D * (1 + 4 * (2 * Real.pi)⁻¹) ^ (110 : ℕ)) * M) *
      W⁻¹ ^ (110 : ℕ) := by
  have hfactor := scratch_frequencyFactor110_le_sourceWeight_decay W a hW ha hWa
  have hCM : 0 ≤ C * M := mul_nonneg hC hM
  have hCMle : C * M ≤ D * M :=
    mul_le_mul_of_nonneg_right hCD hM
  calc
    X ≤ (2 * Real.pi * a)⁻¹ ^ (110 : ℕ) * (C * M) := hX
    _ ≤ ((1 + 4 * (2 * Real.pi)⁻¹) ^ (110 : ℕ) * W⁻¹ ^ (110 : ℕ)) *
        (C * M) := mul_le_mul_of_nonneg_right hfactor hCM
    _ ≤ ((1 + 4 * (2 * Real.pi)⁻¹) ^ (110 : ℕ) * W⁻¹ ^ (110 : ℕ)) *
        (D * M) :=
      mul_le_mul_of_nonneg_left hCMle (by positivity)
    _ = ((D * (1 + 4 * (2 * Real.pi)⁻¹) ^ (110 : ℕ)) * M) *
        W⁻¹ ^ (110 : ℕ) := by ring

/-- The actual localized torus Fourier coefficients have a scale-uniform
degree-110 source-weight envelope.  The literal integer mode is embedded in
the spatial model lattice only in the displayed weight, keeping the Fourier
index and the source `ν/8` convention explicit. -/
theorem scratch_exists_uniform_mFourierCoeff_unitTorusLocalizedSymbol_sourceWeight_110_decay
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, 0 < t → ∀ ν : Fin 3 → ℤ,
      ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν‖ ≤
        (A * M) *
          (sourceWeight ((scratch_standardModeOfInt ν : standardModeLattice) : E3))⁻¹ ^
            (110 : ℕ) := by
  rcases scratch_exists_uniform_mFourierCoeff_unitTorusLocalizedSymbol_bound
    α M m hm i with ⟨Cz, hCz, hzero⟩
  rcases scratch_exists_uniform_mFourierCoeff_unitTorusLocalizedSymbol_first_110_decay
    α M m hm i with ⟨C0, hC0, hfirst⟩
  rcases scratch_exists_uniform_mFourierCoeff_unitTorusLocalizedSymbol_middle_110_decay
    α M m hm i with ⟨C1, hC1, hmiddle⟩
  rcases scratch_exists_uniform_mFourierCoeff_unitTorusLocalizedSymbol_last_110_decay
    α M m hm i with ⟨C2, hC2, hlast⟩
  let D : ℝ := Cz + C0 + C1 + C2
  let R : ℝ := (1 + 4 * (2 * Real.pi)⁻¹) ^ (110 : ℕ)
  let A : ℝ := D * R
  have hD : 0 ≤ D := by
    dsimp [D]
    linarith
  have hCzD : Cz ≤ D := by
    dsimp [D]
    linarith
  have hC0D : C0 ≤ D := by
    dsimp [D]
    linarith
  have hC1D : C1 ≤ D := by
    dsimp [D]
    linarith
  have hC2D : C2 ≤ D := by
    dsimp [D]
    linarith
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hRone : 1 ≤ R := by
    dsimp [R]
    apply one_le_pow₀
    exact le_add_of_nonneg_right (by positivity)
  refine ⟨A, mul_nonneg hD hR, ?_⟩
  intro t ht ν
  let W : ℝ := sourceWeight ((scratch_standardModeOfInt ν : standardModeLattice) : E3)
  have hW : 0 < W := by
    dsimp [W]
    exact sourceWeight_pos _
  by_cases hν : ν = 0
  · subst ν
    have hWeightzero : sourceWeight
        ((scratch_standardModeOfInt (0 : Fin 3 → ℤ) : standardModeLattice) : E3) = 1 := by
      simp [scratch_sourceWeight_standardModeOfInt]
    rw [hWeightzero]
    simp only [inv_one, one_pow, mul_one]
    change ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) 0‖ ≤
      (D * R) * M
    calc
      ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) 0‖ ≤ Cz * M :=
        hzero t ht 0
      _ ≤ D * M := mul_le_mul_of_nonneg_right hCzD hm.nonneg
      _ = (D * M) * 1 := by ring
      _ ≤ (D * M) * R :=
        mul_le_mul_of_nonneg_left hRone (mul_nonneg hD hm.nonneg)
      _ = (D * R) * M := by ring
  · have hfinish (j : Fin 3) (C : ℝ) (hC : 0 ≤ C) (hCD : C ≤ D)
      (hj : ν j ≠ 0)
      (hmax : ∀ k : Fin 3, scratch_intModeAbs ν k ≤ scratch_intModeAbs ν j)
      (hcoeff : ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν‖ ≤
        (2 * Real.pi * scratch_intModeAbs ν j)⁻¹ ^ (110 : ℕ) * (C * M)) :
      ‖UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν‖ ≤
        (A * M) * W⁻¹ ^ (110 : ℕ) := by
      have hWa : W ≤ 4 * scratch_intModeAbs ν j := by
        dsimp [W]
        exact scratch_sourceWeight_le_four_mul_intModeAbs_of_max ν j hj hmax
      have hone : (1 : ℝ) ≤ scratch_intModeAbs ν j := by
        rw [scratch_intModeAbs, ← Int.cast_one, ← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hj
      have ha : 0 < scratch_intModeAbs ν j := lt_of_lt_of_le zero_lt_one hone
      have hmain := scratch_le_sourceWeight_decay_of_coordinate_bound
        hW ha hWa hC hCD hm.nonneg hcoeff
      simpa only [A, R] using hmain
    by_cases h10 : scratch_intModeAbs ν 1 ≤ scratch_intModeAbs ν 0
    · by_cases h20 : scratch_intModeAbs ν 2 ≤ scratch_intModeAbs ν 0
      · have hmax : ∀ k : Fin 3,
            scratch_intModeAbs ν k ≤ scratch_intModeAbs ν 0 := by
          intro k
          fin_cases k
          · exact le_rfl
          · exact h10
          · exact h20
        have h0 : ν 0 ≠ 0 :=
          scratch_intMode_coordinate_max_ne_zero ν 0 hν hmax
        apply hfinish 0 C0 hC0 hC0D h0 hmax
        simpa only [scratch_intModeAbs] using hfirst t ht ν h0
      · have h02 : scratch_intModeAbs ν 0 ≤ scratch_intModeAbs ν 2 :=
          le_of_not_ge h20
        have h12 : scratch_intModeAbs ν 1 ≤ scratch_intModeAbs ν 2 := h10.trans h02
        have hmax : ∀ k : Fin 3,
            scratch_intModeAbs ν k ≤ scratch_intModeAbs ν 2 := by
          intro k
          fin_cases k
          · exact h02
          · exact h12
          · exact le_rfl
        have h2 : ν 2 ≠ 0 :=
          scratch_intMode_coordinate_max_ne_zero ν 2 hν hmax
        apply hfinish 2 C2 hC2 hC2D h2 hmax
        simpa only [scratch_intModeAbs] using hlast t ht ν h2
    · have h01 : scratch_intModeAbs ν 0 ≤ scratch_intModeAbs ν 1 :=
        le_of_not_ge h10
      by_cases h21 : scratch_intModeAbs ν 2 ≤ scratch_intModeAbs ν 1
      · have hmax : ∀ k : Fin 3,
            scratch_intModeAbs ν k ≤ scratch_intModeAbs ν 1 := by
          intro k
          fin_cases k
          · exact h01
          · exact le_rfl
          · exact h21
        have h1 : ν 1 ≠ 0 :=
          scratch_intMode_coordinate_max_ne_zero ν 1 hν hmax
        apply hfinish 1 C1 hC1 hC1D h1 hmax
        simpa only [scratch_intModeAbs] using hmiddle t ht ν h1
      · have h12 : scratch_intModeAbs ν 1 ≤ scratch_intModeAbs ν 2 :=
          le_of_not_ge h21
        have h02 : scratch_intModeAbs ν 0 ≤ scratch_intModeAbs ν 2 := h01.trans h12
        have hmax : ∀ k : Fin 3,
            scratch_intModeAbs ν k ≤ scratch_intModeAbs ν 2 := by
          intro k
          fin_cases k
          · exact h02
          · exact h12
          · exact le_rfl
        have h2 : ν 2 ≠ 0 :=
          scratch_intMode_coordinate_max_ne_zero ν 2 hν hmax
        apply hfinish 2 C2 hC2 hC2D h2 hmax
        simpa only [scratch_intModeAbs] using hlast t ht ν h2

/-- The degree-110 source-weight tail is pointwise dominated by the existing
degree-ten lattice-summability tail. -/
theorem scratch_sourceWeight_inv_pow_110_le_pow_10
    (z : standardModeLattice) :
    (sourceWeight (z : E3))⁻¹ ^ (110 : ℕ) ≤
      (sourceWeight (z : E3))⁻¹ ^ (10 : ℕ) := by
  let W : ℝ := sourceWeight (z : E3)
  have hW : 0 < W := by
    dsimp [W]
    exact sourceWeight_pos _
  have hWone : 1 ≤ W := by
    dsimp [W]
    unfold sourceWeight
    linarith [abs_nonneg ((z : E3) 0), abs_nonneg ((z : E3) 1),
      abs_nonneg ((z : E3) 2)]
  have hWinv : W⁻¹ ≤ 1 := (inv_le_one₀ hW).mpr hWone
  have hWinvnonneg : 0 ≤ W⁻¹ := inv_nonneg.mpr hW.le
  have htail : W⁻¹ ^ (100 : ℕ) ≤ 1 :=
    pow_le_one₀ hWinvnonneg hWinv
  calc
    W⁻¹ ^ (110 : ℕ) = W⁻¹ ^ (10 : ℕ) * W⁻¹ ^ (100 : ℕ) := by
      rw [← pow_add]
    _ ≤ W⁻¹ ^ (10 : ℕ) * 1 :=
      mul_le_mul_of_nonneg_left htail (pow_nonneg hWinvnonneg _)
    _ = W⁻¹ ^ (10 : ℕ) := by ring

/-- At each positive scale, the actual localized torus coefficient family is
absolutely summable over the literal integer Fourier modes. -/
theorem scratch_summable_mFourierCoeff_unitTorusLocalizedSymbol
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) (t : ℝ) (ht : 0 < t) :
    Summable (fun ν : Fin 3 → ℤ ↦
      UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν) := by
  rcases scratch_exists_uniform_mFourierCoeff_unitTorusLocalizedSymbol_sourceWeight_110_decay
    α M m hm i with ⟨A, hA, hdecay⟩
  have hmajor : Summable (fun ν : Fin 3 → ℤ ↦
      (A * M) *
        (sourceWeight ((scratch_standardModeOfInt ν : standardModeLattice) : E3))⁻¹ ^
          (10 : ℕ)) := by
    change Summable ((fun z : standardModeLattice ↦
      (A * M) * (sourceWeight (z : E3))⁻¹ ^ (10 : ℕ)) ∘ scratch_standardModeOfInt)
    exact ((summable_standardMode_sourceWeight_inv).mul_left (A * M)).comp_injective
      scratch_standardModeOfInt_injective
  apply Summable.of_norm_bounded hmajor
  intro ν
  have h110 := hdecay t ht ν
  have htail := scratch_sourceWeight_inv_pow_110_le_pow_10
    (scratch_standardModeOfInt ν)
  exact h110.trans
    (mul_le_mul_of_nonneg_left htail (mul_nonneg hA hm.nonneg))

/-- Conditional strict-range summability of the literal third-mode full forms
with the actual torus Fourier coefficients.  The only additional hypothesis is
measurability in the scale variable; coefficients are extended by zero off the
positive scale half-line, which leaves the source form unchanged. -/
theorem scratch_summable_thirdModeFrequencyFullForm_of_torusCoefficient
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) (q : Fin 4 → ℝ)
    (hq : ∀ j : Fin 4, 0 < q j)
    (hsum : ∑ j : Fin 4, (q j)⁻¹ = 1)
    (hqs : ∀ j : Fin 4, activeSourceStoppingExponent 2 j < q j)
    (hmeas : ∀ ν : Fin 3 → ℤ, Measurable (fun t : ℝ ↦
      if 0 < t then UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν else 0))
    (F : ModelComplexSchwartzInput) :
    Summable (fun ν : Fin 3 → ℤ ↦
      thirdModeFrequencyFullForm α (scratch_standardModeOfInt ν)
        (fun t ↦ if 0 < t then
          UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν else 0) F) := by
  rcases scratch_exists_uniform_mFourierCoeff_unitTorusLocalizedSymbol_sourceWeight_110_decay
    α M m hm i with ⟨A, hA, hcoeff⟩
  rcases scratch_exists_uniform_thirdModeFrequencyFullForm_bound_of_coefficient_bound
    α q hq hsum hqs with ⟨C, hC, hmode⟩
  let N : ℝ := ∏ j : Fin 4,
    lpNorm (F j : E3 → ℂ) (ENNReal.ofReal (q j)) volume
  let D : ℝ := 32 * C * N
  have hN : 0 ≤ N := Finset.prod_nonneg fun j _ ↦ lpNorm_nonneg
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hAM : 0 ≤ A * M := mul_nonneg hA hm.nonneg
  have hmajor : Summable (fun ν : Fin 3 → ℤ ↦
      (A * M * D) *
        (sourceWeight ((scratch_standardModeOfInt ν : standardModeLattice) : E3))⁻¹ ^
          (10 : ℕ)) := by
    change Summable ((fun z : standardModeLattice ↦
      (A * M * D) * (sourceWeight (z : E3))⁻¹ ^ (10 : ℕ)) ∘ scratch_standardModeOfInt)
    exact ((summable_standardMode_sourceWeight_inv).mul_left (A * M * D)).comp_injective
      scratch_standardModeOfInt_injective
  apply Summable.of_norm_bounded hmajor
  intro ν
  let z : standardModeLattice := scratch_standardModeOfInt ν
  let W : ℝ := sourceWeight (z : E3)
  let B : ℝ := (A * M) * W⁻¹ ^ (110 : ℕ)
  let a : ℝ → ℂ := fun t ↦
    if 0 < t then UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν else 0
  have hW : 0 < W := by
    dsimp [W]
    exact sourceWeight_pos _
  have hWne : W ≠ 0 := hW.ne'
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hameas : Measurable a := by
    simpa only [a] using hmeas ν
  have hBpoint : ∀ t : ℝ, ‖a t‖ ≤ B := by
    intro t
    by_cases ht : 0 < t
    · simpa only [a, if_pos ht] using hcoeff t ht ν
    · rw [show a t = 0 by simp [a, ht], norm_zero]
      exact hB
  have hraw := hmode z B a F hB hameas hBpoint
  have htranslate : sourceWeight (standardModeTranslate z) ^ (100 : ℕ) ≤
      W ^ (100 : ℕ) := by
    simpa only [W] using sourceWeight_standardModeTranslate_pow_le z
  have hscale : B * (D * sourceWeight (standardModeTranslate z) ^ (100 : ℕ)) ≤
      B * (D * W ^ (100 : ℕ)) := by
    apply mul_le_mul_of_nonneg_left
    · exact mul_le_mul_of_nonneg_left htranslate hD
    · exact hB
  have hident : B * (D * W ^ (100 : ℕ)) =
      (A * M * D) * W⁻¹ ^ (10 : ℕ) := by
    dsimp [B]
    field_simp [hWne]
  calc
    ‖thirdModeFrequencyFullForm α z a F‖ ≤
        B * (32 * C * sourceWeight (standardModeTranslate z) ^ 100 * N) := by
      simpa only [N] using hraw
    _ = B * (D * sourceWeight (standardModeTranslate z) ^ (100 : ℕ)) := by
      dsimp [D]
      ring
    _ ≤ B * (D * W ^ (100 : ℕ)) := hscale
    _ = (A * M * D) * W⁻¹ ^ (10 : ℕ) := hident
    _ = (A * M * D) *
        (sourceWeight ((scratch_standardModeOfInt ν : standardModeLattice) : E3))⁻¹ ^
          (10 : ℕ) := by
      rfl

end

end Twisted
end Auto
