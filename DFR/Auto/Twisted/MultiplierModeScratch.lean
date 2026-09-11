import Auto.Twisted.Twisted

namespace Auto.Twisted

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal RealInnerProductSpace Topology

noncomputable section

/-- The zero multiplier scale forces the multiplier itself to vanish, so the
zero case in the cone decomposition does not need any division by `M`. -/
theorem scratch_multiplier_eq_zero_of_M_eq_zero
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m) (hM : M = 0) :
    m = 0 := by
  funext ξ
  apply norm_eq_zero.mp
  apply le_antisymm
  · calc
      ‖m ξ‖ ≤ M := hm.norm_le_all ξ
      _ = 0 := hM
  · exact norm_nonneg _

/-- Consequently the literal multiplier form is zero in the zero-scale
case. -/
theorem scratch_multiplierForm_eq_zero_of_M_eq_zero
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m) (hM : M = 0)
    (f₀ f₁ f₂ f₃ : Schwartz3) :
    multiplierForm m f₀ f₁ f₂ f₃ = 0 := by
  rw [scratch_multiplier_eq_zero_of_M_eq_zero α M m hm hM]
  simp [multiplierForm]

/-- A mode family with the coefficient decay produced by the Fourier-series
step is absolutely summable on the standard three-dimensional lattice. -/
theorem scratch_summable_standardMode_of_sourceWeight_decay
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : standardModeLattice → E) (C : ℝ)
    (hF : ∀ z : standardModeLattice,
      ‖F z‖ ≤ C * (sourceWeight (z : E3))⁻¹ ^ (10 : ℕ)) :
    Summable F := by
  apply Summable.of_norm_bounded
  · exact (summable_standardMode_sourceWeight_inv).mul_left C
  · intro z
    exact hF z

/-- The three active-coordinate mode sums remain summable under a common
degree-ten coefficient bound. -/
theorem scratch_summable_threeCoordinateModes_of_sourceWeight_decay
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : Fin 3 → standardModeLattice → E) (C : ℝ)
    (hF : ∀ i z, ‖F i z‖ ≤ C * (sourceWeight (z : E3))⁻¹ ^ (10 : ℕ)) :
    Summable (fun z ↦ F 0 z + F 1 z + F 2 z) := by
  let g : standardModeLattice → ℝ := fun z ↦
    (sourceWeight (z : E3))⁻¹ ^ (10 : ℕ)
  apply Summable.of_norm_bounded ((summable_standardMode_sourceWeight_inv).mul_left (3 * C))
  intro z
  change ‖F 0 z + F 1 z + F 2 z‖ ≤ (3 * C) * g z
  calc
    ‖F 0 z + F 1 z + F 2 z‖ ≤ ‖F 0 z + F 1 z‖ + ‖F 2 z‖ := norm_add_le _ _
    _ ≤ (‖F 0 z‖ + ‖F 1 z‖) + ‖F 2 z‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (C * g z + C * g z) + C * g z := by
      gcongr
      · exact hF 0 z
      · exact hF 1 z
      · exact hF 2 z
    _ = (3 * C) * g z := by ring

/-- Coefficient decay of order 110 and model growth of order 100 leave the
summable order-10 lattice tail required in the final cone summation. -/
theorem scratch_summable_threeCoordinateModeProducts_of_decay
    (a b : Fin 3 → standardModeLattice → ℂ) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ i z, ‖a i z‖ ≤
      C * (sourceWeight (z : E3))⁻¹ ^ (110 : ℕ))
    (hb : ∀ i z, ‖b i z‖ ≤
      D * sourceWeight (z : E3) ^ (100 : ℕ)) :
    Summable (fun z ↦ ∑ i : Fin 3, a i z * b i z) := by
  let g : standardModeLattice → ℝ := fun z ↦
    (sourceWeight (z : E3))⁻¹ ^ (10 : ℕ)
  apply Summable.of_norm_bounded
    ((summable_standardMode_sourceWeight_inv).mul_left (3 * C * D))
  intro z
  have hwpos : 0 < sourceWeight (z : E3) := sourceWeight_pos _
  have hwne : sourceWeight (z : E3) ≠ 0 := hwpos.ne'
  have hpow :
      (sourceWeight (z : E3))⁻¹ ^ (110 : ℕ) *
          sourceWeight (z : E3) ^ (100 : ℕ) = g z := by
    dsimp [g]
    field_simp [hwne]
  have hterm (i : Fin 3) :
      ‖a i z * b i z‖ ≤ C * D * g z := by
    rw [norm_mul]
    calc
      ‖a i z‖ * ‖b i z‖ ≤
          (C * (sourceWeight (z : E3))⁻¹ ^ (110 : ℕ)) *
            (D * sourceWeight (z : E3) ^ (100 : ℕ)) := by
              apply mul_le_mul (ha i z) (hb i z) (norm_nonneg _)
              exact mul_nonneg hC (pow_nonneg (inv_nonneg.mpr hwpos.le) _)
      _ = C * D *
          ((sourceWeight (z : E3))⁻¹ ^ (110 : ℕ) *
            sourceWeight (z : E3) ^ (100 : ℕ)) := by ring
      _ = C * D * g z := by rw [hpow]
  calc
    ‖∑ i : Fin 3, a i z * b i z‖ ≤ ∑ i : Fin 3, ‖a i z * b i z‖ :=
      by simpa using
        (norm_sum_le (Finset.univ : Finset (Fin 3)) (fun i ↦ a i z * b i z))
    _ ≤ ∑ _i : Fin 3, C * D * g z := by
      exact Finset.sum_le_sum fun i hi ↦ hterm i
    _ = (3 * C * D) * g z := by
      simp [Fin.sum_univ_succ]
      ring

/-- The preceding absolutely convergent mode sum has the explicit final
majorant needed after a Fourier-series form decomposition. -/
theorem scratch_norm_tsum_threeCoordinateModeProducts_le_of_decay
    (a b : Fin 3 → standardModeLattice → ℂ) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ i z, ‖a i z‖ ≤
      C * (sourceWeight (z : E3))⁻¹ ^ (110 : ℕ))
    (hb : ∀ i z, ‖b i z‖ ≤
      D * sourceWeight (z : E3) ^ (100 : ℕ)) :
    ‖∑' z, ∑ i : Fin 3, a i z * b i z‖ ≤
      (3 * C * D) * ∑' z : standardModeLattice,
        (sourceWeight (z : E3))⁻¹ ^ (10 : ℕ) := by
  let F : standardModeLattice → ℂ := fun z ↦ ∑ i : Fin 3, a i z * b i z
  let g : standardModeLattice → ℝ := fun z ↦
    (sourceWeight (z : E3))⁻¹ ^ (10 : ℕ)
  have hF : Summable F := by
    exact scratch_summable_threeCoordinateModeProducts_of_decay
      a b C D hC hD ha hb
  have hg : Summable g := by
    exact summable_standardMode_sourceWeight_inv
  have hpoint (z : standardModeLattice) : ‖F z‖ ≤ (3 * C * D) * g z := by
    dsimp only [F, g]
    have hwpos : 0 < sourceWeight (z : E3) := sourceWeight_pos _
    have hwne : sourceWeight (z : E3) ≠ 0 := hwpos.ne'
    have hpow :
        (sourceWeight (z : E3))⁻¹ ^ (110 : ℕ) *
            sourceWeight (z : E3) ^ (100 : ℕ) =
          (sourceWeight (z : E3))⁻¹ ^ (10 : ℕ) := by
      field_simp [hwne]
    have hterm (i : Fin 3) :
        ‖a i z * b i z‖ ≤ C * D *
          (sourceWeight (z : E3))⁻¹ ^ (10 : ℕ) := by
      rw [norm_mul]
      calc
        ‖a i z‖ * ‖b i z‖ ≤
            (C * (sourceWeight (z : E3))⁻¹ ^ (110 : ℕ)) *
              (D * sourceWeight (z : E3) ^ (100 : ℕ)) := by
                apply mul_le_mul (ha i z) (hb i z) (norm_nonneg _)
                exact mul_nonneg hC (pow_nonneg (inv_nonneg.mpr hwpos.le) _)
        _ = C * D *
            ((sourceWeight (z : E3))⁻¹ ^ (110 : ℕ) *
              sourceWeight (z : E3) ^ (100 : ℕ)) := by ring
        _ = _ := by rw [hpow]
    calc
      ‖∑ i : Fin 3, a i z * b i z‖ ≤ ∑ i : Fin 3, ‖a i z * b i z‖ :=
        by simpa using
          (norm_sum_le (Finset.univ : Finset (Fin 3)) (fun i ↦ a i z * b i z))
      _ ≤ ∑ _i : Fin 3, C * D *
          (sourceWeight (z : E3))⁻¹ ^ (10 : ℕ) := by
        exact Finset.sum_le_sum fun i hi ↦ hterm i
      _ = (3 * C * D) *
          (sourceWeight (z : E3))⁻¹ ^ (10 : ℕ) := by
        simp [Fin.sum_univ_succ]
        ring
  calc
    ‖∑' z, ∑ i : Fin 3, a i z * b i z‖ = ‖∑' z, F z‖ := by rfl
    _ ≤ ∑' z, ‖F z‖ := norm_tsum_le_tsum_norm hF.norm
    _ ≤ ∑' z, (3 * C * D) * g z :=
      hF.norm.tsum_le_tsum hpoint (hg.mul_left _)
    _ = (3 * C * D) * ∑' z, g z := hg.tsum_mul_left _

end

end Auto.Twisted
