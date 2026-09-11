import Auto.Twisted.Twisted

namespace Auto.Twisted

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal RealInnerProductSpace Topology

noncomputable section

/-- At a scale at which every coordinate lies in the low-frequency plateau,
the three-cone product has its full Calderón mass. -/
theorem scratch_coneProduct_eq_cPsi_pow_of_small
    (α : Anisotropy) (ξ : E3) (t : ℝ)
    (h : ∀ i : Fin 3, |t ^ (α.weight i) * ξ i| ≤ 1) :
    coneProduct α ξ t = cPsi ^ 3 := by
  change (conePhi (t ^ (α.weight 0) * ξ 0) *
      conePhi (t ^ (α.weight 1) * ξ 1)) *
        conePhi (t ^ (α.weight 2) * ξ 2) = cPsi ^ 3
  rw [conePhi_eq_cPsi_of_abs_le_one (h 0),
    conePhi_eq_cPsi_of_abs_le_one (h 1),
    conePhi_eq_cPsi_of_abs_le_one (h 2)]
  ring

/-- If one coordinate lies outside the high-frequency support, the product
cutoff vanishes. -/
theorem scratch_coneProduct_eq_zero_of_large
    (α : Anisotropy) (ξ : E3) (t : ℝ)
    (h : ∃ i : Fin 3, 2 ≤ |t ^ (α.weight i) * ξ i|) :
    coneProduct α ξ t = 0 := by
  rcases h with ⟨i, hi⟩
  fin_cases i
  · have hi' : 2 ≤ |t ^ (α.weight 0) * ξ 0| := by simpa using hi
    change (conePhi (t ^ (α.weight 0) * ξ 0) *
      conePhi (t ^ (α.weight 1) * ξ 1)) *
        conePhi (t ^ (α.weight 2) * ξ 2) = 0
    rw [conePhi_eq_zero_of_two_le_abs hi']
    ring
  · have hi' : 2 ≤ |t ^ (α.weight 1) * ξ 1| := by simpa using hi
    change (conePhi (t ^ (α.weight 0) * ξ 0) *
      conePhi (t ^ (α.weight 1) * ξ 1)) *
        conePhi (t ^ (α.weight 2) * ξ 2) = 0
    rw [conePhi_eq_zero_of_two_le_abs hi']
    ring
  · have hi' : 2 ≤ |t ^ (α.weight 2) * ξ 2| := by simpa using hi
    change (conePhi (t ^ (α.weight 0) * ξ 0) *
      conePhi (t ^ (α.weight 1) * ξ 1)) *
        conePhi (t ^ (α.weight 2) * ξ 2) = 0
    rw [conePhi_eq_zero_of_two_le_abs hi']
    ring

/-- The finite interval form of the cone identity once its natural endpoints
have been chosen. -/
theorem scratch_calderon_coneProduct_interval_of_endpoints
    (α : Anisotropy) (ξ : E3) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b)
    (hsmall : coneProduct α ξ a = cPsi ^ 3)
    (hlarge : coneProduct α ξ b = 0) :
    ∫ t in a..b,
      (((α.weight 0 : ℝ) * conePsi (t ^ (α.weight 0) * ξ 0) *
          gaussianDeriv (t ^ (α.weight 0) * ξ 0) ^ 2) *
        conePhi (t ^ (α.weight 1) * ξ 1) *
          conePhi (t ^ (α.weight 2) * ξ 2) +
      conePhi (t ^ (α.weight 0) * ξ 0) *
        ((α.weight 1 : ℝ) * conePsi (t ^ (α.weight 1) * ξ 1) *
          gaussianDeriv (t ^ (α.weight 1) * ξ 1) ^ 2) *
          conePhi (t ^ (α.weight 2) * ξ 2) +
      conePhi (t ^ (α.weight 0) * ξ 0) *
        conePhi (t ^ (α.weight 1) * ξ 1) *
          ((α.weight 2 : ℝ) * conePsi (t ^ (α.weight 2) * ξ 2) *
            gaussianDeriv (t ^ (α.weight 2) * ξ 2) ^ 2)) / t = cPsi ^ 3 := by
  rw [calderon_coneProduct_interval α ξ a b ha hab, hsmall, hlarge]
  ring

/-- Every nonzero three-frequency has positive finite scales at which the
three-cone product respectively equals its full mass and vanishes. -/
theorem scratch_exists_coneProduct_endpoints
    (α : Anisotropy) (ξ : E3) (hξ : ξ ≠ 0) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      coneProduct α ξ a = cPsi ^ 3 ∧ coneProduct α ξ b = 0 := by
  obtain ⟨i, hξi⟩ : ∃ i : Fin 3, ξ i ≠ 0 := by
    by_contra h
    apply hξ
    ext j
    apply not_ne_iff.mp
    intro hj
    exact h ⟨j, hj⟩
  let R : ℝ := max |ξ 0| (max |ξ 1| |ξ 2|)
  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hR (j : Fin 3) : |ξ j| ≤ R := by
    fin_cases j
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  let a : ℝ := 1 / (1 + R)
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
  have hsmall : ∀ j : Fin 3, |a ^ (α.weight j) * ξ j| ≤ 1 := by
    intro j
    have hpow : a ^ (α.weight j) ≤ a :=
      pow_le_of_le_one ha.le haone (Nat.ne_zero_of_lt (α.weight_pos j))
    rw [abs_mul, abs_of_nonneg (pow_nonneg ha.le _)]
    calc
      a ^ (α.weight j) * |ξ j| ≤ a * |ξ j| :=
        mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
      _ ≤ a * R := mul_le_mul_of_nonneg_left (hR j) ha.le
      _ ≤ 1 := haR
  let b : ℝ := max 1 (2 / |ξ i|)
  have hb_one : 1 ≤ b := le_max_left _ _
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb_one
  have hab : a ≤ b := haone.trans hb_one
  have habs : 0 < |ξ i| := abs_pos.mpr hξi
  have hpowb : b ≤ b ^ (α.weight i) :=
    by
      simpa only [pow_one] using
        (pow_le_pow_right₀ hb_one
          (Nat.one_le_iff_ne_zero.mpr (Nat.ne_zero_of_lt (α.weight_pos i))))
  have hlargei : 2 ≤ |b ^ (α.weight i) * ξ i| := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hb.le _)]
    calc
      2 ≤ b * |ξ i| :=
        (div_le_iff₀ habs).mp (le_max_right _ _)
      _ ≤ b ^ (α.weight i) * |ξ i| :=
        mul_le_mul_of_nonneg_right hpowb (abs_nonneg _)
  refine ⟨a, b, ha, hab,
    scratch_coneProduct_eq_cPsi_pow_of_small α ξ a hsmall, ?_⟩
  exact scratch_coneProduct_eq_zero_of_large α ξ b ⟨i, hlargei⟩

/-- The finite positive scale interval can always be chosen to recover the
entire three-cone Calderón mass at a nonzero frequency. -/
theorem scratch_exists_calderon_coneProduct_interval
    (α : Anisotropy) (ξ : E3) (hξ : ξ ≠ 0) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∫ t in a..b,
        (((α.weight 0 : ℝ) * conePsi (t ^ (α.weight 0) * ξ 0) *
            gaussianDeriv (t ^ (α.weight 0) * ξ 0) ^ 2) *
          conePhi (t ^ (α.weight 1) * ξ 1) *
            conePhi (t ^ (α.weight 2) * ξ 2) +
        conePhi (t ^ (α.weight 0) * ξ 0) *
          ((α.weight 1 : ℝ) * conePsi (t ^ (α.weight 1) * ξ 1) *
            gaussianDeriv (t ^ (α.weight 1) * ξ 1) ^ 2) *
            conePhi (t ^ (α.weight 2) * ξ 2) +
        conePhi (t ^ (α.weight 0) * ξ 0) *
          conePhi (t ^ (α.weight 1) * ξ 1) *
            ((α.weight 2 : ℝ) * conePsi (t ^ (α.weight 2) * ξ 2) *
              gaussianDeriv (t ^ (α.weight 2) * ξ 2) ^ 2)) / t = cPsi ^ 3 := by
  obtain ⟨a, b, ha, hab, hsmall, hlarge⟩ :=
    scratch_exists_coneProduct_endpoints α ξ hξ
  exact ⟨a, b, ha, hab,
    scratch_calderon_coneProduct_interval_of_endpoints
      α ξ a b ha hab hsmall hlarge⟩

end

end Auto.Twisted
