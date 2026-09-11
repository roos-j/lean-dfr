/- Copyright (c) 2026. All rights reserved. -/
import Auto.Twisted.Twisted

namespace Auto
namespace Twisted

open scoped BigOperators

noncomputable section

/-! ## Scratch geometry for the three strict active initial ranges

The three active model forms have different analytic kernels, but their
reciprocal-exponent ranges admit a particularly simple common convex cover.
This file records the literal finite barycentric identity, independently of
any interpolation theorem for the forms.
-/

/-- The reciprocal form of the strict initial range when input coordinate
`i` is active.  It is the `2/4` stopping threshold in reciprocal variables. -/
def scratchActiveInitialReciprocalRegion
    (β0 : ℝ) (β : Fin 3 → ℝ) (i : Fin 3) : Prop :=
  0 < β0 ∧ β0 < (1 : ℝ) / 4 ∧
    (∀ j, 0 < β j) ∧ β0 + ∑ j, β j = 1 ∧
    β i < (1 : ℝ) / 2 ∧ ∀ j, j ≠ i → β j < (1 : ℝ) / 4

/-- The reciprocal inequalities occurring in the main theorem, with the
three input coordinates grouped into a `Fin 3` tuple. -/
def scratchMainReciprocalRegion (β0 : ℝ) (β : Fin 3 → ℝ) : Prop :=
  0 < β0 ∧ β0 < (1 : ℝ) / 4 ∧
    (∀ j, (1 : ℝ) / 4 < β j) ∧ β0 + ∑ j, β j = 1

/-- The strict active vertex at fixed output reciprocal `β0`: its active
input reciprocal is twice either passive input reciprocal. -/
def scratchActiveInitialVertex (β0 : ℝ) (i j : Fin 3) : ℝ :=
  if j = i then (1 - β0) / 2 else (1 - β0) / 4

/-- The barycentric weight of the active vertex `i` at a main-region point. -/
def scratchActiveInitialWeight (β0 : ℝ) (β : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  (β i - (1 - β0) / 4) / ((1 - β0) / 4)

/-- Each displayed vertex lies strictly in its corresponding active initial
range. -/
theorem scratch_activeInitialVertex_mem_activeInitialReciprocalRegion
    {β0 : ℝ} (hβ0 : 0 < β0) (hβ0lt : β0 < (1 : ℝ) / 4) (i : Fin 3) :
    scratchActiveInitialReciprocalRegion β0
      (scratchActiveInitialVertex β0 i) i := by
  have hbasepos : 0 < (1 - β0) / 4 := by linarith
  have hsum : β0 + ∑ j : Fin 3, scratchActiveInitialVertex β0 i j = 1 := by
    fin_cases i <;>
      simp [scratchActiveInitialVertex, Fin.sum_univ_three] <;> ring
  refine ⟨hβ0, hβ0lt, ?_, hsum, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simp [scratchActiveInitialVertex]
      linarith
    · simp [scratchActiveInitialVertex, hji]
      linarith
  · simp [scratchActiveInitialVertex]
    linarith
  · intro j hji
    simp [scratchActiveInitialVertex, hji]
    linarith

/-- Every main-region reciprocal tuple is a strict convex combination of
one strict initial-range point for each of the three active coordinates.

The identity is purely geometric: it makes no claim that the three active
model forms are a single operator to which multilinear interpolation applies. -/
theorem scratch_mainReciprocalRegion_strict_activeVertex_decomposition
    {β0 : ℝ} {β : Fin 3 → ℝ}
    (h : scratchMainReciprocalRegion β0 β) :
    (∀ i, scratchActiveInitialReciprocalRegion β0
      (scratchActiveInitialVertex β0 i) i) ∧
    (∀ i, 0 < scratchActiveInitialWeight β0 β i) ∧
    (∑ i : Fin 3, scratchActiveInitialWeight β0 β i = 1) ∧
    (β0 = ∑ i : Fin 3, scratchActiveInitialWeight β0 β i * β0) ∧
    (∀ j : Fin 3, β j = ∑ i : Fin 3,
      scratchActiveInitialWeight β0 β i * scratchActiveInitialVertex β0 i j) := by
  rcases h with ⟨hβ0, hβ0lt, hβ, hsum⟩
  let a : ℝ := (1 - β0) / 4
  have hapos : 0 < a := by
    dsimp [a]
    linarith
  have hane : a ≠ 0 := ne_of_gt hapos
  have hsumβ : ∑ i : Fin 3, β i = 4 * a := by
    calc
      ∑ i : Fin 3, β i = 1 - β0 := by linarith [hsum]
      _ = 4 * a := by
        dsimp [a]
        ring
  have hconstsum : ∑ _ : Fin 3, a = 3 * a := by
    simp
  have hweightsum : ∑ i : Fin 3, scratchActiveInitialWeight β0 β i = 1 := by
    change ∑ i : Fin 3, (β i - a) / a = 1
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hsumβ, hconstsum]
    field_simp [hane]
    norm_num
  have hvertex (i j : Fin 3) : scratchActiveInitialVertex β0 i j =
      if j = i then 2 * a else a := by
    by_cases hji : j = i
    · simp [scratchActiveInitialVertex, hji, a]
      ring
    · simp [scratchActiveInitialVertex, hji, a]
  have hterm (i j : Fin 3) :
      scratchActiveInitialWeight β0 β i * scratchActiveInitialVertex β0 i j =
        if j = i then 2 * (β i - a) else β i - a := by
    rw [hvertex]
    change ((β i - a) / a) * (if j = i then 2 * a else a) = _
    by_cases hji : j = i
    · simp [hji]
      field_simp [hane]
    · simp [hji]
      field_simp [hane]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact scratch_activeInitialVertex_mem_activeInitialReciprocalRegion hβ0 hβ0lt i
  · intro i
    change 0 < (β i - a) / a
    exact div_pos (by
      dsimp [a]
      linarith [hβ i]) hapos
  · exact hweightsum
  · calc
      β0 = 1 * β0 := by ring
      _ = (∑ i : Fin 3, scratchActiveInitialWeight β0 β i) * β0 := by
        rw [hweightsum]
      _ = ∑ i : Fin 3, scratchActiveInitialWeight β0 β i * β0 := by
        rw [Finset.sum_mul]
  · intro j
    rw [show ∑ i : Fin 3, scratchActiveInitialWeight β0 β i *
        scratchActiveInitialVertex β0 i j =
      ∑ i : Fin 3, if j = i then 2 * (β i - a) else β i - a by
        apply Finset.sum_congr rfl
        intro i _
        exact hterm i j]
    have hsumβthree : β 0 + β 1 + β 2 = 4 * a := by
      simpa [Fin.sum_univ_three] using hsumβ
    fin_cases j <;>
      simp [Fin.sum_univ_three] <;>
      linarith [hsumβthree]

end
end Twisted
end Auto
