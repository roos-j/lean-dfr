/- Copyright (c) 2026. All rights reserved.
   SPDX-License-Identifier: Apache-2.0 -/

import Auto.Twisted.Twisted

namespace Auto
namespace Twisted

open scoped BigOperators

noncomputable section

/-! ## Finite trilinear atomic expansion

The four-vertex interpolation step ultimately reduces finite simple inputs to
their dyadic atoms.  This file isolates the purely algebraic three-input
summation estimate, so the analytic restricted estimates can later be fed in
without re-proving multilinearity bookkeeping. -/

/-- A complex trilinear form evaluated on three finite atomic sums is bounded
by the corresponding triple sum of its atomic bounds. -/
theorem scratch_norm_trilinear_finset_sum_le
    {F G H : Type*} [AddCommMonoid F] [AddCommMonoid G] [AddCommMonoid H]
    [Module ℂ F] [Module ℂ G] [Module ℂ H]
    {ι κ ξ : Type*} (B : F →ₗ[ℂ] G →ₗ[ℂ] H →ₗ[ℂ] ℂ)
    (s : Finset ι) (t : Finset κ) (r : Finset ξ)
    (u : ι → F) (v : κ → G) (w : ξ → H)
    (a : ι → ℂ) (b : κ → ℂ) (d : ξ → ℂ)
    (M : ι → κ → ξ → ℝ)
    (hM : ∀ i ∈ s, ∀ j ∈ t, ∀ k ∈ r,
      ‖B (u i) (v j) (w k)‖ ≤ M i j k) :
    ‖B (∑ i ∈ s, a i • u i) (∑ j ∈ t, b j • v j)
        (∑ k ∈ r, d k • w k)‖ ≤
      ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r,
        ‖a i‖ * ‖b j‖ * ‖d k‖ * M i j k := by
  have hexpand :
      B (∑ i ∈ s, a i • u i) (∑ j ∈ t, b j • v j)
          (∑ k ∈ r, d k • w k) =
        ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r,
          (a i * b j * d k) • B (u i) (v j) (w k) := by
    calc
      B (∑ i ∈ s, a i • u i) (∑ j ∈ t, b j • v j)
          (∑ k ∈ r, d k • w k) =
        ∑ i ∈ s, B (a i • u i) (∑ j ∈ t, b j • v j)
          (∑ k ∈ r, d k • w k) := by
            rw [map_sum B, LinearMap.sum_apply, LinearMap.sum_apply]
      _ = ∑ i ∈ s, ∑ j ∈ t, B (a i • u i) (b j • v j)
          (∑ k ∈ r, d k • w k) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [map_sum (B (a i • u i)), LinearMap.sum_apply]
      _ = ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r,
          B (a i • u i) (b j • v j) (d k • w k) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [map_sum (B (a i • u i) (b j • v j))]
      _ = ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r,
          (a i * b j * d k) • B (u i) (v j) (w k) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro k hk
            simp only [map_smul, LinearMap.smul_apply, smul_smul]
            ring
  rw [hexpand]
  calc
    ‖∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r,
        (a i * b j * d k) • B (u i) (v j) (w k)‖ ≤
        ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r,
          ‖(a i * b j * d k) • B (u i) (v j) (w k)‖ := by
      refine le_trans (norm_sum_le _ _) ?_
      apply Finset.sum_le_sum
      intro i hi
      refine le_trans (norm_sum_le _ _) ?_
      apply Finset.sum_le_sum
      intro j hj
      exact norm_sum_le _ _
    _ = ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r,
        ‖a i‖ * ‖b j‖ * ‖d k‖ * ‖B (u i) (v j) (w k)‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_smul, norm_mul, norm_mul]
    _ ≤ ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r,
        ‖a i‖ * ‖b j‖ * ‖d k‖ * M i j k := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hM i hi j hj k hk)
        (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))

/-- Vector-valued version of the finite trilinear atomic expansion.  The
output carrier can later be a normed function space, leaving the analytic
restricted-type estimate separate from the algebraic multilinearity step. -/
theorem scratch_norm_trilinear_finset_sum_le_vector
    {F G H K : Type*} [AddCommMonoid F] [AddCommMonoid G] [AddCommMonoid H]
    [Module ℂ F] [Module ℂ G] [Module ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    {ι κ ξ : Type*} (B : F →ₗ[ℂ] G →ₗ[ℂ] H →ₗ[ℂ] K)
    (s : Finset ι) (t : Finset κ) (r : Finset ξ)
    (u : ι → F) (v : κ → G) (w : ξ → H)
    (a : ι → ℂ) (b : κ → ℂ) (d : ξ → ℂ)
    (M : ι → κ → ξ → ℝ)
    (hM : ∀ i ∈ s, ∀ j ∈ t, ∀ k ∈ r,
      ‖B (u i) (v j) (w k)‖ ≤ M i j k) :
    ‖B (∑ i ∈ s, a i • u i) (∑ j ∈ t, b j • v j)
        (∑ k ∈ r, d k • w k)‖ ≤
      ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r,
        ‖a i‖ * ‖b j‖ * ‖d k‖ * M i j k := by
  have hexpand :
      B (∑ i ∈ s, a i • u i) (∑ j ∈ t, b j • v j)
          (∑ k ∈ r, d k • w k) =
        ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r,
          (a i * b j * d k) • B (u i) (v j) (w k) := by
    calc
      B (∑ i ∈ s, a i • u i) (∑ j ∈ t, b j • v j)
          (∑ k ∈ r, d k • w k) =
        ∑ i ∈ s, B (a i • u i) (∑ j ∈ t, b j • v j)
          (∑ k ∈ r, d k • w k) := by
            rw [map_sum B, LinearMap.sum_apply, LinearMap.sum_apply]
      _ = ∑ i ∈ s, ∑ j ∈ t, B (a i • u i) (b j • v j)
          (∑ k ∈ r, d k • w k) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [map_sum (B (a i • u i)), LinearMap.sum_apply]
      _ = ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r,
          B (a i • u i) (b j • v j) (d k • w k) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [map_sum (B (a i • u i) (b j • v j))]
      _ = ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r,
          (a i * b j * d k) • B (u i) (v j) (w k) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro k hk
            simp only [map_smul, LinearMap.smul_apply, smul_smul]
            ring
  rw [hexpand]
  calc
    ‖∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r,
        (a i * b j * d k) • B (u i) (v j) (w k)‖ ≤
        ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r,
          ‖(a i * b j * d k) • B (u i) (v j) (w k)‖ := by
      refine le_trans (norm_sum_le _ _) ?_
      apply Finset.sum_le_sum
      intro i hi
      refine le_trans (norm_sum_le _ _) ?_
      apply Finset.sum_le_sum
      intro j hj
      exact norm_sum_le _ _
    _ = ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r,
        ‖a i‖ * ‖b j‖ * ‖d k‖ * ‖B (u i) (v j) (w k)‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_smul, norm_mul, norm_mul]
    _ ≤ ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r,
        ‖a i‖ * ‖b j‖ * ‖d k‖ * M i j k := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hM i hi j hj k hk)
        (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))

/-- The elementary eight-term expansion behind a simultaneous three-input
amplitude split.  It is the pointwise algebra required before endpoint weak
distribution estimates can be applied term by term. -/
theorem scratch_norm_trilinear_eight_split_le
    {F G H K : Type*} [Add F] [Add G] [Add H] [NormedAddCommGroup K]
    (T : F → G → H → K)
    (haddF : ∀ f f' g h, T (f + f') g h = T f g h + T f' g h)
    (haddG : ∀ f g g' h, T f (g + g') h = T f g h + T f g' h)
    (haddH : ∀ f g h h', T f g (h + h') = T f g h + T f g h')
    (f0 g0 : F) (f1 g1 : G) (f2 g2 : H) :
    ‖T (f0 + g0) (f1 + g1) (f2 + g2)‖ ≤
      ‖T f0 f1 f2‖ + ‖T f0 f1 g2‖ +
        ‖T f0 g1 f2‖ + ‖T f0 g1 g2‖ +
          ‖T g0 f1 f2‖ + ‖T g0 f1 g2‖ +
            ‖T g0 g1 f2‖ + ‖T g0 g1 g2‖ := by
  have hexpand :
      T (f0 + g0) (f1 + g1) (f2 + g2) =
        (T f0 f1 f2 + T f0 f1 g2) +
          (T f0 g1 f2 + T f0 g1 g2) +
            ((T g0 f1 f2 + T g0 f1 g2) +
              (T g0 g1 f2 + T g0 g1 g2)) := by
    simp_rw [haddF, haddG, haddH]
  rw [hexpand]
  calc
    ‖(T f0 f1 f2 + T f0 f1 g2) +
        (T f0 g1 f2 + T f0 g1 g2) +
          ((T g0 f1 f2 + T g0 f1 g2) +
            (T g0 g1 f2 + T g0 g1 g2))‖ ≤
        ‖(T f0 f1 f2 + T f0 f1 g2) +
          (T f0 g1 f2 + T f0 g1 g2)‖ +
          ‖(T g0 f1 f2 + T g0 f1 g2) +
            (T g0 g1 f2 + T g0 g1 g2)‖ := norm_add_le _ _
    _ ≤ (‖T f0 f1 f2‖ + ‖T f0 f1 g2‖) +
          (‖T f0 g1 f2‖ + ‖T f0 g1 g2‖) +
            ((‖T g0 f1 f2‖ + ‖T g0 f1 g2‖) +
              (‖T g0 g1 f2‖ + ‖T g0 g1 g2‖)) := by
      calc
        ‖(T f0 f1 f2 + T f0 f1 g2) +
            (T f0 g1 f2 + T f0 g1 g2)‖ +
            ‖(T g0 f1 f2 + T g0 f1 g2) +
              (T g0 g1 f2 + T g0 g1 g2)‖ ≤
            (‖T f0 f1 f2 + T f0 f1 g2‖ +
              ‖T f0 g1 f2 + T f0 g1 g2‖) +
              (‖T g0 f1 f2 + T g0 f1 g2‖ +
                ‖T g0 g1 f2 + T g0 g1 g2‖) := by
              exact add_le_add (norm_add_le _ _) (norm_add_le _ _)
        _ ≤ (‖T f0 f1 f2‖ + ‖T f0 f1 g2‖) +
              (‖T f0 g1 f2‖ + ‖T f0 g1 g2‖) +
                ((‖T g0 f1 f2‖ + ‖T g0 f1 g2‖) +
                  (‖T g0 g1 f2‖ + ‖T g0 g1 g2‖)) := by
              exact add_le_add
                (add_le_add (norm_add_le _ _) (norm_add_le _ _))
                (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ = ‖T f0 f1 f2‖ + ‖T f0 f1 g2‖ +
        ‖T f0 g1 f2‖ + ‖T f0 g1 g2‖ +
          ‖T g0 f1 f2‖ + ‖T g0 f1 g2‖ +
            ‖T g0 g1 f2‖ + ‖T g0 g1 g2‖ := by ring

/-- If a three-input split is large at a level `s`, at least one of its
eight multilinear pieces is large at the divided level `s / 8`.  This is the
finite union step preceding the weak-distribution estimate in a genuine
multilinear Marcinkiewicz proof. -/
theorem scratch_trilinear_eight_split_exists_large
    {F G H K : Type*} [Add F] [Add G] [Add H] [NormedAddCommGroup K]
    (T : F → G → H → K)
    (haddF : ∀ f f' g h, T (f + f') g h = T f g h + T f' g h)
    (haddG : ∀ f g g' h, T f (g + g') h = T f g h + T f g' h)
    (haddH : ∀ f g h h', T f g (h + h') = T f g h + T f g h')
    (f0 g0 : F) (f1 g1 : G) (f2 g2 : H) (s : ℝ)
    (_hs : 0 < s)
    (hlarge : s < ‖T (f0 + g0) (f1 + g1) (f2 + g2)‖) :
    s / 8 < ‖T f0 f1 f2‖ ∨ s / 8 < ‖T f0 f1 g2‖ ∨
      s / 8 < ‖T f0 g1 f2‖ ∨ s / 8 < ‖T f0 g1 g2‖ ∨
        s / 8 < ‖T g0 f1 f2‖ ∨ s / 8 < ‖T g0 f1 g2‖ ∨
          s / 8 < ‖T g0 g1 f2‖ ∨ s / 8 < ‖T g0 g1 g2‖ := by
  by_contra hnone
  push Not at hnone
  rcases hnone with ⟨h000, h001, h010, h011, h100, h101, h110, h111⟩
  have hsplit := scratch_norm_trilinear_eight_split_le T haddF haddG haddH
    f0 g0 f1 g1 f2 g2
  have hsum :
      ‖T f0 f1 f2‖ + ‖T f0 f1 g2‖ +
        ‖T f0 g1 f2‖ + ‖T f0 g1 g2‖ +
          ‖T g0 f1 f2‖ + ‖T g0 f1 g2‖ +
            ‖T g0 g1 f2‖ + ‖T g0 g1 g2‖ ≤ s := by
    nlinarith
  linarith

/-- The trilinear finite expansion becomes a product of three atomic sums
when the atomwise estimate is separable.  This is the summation terminal
needed by an open-neighbourhood restricted-type argument. -/
theorem scratch_norm_trilinear_finset_sum_le_of_separable_majorant
    {F G H : Type*} [AddCommMonoid F] [AddCommMonoid G] [AddCommMonoid H]
    [Module ℂ F] [Module ℂ G] [Module ℂ H]
    {ι κ ξ : Type*} (B : F →ₗ[ℂ] G →ₗ[ℂ] H →ₗ[ℂ] ℂ)
    (s : Finset ι) (t : Finset κ) (r : Finset ξ)
    (u : ι → F) (v : κ → G) (w : ξ → H)
    (a : ι → ℂ) (b : κ → ℂ) (d : ξ → ℂ)
    (A : ι → ℝ) (D : κ → ℝ) (E : ξ → ℝ) (C : ℝ)
    (_hC : 0 ≤ C) (_hA : ∀ i ∈ s, 0 ≤ A i)
    (_hD : ∀ j ∈ t, 0 ≤ D j) (_hE : ∀ k ∈ r, 0 ≤ E k)
    (hpair : ∀ i ∈ s, ∀ j ∈ t, ∀ k ∈ r,
      ‖B (u i) (v j) (w k)‖ ≤ C * A i * D j * E k) :
    ‖B (∑ i ∈ s, a i • u i) (∑ j ∈ t, b j • v j)
        (∑ k ∈ r, d k • w k)‖ ≤
      C * (∑ i ∈ s, ‖a i‖ * A i) *
        (∑ j ∈ t, ‖b j‖ * D j) *
        (∑ k ∈ r, ‖d k‖ * E k) := by
  have hmain := scratch_norm_trilinear_finset_sum_le B s t r u v w a b d
    (fun i j k => C * A i * D j * E k) hpair
  calc
    ‖B (∑ i ∈ s, a i • u i) (∑ j ∈ t, b j • v j)
        (∑ k ∈ r, d k • w k)‖ ≤
        ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r,
          ‖a i‖ * ‖b j‖ * ‖d k‖ * (C * A i * D j * E k) := hmain
    _ = C * (∑ i ∈ s, ‖a i‖ * A i) *
        (∑ j ∈ t, ‖b j‖ * D j) *
        (∑ k ∈ r, ‖d k‖ * E k) := by
      let X : ι → ℝ := fun i => ‖a i‖ * A i
      let Y : κ → ℝ := fun j => ‖b j‖ * D j
      let Z : ξ → ℝ := fun k => ‖d k‖ * E k
      have hcollapse :
          C * (∑ i ∈ s, X i) * (∑ j ∈ t, Y j) * (∑ k ∈ r, Z k) =
            ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r, C * X i * Y j * Z k := by
        calc
          C * (∑ i ∈ s, X i) * (∑ j ∈ t, Y j) * (∑ k ∈ r, Z k) =
              (∑ i ∈ s, C * X i) * (∑ j ∈ t, Y j) * (∑ k ∈ r, Z k) := by
                exact congrArg (fun q : ℝ => q * (∑ j ∈ t, Y j) *
                  (∑ k ∈ r, Z k)) (Finset.mul_sum s (fun i => X i) C)
          _ = (∑ i ∈ s, (C * X i) * (∑ j ∈ t, Y j)) *
              (∑ k ∈ r, Z k) := by
                rw [Finset.sum_mul]
          _ = (∑ i ∈ s, ∑ j ∈ t, (C * X i) * Y j) *
              (∑ k ∈ r, Z k) := by
                apply congrArg (fun q : ℝ => q * (∑ k ∈ r, Z k))
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.mul_sum]
          _ = ∑ i ∈ s, (∑ j ∈ t, (C * X i) * Y j) *
              (∑ k ∈ r, Z k) := by
                rw [Finset.sum_mul]
          _ = ∑ i ∈ s, ∑ j ∈ t, ((C * X i) * Y j) *
              (∑ k ∈ r, Z k) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.sum_mul]
          _ = ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r,
              ((C * X i) * Y j) * Z k := by
                apply Finset.sum_congr rfl
                intro i hi
                apply Finset.sum_congr rfl
                intro j hj
                rw [Finset.mul_sum]
          _ = ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r, C * X i * Y j * Z k := by
                apply Finset.sum_congr rfl
                intro i hi
                apply Finset.sum_congr rfl
                intro j hj
                apply Finset.sum_congr rfl
                intro k hk
                ring
      calc
        (∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r,
            ‖a i‖ * ‖b j‖ * ‖d k‖ * (C * A i * D j * E k)) =
            ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ r, C * X i * Y j * Z k := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              apply Finset.sum_congr rfl
              intro k hk
              dsimp only [X, Y, Z]
              ring
        _ = C * (∑ i ∈ s, X i) * (∑ j ∈ t, Y j) *
            (∑ k ∈ r, Z k) := hcollapse.symm
        _ = C * (∑ i ∈ s, ‖a i‖ * A i) *
            (∑ j ∈ t, ‖b j‖ * D j) *
            (∑ k ∈ r, ‖d k‖ * E k) := by rfl

end
end Twisted
end Auto
