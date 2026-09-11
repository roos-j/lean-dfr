/- Copyright (c) 2026. All rights reserved. -/
import Auto.Twisted.FourierOneDimScratch

namespace Auto.Twisted

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal Topology

noncomputable section

/-- Repeated one-dimensional integration by parts, stated at arbitrary finite
order.  The endpoint equalities are deliberately explicit so compact support
of a torus representative can supply them without an unproved periodicity
shortcut. -/
theorem scratch_norm_fourierCoeffOn_le_of_iteratedDeriv_bound
    {a b C : ℝ} (hab : a < b) {f : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (N : ℕ) (hf : ContDiff ℝ N f)
    (hboundary : ∀ r : ℕ, r < N →
      iteratedDeriv r f b = iteratedDeriv r f a)
    (hbound : ∀ x ∈ Set.uIoc a b, ‖iteratedDeriv N f x‖ ≤ C) :
    ‖fourierCoeffOn hab f n‖ ≤
      ((2 * Real.pi * |(n : ℝ)|)⁻¹ * |b - a|) ^ N * C := by
  induction N generalizing f with
  | zero =>
      simpa using scratch_norm_fourierCoeffOn_le_of_norm_le hab n hbound
  | succ N ih =>
      let g : ℝ → ℂ := deriv f
      have hg : ContDiff ℝ N g := by
        dsimp [g]
        exact hf.deriv'
      have hgboundary : ∀ r : ℕ, r < N →
          iteratedDeriv r g b = iteratedDeriv r g a := by
        intro r hr
        change iteratedDeriv r (deriv f) b = iteratedDeriv r (deriv f) a
        rw [← iteratedDeriv_succ']
        exact hboundary (r + 1) (Nat.succ_lt_succ hr)
      have hgbound : ∀ x ∈ Set.uIoc a b, ‖iteratedDeriv N g x‖ ≤ C := by
        intro x hx
        rw [← iteratedDeriv_succ']
        exact hbound x hx
      have hrec := ih hg hgboundary hgbound
      let d : ℝ := (2 * Real.pi * |(n : ℝ)|)⁻¹ * |b - a|
      have hd : 0 ≤ d := mul_nonneg (inv_nonneg.mpr (by positivity)) (abs_nonneg _)
      have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt f (g x) x := by
        intro x _
        dsimp [g]
        exact (hf.differentiable_iteratedDeriv 0
          (by exact_mod_cast Nat.zero_lt_succ N)).differentiableAt.hasDerivAt
      have hgint : IntervalIntegrable g volume a b := by
        exact (hf.continuous_deriv
          (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N))).intervalIntegrable a b
      have hzero : f b = f a := by
        simpa using hboundary 0 (by omega)
      have hstep : ‖fourierCoeffOn hab f n‖ = d * ‖fourierCoeffOn hab g n‖ := by
        dsimp [d]
        rw [show (2 * Real.pi * |(n : ℝ)|)⁻¹ * |b - a| =
            ‖1 / (-2 * Real.pi * Complex.I * n)‖ * |b - a| by
              rw [scratch_norm_fourier_antideriv_factor]]
        exact scratch_norm_fourierCoeffOn_of_hasDerivAt_zeroBoundary
          hab hn hderiv hgint hzero
      rw [hstep]
      calc
        d * ‖fourierCoeffOn hab g n‖ ≤ d * (d ^ N * C) :=
          mul_le_mul_of_nonneg_left hrec hd
        _ = d ^ (N + 1) * C := by ring

end

end Auto.Twisted
