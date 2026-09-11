import Auto.Twisted.Twisted

namespace Auto.Twisted

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal Topology

theorem scratch_fourierCoeffOn_of_hasDerivAt_zeroBoundary
    {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (hf : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b)
    (hboundary : f b = f a) :
    fourierCoeffOn hab f n =
      -(1 / (-2 * Real.pi * Complex.I * n)) *
        ((b - a) * fourierCoeffOn hab f' n) := by
  rw [fourierCoeffOn_of_hasDerivAt hab hn hf hf', hboundary, sub_self, mul_zero, zero_sub]
  ring_nf

theorem scratch_norm_fourierCoeffOn_of_hasDerivAt_zeroBoundary
    {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (hf : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b)
    (hboundary : f b = f a) :
    ‖fourierCoeffOn hab f n‖ =
      ‖1 / (-2 * Real.pi * Complex.I * n)‖ * |b - a| * ‖fourierCoeffOn hab f' n‖ := by
  rw [scratch_fourierCoeffOn_of_hasDerivAt_zeroBoundary hab hn hf hf' hboundary]
  simp only [norm_neg, norm_mul]
  have hcast : (↑b : ℂ) - ↑a = ↑(b - a) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  ring

theorem scratch_norm_fourierCoeffOn_le_of_norm_le
    {a b C : ℝ} (hab : a < b) {f : ℝ → ℂ} (n : ℤ)
    (hf : ∀ x ∈ Set.uIoc a b, ‖f x‖ ≤ C) :
    ‖fourierCoeffOn hab f n‖ ≤ C := by
  have hperiod : Fact (0 < b - a) := ⟨by linarith⟩
  letI : Fact (0 < b - a) := hperiod
  rw [fourierCoeffOn_eq_integral]
  have hint : ‖∫ x in a..b,
      fourier (-n) (x : AddCircle (b - a)) • f x‖ ≤ C * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hfourier : ‖fourier (-n) (x : AddCircle (b - a))‖ = 1 := Circle.norm_coe _
    rw [norm_smul, hfourier, one_mul]
    exact hf x hx
  rw [norm_smul, Real.norm_eq_abs]
  calc
    |1 / (b - a)| * ‖∫ x in a..b,
        fourier (-n) (x : AddCircle (b - a)) • f x‖ ≤
        |1 / (b - a)| * (C * |b - a|) :=
      mul_le_mul_of_nonneg_left hint (abs_nonneg _)
    _ = C := by
      rw [abs_of_pos (by positivity : 0 < b - a)]
      rw [abs_of_pos (by positivity : 0 < 1 / (b - a))]
      calc
        1 / (b - a) * (C * (b - a)) =
            C * ((b - a)⁻¹ * (b - a)) := by rw [one_div]; ring
        _ = C := by rw [inv_mul_cancel₀ (ne_of_gt (sub_pos.mpr hab)), mul_one]

theorem scratch_norm_fourier_antideriv_factor (n : ℤ) :
    ‖1 / (-2 * Real.pi * Complex.I * n)‖ =
      (2 * Real.pi * |(n : ℝ)|)⁻¹ := by
  rw [one_div, norm_inv, norm_mul, norm_mul, norm_mul]
  have htwoC : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [norm_neg, htwoC, Complex.norm_real, Complex.norm_I, Complex.norm_intCast]
  simp only [Real.norm_eq_abs]
  rw [abs_of_pos Real.pi_pos]
  simp

theorem scratch_norm_fourierCoeffOn_le_of_deriv_bound
    {a b C : ℝ} (hab : a < b) {f f' : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (hf : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b)
    (hboundary : f b = f a)
    (hbound : ∀ x ∈ Set.uIoc a b, ‖f' x‖ ≤ C) :
    ‖fourierCoeffOn hab f n‖ ≤
      (2 * Real.pi * |(n : ℝ)|)⁻¹ * |b - a| * C := by
  rw [scratch_norm_fourierCoeffOn_of_hasDerivAt_zeroBoundary
    hab hn hf hf' hboundary, scratch_norm_fourier_antideriv_factor]
  exact mul_le_mul_of_nonneg_left
    (scratch_norm_fourierCoeffOn_le_of_norm_le hab n hbound)
    (mul_nonneg (inv_nonneg.mpr (by positivity)) (abs_nonneg _))

theorem scratch_norm_fourierCoeffOn_le_of_four_deriv_bound
    {a b C : ℝ} (hab : a < b) {f0 f1 f2 f3 f4 : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (h0 : ∀ x ∈ Set.uIcc a b, HasDerivAt f0 (f1 x) x)
    (h1 : ∀ x ∈ Set.uIcc a b, HasDerivAt f1 (f2 x) x)
    (h2 : ∀ x ∈ Set.uIcc a b, HasDerivAt f2 (f3 x) x)
    (h3 : ∀ x ∈ Set.uIcc a b, HasDerivAt f3 (f4 x) x)
    (hi1 : IntervalIntegrable f1 volume a b)
    (hi2 : IntervalIntegrable f2 volume a b)
    (hi3 : IntervalIntegrable f3 volume a b)
    (hi4 : IntervalIntegrable f4 volume a b)
    (hb0 : f0 b = f0 a) (hb1 : f1 b = f1 a)
    (hb2 : f2 b = f2 a) (hb3 : f3 b = f3 a)
    (hbound : ∀ x ∈ Set.uIoc a b, ‖f4 x‖ ≤ C) :
    ‖fourierCoeffOn hab f0 n‖ ≤
      ((2 * Real.pi * |(n : ℝ)|)⁻¹ * |b - a|) ^ 4 * C := by
  let d : ℝ := (2 * Real.pi * |(n : ℝ)|)⁻¹ * |b - a|
  have hd : 0 ≤ d := mul_nonneg (inv_nonneg.mpr (by positivity)) (abs_nonneg _)
  have h4 : ‖fourierCoeffOn hab f4 n‖ ≤ C :=
    scratch_norm_fourierCoeffOn_le_of_norm_le hab n hbound
  have heq3 : ‖fourierCoeffOn hab f3 n‖ = d * ‖fourierCoeffOn hab f4 n‖ := by
    rw [show d = ‖1 / (-2 * Real.pi * Complex.I * n)‖ * |b - a| by
      rw [scratch_norm_fourier_antideriv_factor]]
    exact scratch_norm_fourierCoeffOn_of_hasDerivAt_zeroBoundary hab hn h3 hi4 hb3
  have h3bound : ‖fourierCoeffOn hab f3 n‖ ≤ d * C := by
    rw [heq3]
    exact mul_le_mul_of_nonneg_left h4 hd
  have heq2 : ‖fourierCoeffOn hab f2 n‖ = d * ‖fourierCoeffOn hab f3 n‖ := by
    rw [show d = ‖1 / (-2 * Real.pi * Complex.I * n)‖ * |b - a| by
      rw [scratch_norm_fourier_antideriv_factor]]
    exact scratch_norm_fourierCoeffOn_of_hasDerivAt_zeroBoundary hab hn h2 hi3 hb2
  have h2bound : ‖fourierCoeffOn hab f2 n‖ ≤ d * (d * C) := by
    rw [heq2]
    exact mul_le_mul_of_nonneg_left h3bound hd
  have heq1 : ‖fourierCoeffOn hab f1 n‖ = d * ‖fourierCoeffOn hab f2 n‖ := by
    rw [show d = ‖1 / (-2 * Real.pi * Complex.I * n)‖ * |b - a| by
      rw [scratch_norm_fourier_antideriv_factor]]
    exact scratch_norm_fourierCoeffOn_of_hasDerivAt_zeroBoundary hab hn h1 hi2 hb1
  have h1bound : ‖fourierCoeffOn hab f1 n‖ ≤ d * (d * (d * C)) := by
    rw [heq1]
    exact mul_le_mul_of_nonneg_left h2bound hd
  have heq0 : ‖fourierCoeffOn hab f0 n‖ = d * ‖fourierCoeffOn hab f1 n‖ := by
    rw [show d = ‖1 / (-2 * Real.pi * Complex.I * n)‖ * |b - a| by
      rw [scratch_norm_fourier_antideriv_factor]]
    exact scratch_norm_fourierCoeffOn_of_hasDerivAt_zeroBoundary hab hn h0 hi1 hb0
  rw [heq0]
  calc
    d * ‖fourierCoeffOn hab f1 n‖ ≤ d * (d * (d * (d * C))) :=
      mul_le_mul_of_nonneg_left h1bound hd
    _ = d ^ 4 * C := by ring

end Auto.Twisted
