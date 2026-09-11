import Auto.Twisted.Twisted

namespace Auto.Twisted

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal RealInnerProductSpace Topology

noncomputable section

/-- The low-frequency Calderón cutoff is nonnegative. -/
theorem scratch_conePhi_nonneg (x : ℝ) :
    0 ≤ conePhi x := by
  by_cases hx : |x| ≤ 2
  · rw [conePhi_eq_tail]
    exact intervalIntegral.integral_nonneg hx fun y hy ↦
      coneWeight_nonneg_of_nonneg (le_trans (abs_nonneg x) hy.1)
  · have hx' : 2 ≤ |x| := le_of_lt (lt_of_not_ge hx)
    rw [conePhi_eq_zero_of_two_le_abs hx']

/-- The low-frequency cutoff never exceeds its positive Calderón mass. -/
theorem scratch_conePhi_le_cPsi (x : ℝ) :
    conePhi x ≤ cPsi := by
  by_cases hx : |x| ≤ 2
  · rw [conePhi_eq_tail, cPsi]
    apply intervalIntegral.integral_mono_interval (c := (0 : ℝ)) (d := 2)
      (by positivity) hx (by norm_num) ?_
      (coneWeight_contDiff.continuous.intervalIntegrable _ _)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact coneWeight_nonneg_of_nonneg hy.1.le
  · have hx' : 2 ≤ |x| := le_of_lt (lt_of_not_ge hx)
    rw [conePhi_eq_zero_of_two_le_abs hx']
    exact le_of_lt cPsi_pos

/-- The smooth primitive differentiates to the Calderón density. -/
theorem scratch_hasDerivAt_conePrimitive (x : ℝ) :
    HasDerivAt conePrimitive (coneWeight x) x := by
  unfold conePrimitive
  exact intervalIntegral.integral_hasDerivAt_right
    (coneWeight_contDiff.continuous.intervalIntegrable _ _)
    coneWeight_contDiff.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    coneWeight_contDiff.continuous.continuousAt

/-- The derivative of the low-frequency cutoff is the negative Calderón
density, including at the removable origin. -/
theorem scratch_hasDerivAt_conePhi (x : ℝ) :
    HasDerivAt conePhi (-coneWeight x) x := by
  unfold conePhi
  have hfun : (fun y : ℝ ↦ cPsi - conePrimitive y) =
      (fun _ : ℝ ↦ cPsi) - conePrimitive := by
    funext y
    rfl
  rw [hfun]
  simpa using (hasDerivAt_const x cPsi).sub (scratch_hasDerivAt_conePrimitive x)

theorem scratch_deriv_conePhi (x : ℝ) :
    deriv conePhi x = -coneWeight x :=
  (scratch_hasDerivAt_conePhi x).deriv

/-- The one-dimensional differential Calderón identity at an anisotropic
natural scale. -/
theorem scratch_neg_mul_deriv_conePhi_nat_scale
    (n : ℕ) (hn : 0 < n) (ξ t : ℝ) (hξ : ξ ≠ 0) (ht : 0 < t) :
    -t * deriv (fun s : ℝ ↦ conePhi (s ^ n * ξ)) t =
      (n : ℝ) * conePsi (t ^ n * ξ) * gaussianDeriv (t ^ n * ξ) ^ 2 := by
  have hpow : HasDerivAt (fun s : ℝ ↦ s ^ n * ξ)
      ((n : ℝ) * t ^ (n - 1) * ξ) t := by
    convert (hasDerivAt_pow n t).mul_const ξ using 1 <;> ring
  have hcomp := (scratch_hasDerivAt_conePhi (t ^ n * ξ)).comp t hpow
  have hderiv : deriv (fun s : ℝ ↦ conePhi (s ^ n * ξ)) t =
      (-coneWeight (t ^ n * ξ)) * ((n : ℝ) * t ^ (n - 1) * ξ) :=
    hcomp.deriv
  rw [hderiv]
  have htn : t ^ n * ξ ≠ 0 := mul_ne_zero (pow_ne_zero _ ht.ne') hξ
  have hpow' : t * t ^ (n - 1) = t ^ n := by
    calc
      t * t ^ (n - 1) = t ^ (n - 1) * t := by ring
      _ = t ^ ((n - 1) + 1) := (pow_succ t (n - 1)).symm
      _ = t ^ n := by congr 1 <;> omega
  rw [coneWeight_eq_source_integrand htn]
  field_simp
  calc
    t * conePsi (t ^ n * ξ) * gaussianDeriv (t ^ n * ξ) ^ 2 * t ^ (n - 1) =
        (t * t ^ (n - 1)) * conePsi (t ^ n * ξ) * gaussianDeriv (t ^ n * ξ) ^ 2 := by
          ring
    _ = _ := by rw [hpow']

/-- Integrating the differential identity gives the finite-scale Calderón
telescoping formula. -/
theorem scratch_calderon_interval_nat_scale
    (n : ℕ) (hn : 0 < n) (ξ a b : ℝ) (hξ : ξ ≠ 0)
    (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b,
      (n : ℝ) * conePsi (t ^ n * ξ) * gaussianDeriv (t ^ n * ξ) ^ 2 / t =
        conePhi (a ^ n * ξ) - conePhi (b ^ n * ξ) := by
  let F : ℝ → ℝ :=
    (fun _ : ℝ ↦ cPsi) - conePrimitive ∘ (fun s : ℝ ↦ s ^ n * ξ)
  let F' : ℝ → ℝ := fun s ↦
    (-coneWeight (s ^ n * ξ)) * ((n : ℝ) * s ^ (n - 1) * ξ)
  have hpowcont : Continuous (fun s : ℝ ↦ s ^ n * ξ) :=
    (continuous_pow n).mul continuous_const
  have hFcont : Continuous F := by
    dsimp [F]
    exact continuous_const.sub (conePrimitive_contDiff.continuous.comp hpowcont)
  have hF'cont : Continuous F' := by
    dsimp [F']
    exact (coneWeight_contDiff.continuous.comp hpowcont).neg.mul
      ((continuous_const.mul (continuous_pow (n - 1))).mul continuous_const)
  have hFderiv (s : ℝ) : HasDerivAt F (F' s) s := by
    have hpow : HasDerivAt (fun y : ℝ ↦ y ^ n * ξ)
        ((n : ℝ) * s ^ (n - 1) * ξ) s := by
      convert (hasDerivAt_pow n s).mul_const ξ using 1 <;> ring
    have hprim := (hasDerivAt_conePrimitive (s ^ n * ξ)).comp s hpow
    have h := (hasDerivAt_const s cPsi).sub hprim
    simpa only [F, F', Pi.sub_apply, Pi.zero_apply, zero_sub, neg_mul] using h
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hFcont.continuousOn (fun s _ ↦ hFderiv s) (hF'cont.intervalIntegrable _ _)
  have hneg : (∫ t in a..b, -F' t) = F a - F b := by
    rw [intervalIntegral.integral_neg, hFTC]
    ring
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc a b) :
      (n : ℝ) * conePsi (t ^ n * ξ) * gaussianDeriv (t ^ n * ξ) ^ 2 / t =
        -F' t := by
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    change (n : ℝ) * conePsi (t ^ n * ξ) * gaussianDeriv (t ^ n * ξ) ^ 2 / t =
      -F' t
    dsimp [F']
    have htn : t ^ n * ξ ≠ 0 := mul_ne_zero (pow_ne_zero _ htpos.ne') hξ
    have hpow' : t * t ^ (n - 1) = t ^ n := by
      calc
        t * t ^ (n - 1) = t ^ (n - 1) * t := by ring
        _ = t ^ ((n - 1) + 1) := (pow_succ t (n - 1)).symm
        _ = t ^ n := by congr 1 <;> omega
    rw [coneWeight_eq_source_integrand htn]
    field_simp
    rw [← hpow']
    ring
  calc
    ∫ t in a..b,
        (n : ℝ) * conePsi (t ^ n * ξ) * gaussianDeriv (t ^ n * ξ) ^ 2 / t =
        ∫ t in a..b, -F' t := by
          apply intervalIntegral.integral_congr
          rw [Set.uIcc_of_le hab]
          exact fun t ht ↦ hpoint t ht
    _ = F a - F b := hneg
    _ = conePhi (a ^ n * ξ) - conePhi (b ^ n * ξ) := by
      have hFapply (s : ℝ) : F s = conePhi (s ^ n * ξ) := by
        dsimp [F, conePhi]
      rw [hFapply a, hFapply b]

end

end Auto.Twisted
