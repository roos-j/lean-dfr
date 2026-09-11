import Auto.Twisted.Twisted

namespace Auto.Twisted

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal RealInnerProductSpace Topology

noncomputable section

theorem scratch_hasDerivAt_conePhi_nat_scale
    (n : ℕ) (ξ s : ℝ) :
    HasDerivAt (conePhi ∘ fun y : ℝ ↦ y ^ n * ξ)
      ((-coneWeight (s ^ n * ξ)) * ((n : ℝ) * s ^ (n - 1) * ξ)) s := by
  have hpow : HasDerivAt (fun y : ℝ ↦ y ^ n * ξ)
      ((n : ℝ) * s ^ (n - 1) * ξ) s := by
    convert (hasDerivAt_pow n s).mul_const ξ using 1 <;> ring
  exact (hasDerivAt_conePhi (s ^ n * ξ)).comp s hpow

/-- The product of the three anisotropically scaled low-frequency cutoffs. -/
noncomputable def scratch_coneProduct (α : Anisotropy) (ξ : E3) : ℝ → ℝ :=
  ((conePhi ∘ fun t : ℝ ↦ t ^ (α.weight 0) * ξ 0) *
    (conePhi ∘ fun t : ℝ ↦ t ^ (α.weight 1) * ξ 1)) *
      (conePhi ∘ fun t : ℝ ↦ t ^ (α.weight 2) * ξ 2)

/-- Product-rule form of the finite-scale three-cone identity. -/
theorem scratch_hasDerivAt_coneProduct
    (α : Anisotropy) (ξ : E3) (t : ℝ) :
    let A : ℝ → ℝ := conePhi ∘ fun s : ℝ ↦ s ^ (α.weight 0) * ξ 0
    let B : ℝ → ℝ := conePhi ∘ fun s : ℝ ↦ s ^ (α.weight 1) * ξ 1
    let C : ℝ → ℝ := conePhi ∘ fun s : ℝ ↦ s ^ (α.weight 2) * ξ 2
    let d0 : ℝ := -coneWeight (t ^ (α.weight 0) * ξ 0) *
      ((α.weight 0 : ℝ) * t ^ (α.weight 0 - 1) * ξ 0)
    let d1 : ℝ := -coneWeight (t ^ (α.weight 1) * ξ 1) *
      ((α.weight 1 : ℝ) * t ^ (α.weight 1 - 1) * ξ 1)
    let d2 : ℝ := -coneWeight (t ^ (α.weight 2) * ξ 2) *
      ((α.weight 2 : ℝ) * t ^ (α.weight 2 - 1) * ξ 2)
    HasDerivAt ((A * B) * C)
      ((d0 * B t + A t * d1) * C t + (A * B) t * d2) t := by
  dsimp only
  exact
    ((scratch_hasDerivAt_conePhi_nat_scale (α.weight 0) (ξ 0) t).mul
      (scratch_hasDerivAt_conePhi_nat_scale (α.weight 1) (ξ 1) t)).mul
      (scratch_hasDerivAt_conePhi_nat_scale (α.weight 2) (ξ 2) t)

/-- The differentiated product is the three-cone Calderón integrand, with
the identity continuing across the coordinate planes. -/
theorem scratch_neg_mul_deriv_coneProduct
    (α : Anisotropy) (ξ : E3) (t : ℝ) :
    -t * deriv (scratch_coneProduct α ξ) t =
      ((α.weight 0 : ℝ) * conePsi (t ^ (α.weight 0) * ξ 0) *
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
            gaussianDeriv (t ^ (α.weight 2) * ξ 2) ^ 2) := by
  let A : ℝ → ℝ := conePhi ∘ fun s : ℝ ↦ s ^ (α.weight 0) * ξ 0
  let B : ℝ → ℝ := conePhi ∘ fun s : ℝ ↦ s ^ (α.weight 1) * ξ 1
  let C : ℝ → ℝ := conePhi ∘ fun s : ℝ ↦ s ^ (α.weight 2) * ξ 2
  let d0 : ℝ := -coneWeight (t ^ (α.weight 0) * ξ 0) *
    ((α.weight 0 : ℝ) * t ^ (α.weight 0 - 1) * ξ 0)
  let d1 : ℝ := -coneWeight (t ^ (α.weight 1) * ξ 1) *
    ((α.weight 1 : ℝ) * t ^ (α.weight 1 - 1) * ξ 1)
  let d2 : ℝ := -coneWeight (t ^ (α.weight 2) * ξ 2) *
    ((α.weight 2 : ℝ) * t ^ (α.weight 2 - 1) * ξ 2)
  let g0 : ℝ := (α.weight 0 : ℝ) * conePsi (t ^ (α.weight 0) * ξ 0) *
    gaussianDeriv (t ^ (α.weight 0) * ξ 0) ^ 2
  let g1 : ℝ := (α.weight 1 : ℝ) * conePsi (t ^ (α.weight 1) * ξ 1) *
    gaussianDeriv (t ^ (α.weight 1) * ξ 1) ^ 2
  let g2 : ℝ := (α.weight 2 : ℝ) * conePsi (t ^ (α.weight 2) * ξ 2) *
    gaussianDeriv (t ^ (α.weight 2) * ξ 2) ^ 2
  have hderiv : deriv ((A * B) * C) t =
      (d0 * B t + A t * d1) * C t + (A * B) t * d2 :=
    (scratch_hasDerivAt_coneProduct α ξ t).deriv
  have h0 : -t * d0 = g0 := by
    dsimp [d0, g0, coneWeight, gaussianDeriv]
    have hpow : t * t ^ (α.weight 0 - 1) = t ^ (α.weight 0) := by
      calc
        t * t ^ (α.weight 0 - 1) = t ^ (α.weight 0 - 1) * t := by ring
        _ = t ^ ((α.weight 0 - 1) + 1) := (pow_succ t (α.weight 0 - 1)).symm
        _ = t ^ (α.weight 0) := by
          have hpos : 0 < α.weight 0 := α.weight_pos 0
          congr 1
          omega
    rw [← hpow]
    ring
  have h1 : -t * d1 = g1 := by
    dsimp [d1, g1, coneWeight, gaussianDeriv]
    have hpow : t * t ^ (α.weight 1 - 1) = t ^ (α.weight 1) := by
      calc
        t * t ^ (α.weight 1 - 1) = t ^ (α.weight 1 - 1) * t := by ring
        _ = t ^ ((α.weight 1 - 1) + 1) := (pow_succ t (α.weight 1 - 1)).symm
        _ = t ^ (α.weight 1) := by
          have hpos : 0 < α.weight 1 := α.weight_pos 1
          congr 1
          omega
    rw [← hpow]
    ring
  have h2 : -t * d2 = g2 := by
    dsimp [d2, g2, coneWeight, gaussianDeriv]
    have hpow : t * t ^ (α.weight 2 - 1) = t ^ (α.weight 2) := by
      calc
        t * t ^ (α.weight 2 - 1) = t ^ (α.weight 2 - 1) * t := by ring
        _ = t ^ ((α.weight 2 - 1) + 1) := (pow_succ t (α.weight 2 - 1)).symm
        _ = t ^ (α.weight 2) := by
          have hpos : 0 < α.weight 2 := α.weight_pos 2
          congr 1
          omega
    rw [← hpow]
    ring
  change -t * deriv ((A * B) * C) t =
    g0 * B t * C t + A t * g1 * C t + A t * B t * g2
  rw [hderiv]
  have h0' : t * d0 = -g0 := by linarith
  have h1' : t * d1 = -g1 := by linarith
  have h2' : t * d2 = -g2 := by linarith
  calc
    -t * ((d0 * B t + A t * d1) * C t + (A * B) t * d2) =
        (-t * d0) * B t * C t + A t * (-t * d1) * C t +
          A t * B t * (-t * d2) := by
            simp only [Pi.mul_apply]
            ring
    _ = _ := by rw [h0, h1, h2]

/-- Finite-scale telescoping for the three-cone product.  It is valid without
excluding coordinate planes, because the smooth cone weight fills the
removable zero identically. -/
theorem scratch_calderon_coneProduct_interval
    (α : Anisotropy) (ξ : E3) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
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
            gaussianDeriv (t ^ (α.weight 2) * ξ 2) ^ 2)) / t =
      scratch_coneProduct α ξ a - scratch_coneProduct α ξ b := by
  let A : ℝ → ℝ := conePhi ∘ fun s : ℝ ↦ s ^ (α.weight 0) * ξ 0
  let B : ℝ → ℝ := conePhi ∘ fun s : ℝ ↦ s ^ (α.weight 1) * ξ 1
  let C : ℝ → ℝ := conePhi ∘ fun s : ℝ ↦ s ^ (α.weight 2) * ξ 2
  let F : ℝ → ℝ := (A * B) * C
  let G : ℝ → ℝ := fun t ↦
    ((α.weight 0 : ℝ) * conePsi (t ^ (α.weight 0) * ξ 0) *
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
          gaussianDeriv (t ^ (α.weight 2) * ξ 2) ^ 2)
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A := by
    dsimp [A]
    exact conePhi_contDiff.comp
      ((contDiff_id.pow (α.weight 0)).mul contDiff_const)
  have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B := by
    dsimp [B]
    exact conePhi_contDiff.comp
      ((contDiff_id.pow (α.weight 1)).mul contDiff_const)
  have hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) C := by
    dsimp [C]
    exact conePhi_contDiff.comp
      ((contDiff_id.pow (α.weight 2)).mul contDiff_const)
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := hA.mul hB |>.mul hC
  have hInt : IntervalIntegrable (deriv F) volume a b :=
    (hF.continuous_deriv (by norm_num)).intervalIntegrable a b
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hF.continuous.continuousOn
    (fun s _ ↦ (hF.differentiable (by norm_num) s).hasDerivAt)
    hInt
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc a b) : G t / t = -deriv F t := by
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    have hderiv := scratch_neg_mul_deriv_coneProduct α ξ t
    change G t / t = -deriv F t
    rw [div_eq_iff htpos.ne']
    calc
      G t = -t * deriv (scratch_coneProduct α ξ) t := hderiv.symm
      _ = -deriv F t * t := by
        change -t * deriv F t = -deriv F t * t
        ring
  change (∫ t in a..b, G t / t) = F a - F b
  calc
    ∫ t in a..b, G t / t = ∫ t in a..b, -deriv F t := by
      apply intervalIntegral.integral_congr
      rw [Set.uIcc_of_le hab]
      exact fun t ht ↦ hpoint t ht
    _ = -(∫ t in a..b, deriv F t) := by
      rw [intervalIntegral.integral_neg]
    _ = F a - F b := by rw [hFTC]; ring

end

end Auto.Twisted
