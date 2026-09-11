import Auto.Twisted.Twisted

namespace Auto
namespace Twisted

open MeasureTheory Filter
open scoped BigOperators ENNReal

/-! ### Scalar scale-tail integration -/

/-- The elementary shifted power integral needed after the substitution in
the bad-fiber scale tail. -/
theorem scratch_integral_Ioi_one_add_rpow (n : ℝ) (hn : 1 < n) :
    ∫ t : ℝ in Set.Ioi 0, (t + 1) ^ (-n) = (n - 1)⁻¹ := by
  have hd : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ ↦ (t + 1) ^ ((-n) + 1) / ((-n) + 1))
        ((x + 1) ^ (-n)) x := by
    intro x hx
    convert! (((hasDerivAt_id x).add_const 1).rpow_const _).div_const _ using 1
    · simp [show (-n) + 1 ≠ 0 by linarith]
    · left
      simp only [id_eq]
      linarith [Set.mem_Ici.mp hx]
  have hint : IntegrableOn (fun t : ℝ ↦ (t + 1) ^ (-n)) (Set.Ioi 0) := by
    simpa only using
      (integrableOn_add_rpow_Ioi_of_lt (a := -n) (c := 0) (m := 1)
        (by linarith) (by norm_num))
  have ht : Tendsto (fun t : ℝ ↦ (t + 1) ^ ((-n) + 1) / ((-n) + 1))
      atTop (nhds (0 / ((-n) + 1))) := by
    rw [← neg_neg ((-n) + 1)]
    exact (tendsto_rpow_neg_atTop (by linarith : 0 < -((-n) + 1))).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_id) |>.div_const _
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hd hint ht
  rw [hmain]
  simp only [zero_div, zero_add, Real.one_rpow, zero_sub]
  rw [one_div, ← inv_neg]
  ring

/-- The beta-type scalar integral in the source scale calculation. -/
theorem scratch_integral_Ioi_weighted_one_add_tail :
    ∫ y : ℝ in Set.Ioi 0, y * (y + 1) ^ (-10 : ℝ) = 1 / 72 := by
  have h9 : IntegrableOn (fun y : ℝ ↦ (y + 1) ^ (-9 : ℝ)) (Set.Ioi 0) := by
    simpa using
      (integrableOn_add_rpow_Ioi_of_lt (a := (-9 : ℝ)) (c := 0) (m := 1)
        (by norm_num) (by norm_num))
  have h10 : IntegrableOn (fun y : ℝ ↦ (y + 1) ^ (-10 : ℝ)) (Set.Ioi 0) := by
    simpa using
      (integrableOn_add_rpow_Ioi_of_lt (a := (-10 : ℝ)) (c := 0) (m := 1)
        (by norm_num) (by norm_num))
  have hident : ∀ y ∈ Set.Ioi (0 : ℝ),
      y * (y + 1) ^ (-10 : ℝ) =
        (y + 1) ^ (-9 : ℝ) - (y + 1) ^ (-10 : ℝ) := by
    intro y hy
    have hy1 : 0 < y + 1 := by linarith [Set.mem_Ioi.mp hy]
    rw [Real.rpow_neg hy1.le, Real.rpow_neg hy1.le]
    field_simp
    calc
      y * (y + 1) ^ (9 : ℝ) = ((y + 1) - 1) * (y + 1) ^ (9 : ℝ) := by ring
      _ = (y + 1) ^ (10 : ℝ) - (y + 1) ^ (9 : ℝ) := by
        rw [show (10 : ℝ) = 9 + 1 by norm_num, Real.rpow_add hy1,
          Real.rpow_one]
        ring
  calc
    (∫ y : ℝ in Set.Ioi 0, y * (y + 1) ^ (-10 : ℝ)) =
        ∫ y : ℝ in Set.Ioi 0,
          ((y + 1) ^ (-9 : ℝ) - (y + 1) ^ (-10 : ℝ)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact hident y hy
    _ = (∫ y : ℝ in Set.Ioi 0, (y + 1) ^ (-9 : ℝ)) -
        ∫ y : ℝ in Set.Ioi 0, (y + 1) ^ (-10 : ℝ) := by
      exact MeasureTheory.integral_sub h9 h10
    _ = 1 / 72 := by
      rw [scratch_integral_Ioi_one_add_rpow 9 (by norm_num),
        scratch_integral_Ioi_one_add_rpow 10 (by norm_num)]
      norm_num

/-- Scaling the beta-type tail supplies the distance-squared decay produced
by the bad-fiber scale integration. -/
theorem scratch_integral_Ioi_scaled_weighted_one_add_tail (d : ℝ) (hd : 0 < d) :
    ∫ x : ℝ in Set.Ioi 0, x * (1 + d * x) ^ (-10 : ℝ) = d⁻¹ ^ 2 * (1 / 72) := by
  let g : ℝ → ℝ := fun y ↦ y * (y + 1) ^ (-10 : ℝ)
  have hcomp := MeasureTheory.integral_comp_mul_left_Ioi g 0 hd
  have hfun : (fun x : ℝ ↦ g (d * x)) =
      fun x ↦ d * (x * (1 + d * x) ^ (-10 : ℝ)) := by
    funext x
    dsimp only [g]
    have hbase : d * x + 1 = 1 + d * x := by ring
    rw [hbase]
    ring
  have hgint : ∫ x : ℝ in Set.Ioi (d * 0), g x = 1 / 72 := by
    simp only [mul_zero, g]
    exact scratch_integral_Ioi_weighted_one_add_tail
  rw [hfun, integral_const_mul, hgint] at hcomp
  have hcomp' : d * (∫ x : ℝ in Set.Ioi 0,
      x * (1 + d * x) ^ (-10 : ℝ)) = d⁻¹ * (1 / 72) := by
    simpa only [smul_eq_mul] using hcomp
  calc
    (∫ x : ℝ in Set.Ioi 0, x * (1 + d * x) ^ (-10 : ℝ)) =
        d⁻¹ * (d * (∫ x : ℝ in Set.Ioi 0,
          x * (1 + d * x) ^ (-10 : ℝ))) := by
      symm
      rw [← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul]
    _ = d⁻¹ * (d⁻¹ * (1 / 72)) := by rw [hcomp']
    _ = d⁻¹ ^ 2 * (1 / 72) := by ring

/-- The exact scalar scale integral in the bad-fiber calculation.  The
substitution is `x = t^{-α}` and its Jacobian is kept explicit. -/
theorem scratch_integral_Ioi_scale_badFiber_tail
    (α d : ℝ) (hα : 0 < α) (hd : 0 < d) :
    (∫ t : ℝ in Set.Ioi 0,
      t ^ (-2 * α) * (1 + d * t ^ (-α)) ^ (-10 : ℝ) * t⁻¹) =
      α⁻¹ * d⁻¹ ^ 2 * (1 / 72) := by
  let g : ℝ → ℝ := fun x ↦ α⁻¹ * (x * (1 + d * x) ^ (-10 : ℝ))
  have hchange := MeasureTheory.integral_comp_rpow_Ioi g
    (show (-α) ≠ 0 by linarith)
  have hleft :
      (∫ t : ℝ in Set.Ioi 0,
        (|(-α)| * t ^ ((-α) - 1)) • g (t ^ (-α))) =
        ∫ t : ℝ in Set.Ioi 0,
          t ^ (-2 * α) * (1 + d * t ^ (-α)) ^ (-10 : ℝ) * t⁻¹ := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := Set.mem_Ioi.mp ht
    dsimp only [g]
    rw [abs_neg, abs_of_pos hα, smul_eq_mul]
    calc
      (α * t ^ ((-α) - 1)) *
          (α⁻¹ * (t ^ (-α) * (1 + d * t ^ (-α)) ^ (-10 : ℝ))) =
          (α * α⁻¹) * (t ^ ((-α) - 1) * t ^ (-α)) *
            (1 + d * t ^ (-α)) ^ (-10 : ℝ) := by ring
      _ = t ^ (((-α) - 1) + (-α)) *
            (1 + d * t ^ (-α)) ^ (-10 : ℝ) := by
          rw [mul_inv_cancel₀ hα.ne', one_mul, ← Real.rpow_add ht0]
      _ = t ^ (-2 * α) * (1 + d * t ^ (-α)) ^ (-10 : ℝ) * t⁻¹ := by
          rw [show ((-α) - 1) + (-α) = (-2 * α) + (-1 : ℝ) by ring,
            Real.rpow_add ht0, Real.rpow_neg_one]
          ring
  have hright : (∫ x : ℝ in Set.Ioi 0, g x) =
      α⁻¹ * (d⁻¹ ^ 2 * (1 / 72)) := by
    dsimp only [g]
    rw [integral_const_mul, scratch_integral_Ioi_scaled_weighted_one_add_tail d hd]
  calc
    (∫ t : ℝ in Set.Ioi 0,
      t ^ (-2 * α) * (1 + d * t ^ (-α)) ^ (-10 : ℝ) * t⁻¹) =
        ∫ t : ℝ in Set.Ioi 0,
          (|(-α)| * t ^ ((-α) - 1)) • g (t ^ (-α)) := hleft.symm
    _ = ∫ x : ℝ in Set.Ioi 0, g x := hchange
    _ = α⁻¹ * d⁻¹ ^ 2 * (1 / 72) := by
      rw [hright]
      ring

/-- The source bracket kernel, with its outer cancellation derivative factor,
is literally the scalar scale-tail integrand. -/
theorem scratch_scale_bracketKernelAt_eq_badFiber_tail
    (t α d : ℝ) (ht : 0 < t) :
    (t ^ α)⁻¹ * bracketKernelAt (t ^ α) 0 d =
      t ^ (-2 * α) * (1 + |d| * t ^ (-α)) ^ (-10 : ℝ) := by
  have hs : 0 < t ^ α := Real.rpow_pos_of_pos ht _
  unfold bracketKernelAt kernelAt kernelDilate bracketKernel
  simp only [sub_zero, smul_eq_mul, abs_div, abs_of_pos hs]
  rw [← Real.rpow_neg ht.le]
  calc
    t ^ (-α) * (t ^ (-α) *
        (1 + |d| / t ^ α) ^ (-10 : ℝ)) =
        (t ^ (-α) * t ^ (-α)) * (1 + |d| / t ^ α) ^ (-10 : ℝ) := by ring
    _ = t ^ ((-α) + (-α)) * (1 + |d| / t ^ α) ^ (-10 : ℝ) := by
      rw [← Real.rpow_add ht]
    _ = t ^ (-2 * α) * (1 + |d| * t ^ (-α)) ^ (-10 : ℝ) := by
      rw [show (-α) + (-α) = -2 * α by ring]
      congr 2
      rw [div_eq_mul_inv, ← Real.rpow_neg ht.le]

/-- Integrating the derivative-sized bracket majorant over all scales gives
the exact inverse-square distance tail used outside a doubled bad interval. -/
theorem scratch_integral_Ioi_scale_bracketKernelAt
    (α d : ℝ) (hα : 0 < α) (hd : 0 < |d|) :
    (∫ t : ℝ in Set.Ioi 0,
      (t ^ α)⁻¹ * bracketKernelAt (t ^ α) 0 d * t⁻¹) =
      α⁻¹ * |d|⁻¹ ^ 2 * (1 / 72) := by
  calc
    (∫ t : ℝ in Set.Ioi 0,
      (t ^ α)⁻¹ * bracketKernelAt (t ^ α) 0 d * t⁻¹) =
        ∫ t : ℝ in Set.Ioi 0,
          t ^ (-2 * α) * (1 + |d| * t ^ (-α)) ^ (-10 : ℝ) * t⁻¹ := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change (t ^ α)⁻¹ * bracketKernelAt (t ^ α) 0 d * t⁻¹ =
        t ^ (-2 * α) * (1 + |d| * t ^ (-α)) ^ (-10 : ℝ) * t⁻¹
      rw [scratch_scale_bracketKernelAt_eq_badFiber_tail t α d (Set.mem_Ioi.mp ht)]
    _ = α⁻¹ * |d|⁻¹ ^ 2 * (1 / 72) :=
      scratch_integral_Ioi_scale_badFiber_tail α |d| hα hd

/-- The literal scale bracket majorant is integrable on the positive scale
half-line.  This removes the remaining scalar side condition from the
scale-integrated bad-fiber estimate. -/
theorem scratch_integrableOn_Ioi_scale_bracketKernelAt
    (α d : ℝ) (hα : 0 < α) (hd : 0 < |d|) :
    IntegrableOn (fun t : ℝ ↦
      (t ^ α)⁻¹ * bracketKernelAt (t ^ α) 0 d * t⁻¹) (Set.Ioi 0) := by
  let G : ℝ → ℝ := fun y ↦ y * (y + 1) ^ (-10 : ℝ)
  have hG₉ : IntegrableOn (fun y : ℝ ↦ (y + 1) ^ (-9 : ℝ))
      (Set.Ioi 0) := by
    simpa using
      (integrableOn_add_rpow_Ioi_of_lt (a := (-9 : ℝ)) (c := 0) (m := 1)
        (by norm_num) (by norm_num))
  have hG₁₀ : IntegrableOn (fun y : ℝ ↦ (y + 1) ^ (-10 : ℝ))
      (Set.Ioi 0) := by
    simpa using
      (integrableOn_add_rpow_Ioi_of_lt (a := (-10 : ℝ)) (c := 0) (m := 1)
        (by norm_num) (by norm_num))
  have hG_ident : ∀ y ∈ Set.Ioi (0 : ℝ),
      G y = (y + 1) ^ (-9 : ℝ) - (y + 1) ^ (-10 : ℝ) := by
    intro y hy
    dsimp only [G]
    have hy1 : 0 < y + 1 := by linarith [Set.mem_Ioi.mp hy]
    rw [Real.rpow_neg hy1.le, Real.rpow_neg hy1.le]
    field_simp
    calc
      y * (y + 1) ^ (9 : ℝ) = ((y + 1) - 1) * (y + 1) ^ (9 : ℝ) := by ring
      _ = (y + 1) ^ (10 : ℝ) - (y + 1) ^ (9 : ℝ) := by
        rw [show (10 : ℝ) = 9 + 1 by norm_num, Real.rpow_add hy1,
          Real.rpow_one]
        ring
  have hG : IntegrableOn G (Set.Ioi 0) := by
    refine (hG₉.sub hG₁₀).congr_fun ?_ measurableSet_Ioi
    intro y hy
    exact (hG_ident y hy).symm
  have hscaled_raw : IntegrableOn (fun y : ℝ ↦ G (|d| * y))
      (Set.Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff G 0 hd).mpr (by
      simpa only [mul_zero] using hG)
  have hscaled : IntegrableOn (fun y : ℝ ↦
      y * (1 + |d| * y) ^ (-10 : ℝ)) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun (hscaled_raw.const_mul |d|⁻¹) ?_ measurableSet_Ioi
    intro y hy
    dsimp only [G]
    have hd0 : |d| ≠ 0 := ne_of_gt hd
    have hbase : |d| * y + 1 = 1 + |d| * y := by ring
    rw [hbase]
    field_simp
  let g : ℝ → ℝ := fun y ↦ α⁻¹ *
    (y * (1 + |d| * y) ^ (-10 : ℝ))
  have hg : IntegrableOn g (Set.Ioi 0) := by
    exact hscaled.const_mul α⁻¹
  have hchange : IntegrableOn (fun t : ℝ ↦
      (|(-α)| * t ^ ((-α) - 1)) • g (t ^ (-α))) (Set.Ioi 0) :=
    (integrableOn_Ioi_comp_rpow_iff g (show (-α) ≠ 0 by linarith)).mpr hg
  refine hchange.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := Set.mem_Ioi.mp ht
  dsimp only [g]
  rw [scratch_scale_bracketKernelAt_eq_badFiber_tail t α d ht0,
    abs_neg, abs_of_pos hα, smul_eq_mul]
  calc
    (α * t ^ ((-α) - 1)) *
        (α⁻¹ * (t ^ (-α) * (1 + |d| * t ^ (-α)) ^ (-10 : ℝ))) =
        (α * α⁻¹) * (t ^ ((-α) - 1) * t ^ (-α)) *
          (1 + |d| * t ^ (-α)) ^ (-10 : ℝ) := by ring
    _ = t ^ (((-α) - 1) + (-α)) *
          (1 + |d| * t ^ (-α)) ^ (-10 : ℝ) := by
      rw [mul_inv_cancel₀ hα.ne', one_mul, ← Real.rpow_add ht0]
    _ = t ^ (-2 * α) * (1 + |d| * t ^ (-α)) ^ (-10 : ℝ) * t⁻¹ := by
      rw [show ((-α) - 1) + (-α) = (-2 * α) + (-1 : ℝ) by ring,
        Real.rpow_add ht0, Real.rpow_neg_one]
      ring

/-- Integrating the canonical interval-radius cancellation bound across the
source scale measure gives the exact inverse-square bad-fiber tail.  The
explicit integrability hypothesis is the only remaining Fubini-facing
interface at this point. -/
theorem scratch_integral_badFiber_scaleTail_of_interval_radius_mass_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i j : Fin 3) (u : E3) (α x c r A : ℝ)
      (b : ℝ → ℝ), 0 < α → 0 < r → Integrable b →
      (∀ t : ℝ, t ∈ Set.Ioi 0 → Integrable (fun y ↦ b y *
        kernelDilate (activeModelKernel i j u) (t ^ α) (x - y))) →
      (∫ y : ℝ, b y) = 0 →
      (∀ y : ℝ, b y ≠ 0 → |y - c| ≤ r) →
      2 * r ≤ |x - c| →
      (∫ y : ℝ, |b y|) ≤ A * r →
      IntegrableOn (fun t : ℝ ↦
        (t ^ α)⁻¹ * bracketKernelAt (t ^ α) 0 (x - c) * t⁻¹) (Set.Ioi 0) →
      (∫ t : ℝ in Set.Ioi 0,
        |∫ y : ℝ, b y *
          kernelDilate (activeModelKernel i j u) (t ^ α) (x - y)| * t⁻¹) ≤
        C * sourceWeight u ^ 10 * A * r ^ 2 *
          (α⁻¹ * |x - c|⁻¹ ^ 2 * (1 / 72)) := by
  rcases abs_integral_activeModelKernel_badFiber_of_interval_radius_mass_bound with
    ⟨C, hC, hcancel⟩
  refine ⟨C, hC, ?_⟩
  intro i j u α x c r A b hα hr hb hkernel hzero hsupport hfar hmass hmajor
  have hd : 0 < |x - c| := by
    exact lt_of_lt_of_le (by nlinarith) hfar
  let Q : ℝ := C * sourceWeight u ^ 10 * A * r ^ 2
  let K : ℝ → ℝ := fun t ↦
    (t ^ α)⁻¹ * bracketKernelAt (t ^ α) 0 (x - c) * t⁻¹
  have hpoint (t : ℝ) (ht : t ∈ Set.Ioi 0) :
      |∫ y : ℝ, b y *
        kernelDilate (activeModelKernel i j u) (t ^ α) (x - y)| * t⁻¹ ≤
        Q * K t := by
    have hs : 0 < t ^ α := Real.rpow_pos_of_pos (Set.mem_Ioi.mp ht) _
    have hbase := hcancel i j u (t ^ α) x c r A b hs hr.le hb
      (hkernel t ht) hzero hsupport hfar hmass
    calc
      |∫ y : ℝ, b y *
          kernelDilate (activeModelKernel i j u) (t ^ α) (x - y)| * t⁻¹ ≤
          (C * sourceWeight u ^ 10 * (t ^ α)⁻¹ *
            bracketKernelAt (t ^ α) 0 (x - c) * A * r ^ 2) * t⁻¹ :=
        mul_le_mul_of_nonneg_right hbase (inv_nonneg.mpr (Set.mem_Ioi.mp ht).le)
      _ = Q * K t := by
        dsimp only [Q, K]
        ring
  have hmono :
      (∫ t : ℝ in Set.Ioi 0,
        |∫ y : ℝ, b y *
          kernelDilate (activeModelKernel i j u) (t ^ α) (x - y)| * t⁻¹) ≤
        ∫ t : ℝ in Set.Ioi 0, Q * K t := by
    apply integral_mono_of_nonneg
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (abs_nonneg _) (inv_nonneg.mpr (Set.mem_Ioi.mp ht).le)
    · change Integrable (fun t ↦ Q * K t) (volume.restrict (Set.Ioi 0))
      exact hmajor.const_mul Q
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hpoint t ht
  calc
    (∫ t : ℝ in Set.Ioi 0,
      |∫ y : ℝ, b y *
        kernelDilate (activeModelKernel i j u) (t ^ α) (x - y)| * t⁻¹) ≤
        ∫ t : ℝ in Set.Ioi 0, Q * K t := hmono
    _ = Q * ∫ t : ℝ in Set.Ioi 0, K t := by rw [integral_const_mul]
    _ = Q * (α⁻¹ * |x - c|⁻¹ ^ 2 * (1 / 72)) := by
      rw [scratch_integral_Ioi_scale_bracketKernelAt α (x - c) hα hd]
    _ = C * sourceWeight u ^ 10 * A * r ^ 2 *
        (α⁻¹ * |x - c|⁻¹ ^ 2 * (1 / 72)) := by
      rfl

/-- Outside the doubled interval, the scale-integrated cancellation term is
controlled directly by the source interval tail.  This is the pointwise
bad-coordinate input to the subsequent three-factor Hölder step. -/
theorem scratch_integral_badFiber_scaleTail_le_intervalTail :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i j : Fin 3) (u : E3) (α x c r A : ℝ)
      (b : ℝ → ℝ), 0 < α → 0 < r → Integrable b →
      (∀ t : ℝ, t ∈ Set.Ioi 0 → Integrable (fun y ↦ b y *
        kernelDilate (activeModelKernel i j u) (t ^ α) (x - y))) →
      (∫ y : ℝ, b y) = 0 →
      (∀ y : ℝ, b y ≠ 0 → |y - c| ≤ r) →
      2 * r ≤ |x - c| →
      (∫ y : ℝ, |b y|) ≤ A * r →
      IntegrableOn (fun t : ℝ ↦
        (t ^ α)⁻¹ * bracketKernelAt (t ^ α) 0 (x - c) * t⁻¹) (Set.Ioi 0) →
      (∫ t : ℝ in Set.Ioi 0,
        |∫ y : ℝ, b y *
          kernelDilate (activeModelKernel i j u) (t ^ α) (x - y)| * t⁻¹) ≤
        C * sourceWeight u ^ 10 * A * (α⁻¹ * (1 / 72)) *
          intervalTail c (2 * r) x := by
  rcases scratch_integral_badFiber_scaleTail_of_interval_radius_mass_bound with
    ⟨C, hC, hscale⟩
  refine ⟨C, hC, ?_⟩
  intro i j u α x c r A b hα hr hb hkernel hzero hsupport hfar hmass hmajor
  have hd : 0 < |x - c| := by
    exact lt_of_lt_of_le (by nlinarith) hfar
  have hA : 0 ≤ A := by
    have hAr : 0 ≤ A * r :=
      le_trans (integral_nonneg fun y ↦ abs_nonneg (b y)) hmass
    nlinarith
  have htail := radius_sq_div_distance_sq_le_intervalTail_of_double_far hr hfar
  have hbase := hscale i j u α x c r A b hα hr hb hkernel hzero hsupport hfar
    hmass hmajor
  have hfactor : 0 ≤ C * sourceWeight u ^ 10 * A * (α⁻¹ * (1 / 72)) := by
    positivity
  have hinv : |x - c|⁻¹ ^ 2 = 1 / |x - c| ^ 2 := by
    field_simp [hd.ne']
  calc
    (∫ t : ℝ in Set.Ioi 0,
      |∫ y : ℝ, b y *
        kernelDilate (activeModelKernel i j u) (t ^ α) (x - y)| * t⁻¹) ≤
        C * sourceWeight u ^ 10 * A * r ^ 2 *
          (α⁻¹ * |x - c|⁻¹ ^ 2 * (1 / 72)) := hbase
    _ = (C * sourceWeight u ^ 10 * A * (α⁻¹ * (1 / 72))) *
        (r ^ 2 / |x - c| ^ 2) := by
      rw [hinv]
      field_simp [hd.ne']
    _ ≤ (C * sourceWeight u ^ 10 * A * (α⁻¹ * (1 / 72))) *
        intervalTail c (2 * r) x :=
      mul_le_mul_of_nonneg_left htail hfactor

/-- The scale-majorant integrability in the preceding interval-tail estimate
is automatic; this is the literal no-extra-hypothesis scalar terminal used
by a finite bad-fiber sum. -/
theorem scratch_integral_badFiber_scaleTail_of_interval_radius_mass_bound_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i j : Fin 3) (u : E3) (α x c r A : ℝ)
      (b : ℝ → ℝ), 0 < α → 0 < r → Integrable b →
      (∀ t : ℝ, t ∈ Set.Ioi 0 → Integrable (fun y ↦ b y *
        kernelDilate (activeModelKernel i j u) (t ^ α) (x - y))) →
      (∫ y : ℝ, b y) = 0 →
      (∀ y : ℝ, b y ≠ 0 → |y - c| ≤ r) →
      2 * r ≤ |x - c| →
      (∫ y : ℝ, |b y|) ≤ A * r →
      (∫ t : ℝ in Set.Ioi 0,
        |∫ y : ℝ, b y *
          kernelDilate (activeModelKernel i j u) (t ^ α) (x - y)| * t⁻¹) ≤
        C * sourceWeight u ^ 10 * A * r ^ 2 *
          (α⁻¹ * |x - c|⁻¹ ^ 2 * (1 / 72)) := by
  rcases scratch_integral_badFiber_scaleTail_of_interval_radius_mass_bound with
    ⟨C, hC, hmain⟩
  refine ⟨C, hC, ?_⟩
  intro i j u α x c r A b hα hr hb hkernel hzero hsupport hfar hmass
  exact hmain i j u α x c r A b hα hr hb hkernel hzero hsupport hfar hmass
    (scratch_integrableOn_Ioi_scale_bracketKernelAt α (x - c) hα (by
      exact lt_of_lt_of_le (by nlinarith) hfar))

/-- Outside a doubled bad interval, the scale-integrated cancellation tail
has the source interval-tail bound with no auxiliary integrability premise. -/
theorem scratch_integral_badFiber_scaleTail_le_intervalTail_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i j : Fin 3) (u : E3) (α x c r A : ℝ)
      (b : ℝ → ℝ), 0 < α → 0 < r → Integrable b →
      (∀ t : ℝ, t ∈ Set.Ioi 0 → Integrable (fun y ↦ b y *
        kernelDilate (activeModelKernel i j u) (t ^ α) (x - y))) →
      (∫ y : ℝ, b y) = 0 →
      (∀ y : ℝ, b y ≠ 0 → |y - c| ≤ r) →
      2 * r ≤ |x - c| →
      (∫ y : ℝ, |b y|) ≤ A * r →
      (∫ t : ℝ in Set.Ioi 0,
        |∫ y : ℝ, b y *
          kernelDilate (activeModelKernel i j u) (t ^ α) (x - y)| * t⁻¹) ≤
        C * sourceWeight u ^ 10 * A * (α⁻¹ * (1 / 72)) *
          intervalTail c (2 * r) x := by
  rcases scratch_integral_badFiber_scaleTail_le_intervalTail with
    ⟨C, hC, hmain⟩
  refine ⟨C, hC, ?_⟩
  intro i j u α x c r A b hα hr hb hkernel hzero hsupport hfar hmass
  exact hmain i j u α x c r A b hα hr hb hkernel hzero hsupport hfar hmass
    (scratch_integrableOn_Ioi_scale_bracketKernelAt α (x - c) hα (by
      exact lt_of_lt_of_le (by nlinarith) hfar))

/-- Summing the literal scale-integrated cancellation estimate over a finite
bad-interval family produces the exact positive interval-tail majorant.  The
same mass coefficient `A` is the source `H^(1/p)` factor. -/
theorem scratch_finset_integral_badFiber_scaleTail_le_intervalTail_sum :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} (S : Finset ι)
      (i j : Fin 3) (u : E3) (α x A : ℝ) (c r : ι → ℝ)
      (b : ι → ℝ → ℝ), 0 < α →
      (∀ k ∈ S, 0 < r k) →
      (∀ k ∈ S, Integrable (b k)) →
      (∀ k ∈ S, ∀ t : ℝ, t ∈ Set.Ioi 0 → Integrable (fun y ↦ b k y *
        kernelDilate (activeModelKernel i j u) (t ^ α) (x - y))) →
      (∀ k ∈ S, (∫ y : ℝ, b k y) = 0) →
      (∀ k ∈ S, ∀ y : ℝ, b k y ≠ 0 → |y - c k| ≤ r k) →
      (∀ k ∈ S, 2 * r k ≤ |x - c k|) →
      (∀ k ∈ S, (∫ y : ℝ, |b k y|) ≤ A * r k) →
      (∑ k ∈ S, ∫ t : ℝ in Set.Ioi 0,
        |∫ y : ℝ, b k y *
          kernelDilate (activeModelKernel i j u) (t ^ α) (x - y)| * t⁻¹) ≤
        C * sourceWeight u ^ 10 * A * (α⁻¹ * (1 / 72)) *
          ∑ k ∈ S, intervalTail (c k) (2 * r k) x := by
  rcases scratch_integral_badFiber_scaleTail_le_intervalTail_unconditional with
    ⟨C, hC, hmain⟩
  refine ⟨C, hC, ?_⟩
  intro ι S i j u α x A c r b hα hr hb hkernel hzero hsupport hfar hmass
  let K : ℝ := C * sourceWeight u ^ 10 * A * (α⁻¹ * (1 / 72))
  have hterm (k : ι) (hk : k ∈ S) :
      (∫ t : ℝ in Set.Ioi 0,
        |∫ y : ℝ, b k y *
          kernelDilate (activeModelKernel i j u) (t ^ α) (x - y)| * t⁻¹) ≤
        K * intervalTail (c k) (2 * r k) x := by
    simpa only [K] using
      hmain i j u α x (c k) (r k) A (b k) hα (hr k hk) (hb k hk)
        (hkernel k hk) (hzero k hk) (hsupport k hk) (hfar k hk) (hmass k hk)
  calc
    (∑ k ∈ S, ∫ t : ℝ in Set.Ioi 0,
      |∫ y : ℝ, b k y *
        kernelDilate (activeModelKernel i j u) (t ^ α) (x - y)| * t⁻¹) ≤
        ∑ k ∈ S, K * intervalTail (c k) (2 * r k) x := by
      exact Finset.sum_le_sum fun k hk ↦ hterm k hk
    _ = K * ∑ k ∈ S, intervalTail (c k) (2 * r k) x := by
      rw [Finset.mul_sum]

end Twisted
end Auto
