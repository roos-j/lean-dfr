import Auto.Twisted.Twisted

namespace Auto
namespace Twisted

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal RealInnerProductSpace Topology

noncomputable section

/-- Conditional small-scale profile estimate.  The only kernel-specific
premise is the first absolute moment of the signed third factor. -/
theorem scratch_abs_ModelSpatialProfile_le_small_scale_of_third_moment
    (α : Anisotropy) (u : E3) (F : ModelSchwartzInput) (t : ℝ)
    (ht : 0 < t)
    (hthirdmoment : Integrable (fun r : ℝ ↦
      |r| * |ModelThirdKernel (u 2) r|)) :
    ∃ C : ℝ, 0 ≤ C ∧
      |ModelSpatialProfile α u F t| ≤ C * t ^ α.weight 2 := by
  let B0 : ℝ := SchwartzMap.seminorm ℝ 0 0 (F 0)
  let B1 : ℝ := SchwartzMap.seminorm ℝ 0 0 (F 1)
  let B2 : ℝ := SchwartzMap.seminorm ℝ 0 0 (F 2)
  have hB0 : 0 ≤ B0 := by
    exact (norm_nonneg ((F 0) 0)).trans
      (SchwartzMap.norm_le_seminorm ℝ (F 0) (0 : E3))
  have hB1 : 0 ≤ B1 := by
    exact (norm_nonneg ((F 1) 0)).trans
      (SchwartzMap.norm_le_seminorm ℝ (F 1) (0 : E3))
  have hB2 : 0 ≤ B2 := by
    exact (norm_nonneg ((F 2) 0)).trans
      (SchwartzMap.norm_le_seminorm ℝ (F 2) (0 : E3))
  have hF0 (x : E3) : |F 0 x| ≤ B0 := by
    simpa only [B0, Real.norm_eq_abs] using
      SchwartzMap.norm_le_seminorm ℝ (F 0) x
  have hF1 (x : E3) : |F 1 x| ≤ B1 := by
    simpa only [B1, Real.norm_eq_abs] using
      SchwartzMap.norm_le_seminorm ℝ (F 1) x
  have hF2 (x : E3) : |F 2 x| ≤ B2 := by
    simpa only [B2, Real.norm_eq_abs] using
      SchwartzMap.norm_le_seminorm ℝ (F 2) x
  let M1 : ℝ := ∫ r : ℝ, |ModelLowKernel (u 0) r|
  let M2 : ℝ := ∫ r : ℝ, |ModelLowKernel (u 1) r|
  let M3 : ℝ := ∫ r : ℝ, |r| * |ModelThirdKernel (u 2) r|
  have hM1 : 0 ≤ M1 := by
    dsimp only [M1]
    exact integral_nonneg fun _ ↦ abs_nonneg _
  have hM2 : 0 ≤ M2 := by
    dsimp only [M2]
    exact integral_nonneg fun _ ↦ abs_nonneg _
  have hM3 : 0 ≤ M3 := by
    dsimp only [M3]
    exact integral_nonneg fun _ ↦ mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hs0 : 0 < t ^ α.weight 0 := pow_pos ht _
  have hs1 : 0 < t ^ α.weight 1 := pow_pos ht _
  have hs2 : 0 < t ^ α.weight 2 := pow_pos ht _
  rcases schwartz_real_global_lipschitz (F 3) with ⟨L, hL, hLip⟩
  have hA0 (x : E3) :
      |ModelCoordinateConvolution 0 (F 1) (ModelLowKernel (u 0))
        (t ^ α.weight 0) x| ≤ B1 * M1 := by
    simpa only [M1] using abs_ModelCoordinateConvolution_le
      0 (F 1) (ModelLowKernel (u 0)) (t ^ α.weight 0) x
      (F 1).continuous B1 hF1 (integrable_ModelLowKernel (u 0)) hs0
  have hA1 (x : E3) :
      |ModelCoordinateConvolution 1 (F 2) (ModelLowKernel (u 1))
        (t ^ α.weight 1) x| ≤ B2 * M2 := by
    simpa only [M2] using abs_ModelCoordinateConvolution_le
      1 (F 2) (ModelLowKernel (u 1)) (t ^ α.weight 1) x
      (F 2).continuous B2 hF2 (integrable_ModelLowKernel (u 1)) hs1
  have hA2 (x : E3) :
      |ModelCoordinateConvolution 2 (F 3) (ModelThirdKernel (u 2))
        (t ^ α.weight 2) x| ≤ L * (t ^ α.weight 2) * M3 := by
    simpa only [M3] using abs_ModelCoordinateConvolution_le_of_mean_zero
      2 (F 3) (ModelThirdKernel (u 2)) (t ^ α.weight 2) x
        (F 3).continuous L (by
          intro r
          have h := hLip x (x - r • Anisotropy.coordinateDirection 2)
          have hv : x - r • Anisotropy.coordinateDirection 2 - x =
              -(r • Anisotropy.coordinateDirection 2) := by abel
          rw [Real.norm_eq_abs, hv, norm_neg,
            norm_smul_coordinateDirection] at h
          exact h)
        (integrable_ModelThirdKernel (u 2)) hthirdmoment
        (integral_ModelThirdKernel (u 2)) hs2
  let D : ℝ := (B1 * M1) * (B2 * M2) * L * M3
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hF0int : Integrable (fun x : E3 ↦ |F 0 x|) := by
    simpa only [Real.norm_eq_abs] using (F 0).integrable.norm
  let H : E3 → ℝ := fun x ↦ D * (t ^ α.weight 2) * |F 0 x|
  have hH : Integrable H := by
    dsimp only [H]
    exact hF0int.const_mul (D * (t ^ α.weight 2))
  have hImeas : AEStronglyMeasurable
      (fun x : E3 ↦ ModelSpatialIntegrand α u F t x) volume := by
    exact ((stronglyMeasurable_ModelSpatialIntegrand α u F).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hpoint (x : E3) :
      |ModelSpatialIntegrand α u F t x| ≤ H x := by
    unfold ModelSpatialIntegrand
    dsimp only [H, D]
    rw [abs_mul, abs_mul, abs_mul]
    calc
      |F 0 x| *
          |ModelCoordinateConvolution 0 (F 1) (ModelLowKernel (u 0))
              (t ^ α.weight 0) x| *
          |ModelCoordinateConvolution 1 (F 2) (ModelLowKernel (u 1))
              (t ^ α.weight 1) x| *
          |ModelCoordinateConvolution 2 (F 3) (ModelThirdKernel (u 2))
              (t ^ α.weight 2) x| ≤
          |F 0 x| * (B1 * M1) * (B2 * M2) *
            (L * (t ^ α.weight 2) * M3) := by
              gcongr
              · exact hA0 x
              · exact hA1 x
              · exact hA2 x
      _ = (B1 * M1) * (B2 * M2) * L * M3 *
          (t ^ α.weight 2) * |F 0 x| := by
            ring
  have hI : Integrable (fun x : E3 ↦ ModelSpatialIntegrand α u F t x) := by
    apply hH.mono' hImeas
    filter_upwards [] with x
    change ‖ModelSpatialIntegrand α u F t x‖ ≤
      D * (t ^ α.weight 2) * |F 0 x|
    simp only [Real.norm_eq_abs]
    exact hpoint x
  let C : ℝ := D * ∫ x : E3, |F 0 x|
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg hD (integral_nonneg fun _ ↦ abs_nonneg _)
  refine ⟨C, hC, ?_⟩
  unfold ModelSpatialProfile
  change |∫ x : E3, ModelSpatialIntegrand α u F t x| ≤
    C * t ^ α.weight 2
  calc
    |∫ x : E3, ModelSpatialIntegrand α u F t x| ≤
        ∫ x : E3, |ModelSpatialIntegrand α u F t x| :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ x : E3, H x := by
      apply integral_mono hI.norm hH
      intro x
      exact hpoint x
    _ = C * t ^ α.weight 2 := by
      dsimp only [H, C]
      rw [integral_const_mul]
      ring

/-- Conditional large-scale profile estimate.  A bounded third kernel and a
uniform absolute mass bound for the third input along third-coordinate lines
give the reciprocal-scale decay. -/
theorem scratch_abs_ModelSpatialProfile_le_large_scale_of_third_bound
    (α : Anisotropy) (u : E3) (F : ModelSchwartzInput) (t : ℝ)
    (ht : 0 < t) (A Z : ℝ)
    (hkernel : ∀ r : ℝ, |ModelThirdKernel (u 2) r| ≤ A)
    (hline : ∀ x : E3, Integrable (fun r : ℝ ↦
      F 3 (x - r • Anisotropy.coordinateDirection 2)))
    (hline_mass : ∀ x : E3, ∫ r : ℝ,
      |F 3 (x - r • Anisotropy.coordinateDirection 2)| ≤ Z) :
    ∃ C : ℝ, 0 ≤ C ∧
      |ModelSpatialProfile α u F t| ≤ C * (t ^ α.weight 2)⁻¹ := by
  let B1 : ℝ := SchwartzMap.seminorm ℝ 0 0 (F 1)
  let B2 : ℝ := SchwartzMap.seminorm ℝ 0 0 (F 2)
  have hB1 : 0 ≤ B1 := by
    exact (norm_nonneg ((F 1) 0)).trans
      (SchwartzMap.norm_le_seminorm ℝ (F 1) (0 : E3))
  have hB2 : 0 ≤ B2 := by
    exact (norm_nonneg ((F 2) 0)).trans
      (SchwartzMap.norm_le_seminorm ℝ (F 2) (0 : E3))
  have hF1 (x : E3) : |F 1 x| ≤ B1 := by
    simpa only [B1, Real.norm_eq_abs] using
      SchwartzMap.norm_le_seminorm ℝ (F 1) x
  have hF2 (x : E3) : |F 2 x| ≤ B2 := by
    simpa only [B2, Real.norm_eq_abs] using
      SchwartzMap.norm_le_seminorm ℝ (F 2) x
  let M1 : ℝ := ∫ r : ℝ, |ModelLowKernel (u 0) r|
  let M2 : ℝ := ∫ r : ℝ, |ModelLowKernel (u 1) r|
  have hM1 : 0 ≤ M1 := by
    dsimp only [M1]
    exact integral_nonneg fun _ ↦ abs_nonneg _
  have hM2 : 0 ≤ M2 := by
    dsimp only [M2]
    exact integral_nonneg fun _ ↦ abs_nonneg _
  have hA : 0 ≤ A := by
    exact (abs_nonneg (ModelThirdKernel (u 2) 0)).trans (hkernel 0)
  have hZ : 0 ≤ Z := by
    exact (integral_nonneg fun r ↦ abs_nonneg
      (F 3 ((0 : E3) - r • Anisotropy.coordinateDirection 2))).trans
      (hline_mass 0)
  have hs0 : 0 < t ^ α.weight 0 := pow_pos ht _
  have hs1 : 0 < t ^ α.weight 1 := pow_pos ht _
  have hs2 : 0 < t ^ α.weight 2 := pow_pos ht _
  have hA0 (x : E3) :
      |ModelCoordinateConvolution 0 (F 1) (ModelLowKernel (u 0))
        (t ^ α.weight 0) x| ≤ B1 * M1 := by
    simpa only [M1] using abs_ModelCoordinateConvolution_le
      0 (F 1) (ModelLowKernel (u 0)) (t ^ α.weight 0) x
      (F 1).continuous B1 hF1 (integrable_ModelLowKernel (u 0)) hs0
  have hA1 (x : E3) :
      |ModelCoordinateConvolution 1 (F 2) (ModelLowKernel (u 1))
        (t ^ α.weight 1) x| ≤ B2 * M2 := by
    simpa only [M2] using abs_ModelCoordinateConvolution_le
      1 (F 2) (ModelLowKernel (u 1)) (t ^ α.weight 1) x
      (F 2).continuous B2 hF2 (integrable_ModelLowKernel (u 1)) hs1
  have hA2 (x : E3) :
      |ModelCoordinateConvolution 2 (F 3) (ModelThirdKernel (u 2))
        (t ^ α.weight 2) x| ≤ (t ^ α.weight 2)⁻¹ * A * Z := by
    calc
      |ModelCoordinateConvolution 2 (F 3) (ModelThirdKernel (u 2))
          (t ^ α.weight 2) x| ≤
          (t ^ α.weight 2)⁻¹ * A * ∫ r : ℝ,
            |F 3 (x - r • Anisotropy.coordinateDirection 2)| := by
            apply abs_ModelCoordinateConvolution_le_of_bounded_kernel_line_mass
              2 (F 3) (ModelThirdKernel (u 2)) (t ^ α.weight 2) x
              (integrable_ModelThirdKernel (u 2)) A hkernel (hline x) hs2
      _ ≤ (t ^ α.weight 2)⁻¹ * A * Z := by
        exact mul_le_mul_of_nonneg_left (hline_mass x) (by positivity)
  let D : ℝ := (B1 * M1) * (B2 * M2) * A * Z
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hF0int : Integrable (fun x : E3 ↦ |F 0 x|) := by
    simpa only [Real.norm_eq_abs] using (F 0).integrable.norm
  let H : E3 → ℝ := fun x ↦ D * (t ^ α.weight 2)⁻¹ * |F 0 x|
  have hH : Integrable H := by
    dsimp only [H]
    exact hF0int.const_mul (D * (t ^ α.weight 2)⁻¹)
  have hImeas : AEStronglyMeasurable
      (fun x : E3 ↦ ModelSpatialIntegrand α u F t x) volume := by
    exact ((stronglyMeasurable_ModelSpatialIntegrand α u F).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hpoint (x : E3) :
      |ModelSpatialIntegrand α u F t x| ≤ H x := by
    unfold ModelSpatialIntegrand
    dsimp only [H, D]
    rw [abs_mul, abs_mul, abs_mul]
    calc
      |F 0 x| *
          |ModelCoordinateConvolution 0 (F 1) (ModelLowKernel (u 0))
              (t ^ α.weight 0) x| *
          |ModelCoordinateConvolution 1 (F 2) (ModelLowKernel (u 1))
              (t ^ α.weight 1) x| *
          |ModelCoordinateConvolution 2 (F 3) (ModelThirdKernel (u 2))
              (t ^ α.weight 2) x| ≤
          |F 0 x| * (B1 * M1) * (B2 * M2) *
            ((t ^ α.weight 2)⁻¹ * A * Z) := by
              gcongr
              · exact hA0 x
              · exact hA1 x
              · exact hA2 x
      _ = (B1 * M1) * (B2 * M2) * A * Z *
          (t ^ α.weight 2)⁻¹ * |F 0 x| := by
            ring
  have hI : Integrable (fun x : E3 ↦ ModelSpatialIntegrand α u F t x) := by
    apply hH.mono' hImeas
    filter_upwards [] with x
    change ‖ModelSpatialIntegrand α u F t x‖ ≤
      D * (t ^ α.weight 2)⁻¹ * |F 0 x|
    simp only [Real.norm_eq_abs]
    exact hpoint x
  let C : ℝ := D * ∫ x : E3, |F 0 x|
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg hD (integral_nonneg fun _ ↦ abs_nonneg _)
  refine ⟨C, hC, ?_⟩
  unfold ModelSpatialProfile
  change |∫ x : E3, ModelSpatialIntegrand α u F t x| ≤
    C * (t ^ α.weight 2)⁻¹
  calc
    |∫ x : E3, ModelSpatialIntegrand α u F t x| ≤
        ∫ x : E3, |ModelSpatialIntegrand α u F t x| :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ x : E3, H x := by
      apply integral_mono hI.norm hH
      intro x
      exact hpoint x
    _ = C * (t ^ α.weight 2)⁻¹ := by
      dsimp only [H, C]
      rw [integral_const_mul]
      ring

/-- A real Schwartz input has uniformly integrable restrictions to all lines
parallel to a fixed coordinate axis.  The proof uses only its radial
order-ten decay and the fixed integrable comparison kernel. -/
theorem scratch_realSchwartz_uniform_coordinate_line_mass
    (i : Fin 3) (f : SchwartzMap E3 ℝ) :
    ∃ Z : ℝ, 0 ≤ Z ∧ ∀ x : E3,
      Integrable (fun r : ℝ ↦
        f (x - r • Anisotropy.coordinateDirection i)) ∧
      ∫ r : ℝ, |f (x - r • Anisotropy.coordinateDirection i)| ≤ Z := by
  rcases realSchwartz_decay_norm f 10 with ⟨C, hC, hdecay⟩
  let Z : ℝ := C * ∫ r : ℝ, bracketKernel r
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    exact mul_nonneg hC (integral_nonneg fun r ↦ bracketKernel_nonneg r)
  refine ⟨Z, hZ, fun x ↦ ?_⟩
  let g : ℝ → ℝ := fun r ↦
    f (x - r • Anisotropy.coordinateDirection i)
  let q : ℝ → ℝ := fun r ↦ C * bracketKernel (x i - r)
  have hmap : Continuous (fun r : ℝ ↦
      x - r • Anisotropy.coordinateDirection i) :=
    continuous_const.sub (continuous_id.smul continuous_const)
  have hcoord (r : ℝ) :
      (x - r • Anisotropy.coordinateDirection i) i = x i - r := by
    simp [coordinateDirection_apply]
  have hdecayq (r : ℝ) : |g r| ≤ q r := by
    have hcoordle : |(x - r • Anisotropy.coordinateDirection i) i| ≤
        ‖x - r • Anisotropy.coordinateDirection i‖ := by
      simpa only [Real.norm_eq_abs] using
        PiLp.norm_apply_le (x - r • Anisotropy.coordinateDirection i) i
    have hweight : 1 + |x i - r| ≤
        1 + ‖x - r • Anisotropy.coordinateDirection i‖ := by
      rw [← hcoord r]
      linarith
    have hweightpow : (1 + |x i - r|) ^ 10 ≤
        (1 + ‖x - r • Anisotropy.coordinateDirection i‖) ^ 10 := by
      exact pow_le_pow_left₀ (by positivity) hweight 10
    have hdenleft : 0 <
        (1 + ‖x - r • Anisotropy.coordinateDirection i‖) ^ 10 := by
      positivity
    have hdenright : 0 < (1 + |x i - r|) ^ 10 := by
      positivity
    dsimp only [g, q]
    calc
      |f (x - r • Anisotropy.coordinateDirection i)| ≤
          C / (1 + ‖x - r • Anisotropy.coordinateDirection i‖) ^ 10 :=
        hdecay _
      _ ≤ C / (1 + |x i - r|) ^ 10 := by
        apply (div_le_div_iff₀ hdenleft hdenright).mpr
        gcongr
      _ = C * bracketKernel (x i - r) := by
        rw [bracketKernel_eq_inv_pow, div_eq_mul_inv]
  have hq : Integrable q := by
    dsimp only [q]
    exact (integrable_bracketKernel.comp_sub_left (x i)).const_mul C
  have hgmeas : AEStronglyMeasurable g volume := by
    dsimp only [g]
    exact (f.continuous.comp hmap).aestronglyMeasurable
  have hg : Integrable g := by
    apply hq.mono' hgmeas
    filter_upwards [] with r
    simpa only [Real.norm_eq_abs] using hdecayq r
  constructor
  · exact hg
  · calc
      ∫ r : ℝ, |f (x - r • Anisotropy.coordinateDirection i)| =
          ∫ r : ℝ, |g r| := by rfl
      _ ≤ ∫ r : ℝ, q r := by
        apply integral_mono hg.norm hq
        intro r
        simpa only [Real.norm_eq_abs] using hdecayq r
      _ = Z := by
        dsimp only [q, Z]
        rw [integral_const_mul,
          integral_sub_left_eq_self bracketKernel volume (x i)]

/-- The large-scale profile estimate is unconditional once the third kernel
has a global pointwise bound: the required coordinate-line mass of the
Schwartz input is supplied by the preceding uniform fiber estimate. -/
theorem scratch_abs_ModelSpatialProfile_le_large_scale_of_bounded_ModelThirdKernel
    (α : Anisotropy) (u : E3) (F : ModelSchwartzInput) (t : ℝ)
    (ht : 0 < t) (A : ℝ)
    (hkernel : ∀ r : ℝ, |ModelThirdKernel (u 2) r| ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧
      |ModelSpatialProfile α u F t| ≤ C * (t ^ α.weight 2)⁻¹ := by
  rcases scratch_realSchwartz_uniform_coordinate_line_mass 2 (F 3)
    with ⟨Z, hZ, hlines⟩
  exact scratch_abs_ModelSpatialProfile_le_large_scale_of_third_bound
    α u F t ht A Z hkernel
    (fun x ↦ (hlines x).1) (fun x ↦ (hlines x).2)

/-- Spatial integration of three pointwise coordinate-convolution bounds.
This is the common bookkeeping step behind both ends of the scale range. -/
theorem scratch_abs_ModelSpatialProfile_le_of_coordinate_bounds
    (α : Anisotropy) (u : E3) (F : ModelSchwartzInput) (t : ℝ)
    (A0 A1 A2 : ℝ) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (h0 : ∀ x : E3,
      |ModelCoordinateConvolution 0 (F 1) (ModelLowKernel (u 0))
        (t ^ α.weight 0) x| ≤ A0)
    (h1 : ∀ x : E3,
      |ModelCoordinateConvolution 1 (F 2) (ModelLowKernel (u 1))
        (t ^ α.weight 1) x| ≤ A1)
    (h2 : ∀ x : E3,
      |ModelCoordinateConvolution 2 (F 3) (ModelThirdKernel (u 2))
        (t ^ α.weight 2) x| ≤ A2) :
    |ModelSpatialProfile α u F t| ≤
      A0 * A1 * A2 * ∫ x : E3, |F 0 x| := by
  let D : ℝ := A0 * A1 * A2
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hF0int : Integrable (fun x : E3 ↦ |F 0 x|) := by
    simpa only [Real.norm_eq_abs] using (F 0).integrable.norm
  let H : E3 → ℝ := fun x ↦ D * |F 0 x|
  have hH : Integrable H := by
    dsimp only [H]
    exact hF0int.const_mul D
  have hImeas : AEStronglyMeasurable
      (fun x : E3 ↦ ModelSpatialIntegrand α u F t x) volume := by
    exact ((stronglyMeasurable_ModelSpatialIntegrand α u F).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hpoint (x : E3) :
      |ModelSpatialIntegrand α u F t x| ≤ H x := by
    unfold ModelSpatialIntegrand
    dsimp only [H, D]
    rw [abs_mul, abs_mul, abs_mul]
    calc
      |F 0 x| *
          |ModelCoordinateConvolution 0 (F 1) (ModelLowKernel (u 0))
              (t ^ α.weight 0) x| *
          |ModelCoordinateConvolution 1 (F 2) (ModelLowKernel (u 1))
              (t ^ α.weight 1) x| *
          |ModelCoordinateConvolution 2 (F 3) (ModelThirdKernel (u 2))
              (t ^ α.weight 2) x| ≤
          |F 0 x| * A0 * A1 * A2 := by
            gcongr
            · exact h0 x
            · exact h1 x
            · exact h2 x
      _ = A0 * A1 * A2 * |F 0 x| := by ring
  have hI : Integrable (fun x : E3 ↦ ModelSpatialIntegrand α u F t x) := by
    apply hH.mono' hImeas
    filter_upwards [] with x
    change ‖ModelSpatialIntegrand α u F t x‖ ≤ D * |F 0 x|
    simpa only [Real.norm_eq_abs] using hpoint x
  unfold ModelSpatialProfile
  calc
    |∫ x : E3, ModelSpatialIntegrand α u F t x| ≤
        ∫ x : E3, |ModelSpatialIntegrand α u F t x| :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ x : E3, H x := by
      apply integral_mono hI.norm hH
      intro x
      exact hpoint x
    _ = A0 * A1 * A2 * ∫ x : E3, |F 0 x| := by
      dsimp only [H, D]
      rw [integral_const_mul]

/-- The small-scale profile constant can be chosen uniformly over all
positive scales. -/
theorem scratch_exists_ModelSpatialProfile_small_scale_bound
    (α : Anisotropy) (u : E3) (F : ModelSchwartzInput)
    (hthirdmoment : Integrable (fun r : ℝ ↦
      |r| * |ModelThirdKernel (u 2) r|)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      |ModelSpatialProfile α u F t| ≤ C * t ^ α.weight 2 := by
  let B1 : ℝ := SchwartzMap.seminorm ℝ 0 0 (F 1)
  let B2 : ℝ := SchwartzMap.seminorm ℝ 0 0 (F 2)
  have hB1 : 0 ≤ B1 := by
    exact (norm_nonneg ((F 1) 0)).trans
      (SchwartzMap.norm_le_seminorm ℝ (F 1) (0 : E3))
  have hB2 : 0 ≤ B2 := by
    exact (norm_nonneg ((F 2) 0)).trans
      (SchwartzMap.norm_le_seminorm ℝ (F 2) (0 : E3))
  have hF1 (x : E3) : |F 1 x| ≤ B1 := by
    simpa only [B1, Real.norm_eq_abs] using
      SchwartzMap.norm_le_seminorm ℝ (F 1) x
  have hF2 (x : E3) : |F 2 x| ≤ B2 := by
    simpa only [B2, Real.norm_eq_abs] using
      SchwartzMap.norm_le_seminorm ℝ (F 2) x
  let M1 : ℝ := ∫ r : ℝ, |ModelLowKernel (u 0) r|
  let M2 : ℝ := ∫ r : ℝ, |ModelLowKernel (u 1) r|
  let M3 : ℝ := ∫ r : ℝ, |r| * |ModelThirdKernel (u 2) r|
  have hM1 : 0 ≤ M1 := by
    dsimp only [M1]
    exact integral_nonneg fun _ ↦ abs_nonneg _
  have hM2 : 0 ≤ M2 := by
    dsimp only [M2]
    exact integral_nonneg fun _ ↦ abs_nonneg _
  have hM3 : 0 ≤ M3 := by
    dsimp only [M3]
    exact integral_nonneg fun _ ↦ mul_nonneg (abs_nonneg _) (abs_nonneg _)
  rcases schwartz_real_global_lipschitz (F 3) with ⟨L, hL, hLip⟩
  let C : ℝ := (B1 * M1) * (B2 * M2) * L * M3 *
    ∫ x : E3, |F 0 x|
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, fun t ht ↦ ?_⟩
  have hs0 : 0 < t ^ α.weight 0 := pow_pos ht _
  have hs1 : 0 < t ^ α.weight 1 := pow_pos ht _
  have hs2 : 0 < t ^ α.weight 2 := pow_pos ht _
  have hA0 (x : E3) :
      |ModelCoordinateConvolution 0 (F 1) (ModelLowKernel (u 0))
        (t ^ α.weight 0) x| ≤ B1 * M1 := by
    simpa only [M1] using abs_ModelCoordinateConvolution_le
      0 (F 1) (ModelLowKernel (u 0)) (t ^ α.weight 0) x
      (F 1).continuous B1 hF1 (integrable_ModelLowKernel (u 0)) hs0
  have hA1 (x : E3) :
      |ModelCoordinateConvolution 1 (F 2) (ModelLowKernel (u 1))
        (t ^ α.weight 1) x| ≤ B2 * M2 := by
    simpa only [M2] using abs_ModelCoordinateConvolution_le
      1 (F 2) (ModelLowKernel (u 1)) (t ^ α.weight 1) x
      (F 2).continuous B2 hF2 (integrable_ModelLowKernel (u 1)) hs1
  have hA2 (x : E3) :
      |ModelCoordinateConvolution 2 (F 3) (ModelThirdKernel (u 2))
        (t ^ α.weight 2) x| ≤ L * (t ^ α.weight 2) * M3 := by
    simpa only [M3] using abs_ModelCoordinateConvolution_le_of_mean_zero
      2 (F 3) (ModelThirdKernel (u 2)) (t ^ α.weight 2) x
        (F 3).continuous L (by
          intro r
          have h := hLip x (x - r • Anisotropy.coordinateDirection 2)
          have hv : x - r • Anisotropy.coordinateDirection 2 - x =
              -(r • Anisotropy.coordinateDirection 2) := by abel
          rw [Real.norm_eq_abs, hv, norm_neg,
            norm_smul_coordinateDirection] at h
          exact h)
        (integrable_ModelThirdKernel (u 2)) hthirdmoment
        (integral_ModelThirdKernel (u 2)) hs2
  calc
    |ModelSpatialProfile α u F t| ≤
        (B1 * M1) * (B2 * M2) *
          (L * (t ^ α.weight 2) * M3) * ∫ x : E3, |F 0 x| := by
      apply scratch_abs_ModelSpatialProfile_le_of_coordinate_bounds
      · exact mul_nonneg hB1 hM1
      · exact mul_nonneg hB2 hM2
      · positivity
      · exact hA0
      · exact hA1
      · exact hA2
    _ = C * t ^ α.weight 2 := by
      dsimp only [C]
      ring

/-- The large-scale profile constant can likewise be chosen uniformly over
all positive scales once the fixed third kernel is pointwise bounded. -/
theorem scratch_exists_ModelSpatialProfile_large_scale_bound
    (α : Anisotropy) (u : E3) (F : ModelSchwartzInput)
    (A : ℝ) (hkernel : ∀ r : ℝ, |ModelThirdKernel (u 2) r| ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      |ModelSpatialProfile α u F t| ≤ C * (t ^ α.weight 2)⁻¹ := by
  let B1 : ℝ := SchwartzMap.seminorm ℝ 0 0 (F 1)
  let B2 : ℝ := SchwartzMap.seminorm ℝ 0 0 (F 2)
  have hB1 : 0 ≤ B1 := by
    exact (norm_nonneg ((F 1) 0)).trans
      (SchwartzMap.norm_le_seminorm ℝ (F 1) (0 : E3))
  have hB2 : 0 ≤ B2 := by
    exact (norm_nonneg ((F 2) 0)).trans
      (SchwartzMap.norm_le_seminorm ℝ (F 2) (0 : E3))
  have hF1 (x : E3) : |F 1 x| ≤ B1 := by
    simpa only [B1, Real.norm_eq_abs] using
      SchwartzMap.norm_le_seminorm ℝ (F 1) x
  have hF2 (x : E3) : |F 2 x| ≤ B2 := by
    simpa only [B2, Real.norm_eq_abs] using
      SchwartzMap.norm_le_seminorm ℝ (F 2) x
  let M1 : ℝ := ∫ r : ℝ, |ModelLowKernel (u 0) r|
  let M2 : ℝ := ∫ r : ℝ, |ModelLowKernel (u 1) r|
  have hM1 : 0 ≤ M1 := by
    dsimp only [M1]
    exact integral_nonneg fun _ ↦ abs_nonneg _
  have hM2 : 0 ≤ M2 := by
    dsimp only [M2]
    exact integral_nonneg fun _ ↦ abs_nonneg _
  have hA : 0 ≤ A := by
    exact (abs_nonneg (ModelThirdKernel (u 2) 0)).trans (hkernel 0)
  rcases scratch_realSchwartz_uniform_coordinate_line_mass 2 (F 3)
    with ⟨Z, hZ, hlines⟩
  let C : ℝ := (B1 * M1) * (B2 * M2) * A * Z *
    ∫ x : E3, |F 0 x|
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, fun t ht ↦ ?_⟩
  have hs0 : 0 < t ^ α.weight 0 := pow_pos ht _
  have hs1 : 0 < t ^ α.weight 1 := pow_pos ht _
  have hs2 : 0 < t ^ α.weight 2 := pow_pos ht _
  have hA0 (x : E3) :
      |ModelCoordinateConvolution 0 (F 1) (ModelLowKernel (u 0))
        (t ^ α.weight 0) x| ≤ B1 * M1 := by
    simpa only [M1] using abs_ModelCoordinateConvolution_le
      0 (F 1) (ModelLowKernel (u 0)) (t ^ α.weight 0) x
      (F 1).continuous B1 hF1 (integrable_ModelLowKernel (u 0)) hs0
  have hA1 (x : E3) :
      |ModelCoordinateConvolution 1 (F 2) (ModelLowKernel (u 1))
        (t ^ α.weight 1) x| ≤ B2 * M2 := by
    simpa only [M2] using abs_ModelCoordinateConvolution_le
      1 (F 2) (ModelLowKernel (u 1)) (t ^ α.weight 1) x
      (F 2).continuous B2 hF2 (integrable_ModelLowKernel (u 1)) hs1
  have hA2 (x : E3) :
      |ModelCoordinateConvolution 2 (F 3) (ModelThirdKernel (u 2))
        (t ^ α.weight 2) x| ≤ (t ^ α.weight 2)⁻¹ * A * Z := by
    calc
      |ModelCoordinateConvolution 2 (F 3) (ModelThirdKernel (u 2))
          (t ^ α.weight 2) x| ≤
          (t ^ α.weight 2)⁻¹ * A * ∫ r : ℝ,
            |F 3 (x - r • Anisotropy.coordinateDirection 2)| := by
            apply abs_ModelCoordinateConvolution_le_of_bounded_kernel_line_mass
              2 (F 3) (ModelThirdKernel (u 2)) (t ^ α.weight 2) x
              (integrable_ModelThirdKernel (u 2)) A hkernel
              (hlines x).1 hs2
      _ ≤ (t ^ α.weight 2)⁻¹ * A * Z := by
        exact mul_le_mul_of_nonneg_left (hlines x).2 (by positivity)
  calc
    |ModelSpatialProfile α u F t| ≤
        (B1 * M1) * (B2 * M2) *
          ((t ^ α.weight 2)⁻¹ * A * Z) * ∫ x : E3, |F 0 x| := by
      apply scratch_abs_ModelSpatialProfile_le_of_coordinate_bounds
      · exact mul_nonneg hB1 hM1
      · exact mul_nonneg hB2 hM2
      · positivity
      · exact hA0
      · exact hA1
      · exact hA2
    _ = C * (t ^ α.weight 2)⁻¹ := by
      dsimp only [C]
      ring

/-- The two uniform scale estimates combine into the exact integrable
small/large envelope required by the full model-profile convergence bridge. -/
theorem scratch_exists_ModelSpatialProfile_scale_envelope
    (α : Anisotropy) (u : E3) (F : ModelSchwartzInput)
    (hmoment : Integrable (fun r : ℝ ↦
      |r| * |ModelThirdKernel (u 2) r|))
    (A : ℝ) (hkernel : ∀ r : ℝ, |ModelThirdKernel (u 2) r| ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      |ModelSpatialProfile α u F t| ≤ C *
        min (t ^ (α.weight 2 : ℝ)) (t ^ (-(α.weight 2 : ℝ))) := by
  rcases scratch_exists_ModelSpatialProfile_small_scale_bound α u F hmoment
    with ⟨Cs, hCs, hsmall⟩
  rcases scratch_exists_ModelSpatialProfile_large_scale_bound α u F A hkernel
    with ⟨Cl, hCl, hlarge⟩
  refine ⟨Cs + Cl, add_nonneg hCs hCl, fun t ht ↦ ?_⟩
  let s : ℝ := t ^ α.weight 2
  have hs : 0 < s := by
    dsimp only [s]
    exact pow_pos ht _
  have hsmall' : |ModelSpatialProfile α u F t| ≤ Cs * s := by
    simpa only [s] using hsmall t ht
  have hlarge' : |ModelSpatialProfile α u F t| ≤ Cl * s⁻¹ := by
    simpa only [s] using hlarge t ht
  have hrpow : min (t ^ (α.weight 2 : ℝ))
      (t ^ (-(α.weight 2 : ℝ))) = min s s⁻¹ := by
    dsimp only [s]
    rw [Real.rpow_natCast, Real.rpow_neg (le_of_lt ht),
      Real.rpow_natCast]
  rw [hrpow]
  by_cases hsmallscale : s ≤ 1
  · have hmin : min s s⁻¹ = s := by
      apply min_eq_left
      rw [show s⁻¹ = s⁻¹ * 1 by ring]
      apply (le_inv_mul_iff₀ hs).mpr
      nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hsmallscale)]
    rw [hmin]
    calc
      |ModelSpatialProfile α u F t| ≤ Cs * s := hsmall'
      _ ≤ (Cs + Cl) * s := by
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right hCl) hs.le
  · have hlargescale : 1 ≤ s := le_of_not_ge hsmallscale
    have hmin : min s s⁻¹ = s⁻¹ := by
      apply min_eq_right
      apply (inv_le_iff_one_le_mul₀ hs).mpr
      nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hlargescale)]
    rw [hmin]
    calc
      |ModelSpatialProfile α u F t| ≤ Cl * s⁻¹ := hlarge'
      _ ≤ (Cs + Cl) * s⁻¹ := by
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left hCs) (inv_nonneg.mpr hs.le)

/-- The profile envelope is unconditional for every real Schwartz tuple:
the third-kernel moment and uniform bound have now both been established. -/
theorem scratch_exists_ModelSpatialProfile_scale_envelope_unconditional
    (α : Anisotropy) (u : E3) (F : ModelSchwartzInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      |ModelSpatialProfile α u F t| ≤ C *
        min (t ^ (α.weight 2 : ℝ)) (t ^ (-(α.weight 2 : ℝ))) := by
  rcases exists_bound_ModelThirdKernel with ⟨A, hA, hbound⟩
  exact scratch_exists_ModelSpatialProfile_scale_envelope α u F
    (integrable_abs_mul_ModelThirdKernel (u 2)) A (hbound (u 2))

/-- Every bounded measurable coefficient gives an integrable full model
scale profile for real Schwartz input. -/
theorem scratch_integrableOn_modelScaleProfile_of_realSchwartz
    (α : Anisotropy) (u : E3) (c : ℝ → ℝ) (F : ModelSchwartzInput)
    (hcmeas : Measurable c) (hc : ∀ t : ℝ, |c t| ≤ 1) :
    IntegrableOn (fun t : ℝ ↦ c t * ModelSpatialProfile α u F t)
      (Set.Ioi (0 : ℝ)) ((volume : Measure ℝ).withDensity cubeScaleDensity) := by
  rcases scratch_exists_ModelSpatialProfile_scale_envelope_unconditional α u F
    with ⟨C, hC, hprofile⟩
  apply integrableOn_modelScaleProfile_of_bound
    (a := (α.weight 2 : ℝ)) (C := C)
  · exact_mod_cast α.weight_pos 2
  · exact hc
  · exact aestronglyMeasurable_modelScaleProfile_of_measurable
      α u c F hcmeas
  · exact hprofile

/-- The literal dyadic scale truncations converge to the full model form for
every bounded measurable coefficient and real Schwartz input. -/
theorem scratch_tendsto_ModelScaleTruncation_of_realSchwartz
    (α : Anisotropy) (u : E3) (c : ℝ → ℝ) (F : ModelSchwartzInput)
    (hcmeas : Measurable c) (hc : ∀ t : ℝ, |c t| ≤ 1) :
    Tendsto (fun N ↦ ModelScaleTruncation α u c F N) atTop
      (𝓝 (ModelFullForm α u c F)) := by
  rcases scratch_exists_ModelSpatialProfile_scale_envelope_unconditional α u F
    with ⟨C, hC, hprofile⟩
  apply tendsto_modelScaleTruncation_of_bound
    (a := (α.weight 2 : ℝ)) (C := C)
  · exact_mod_cast α.weight_pos 2
  · exact hc
  · exact aestronglyMeasurable_modelScaleProfile_of_measurable
      α u c F hcmeas
  · exact hprofile

example (a : ℝ) : Integrable (fun r : ℝ ↦ bracketKernel (a - r)) := by
  exact integrable_bracketKernel.comp_sub_left a

example (i : Fin 3) (x : E3) (r : ℝ) :
    (x - r • Anisotropy.coordinateDirection i) i = x i - r := by
  simp [coordinateDirection_apply]

example (t : ℝ) (ht : 0 < t) (n : ℕ) :
    min (t ^ (n : ℝ)) (t ^ (-(n : ℝ))) = min (t ^ n) (t ^ n)⁻¹ := by
  rw [Real.rpow_natCast, Real.rpow_neg (le_of_lt ht), Real.rpow_natCast]

example (s : ℝ) (hs : 0 < s) (hle : s ≤ 1) : min s s⁻¹ = s := by
  apply min_eq_left
  rw [show s⁻¹ = s⁻¹ * 1 by ring]
  apply (le_inv_mul_iff₀ hs).mpr
  nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hle)]

example (s : ℝ) (hs : 0 < s) (hle : 1 ≤ s) : min s s⁻¹ = s⁻¹ := by
  apply min_eq_right
  apply (inv_le_iff_one_le_mul₀ hs).mpr
  nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hle)]

end

end Twisted
end Auto
