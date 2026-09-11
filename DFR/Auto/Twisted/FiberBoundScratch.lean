import Auto.Twisted.Twisted

namespace Auto.Twisted

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal RealInnerProductSpace

noncomputable section

/-- Positive normalized dilation and translation preserve the `L¹` mass of
the absolute Gaussian derivative. -/
theorem scratch_integral_abs_gaussianDerivAt {s : ℝ} (hs : 0 < s) (a : ℝ) :
    ∫ x : ℝ, |gaussianDerivAt s a x| = ∫ x : ℝ, |gaussianDeriv x| := by
  unfold gaussianDerivAt kernelAt kernelDilate
  have hinv : 0 ≤ s⁻¹ := (inv_pos.mpr hs).le
  calc
    (∫ x : ℝ, |s⁻¹ • gaussianDeriv ((x - a) / s)|) =
        ∫ x : ℝ, s⁻¹ • |gaussianDeriv ((x - a) / s)| := by
          apply integral_congr_ae
          filter_upwards [] with x
          simp only [smul_eq_mul, abs_mul, abs_of_nonneg hinv]
    _ = s⁻¹ • ∫ x : ℝ, |gaussianDeriv ((x - a) / s)| := by
          rw [integral_smul]
    _ = _ := by
      rw [integral_sub_right_eq_self (μ := volume)
        (fun x : ℝ ↦ |gaussianDeriv (x / s)|) a]
      rw [Measure.integral_comp_div (fun x : ℝ ↦ |gaussianDeriv x|) s]
      simp [smul_eq_mul, abs_of_pos hs, hs.ne']

/-- The absolute Gaussian-derivative mass is finite. -/
theorem scratch_integrable_abs_gaussianDerivAt {s : ℝ} (hs : 0 < s) (a : ℝ) :
    Integrable (fun x : ℝ ↦ |gaussianDerivAt s a x|) := by
  have hbase : Integrable (fun x : ℝ ↦ |gaussianDeriv x|) := by
    simpa only [Real.norm_eq_abs] using integrable_gaussianDeriv.norm
  unfold gaussianDerivAt kernelAt kernelDilate
  refine (((hbase.comp_div hs.ne').comp_sub_right a).smul (s⁻¹ : ℝ)).congr ?_
  filter_upwards [] with x
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul,
    abs_of_pos (inv_pos.mpr hs)]

/-- A single varying coordinate of `modelPoint` is continuous. -/
theorem scratch_continuous_modelPoint_third (a b : ℝ) :
    Continuous (fun v : ℝ ↦ modelPoint a b v) := by
  have hcoords : Continuous (fun v : ℝ ↦ fun i : Fin 3 ↦
      if i = 0 then a else if i = 1 then b else v) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const
    · exact continuous_const
    · exact continuous_id
  change Continuous (WithLp.toLp 2 ∘ fun v : ℝ ↦ fun i : Fin 3 ↦
    if i = 0 then a else if i = 1 then b else v)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℝ)).comp hcoords

/-- The integrand of the first fiber is integrable under uniform continuous
input bounds. -/
theorem scratch_integrable_modelFirstFiber_integrand
    (α : Anisotropy) (f : ModelRealInput) (p : E3) {t : ℝ} (z : ModelE5)
    (hfcont : ∀ j, Continuous (f j))
    (B0 B1 B2 : ℝ) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hf0 : ∀ y, |f 0 y| ≤ B0) (hf1 : ∀ y, |f 1 y| ≤ B1)
    (hf2 : ∀ y, |f 2 y| ≤ B2)
    (ht : 0 < t) :
    Integrable (fun v : ℝ ↦
      f 0 (modelPoint (z 0) (z 1) v) *
      f 1 (modelPoint (z 2) (z 1) v) *
      f 2 (modelPoint (z 0) (z 3) v) *
      gaussianDerivAt (t ^ α.weight 2) (p 2) v) := by
  have hs : 0 < t ^ α.weight 2 := pow_pos ht _
  have hk := scratch_integrable_abs_gaussianDerivAt hs (p 2)
  have h0 : Continuous (fun v : ℝ ↦ f 0 (modelPoint (z 0) (z 1) v)) :=
    (hfcont 0).comp (scratch_continuous_modelPoint_third _ _)
  have h1 : Continuous (fun v : ℝ ↦ f 1 (modelPoint (z 2) (z 1) v)) :=
    (hfcont 1).comp (scratch_continuous_modelPoint_third _ _)
  have h2 : Continuous (fun v : ℝ ↦ f 2 (modelPoint (z 0) (z 3) v)) :=
    (hfcont 2).comp (scratch_continuous_modelPoint_third _ _)
  have hkmeas : AEStronglyMeasurable
      (fun v : ℝ ↦ gaussianDerivAt (t ^ α.weight 2) (p 2) v) volume :=
    (integrable_gaussianDerivAt hs (p 2)).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun v : ℝ ↦
      f 0 (modelPoint (z 0) (z 1) v) *
      f 1 (modelPoint (z 2) (z 1) v) *
      f 2 (modelPoint (z 0) (z 3) v) *
      gaussianDerivAt (t ^ α.weight 2) (p 2) v) volume :=
    (((h0.aestronglyMeasurable.mul h1.aestronglyMeasurable).mul
      h2.aestronglyMeasurable).mul hkmeas)
  apply Integrable.mono' (hk.const_mul (B0 * B1 * B2)) hmeas
  filter_upwards [] with v
  rw [Real.norm_eq_abs]
  rw [abs_mul, abs_mul, abs_mul]
  apply mul_le_mul_of_nonneg_right
  · gcongr
    · exact hf0 _
    · exact hf1 _
    · exact hf2 _
  · exact abs_nonneg _

/-- The one-input integrand defining the second fiber is integrable under a
uniform continuous input bound. -/
theorem scratch_integrable_modelSecondFiber_integrand
    (α : Anisotropy) (f : E3 → ℝ) (p : E3) {t : ℝ} (z : ModelE5)
    (hfcont : Continuous f)
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ y, |f y| ≤ B)
    (ht : 0 < t) :
    Integrable (fun v : ℝ ↦
      f (modelPoint (z 0) (z 1) v) *
        gaussianDerivAt (t ^ α.weight 2)
          (p 2 + z 4 * t ^ α.weight 2) v) := by
  have hs : 0 < t ^ α.weight 2 := pow_pos ht _
  have hk := scratch_integrable_abs_gaussianDerivAt hs
    (p 2 + z 4 * t ^ α.weight 2)
  have hfm : Continuous (fun v : ℝ ↦ f (modelPoint (z 0) (z 1) v)) :=
    hfcont.comp (scratch_continuous_modelPoint_third _ _)
  have hkmeas : AEStronglyMeasurable
      (fun v : ℝ ↦ gaussianDerivAt (t ^ α.weight 2)
        (p 2 + z 4 * t ^ α.weight 2) v) volume :=
    (integrable_gaussianDerivAt hs _).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun v : ℝ ↦
      f (modelPoint (z 0) (z 1) v) *
        gaussianDerivAt (t ^ α.weight 2)
          (p 2 + z 4 * t ^ α.weight 2) v) volume :=
    hfm.aestronglyMeasurable.mul hkmeas
  apply Integrable.mono' (hk.const_mul B) hmeas
  filter_upwards [] with v
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hf _) (abs_nonneg _)

/-- Uniform boundedness controls the absolute value of the first fiber by the
fixed `L¹` mass of the Gaussian derivative. -/
theorem scratch_abs_modelFirstFiber_le
    (α : Anisotropy) (f : ModelRealInput) (p : E3) {t : ℝ} (z : ModelE5)
    (hfcont : ∀ j, Continuous (f j))
    (B0 B1 B2 : ℝ) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hf0 : ∀ y, |f 0 y| ≤ B0) (hf1 : ∀ y, |f 1 y| ≤ B1)
    (hf2 : ∀ y, |f 2 y| ≤ B2)
    (ht : 0 < t) :
    |modelFirstFiber α f p t z| ≤
      (B0 * B1 * B2) * ∫ v : ℝ, |gaussianDeriv v| := by
  let G : ℝ → ℝ := fun v ↦
    f 0 (modelPoint (z 0) (z 1) v) *
    f 1 (modelPoint (z 2) (z 1) v) *
    f 2 (modelPoint (z 0) (z 3) v) *
    gaussianDerivAt (t ^ α.weight 2) (p 2) v
  have hG : Integrable G := scratch_integrable_modelFirstFiber_integrand
    α f p z hfcont B0 B1 B2 hB0 hB1 hB2 hf0 hf1 hf2 ht
  have hGabs : Integrable (fun v ↦ |G v|) := by
    simpa only [Real.norm_eq_abs] using hG.norm
  have hs : 0 < t ^ α.weight 2 := pow_pos ht _
  have hkernel := scratch_integrable_abs_gaussianDerivAt hs (p 2)
  have hupper : Integrable (fun v : ℝ ↦
      (B0 * B1 * B2) * |gaussianDerivAt (t ^ α.weight 2) (p 2) v|) :=
    hkernel.const_mul _
  have hpoint (v : ℝ) : |G v| ≤
      (B0 * B1 * B2) * |gaussianDerivAt (t ^ α.weight 2) (p 2) v| := by
    dsimp [G]
    rw [abs_mul, abs_mul, abs_mul]
    apply mul_le_mul_of_nonneg_right
    · gcongr
      · exact hf0 _
      · exact hf1 _
      · exact hf2 _
    · exact abs_nonneg _
  unfold modelFirstFiber
  change |∫ v : ℝ, G v| ≤ _
  calc
    |∫ v : ℝ, G v| ≤ ∫ v : ℝ, |G v| :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ v : ℝ,
        (B0 * B1 * B2) * |gaussianDerivAt (t ^ α.weight 2) (p 2) v| :=
      integral_mono hGabs hupper hpoint
    _ = (B0 * B1 * B2) * ∫ v : ℝ, |gaussianDeriv v| := by
      rw [integral_const_mul, scratch_integral_abs_gaussianDerivAt hs (p 2)]

/-- Uniform boundedness controls the absolute value of the second fiber by
the same fixed Gaussian-derivative mass. -/
theorem scratch_abs_modelSecondFiber_le
    (α : Anisotropy) (f : E3 → ℝ) (p : E3) {t : ℝ} (z : ModelE5)
    (hfcont : Continuous f)
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ y, |f y| ≤ B)
    (ht : 0 < t) :
    |modelSecondFiber α f p t z| ≤ B * ∫ v : ℝ, |gaussianDeriv v| := by
  let G : ℝ → ℝ := fun v ↦
    f (modelPoint (z 0) (z 1) v) *
      gaussianDerivAt (t ^ α.weight 2)
        (p 2 + z 4 * t ^ α.weight 2) v
  have hG : Integrable G := scratch_integrable_modelSecondFiber_integrand
    α f p z hfcont B hB hf ht
  have hGabs : Integrable (fun v ↦ |G v|) := by
    simpa only [Real.norm_eq_abs] using hG.norm
  have hs : 0 < t ^ α.weight 2 := pow_pos ht _
  have hkernel := scratch_integrable_abs_gaussianDerivAt hs
    (p 2 + z 4 * t ^ α.weight 2)
  have hupper : Integrable (fun v : ℝ ↦
      B * |gaussianDerivAt (t ^ α.weight 2)
        (p 2 + z 4 * t ^ α.weight 2) v|) := hkernel.const_mul _
  have hpoint (v : ℝ) : |G v| ≤ B *
      |gaussianDerivAt (t ^ α.weight 2)
        (p 2 + z 4 * t ^ α.weight 2) v| := by
    dsimp [G]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hf _) (abs_nonneg _)
  unfold modelSecondFiber
  change |∫ v : ℝ, G v| ≤ _
  calc
    |∫ v : ℝ, G v| ≤ ∫ v : ℝ, |G v| :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ v : ℝ, B * |gaussianDerivAt (t ^ α.weight 2)
        (p 2 + z 4 * t ^ α.weight 2) v| :=
      integral_mono hGabs hupper hpoint
    _ = B * ∫ v : ℝ, |gaussianDeriv v| := by
      rw [integral_const_mul,
        scratch_integral_abs_gaussianDerivAt hs
          (p 2 + z 4 * t ^ α.weight 2)]

/-- Absolute `L¹` mass of the translated low-frequency model kernel is
invariant under positive normalized dilation and translation. -/
theorem scratch_integral_abs_modelPhiAt {s : ℝ} (hs : 0 < s) (a : ℝ) :
    ∫ x : ℝ, |modelPhiAt s a x| =
      ∫ x : ℝ, |conePhiPhysicalReal x| := by
  unfold modelPhiAt kernelAt kernelDilate
  have hinv : 0 ≤ s⁻¹ := (inv_pos.mpr hs).le
  calc
    (∫ x : ℝ, |s⁻¹ • conePhiPhysicalReal ((x - a) / s)|) =
        ∫ x : ℝ, s⁻¹ • |conePhiPhysicalReal ((x - a) / s)| := by
          apply integral_congr_ae
          filter_upwards [] with x
          simp only [smul_eq_mul, abs_mul, abs_of_nonneg hinv]
    _ = s⁻¹ • ∫ x : ℝ, |conePhiPhysicalReal ((x - a) / s)| := by
          rw [integral_smul]
    _ = _ := by
      rw [integral_sub_right_eq_self (μ := volume)
        (fun x : ℝ ↦ |conePhiPhysicalReal (x / s)|) a]
      rw [Measure.integral_comp_div (fun x : ℝ ↦ |conePhiPhysicalReal x|) s]
      simp [smul_eq_mul, abs_of_pos hs, hs.ne']

/-- The absolute translated low-frequency model kernel is integrable. -/
theorem scratch_integrable_abs_modelPhiAt {s : ℝ} (hs : 0 < s) (a : ℝ) :
    Integrable (fun x : ℝ ↦ |modelPhiAt s a x|) := by
  have hbase : Integrable (fun x : ℝ ↦ |conePhiPhysicalReal x|) := by
    simpa only [Real.norm_eq_abs] using conePhiPhysicalReal.integrable.norm
  unfold modelPhiAt kernelAt kernelDilate
  refine (((hbase.comp_div hs.ne').comp_sub_right a).smul (s⁻¹ : ℝ)).congr ?_
  filter_upwards [] with x
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul,
    abs_of_pos (inv_pos.mpr hs)]

/-- The five one-dimensional factors in the positive local-energy density. -/
noncomputable def scratch_modelEnergyDensityFactor
    (α : Anisotropy) (u p : E3) (t : ℝ) (i : Fin 5) (x : ℝ) : ℝ :=
  match i.1 with
  | 0 => |modelPhiAt (t ^ α.weight 0) (p 0 + t ^ α.weight 0 * u 0) x|
  | 1 => |modelPhiAt (t ^ α.weight 1) (p 1 + t ^ α.weight 1 * u 1) x|
  | 2 => gaussianAt (t ^ α.weight 0) (p 0) x
  | 3 => gaussianAt (t ^ α.weight 1) (p 1) x
  | _ => |conePsiPhysicalReal (x + u 2)|

/-- The energy density is literally the product of its five independent
one-dimensional factors. -/
theorem scratch_modelEnergyDensity_eq_prod_factor
    (α : Anisotropy) (u p : E3) (t : ℝ) (z : ModelE5) :
    modelEnergyDensity α u p t z =
      ∏ i : Fin 5, scratch_modelEnergyDensityFactor α u p t i (z i) := by
  simp only [Fin.prod_univ_succ, Finset.prod_empty]
  simp [modelEnergyDensity, scratch_modelEnergyDensityFactor]
  ring

/-- Each one-dimensional density factor is integrable at a positive scale. -/
theorem scratch_integrable_modelEnergyDensityFactor
    (α : Anisotropy) (u p : E3) {t : ℝ} (ht : 0 < t) (i : Fin 5) :
    Integrable (scratch_modelEnergyDensityFactor α u p t i) := by
  have hs0 : 0 < t ^ α.weight 0 := pow_pos ht _
  have hs1 : 0 < t ^ α.weight 1 := pow_pos ht _
  fin_cases i
  · change Integrable (fun x ↦
      |modelPhiAt (t ^ α.weight 0) (p 0 + t ^ α.weight 0 * u 0) x|)
    exact scratch_integrable_abs_modelPhiAt hs0 (p 0 + t ^ α.weight 0 * u 0)
  · change Integrable (fun x ↦
      |modelPhiAt (t ^ α.weight 1) (p 1 + t ^ α.weight 1 * u 1) x|)
    exact scratch_integrable_abs_modelPhiAt hs1 (p 1 + t ^ α.weight 1 * u 1)
  · change Integrable (gaussianAt (t ^ α.weight 0) (p 0))
    exact integrable_gaussianAt hs0 (p 0)
  · change Integrable (gaussianAt (t ^ α.weight 1) (p 1))
    exact integrable_gaussianAt hs1 (p 1)
  · change Integrable (fun x ↦ |conePsiPhysicalReal (x + u 2)|)
    exact integrable_abs_conePsiPhysicalReal.comp_add_right (u 2)

/-- At positive scale the fixed center density is an integrable function on
the literal five-dimensional fiber space. -/
theorem scratch_integrable_modelEnergyDensity
    (α : Anisotropy) (u p : E3) {t : ℝ} (ht : 0 < t) :
    Integrable (modelEnergyDensity α u p t) := by
  rw [← (PiLp.volume_preserving_toLp (Fin 5)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  have hfactor : (modelEnergyDensity α u p t ∘ WithLp.toLp 2) =
      (fun x : Fin 5 → ℝ ↦
        ∏ i : Fin 5, scratch_modelEnergyDensityFactor α u p t i (x i)) := by
    funext x
    change modelEnergyDensity α u p t (WithLp.toLp 2 x) = _
    rw [scratch_modelEnergyDensity_eq_prod_factor]
  rw [hfactor]
  exact Integrable.fintype_prod fun i ↦
    scratch_integrable_modelEnergyDensityFactor α u p ht i

/-- Exact mass of the positive five-dimensional density. -/
theorem scratch_integral_modelEnergyDensity
    (α : Anisotropy) (u p : E3) {t : ℝ} (ht : 0 < t) :
    ∫ z : ModelE5, modelEnergyDensity α u p t z =
      (∫ x : ℝ, |conePhiPhysicalReal x|) ^ 2 * conePsiPhysicalRealL1 := by
  have hs0 : 0 < t ^ α.weight 0 := pow_pos ht _
  have hs1 : 0 < t ^ α.weight 1 := pow_pos ht _
  have h0 : ∫ x : ℝ, scratch_modelEnergyDensityFactor α u p t 0 x =
      ∫ x : ℝ, |conePhiPhysicalReal x| := by
    change (∫ x : ℝ, |modelPhiAt (t ^ α.weight 0)
      (p 0 + t ^ α.weight 0 * u 0) x|) = _
    exact scratch_integral_abs_modelPhiAt hs0 _
  have h1 : ∫ x : ℝ, scratch_modelEnergyDensityFactor α u p t 1 x =
      ∫ x : ℝ, |conePhiPhysicalReal x| := by
    change (∫ x : ℝ, |modelPhiAt (t ^ α.weight 1)
      (p 1 + t ^ α.weight 1 * u 1) x|) = _
    exact scratch_integral_abs_modelPhiAt hs1 _
  have h2 : ∫ x : ℝ, scratch_modelEnergyDensityFactor α u p t 2 x = 1 := by
    change ∫ x : ℝ, gaussianAt (t ^ α.weight 0) (p 0) x = 1
    exact integral_gaussianAt hs0 _
  have h3 : ∫ x : ℝ, scratch_modelEnergyDensityFactor α u p t 3 x = 1 := by
    change ∫ x : ℝ, gaussianAt (t ^ α.weight 1) (p 1) x = 1
    exact integral_gaussianAt hs1 _
  have h4 : ∫ x : ℝ, scratch_modelEnergyDensityFactor α u p t 4 x =
      conePsiPhysicalRealL1 := by
    change ∫ x : ℝ, |conePsiPhysicalReal (x + u 2)| = _
    exact integral_abs_conePsiPhysicalReal_add _
  rw [← (PiLp.volume_preserving_toLp (Fin 5)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  have hfactor : (modelEnergyDensity α u p t ∘ WithLp.toLp 2) =
      (fun x : Fin 5 → ℝ ↦
        ∏ i : Fin 5, scratch_modelEnergyDensityFactor α u p t i (x i)) := by
    funext x
    change modelEnergyDensity α u p t (WithLp.toLp 2 x) = _
    rw [scratch_modelEnergyDensity_eq_prod_factor]
  change (∫ x : Fin 5 → ℝ,
    (modelEnergyDensity α u p t ∘ WithLp.toLp 2) x) = _
  rw [hfactor, integral_fintype_prod_volume_eq_prod]
  have hfac (i : Fin 5) :
      ∫ x : ℝ, scratch_modelEnergyDensityFactor α u p t i x =
        match i.1 with
        | 0 => ∫ x : ℝ, |conePhiPhysicalReal x|
        | 1 => ∫ x : ℝ, |conePhiPhysicalReal x|
        | 2 => 1
        | 3 => 1
        | _ => conePsiPhysicalRealL1 := by
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  simp_rw [hfac]
  simp only [Fin.prod_univ_succ, Finset.prod_empty, mul_one]
  norm_num
  ring

end

end Auto.Twisted
