import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import DFR.Auto.Twisted.Twisted

open MeasureTheory Filter FourierTransform TopologicalSpace
open scoped FourierTransform RealInnerProductSpace

#check fourier_gaussian_pi
#check Complex.ofReal_exp
#check FourierTransform.fourier
#check Complex.ofRealCLM.hasDerivAt
#check @ContinuousLinearMap.hasDerivAt
#check @HasDerivAt.comp
#check @HasFDerivAt.comp
#check @HasFDerivAt.hasDerivAt
#check @HasDerivAt.hasFDerivAt
#check Complex.ofRealCLM.hasFDerivAt
#check @SchwartzMap.postcompCLM
#check Complex.norm_real
#check Integrable.ofReal

noncomputable def g (x : ℝ) : ℝ := Real.exp (-Real.pi * x ^ 2)

example :
    (𝓕 fun x : ℝ ↦ (g x : ℂ)) = fun t : ℝ ↦ (g t : ℂ) := by
  have h := fourier_gaussian_pi (b := (1 : ℂ)) (by norm_num)
  convert h using 1 <;> ext x <;> simp [g]

namespace Auto.Twisted

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal RealInnerProductSpace

#check IsCompact.image
#check isCompact_pi_infinite
#check PiLp.continuous_toLp
#check WithLp.toLp
#check WithLp.ofLp
#check Set.Ico_subset_Icc_self
#check ContinuousOn.integrableOn_of_subset_isCompact
#check volume_boxSet
#check ENNReal.ofReal_ne_top
#check ENNReal.prod_ne_top
#check coordinateProjection
#check continuous_scalarD_center
#check continuous_scalarDdot_center
#check continuous_scalarP_center
#check continuous_scalarE_center
#check scalarE_differentiableAt_center

/-- Compact coordinatewise closure used only to obtain local integrability on
the half-open source box. -/
noncomputable def scratchBoxClosedSet (α : Anisotropy) (q : AnisoBox α) : Set E3 :=
  (WithLp.toLp 2) '' Set.pi Set.univ (fun i ↦
    Set.Icc ((q.index i : ℝ) * boxSide α q i)
      (((q.index i + 1 : ℤ) : ℝ) * boxSide α q i))

theorem isCompact_scratchBoxClosedSet (α : Anisotropy) (q : AnisoBox α) :
    IsCompact (scratchBoxClosedSet α q) := by
  unfold scratchBoxClosedSet
  let K : Set (Fin 3 → ℝ) := Set.pi Set.univ (fun i ↦
    Set.Icc ((q.index i : ℝ) * boxSide α q i)
      (((q.index i + 1 : ℤ) : ℝ) * boxSide α q i))
  change IsCompact ((WithLp.toLp 2) '' K)
  have hK : IsCompact K := by
    dsimp only [K]
    exact isCompact_univ_pi fun _ ↦ isCompact_Icc
  exact hK.image (PiLp.continuous_toLp 2 _)

theorem boxSet_subset_scratchBoxClosedSet (α : Anisotropy) (q : AnisoBox α) :
    boxSet α q ⊆ scratchBoxClosedSet α q := by
  intro p hp
  refine ⟨WithLp.ofLp p, ?_, ?_⟩
  · rw [Set.mem_pi]
    intro i _
    rw [boxSet, Set.mem_preimage, Set.mem_pi] at hp
    exact Set.Ico_subset_Icc_self (hp i (Set.mem_univ i))
  · simp

theorem volume_boxSet_ne_top_scratch (α : Anisotropy) (q : AnisoBox α) :
    volume (boxSet α q) ≠ ∞ := by
  rw [volume_boxSet]
  exact ENNReal.prod_ne_top fun _ _ ↦ ENNReal.ofReal_ne_top

/-- A continuous ambient function is integrable on every literal source box. -/
theorem scratch_integrableOn_boxSet_of_continuous {α : Anisotropy}
    {f : E3 → ℝ} (hf : Continuous f) (q : AnisoBox α) :
    IntegrableOn f (boxSet α q) := by
  exact hf.continuousOn.integrableOn_of_subset_isCompact
    (isCompact_scratchBoxClosedSet α q) (measurableSet_boxSet α q)
    (boxSet_subset_scratchBoxClosedSet α q) (volume_boxSet_ne_top_scratch α q)

/-- Center-continuity of the active Gaussian pair at positive source scale. -/
theorem scratch_continuous_cubeCoordinateD_center
    (α : Anisotropy) (i : Fin 3) {lam t : ℝ} (r : ℝ) (x : E6)
    (hlam : 1 ≤ lam) (ht : 0 < t) :
    Continuous (fun p : E3 ↦ cubeCoordinateD α i lam r t p x) := by
  have hscale : cubeWidth i lam * t ^ α.weight i ≠ 0 :=
    cubeGaussianScale_ne_zero α i hlam ht
  simpa only [cubeCoordinateD_eq_scalarD, coordinateProjection_apply,
    Function.comp_def] using
    (continuous_scalarD_center (mu := cubeWidth i lam)
      (sig := cubeCenterShift i r) (n := α.weight i) (t := t)
      (u0 := x (i, false)) (u1 := x (i, true)) hscale).comp
      (coordinateProjection i).continuous

/-- Center-continuity of the active derivative-Gaussian pair. -/
theorem scratch_continuous_cubeCoordinateP_center
    (α : Anisotropy) (i : Fin 3) (lam r t : ℝ) (x : E6) :
    Continuous (fun p : E3 ↦ cubeCoordinateP α i lam r t p x) := by
  simpa only [cubeCoordinateP_eq_scalarP, coordinateProjection_apply,
    Function.comp_def] using
    (continuous_scalarP_center (mu := cubeWidth i lam)
      (sig := cubeCenterShift i r) (n := α.weight i) (t := t)
      (u0 := x (i, false)) (u1 := x (i, true))).comp
      (coordinateProjection i).continuous

/-- Center-continuity of the boundary kernel at positive source scale. -/
theorem scratch_continuous_cubeBoundaryKernel_center
    (α : Anisotropy) (i : Fin 3) {lam t : ℝ} (r : ℝ) (x : E6)
    (hlam : 1 ≤ lam) (ht : 0 < t) :
    Continuous (fun p : E3 ↦ cubeBoundaryKernel α i lam r t p x) := by
  have hscale : cubeWidth i lam * t ^ α.weight i ≠ 0 :=
    cubeGaussianScale_ne_zero α i hlam ht
  simpa only [cubeBoundaryKernel_eq_scalarE, coordinateProjection_apply,
    Function.comp_def] using
    (continuous_scalarE_center (mu := cubeWidth i lam)
      (sig := cubeCenterShift i r) (n := α.weight i) (t := t)
      (u0 := x (i, false)) (u1 := x (i, true)) hscale).comp
      (coordinateProjection i).continuous

/-- Center-continuity of the scale derivative of the active Gaussian pair. -/
theorem scratch_continuous_cubeCoordinateDdot_center
    (α : Anisotropy) (i : Fin 3) {lam t : ℝ} (r : ℝ) (x : E6)
    (hlam : 1 ≤ lam) (ht : 0 < t) :
    Continuous (fun p : E3 ↦ deriv (fun s : ℝ ↦
      cubeCoordinateD α i lam r s p x) t) := by
  have hmu : cubeWidth i lam ≠ 0 :=
    (cubeWidth_pos_of_one_le i hlam).ne'
  simpa only [cubeCoordinateD_eq_scalarD, coordinateProjection_apply,
    Function.comp_def] using
    (continuous_scalarDdot_center (mu := cubeWidth i lam)
      (sig := cubeCenterShift i r) (n := α.weight i) (t := t)
      (u0 := x (i, false)) (u1 := x (i, true)) hmu ht.ne').comp
      (coordinateProjection i).continuous

theorem scratch_integrableOn_cubeCoordinateD_boxSet
    (α : Anisotropy) (q : AnisoBox α) (i : Fin 3) {lam t : ℝ}
    (r : ℝ) (x : E6) (hlam : 1 ≤ lam) (ht : 0 < t) :
    IntegrableOn (fun p : E3 ↦ cubeCoordinateD α i lam r t p x) (boxSet α q) :=
  scratch_integrableOn_boxSet_of_continuous
    (scratch_continuous_cubeCoordinateD_center α i r x hlam ht) q

theorem scratch_integrableOn_cubeCoordinateP_boxSet
    (α : Anisotropy) (q : AnisoBox α) (i : Fin 3) (lam r t : ℝ) (x : E6) :
    IntegrableOn (fun p : E3 ↦ cubeCoordinateP α i lam r t p x) (boxSet α q) :=
  scratch_integrableOn_boxSet_of_continuous
    (scratch_continuous_cubeCoordinateP_center α i lam r t x) q

theorem scratch_integrableOn_cubeBoundaryKernel_boxSet
    (α : Anisotropy) (q : AnisoBox α) (i : Fin 3) {lam t : ℝ}
    (r : ℝ) (x : E6) (hlam : 1 ≤ lam) (ht : 0 < t) :
    IntegrableOn (fun p : E3 ↦ cubeBoundaryKernel α i lam r t p x) (boxSet α q) :=
  scratch_integrableOn_boxSet_of_continuous
    (scratch_continuous_cubeBoundaryKernel_center α i r x hlam ht) q

theorem scratch_integrableOn_cubeCoordinateDdot_boxSet
    (α : Anisotropy) (q : AnisoBox α) (i : Fin 3) {lam t : ℝ}
    (r : ℝ) (x : E6) (hlam : 1 ≤ lam) (ht : 0 < t) :
    IntegrableOn (fun p : E3 ↦ deriv (fun s : ℝ ↦
      cubeCoordinateD α i lam r s p x) t) (boxSet α q) :=
  scratch_integrableOn_boxSet_of_continuous
    (scratch_continuous_cubeCoordinateDdot_center α i r x hlam ht) q

/-- Compact coordinatewise closure of a transverse half-open rectangle. -/
noncomputable def scratchTransverseClosedRectangle (α : Anisotropy)
    (q : AnisoBox α) (i : Fin 3) : Set (TransverseSpace i) :=
  (WithLp.toLp 2) '' Set.pi Set.univ (fun j : {m : Fin 3 // m ≠ i} ↦
    Set.Icc ((q.index j.1 : ℝ) * boxSide α q j.1)
      (((q.index j.1 + 1 : ℤ) : ℝ) * boxSide α q j.1))

theorem isCompact_scratchTransverseClosedRectangle (α : Anisotropy)
    (q : AnisoBox α) (i : Fin 3) :
    IsCompact (scratchTransverseClosedRectangle α q i) := by
  unfold scratchTransverseClosedRectangle
  let K : Set ({j : Fin 3 // j ≠ i} → ℝ) := Set.pi Set.univ (fun j ↦
    Set.Icc ((q.index j.1 : ℝ) * boxSide α q j.1)
      (((q.index j.1 + 1 : ℤ) : ℝ) * boxSide α q j.1))
  change IsCompact ((WithLp.toLp 2) '' K)
  have hK : IsCompact K := by
    dsimp only [K]
    exact isCompact_univ_pi fun _ ↦ isCompact_Icc
  exact hK.image (PiLp.continuous_toLp 2 _)

theorem transverseRectangle_subset_scratchTransverseClosedRectangle
    (α : Anisotropy) (q : AnisoBox α) (i : Fin 3) :
    transverseRectangle α q i ⊆ scratchTransverseClosedRectangle α q i := by
  intro y hy
  refine ⟨WithLp.ofLp y, ?_, ?_⟩
  · rw [Set.mem_pi]
    intro j _
    rw [transverseRectangle, Set.mem_preimage, Set.mem_pi] at hy
    exact Set.Ico_subset_Icc_self (hy j (Set.mem_univ j))
  · simp

theorem volume_transverseRectangle_ne_top_scratch (α : Anisotropy)
    (q : AnisoBox α) (i : Fin 3) :
    volume (transverseRectangle α q i) ≠ ∞ := by
  rw [volume_transverseRectangle]
  exact ENNReal.prod_ne_top fun _ _ ↦ ENNReal.ofReal_ne_top

/-- A continuous transverse function is integrable on every source face
rectangle. -/
theorem scratch_integrableOn_transverseRectangle_of_continuous
    {α : Anisotropy} {i : Fin 3} {f : TransverseSpace i → ℝ}
    (hf : Continuous f) (q : AnisoBox α) :
    IntegrableOn f (transverseRectangle α q i) := by
  exact hf.continuousOn.integrableOn_of_subset_isCompact
    (isCompact_scratchTransverseClosedRectangle α q i)
    (measurableSet_transverseRectangle α q i)
    (transverseRectangle_subset_scratchTransverseClosedRectangle α q i)
    (volume_transverseRectangle_ne_top_scratch α q i)

theorem scratch_continuous_cubeBoundaryKernel_face
    (α : Anisotropy) (i : Fin 3) {lam t : ℝ} (r c : ℝ) (x : E6)
    (hlam : 1 ≤ lam) (ht : 0 < t) :
    Continuous (fun y : TransverseSpace i ↦
      cubeBoundaryKernel α i lam r t (faceInsert i c y) x) :=
  (scratch_continuous_cubeBoundaryKernel_center α i r x hlam ht).comp
    (faceInsert_continuous i c)

theorem scratch_integrableOn_cubeBoundaryKernel_face
    (α : Anisotropy) (q : AnisoBox α) (i : Fin 3) {lam t : ℝ}
    (r c : ℝ) (x : E6) (hlam : 1 ≤ lam) (ht : 0 < t) :
    IntegrableOn (fun y : TransverseSpace i ↦
      cubeBoundaryKernel α i lam r t (faceInsert i c y) x)
      (transverseRectangle α q i) :=
  scratch_integrableOn_transverseRectangle_of_continuous
    (scratch_continuous_cubeBoundaryKernel_face α i r c x hlam ht) q

/-- Fubini in literal box coordinates for the scale derivative appearing in
the one-dimensional telescope. -/
theorem scratch_integral_cubeCoordinateDdot_boxSet_eq_transverse_interval
    (α : Anisotropy) (q : AnisoBox α) (i : Fin 3) {lam t : ℝ}
    (r : ℝ) (x : E6) (hlam : 1 ≤ lam) (ht : 0 < t) :
    (∫ p : E3 in boxSet α q, deriv (fun s : ℝ ↦
      cubeCoordinateD α i lam r s p x) t) =
      ∫ y in transverseRectangle α q i,
        ∫ u in boxInterval α q i, deriv (fun s : ℝ ↦
          cubeCoordinateD α i lam r s (faceInsert i u y) x) t := by
  exact integral_boxSet_eq_integral_transverse_interval α q i _
    (scratch_integrableOn_cubeCoordinateDdot_boxSet α q i r x hlam ht)

/-- Fubini in literal box coordinates for the active derivative-Gaussian
pair on the right side of the telescope. -/
theorem scratch_integral_cubeCoordinateP_boxSet_eq_transverse_interval
    (α : Anisotropy) (q : AnisoBox α) (i : Fin 3) (lam r t : ℝ) (x : E6) :
    (∫ p : E3 in boxSet α q, cubeCoordinateP α i lam r t p x) =
      ∫ y in transverseRectangle α q i,
        ∫ u in boxInterval α q i,
          cubeCoordinateP α i lam r t (faceInsert i u y) x := by
  exact integral_boxSet_eq_integral_transverse_interval α q i _
    (scratch_integrableOn_cubeCoordinateP_boxSet α q i lam r t x)

/-! ### Spatial absolute integrability for sixfold Gaussian kernels -/

/-- A choice of either `G` or `H` in each of the six spatial slots. -/
noncomputable def scratchSixfoldGaussianKernel (α : Anisotropy)
    (choose : Fin 3 × Bool → Bool) (lam r t : ℝ) (p : E3) (x : E6) : ℝ :=
  ∏ q : Fin 3 × Bool,
    if choose q then
      cubeGaussianDerivKernel α lam r t p q.1 (x q)
    else
      cubeGaussianKernel α lam r t p q.1 (x q)

/-- The signed cube input product is continuous when every source input is
continuous. -/
theorem scratch_continuous_cubeSignedInputProduct
    (F : CubeVertex → E3 → ℝ) (hF : ∀ j, Continuous (F j)) :
    Continuous (cubeSignedInputProduct F) := by
  unfold cubeSignedInputProduct
  apply continuous_finsetProd Finset.univ
  intro j _
  exact (hF j).comp (cubeProjection_continuous j)

/-- A continuous Gaussian or derivative-Gaussian factor is continuous in its
one selected spatial coordinate. -/
theorem scratch_continuous_sixfoldGaussianFactor
    (α : Anisotropy) (choose : (Fin 3 × Bool) → Bool) (lam r t : ℝ) (p : E3)
    (q : Fin 3 × Bool) :
    Continuous (fun x : E6 ↦
      if choose q then
        cubeGaussianDerivKernel α lam r t p q.1 (x q)
      else
        cubeGaussianKernel α lam r t p q.1 (x q)) := by
  by_cases hq : choose q
  · simp only [hq, ↓reduceIte]
    have harg : Continuous (fun x : E6 ↦
        (x q - (p q.1 + cubeCenterShift q.1 r * t ^ α.weight q.1)) /
          (cubeWidth q.1 lam * t ^ α.weight q.1)) :=
      ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 × Bool ↦ ℝ) q).sub
        continuous_const).div_const _
    have hderiv : Continuous gaussianDeriv := by
      unfold gaussianDeriv
      exact (continuous_const.mul continuous_id).mul gaussian_contDiff.continuous
    unfold cubeGaussianDerivKernel gaussianDerivAt kernelAt kernelDilate
    simp only [smul_eq_mul]
    exact continuous_const.mul (hderiv.comp harg)
  · simp only [hq]
    have harg : Continuous (fun x : E6 ↦
        (x q - (p q.1 + cubeCenterShift q.1 r * t ^ α.weight q.1)) /
          (cubeWidth q.1 lam * t ^ α.weight q.1)) :=
      ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 × Bool ↦ ℝ) q).sub
        continuous_const).div_const _
    unfold cubeGaussianKernel gaussianAt kernelAt kernelDilate
    simp only [smul_eq_mul]
    exact continuous_const.mul (gaussian_contDiff.continuous.comp harg)

/-- Any sixfold `G/H` kernel is continuous in the six spatial variables. -/
theorem scratch_continuous_sixfoldGaussianKernel
    (α : Anisotropy) (choose : (Fin 3 × Bool) → Bool) (lam r t : ℝ) (p : E3) :
    Continuous (scratchSixfoldGaussianKernel α choose lam r t p) := by
  unfold scratchSixfoldGaussianKernel
  apply continuous_finsetProd Finset.univ
  intro q _
  exact scratch_continuous_sixfoldGaussianFactor α choose lam r t p q

/-- A uniform bound for the eightfold input product. -/
theorem scratch_exists_bound_cubeSignedInputProduct
    (F : CubeVertex → E3 → ℝ)
    (hF : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |F j y| ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |cubeSignedInputProduct F x| ≤ B := by
  classical
  choose B hB using hF
  refine ⟨∏ j : CubeVertex, B j, Finset.prod_nonneg (fun j _ ↦ (hB j).1), ?_⟩
  intro x
  rw [cubeSignedInputProduct, Finset.abs_prod]
  exact Finset.prod_le_prod (fun j _ ↦ abs_nonneg _) (fun j _ ↦ (hB j).2 _)

/-- At fixed positive scale, a bounded continuous cube input product times
any sixfold choice of the source `G/H` kernels is absolutely integrable in
the six spatial variables. -/
theorem scratch_integrable_cubeSignedInputProduct_mul_sixfoldGaussianKernel
    (α : Anisotropy) (choose : (Fin 3 × Bool) → Bool) (lam r t : ℝ) (p : E3)
    (F : CubeVertex → E3 → ℝ) (hFcont : ∀ j, Continuous (F j))
    (hFbound : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |F j y| ≤ C)
    (hlam : 1 ≤ lam) (ht : 0 < t) :
    Integrable (fun x : E6 ↦ cubeSignedInputProduct F x *
      scratchSixfoldGaussianKernel α choose lam r t p x) := by
  rcases scratch_exists_bound_cubeSignedInputProduct F hFbound with ⟨B, hB, hinput⟩
  rcases cubeGaussian_sixfold_domination α with ⟨C, hC, hdom⟩
  let D : ℝ := C ^ 6 * lam ^ 36 * translationWeight r ^ 20
  have hmajor : Integrable (fun x : E6 ↦
      (B * D) * cubeBracketWeight α t p x) := by
    simpa only [smul_eq_mul] using
      (integrable_cubeBracketWeight α ht p).const_mul (B * D)
  have hmeas : AEStronglyMeasurable
      (fun x : E6 ↦ cubeSignedInputProduct F x *
        scratchSixfoldGaussianKernel α choose lam r t p x) volume :=
    ((scratch_continuous_cubeSignedInputProduct F hFcont).mul
      (scratch_continuous_sixfoldGaussianKernel α choose lam r t p)).aestronglyMeasurable
  refine hmajor.mono hmeas (Filter.Eventually.of_forall ?_)
  intro x
  have hkernel : |scratchSixfoldGaussianKernel α choose lam r t p x| ≤
      D * cubeBracketWeight α t p x := by
    dsimp [scratchSixfoldGaussianKernel, D]
    rw [Finset.abs_prod]
    exact hdom choose lam r t p x hlam ht
  have hmajor_nonneg : 0 ≤ (B * D) * cubeBracketWeight α t p x := by
    simpa only [mul_assoc] using
      (mul_nonneg hB (le_trans (abs_nonneg _) hkernel))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hmajor_nonneg]
  calc
    |cubeSignedInputProduct F x| *
        |scratchSixfoldGaussianKernel α choose lam r t p x| ≤
        B * (D * cubeBracketWeight α t p x) :=
      mul_le_mul (hinput x) hkernel (abs_nonneg _) hB
    _ = (B * D) * cubeBracketWeight α t p x := by ring

/-- The preceding sixfold statement specialized to the local cube kernel. -/
theorem scratch_integrable_cubeSignedInputProduct_mul_localCubeKernel
    (α : Anisotropy) (i : Fin 3) (lam r t : ℝ) (p : E3)
    (F : CubeVertex → E3 → ℝ) (hFcont : ∀ j, Continuous (F j))
    (hFbound : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |F j y| ≤ C)
    (hlam : 1 ≤ lam) (ht : 0 < t) :
    Integrable (fun x : E6 ↦ cubeSignedInputProduct F x *
      localCubeKernel α i lam r t p x) := by
  simpa [scratchSixfoldGaussianKernel, localCubeKernel] using
    scratch_integrable_cubeSignedInputProduct_mul_sixfoldGaussianKernel
      α (fun q ↦ decide (q.1 = i)) lam r t p F hFcont hFbound hlam ht

end Auto.Twisted
