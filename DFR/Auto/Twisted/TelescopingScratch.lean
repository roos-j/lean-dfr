import DFR.Auto.Twisted.Twisted

namespace Auto.Twisted

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal RealInnerProductSpace

noncomputable section

#check HasDerivAt.inv
#check HasDerivAt.div
#check HasDerivAt.comp
#check intervalIntegral.integral_deriv_eq_sub
#check intervalIntegral.integral_deriv_eq_sub'
#check intervalIntegral.integral_hasDerivAt_right
#check intervalIntegral.integral_hasDerivAt_left
#check intervalIntegral.integral_add
#check Finset.sum_involution
#check Finset.sum_ninvolution
#check Finset.sum_filter_add_sum_filter_not
#check MeasurePreserving.integral_comp
#check MeasureTheory.integral_prod
#check MeasureTheory.integral_prod_symm
#check MeasureTheory.integral_integral_swap
#check MeasureTheory.integral_indicator
#check prod_withDensity_right
#check Measure.volume_eq_prod
#check MeasureTheory.setIntegral_prod
#check Measurable.ite
#check Measurable.inv
#check integral_Ico_eq_integral_Ioc
#check intervalIntegral.integral_of_le
#check MeasureTheory.integral_add
#check MeasureTheory.integral_sub
#check MeasureTheory.integral_const_mul
#check deriv_mul
#check Fin.sum_univ_three
#check Fin.prod_univ_three
#check MeasureTheory.integral_finset_sum
#check MeasureTheory.integral_finsetSum

/-- Scratch version of the Fubini-lifted source box telescope. -/
theorem test_cubeCoordinate_box_telescoping_weighted
    (α : Anisotropy) (Q : AnisoBox α) (i : Fin 3) {lam t : ℝ}
    (r : ℝ) (x : E6) (w : TransverseSpace i → ℝ)
    (hlam : 1 ≤ lam) (ht : 0 < t)
    (hD : IntegrableOn (fun p : E3 ↦
      w (coordinateSplit i p).2 *
        (-t * deriv (fun s : ℝ ↦ cubeCoordinateD α i lam r s p x) t))
      (boxSet α Q))
    (hP : IntegrableOn (fun p : E3 ↦
      w (coordinateSplit i p).2 * cubeCoordinateP α i lam r t p x)
      (boxSet α Q))
    (hElo : IntegrableOn (fun y : TransverseSpace i ↦
      w y * cubeBoundaryKernel α i lam r t
        (faceInsert i (boxFaceCoordinate α Q i FaceOrientation.lower) y) x)
      (transverseRectangle α Q i))
    (hEhi : IntegrableOn (fun y : TransverseSpace i ↦
      w y * cubeBoundaryKernel α i lam r t
        (faceInsert i (boxFaceCoordinate α Q i FaceOrientation.upper) y) x)
      (transverseRectangle α Q i))
    (hPouter : Integrable (fun y : TransverseSpace i ↦
      ∫ u in boxInterval α Q i,
        w y * cubeCoordinateP α i lam r t (faceInsert i u y) x)
      (volume.restrict (transverseRectangle α Q i))) :
    (∫ p : E3 in boxSet α Q,
      w (coordinateSplit i p).2 *
        (-t * deriv (fun s : ℝ ↦ cubeCoordinateD α i lam r s p x) t)) =
      (α.weight i : ℝ) / Real.pi *
        (∫ p : E3 in boxSet α Q,
          w (coordinateSplit i p).2 * cubeCoordinateP α i lam r t p x) +
      (α.weight i : ℝ) * t ^ α.weight i *
        ((∫ y : TransverseSpace i in transverseRectangle α Q i,
          w y * cubeBoundaryKernel α i lam r t
            (faceInsert i (boxFaceCoordinate α Q i FaceOrientation.upper) y) x) -
         (∫ y : TransverseSpace i in transverseRectangle α Q i,
          w y * cubeBoundaryKernel α i lam r t
            (faceInsert i (boxFaceCoordinate α Q i FaceOrientation.lower) y) x)) := by
  have hDsplit := integral_boxSet_eq_integral_transverse_interval α Q i
    (fun p : E3 ↦ w (coordinateSplit i p).2 *
      (-t * deriv (fun s : ℝ ↦ cubeCoordinateD α i lam r s p x) t)) hD
  have hPsplit := integral_boxSet_eq_integral_transverse_interval α Q i
    (fun p : E3 ↦ w (coordinateSplit i p).2 *
      cubeCoordinateP α i lam r t p x) hP
  simp only [coordinateSplit_faceInsert] at hDsplit hPsplit
  rw [hDsplit, hPsplit]
  let c : ℝ := (α.weight i : ℝ) / Real.pi
  let d : ℝ := (α.weight i : ℝ) * t ^ α.weight i
  let lo : ℝ := boxFaceCoordinate α Q i FaceOrientation.lower
  let hi : ℝ := boxFaceCoordinate α Q i FaceOrientation.upper
  let R : Set (TransverseSpace i) := transverseRectangle α Q i
  let Ddot : TransverseSpace i → ℝ → ℝ := fun y u ↦
    w y * (-t * deriv (fun s : ℝ ↦
      cubeCoordinateD α i lam r s (faceInsert i u y) x) t)
  let P : TransverseSpace i → ℝ → ℝ := fun y u ↦
    w y * cubeCoordinateP α i lam r t (faceInsert i u y) x
  let Elo : TransverseSpace i → ℝ := fun y ↦
    w y * cubeBoundaryKernel α i lam r t (faceInsert i lo y) x
  let Ehi : TransverseSpace i → ℝ := fun y ↦
    w y * cubeBoundaryKernel α i lam r t (faceInsert i hi y) x
  have hpoint (y : TransverseSpace i) :
      (∫ u in boxInterval α Q i, Ddot y u) =
        c * (∫ u in boxInterval α Q i, P y u) + d * (Ehi y - Elo y) := by
    dsimp only [Ddot, P, Elo, Ehi, c, d, lo, hi]
    have hbase := cubeCoordinate_oneDim_telescoping_faceInsert_box
      α Q i r 0 y x hlam ht
    have horder := boxFaceCoordinate_lower_le_upper α Q i
    simp_rw [intervalIntegral.integral_of_le horder] at hbase
    simp_rw [← integral_Ico_eq_integral_Ioc] at hbase
    calc
      (∫ u in boxInterval α Q i,
        w y * (-t * deriv (fun s : ℝ ↦
          cubeCoordinateD α i lam r s (faceInsert i u y) x) t)) =
          w y * (∫ u in boxInterval α Q i,
            -t * deriv (fun s : ℝ ↦
              cubeCoordinateD α i lam r s (faceInsert i u y) x) t) := by
            rw [MeasureTheory.integral_const_mul]
      _ = w y * ((α.weight i : ℝ) / Real.pi *
            (∫ u in boxInterval α Q i,
              cubeCoordinateP α i lam r t (faceInsert i u y) x) +
          (α.weight i : ℝ) * t ^ α.weight i *
            (cubeBoundaryKernel α i lam r t
              (faceInsert i (boxFaceCoordinate α Q i FaceOrientation.upper) y) x -
              cubeBoundaryKernel α i lam r t
                (faceInsert i (boxFaceCoordinate α Q i FaceOrientation.lower) y) x)) := by
            simpa only [boxInterval, boxFaceCoordinate] using
              congrArg (fun z : ℝ ↦ w y * z) hbase
      _ = (α.weight i : ℝ) / Real.pi *
            (∫ u in boxInterval α Q i,
              w y * cubeCoordinateP α i lam r t (faceInsert i u y) x) +
          (α.weight i : ℝ) * t ^ α.weight i *
            (w y * cubeBoundaryKernel α i lam r t
              (faceInsert i (boxFaceCoordinate α Q i FaceOrientation.upper) y) x -
              w y * cubeBoundaryKernel α i lam r t
                (faceInsert i (boxFaceCoordinate α Q i FaceOrientation.lower) y) x) := by
            rw [MeasureTheory.integral_const_mul]
            ring
  have hboundary : Integrable (fun y : TransverseSpace i ↦ d * (Ehi y - Elo y))
      (volume.restrict R) := by
    exact ((hEhi.sub hElo).const_mul d)
  calc
    (∫ y : TransverseSpace i in transverseRectangle α Q i,
      ∫ u in boxInterval α Q i,
        w y * (-t * deriv (fun s : ℝ ↦
          cubeCoordinateD α i lam r s (faceInsert i u y) x) t)) =
        ∫ y : TransverseSpace i in R,
          (c * (∫ u in boxInterval α Q i, P y u) + d * (Ehi y - Elo y)) := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact hpoint y
    _ = c * (∫ y : TransverseSpace i in R,
          ∫ u in boxInterval α Q i, P y u) +
        d * ((∫ y : TransverseSpace i in R, Ehi y) -
          (∫ y : TransverseSpace i in R, Elo y)) := by
      rw [MeasureTheory.integral_add (hPouter.const_mul c) hboundary]
      rw [MeasureTheory.integral_const_mul]
      rw [MeasureTheory.integral_const_mul]
      rw [MeasureTheory.integral_sub hEhi hElo]
    _ = _ := by
      simp only [c, d, P, Ehi, Elo, R, hi, lo]

theorem test_cubeCoordinateD_faceInsert_ne
    (α : Anisotropy) (i j : Fin 3) (lam r t u : ℝ)
    (y : TransverseSpace i) (x : E6) (hji : j ≠ i) :
    cubeCoordinateD α j lam r t (faceInsert i u y) x =
      cubeCoordinateD α j lam r t (faceInsert i 0 y) x := by
  simp [cubeCoordinateD, cubeGaussianKernel, faceInsert_apply, hji]

theorem test_passiveProduct_faceInsert
    (α : Anisotropy) (i : Fin 3) (lam r t u : ℝ)
    (y : TransverseSpace i) (x : E6) :
    (∏ m ∈ Finset.univ.erase i,
      cubeCoordinateD α m lam r t (faceInsert i u y) x) =
      ∏ m ∈ Finset.univ.erase i,
        cubeCoordinateD α m lam r t (faceInsert i 0 y) x := by
  apply Finset.prod_congr rfl
  intro m hm
  exact test_cubeCoordinateD_faceInsert_ne α i m lam r t u y x
    (Finset.mem_erase.mp hm).1

noncomputable def test_cubePassiveCoordinateKernel (α : Anisotropy) (i : Fin 3)
    (lam r t : ℝ) (p : E3) (x : E6) : ℝ :=
  ∏ m ∈ Finset.univ.erase i, cubeCoordinateD α m lam r t p x

theorem test_cubePassiveCoordinateKernel_faceInsert
    (α : Anisotropy) (i : Fin 3) (lam r t u : ℝ)
    (y : TransverseSpace i) (x : E6) :
    test_cubePassiveCoordinateKernel α i lam r t (faceInsert i u y) x =
      test_cubePassiveCoordinateKernel α i lam r t (faceInsert i 0 y) x := by
  exact test_passiveProduct_faceInsert α i lam r t u y x

theorem test_cubePassiveCoordinateKernel_coordinateSplit
    (α : Anisotropy) (i : Fin 3) (lam r t : ℝ) (p : E3) (x : E6) :
    test_cubePassiveCoordinateKernel α i lam r t p x =
      test_cubePassiveCoordinateKernel α i lam r t
        (faceInsert i 0 (coordinateSplit i p).2) x := by
  calc
    test_cubePassiveCoordinateKernel α i lam r t p x =
        test_cubePassiveCoordinateKernel α i lam r t
          (coordinateJoin i (coordinateSplit i p)) x :=
      congrArg (fun q : E3 ↦ test_cubePassiveCoordinateKernel α i lam r t q x)
        (coordinateJoin_split i p).symm
    _ = test_cubePassiveCoordinateKernel α i lam r t
          (faceInsert i (coordinateSplit i p).1 (coordinateSplit i p).2) x := rfl
    _ = _ := test_cubePassiveCoordinateKernel_faceInsert α i lam r t
      (coordinateSplit i p).1 (coordinateSplit i p).2 x

theorem test_cubeEndpointKernel_scale_derivative
    (α : Anisotropy) (lam r t : ℝ) (p : E3) (x : E6)
    (hlam : 1 ≤ lam) (ht : 0 < t) :
    -t * deriv (fun s : ℝ ↦ cubeEndpointKernel α lam r s p x) t =
      ∑ i : Fin 3,
        (-t * deriv (fun s : ℝ ↦ cubeCoordinateD α i lam r s p x) t) *
          ∏ m ∈ Finset.univ.erase i, cubeCoordinateD α m lam r t p x := by
  have hwidth (i : Fin 3) : cubeWidth i lam ≠ 0 := by
    unfold cubeWidth
    split_ifs with hi
    · linarith
    · positivity
  have hdif (i : Fin 3) : DifferentiableAt ℝ
      (fun s : ℝ ↦ cubeCoordinateD α i lam r s p x) t := by
    simpa only [cubeCoordinateD_eq_scalarD] using
      (hasDerivAt_scalarD_scale (mu := cubeWidth i lam)
        (sig := cubeCenterShift i r) (n := α.weight i) (t := t)
        (p := p i) (u0 := x (i, false)) (u1 := x (i, true))
        (hwidth i) ht.ne').differentiableAt
  simp only [cubeEndpointKernel, Fin.prod_univ_three]
  change -t * deriv
      (((fun s : ℝ ↦ cubeCoordinateD α 0 lam r s p x) *
        (fun s : ℝ ↦ cubeCoordinateD α 1 lam r s p x)) *
        (fun s : ℝ ↦ cubeCoordinateD α 2 lam r s p x)) t = _
  rw [deriv_mul ((hdif 0).mul (hdif 1)) (hdif 2)]
  rw [deriv_mul (hdif 0) (hdif 1)]
  simp only [Fin.sum_univ_three]
  have herase0 : (Finset.univ.erase (0 : Fin 3)) = {1, 2} := by decide
  have herase1 : (Finset.univ.erase (1 : Fin 3)) = {0, 2} := by decide
  have herase2 : (Finset.univ.erase (2 : Fin 3)) = {0, 1} := by decide
  rw [herase0, herase1, herase2]
  simp
  ring

example {α : Anisotropy} (q : AnisoBox α) (f : Fin 3 → E3 → ℝ)
    (hf : ∀ i, IntegrableOn (f i) (boxSet α q)) :
    (∫ p in boxSet α q, ∑ i, f i p) =
      ∑ i, ∫ p in boxSet α q, f i p := by
  apply MeasureTheory.integral_finset_sum
  intro i hi
  exact hf i

theorem test_integrable_outer_integral_boxInterval
    (α : Anisotropy) (q : AnisoBox α) (i : Fin 3) (f : E3 → ℝ)
    (hf : IntegrableOn f (boxSet α q)) :
    Integrable (fun y : TransverseSpace i ↦
      ∫ u in boxInterval α q i, f (faceInsert i u y))
      (volume.restrict (transverseRectangle α q i)) := by
  let A : Set (ℝ × TransverseSpace i) :=
    boxInterval α q i ×ˢ transverseRectangle α q i
  let g : ℝ × TransverseSpace i → ℝ :=
    fun z ↦ f ((coordinateSplitEquiv i).symm z)
  have htransport : IntegrableOn g A := by
    apply (coordinateSplitEquiv_measurePreserving i).integrableOn_comp_preimage
      (coordinateSplitEquiv i).measurableEmbedding |>.mp
    have hcomp : g ∘ coordinateSplitEquiv i = f := by
      funext p
      simp [g]
    have hpre : (coordinateSplitEquiv i) ⁻¹' A = boxSet α q := by
      ext p
      change coordinateSplit i p ∈
        boxInterval α q i ×ˢ transverseRectangle α q i ↔ p ∈ boxSet α q
      exact coordinateSplit_mem_box_product_iff α q i p
    rw [hcomp, hpre]
    exact hf
  have htransport' : IntegrableOn g A
      ((volume : Measure ℝ).prod (volume : Measure (TransverseSpace i))) := by
    simpa only [Measure.volume_eq_prod] using htransport
  have hswap : Integrable g
      ((volume.restrict (boxInterval α q i)).prod
        (volume.restrict (transverseRectangle α q i))) := by
    simpa only [IntegrableOn, A, ← Measure.prod_restrict] using htransport'
  have hswap' : Integrable (Function.uncurry fun u y ↦ g (u, y))
      ((volume.restrict (boxInterval α q i)).prod
        (volume.restrict (transverseRectangle α q i))) := by
    refine Integrable.congr hswap (Filter.Eventually.of_forall ?_)
    rintro ⟨u, y⟩
    rfl
  convert hswap'.integral_prod_right using 1
  funext y
  congr 1

/-- Scratch version of the fully split fixed-`x` box telescope.  It applies
the general weighted Fubini theorem with the two inactive Gaussian pairs as
the weight, and discharges every resulting integrability obligation from
compact-domain continuity. -/
theorem test_cubeCoordinate_box_telescoping_split_of_pos
    (α : Anisotropy) (Q : AnisoBox α) (i : Fin 3) {lam t : ℝ}
    (r : ℝ) (x : E6) (hlam : 1 ≤ lam) (ht : 0 < t) :
    ∫ p in boxSet α Q,
      (-t * deriv (fun s : ℝ ↦ cubeCoordinateD α i lam r s p x) t) *
        ∏ m ∈ Finset.univ.erase i, cubeCoordinateD α m lam r t p x =
      (α.weight i : ℝ) / Real.pi *
        (∫ p in boxSet α Q, localCubeKernel α i lam r t p x) +
      (α.weight i : ℝ) * t ^ α.weight i *
        ((∫ y in transverseRectangle α Q i,
          cubeFaceKernel α i lam r t
            (faceInsert i (boxFaceCoordinate α Q i FaceOrientation.upper) y) x) -
         (∫ y in transverseRectangle α Q i,
          cubeFaceKernel α i lam r t
            (faceInsert i (boxFaceCoordinate α Q i FaceOrientation.lower) y) x)) := by
  let w : TransverseSpace i → ℝ := cubeInactiveWeight α i lam r t x
  have hpassive : Continuous (fun p : E3 ↦
      ∏ m ∈ Finset.univ.erase i, cubeCoordinateD α m lam r t p x) := by
    apply continuous_finsetProd
    intro m hm
    exact continuous_cubeCoordinateD_center α m r x hlam ht
  have hw : Continuous (fun p : E3 ↦ w (coordinateSplit i p).2) := by
    apply Continuous.congr hpassive
    intro p
    dsimp only [w]
    exact cubeInactiveWeight_coordinateSplit α i lam r t p x
  have hD : IntegrableOn (fun p : E3 ↦
      w (coordinateSplit i p).2 *
        (-t * deriv (fun s : ℝ ↦ cubeCoordinateD α i lam r s p x) t))
      (boxSet α Q) := by
    apply integrableOn_boxSet_of_continuous
    exact hw.mul ((continuous_const.mul
      (continuous_cubeCoordinateDdot_center α i r x hlam ht)))
  have hP : IntegrableOn (fun p : E3 ↦
      w (coordinateSplit i p).2 * cubeCoordinateP α i lam r t p x)
      (boxSet α Q) := by
    apply integrableOn_boxSet_of_continuous
    exact hw.mul (continuous_cubeCoordinateP_center α i lam r t x)
  have hE (o : FaceOrientation) : IntegrableOn
      (fun y : TransverseSpace i ↦
        w y * cubeBoundaryKernel α i lam r t
          (faceInsert i (boxFaceCoordinate α Q i o) y) x)
      (transverseRectangle α Q i) := by
    apply integrableOn_transverseRectangle_of_continuous
    have hwface : Continuous w := by
      dsimp only [w, cubeInactiveWeight]
      apply continuous_finsetProd
      intro m hm
      exact (continuous_cubeCoordinateD_center α m r x hlam ht).comp
        (faceInsert_continuous i 0)
    exact hwface.mul (continuous_cubeBoundaryKernel_face α i r
      (boxFaceCoordinate α Q i o) x hlam ht)
  have hPouter : Integrable (fun y : TransverseSpace i ↦
      ∫ u in boxInterval α Q i,
        w y * cubeCoordinateP α i lam r t (faceInsert i u y) x)
      (volume.restrict (transverseRectangle α Q i)) := by
    have h := integrable_outer_integral_boxInterval_of_integrableOn α Q i
      (fun p : E3 ↦ w (coordinateSplit i p).2 *
        cubeCoordinateP α i lam r t p x) hP
    simpa only [coordinateSplit_faceInsert] using h
  have htel := cubeCoordinate_box_telescoping_weighted α Q i r x w hlam ht
    hD hP (hE FaceOrientation.lower) (hE FaceOrientation.upper) hPouter
  have hlocal :
      (∫ p in boxSet α Q,
        w (coordinateSplit i p).2 * cubeCoordinateP α i lam r t p x) =
        ∫ p in boxSet α Q, localCubeKernel α i lam r t p x := by
    apply integral_congr_ae
    filter_upwards [] with p
    dsimp only [w]
    rw [← cubeInactiveWeight_coordinateSplit]
    simpa only [mul_comm] using
      (localCubeKernel_eq_coordinateP_mul α i lam r t p x).symm
  have hleft :
      (∫ p in boxSet α Q,
        (-t * deriv (fun s : ℝ ↦ cubeCoordinateD α i lam r s p x) t) *
          ∏ m ∈ Finset.univ.erase i, cubeCoordinateD α m lam r t p x) =
        ∫ p in boxSet α Q,
          w (coordinateSplit i p).2 *
            (-t * deriv (fun s : ℝ ↦ cubeCoordinateD α i lam r s p x) t) := by
    apply integral_congr_ae
    filter_upwards [] with p
    dsimp only [w]
    rw [← cubeInactiveWeight_coordinateSplit]
    ring
  have hface (o : FaceOrientation) :
      (∫ y in transverseRectangle α Q i,
        w y * cubeBoundaryKernel α i lam r t
          (faceInsert i (boxFaceCoordinate α Q i o) y) x) =
        ∫ y in transverseRectangle α Q i,
          cubeFaceKernel α i lam r t
            (faceInsert i (boxFaceCoordinate α Q i o) y) x := by
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [w]
    rw [cubeFaceKernel, cubeInactiveWeight_faceInsert]
    ring
  rw [hleft, htel, hlocal, hface FaceOrientation.upper,
    hface FaceOrientation.lower]

end

end Auto.Twisted
