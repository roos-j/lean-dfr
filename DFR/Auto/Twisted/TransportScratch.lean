import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod
import DFR.Auto.Twisted.Twisted

open MeasureTheory
open scoped RealInnerProductSpace

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev E6 := WithLp 2 (E3 × E3)
abbrev E9p := WithLp 2 (E6 × E3)
abbrev E9 := EuclideanSpace ℝ (Fin 9)

noncomputable def split6Hilbert :
    WithLp 2 (Fin 3 ⊕ Fin 3 → ℝ) ≃ₗᵢ[ℝ] E6 :=
  PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin 3 ⊕ Fin 3 => ℝ)

noncomputable def idx9 : Fin 9 ≃ Fin 3 ⊕ (Fin 3 ⊕ Fin 3) :=
  (finSumFinEquiv (m := 3) (n := 6)).symm.trans
    (Equiv.sumCongr (Equiv.refl _) (finSumFinEquiv (m := 3) (n := 3)).symm)

def frequencyIndexPermutation : Fin 9 ≃ Fin 9 where
  toFun i :=
    match i.1 with
    | 0 => 3
    | 1 => 7
    | 2 => 2
    | 3 => 4
    | 4 => 5
    | 5 => 6
    | 6 => 8
    | 7 => 0
    | _ => 1
  invFun i :=
    match i.1 with
    | 0 => 7
    | 1 => 8
    | 2 => 2
    | 3 => 0
    | 4 => 3
    | 5 => 4
    | 6 => 5
    | 7 => 1
    | _ => 6
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl


noncomputable def split6 : E6 ≃ₗᵢ[ℝ]
    WithLp 2 (E3 × E3) := LinearIsometryEquiv.refl ℝ E6

noncomputable def e9_to_freqHilbert : E9 ≃ₗᵢ[ℝ] E9p :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ idx9).trans
    ((PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin 3 ⊕ (Fin 3 ⊕ Fin 3) => ℝ)).trans
      ((LinearIsometryEquiv.withLpProdCongr 2
        (LinearIsometryEquiv.refl ℝ E3)
        (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin 3 ⊕ Fin 3 => ℝ))).trans
          (LinearIsometryEquiv.withLpProdComm 2 ℝ E3 E6)))

noncomputable def splitToE9 : WithLp 2 (E3 × E6) ≃ₗᵢ[ℝ] E9 :=
  (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ E3)
    split6Hilbert.symm).trans
      ((PiLp.sumPiLpEquivProdLpPiLp 2
        (fun _ : Fin 3 ⊕ (Fin 3 ⊕ Fin 3) => ℝ)).symm.trans
          (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ idx9.symm))

noncomputable def reassemblyHilbert : E9 ≃ₗᵢ[ℝ] E9p :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ frequencyIndexPermutation).trans
    e9_to_freqHilbert

noncomputable def rawFrequencyEquiv : E9p ≃ᵐ ((E3 × E3) × E3) :=
  (MeasurableEquiv.toLp 2 (E6 × E3)).symm.trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.toLp 2 (E3 × E3)).symm (MeasurableEquiv.refl E3))

noncomputable def rawFrequencyCLE : E9p ≃L[ℝ] ((E3 × E3) × E3) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E6 E3).trans
    (ContinuousLinearEquiv.prodCongr
      (WithLp.prodContinuousLinearEquiv 2 ℝ E3 E3)
      (ContinuousLinearEquiv.refl ℝ E3))

noncomputable def frequencyReassemblyCLE :
    (E3 × E6) ≃L[ℝ] ((E3 × E3) × E3) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E3 E6).symm.trans
    ((splitToE9.toContinuousLinearEquiv.trans
      reassemblyHilbert.toContinuousLinearEquiv).trans rawFrequencyCLE)

noncomputable def assemble3 (a b c : ℝ) : E3 :=
  WithLp.toLp 2 ![a, b, c]

@[simp] theorem assemble3_apply (a b c : ℝ) (i : Fin 3) :
    assemble3 a b c i = ![a, b, c] i := rfl

theorem frequencyReassemblyCLE_apply (η : E3) (r : E6) :
    frequencyReassemblyCLE (η, r) =
      ((assemble3 (η 0) (r.fst 0) (r.fst 1),
        assemble3 (r.fst 2) (η 1) (r.snd 0)),
        assemble3 (r.snd 1) (r.snd 2) (η 2)) := by
  apply Prod.ext
  · apply Prod.ext
    · ext i
      fin_cases i <;> rfl
    · ext i
      fin_cases i <;> rfl
  · ext i
    fin_cases i <;> rfl

theorem rawFrequencyEquiv_measurePreserving :
    MeasurePreserving rawFrequencyEquiv volume volume := by
  exact (WithLp.volume_preserving_symm_measurableEquiv_toLp_prod E6 E3).trans
    (MeasurePreserving.prod
      (WithLp.volume_preserving_symm_measurableEquiv_toLp_prod E3 E3)
      (MeasurePreserving.id volume))

theorem reassemblyHilbert_measurePreserving :
    MeasurePreserving reassemblyHilbert volume volume :=
  reassemblyHilbert.measurePreserving

theorem frequencyReassembly_measurePreserving :
    MeasurePreserving frequencyReassemblyCLE volume volume := by
  have h1 : MeasurePreserving (WithLp.toLp 2)
      (volume : Measure (E3 × E6)) (volume : Measure (WithLp 2 (E3 × E6))) :=
    WithLp.volume_preserving_toLp (U := E3) (V := E6)
  have h2 : MeasurePreserving splitToE9
      (volume : Measure (WithLp 2 (E3 × E6))) (volume : Measure E9) :=
    splitToE9.measurePreserving
  have h3 : MeasurePreserving reassemblyHilbert
      (volume : Measure E9) (volume : Measure E9p) :=
    reassemblyHilbert.measurePreserving
  have h4 : MeasurePreserving rawFrequencyEquiv
      (volume : Measure E9p) (volume : Measure ((E3 × E3) × E3)) :=
    rawFrequencyEquiv_measurePreserving
  have h := h4.comp (h3.comp (h2.comp h1))
  convert h using 1
  ext z <;> rfl

#check e9_to_freqHilbert
#check finSumFinEquiv
#check e9_to_freqHilbert.measurePreserving
#check WithLp.volume_preserving_symm_measurableEquiv_toLp_prod
#check WithLp.prodContinuousLinearEquiv
#check LinearIsometryEquiv.piLpCongrLeft
#check MeasurePreserving.comp
#check MeasurePreserving.trans
#check integral_prod
#check MeasureTheory.integral_prod
#check MeasureTheory.integral_integral_swap
#check MeasurePreserving.integral_comp
#check ContinuousLinearEquiv.toHomeomorph
#check Homeomorph.measurableEmbedding
#check MeasurePreserving.integrable_comp_of_integrable
#check MeasureTheory.integral_smul
#check AddChar.map_add_eq_mul

namespace Auto.Twisted.TransportScratch

/-- The half-open active interval of a box has the same integral as its
oriented interval integral.  This is the harmless endpoint-null-set bridge
between the box decomposition and the one-dimensional FTC identity. -/
theorem integral_boxInterval_eq_intervalIntegral
    (α : Anisotropy) (Q : AnisoBox α) (i : Fin 3) (f : ℝ → ℝ) :
    ∫ u in boxInterval α Q i, f u =
      ∫ u in boxFaceCoordinate α Q i FaceOrientation.lower..
        boxFaceCoordinate α Q i FaceOrientation.upper, f u := by
  let a := boxFaceCoordinate α Q i FaceOrientation.lower
  let b := boxFaceCoordinate α Q i FaceOrientation.upper
  have hab : a ≤ b := boxFaceCoordinate_lower_le_upper α Q i
  change ∫ u in Set.Ico a b, f u = ∫ u in a..b, f u
  rw [integral_Ico_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le hab).symm

/-- Fubini lift of the active-coordinate telescope on one box, at a fixed
six-variable point and with an arbitrary transverse weight.  The sole
integrability assumption is exactly the local assumption needed to transport
the left hand side through `integral_boxSet_eq_integral_transverse_interval`.
In the source application `w` is the product of the two inactive `D_m`
factors. -/
theorem weighted_cubeCoordinate_box_telescoping
    (α : Anisotropy) (Q : AnisoBox α) (i : Fin 3) {lam t : ℝ}
    (r : ℝ) (x : E6) (w : TransverseSpace i → ℝ)
    (hlam : 1 ≤ lam) (ht : 0 < t)
    (hlocal : IntegrableOn
      (fun p : E3 =>
        (-t * deriv (fun s : ℝ => cubeCoordinateD α i lam r s p x) t) *
          w (coordinateSplit i p).2)
      (boxSet α Q)) :
    ∫ p in boxSet α Q,
      (-t * deriv (fun s : ℝ => cubeCoordinateD α i lam r s p x) t) *
        w (coordinateSplit i p).2 =
      ∫ y in transverseRectangle α Q i,
        ((α.weight i : ℝ) / Real.pi *
            (∫ u in boxFaceCoordinate α Q i FaceOrientation.lower..
              boxFaceCoordinate α Q i FaceOrientation.upper,
              cubeCoordinateP α i lam r t (faceInsert i u y) x) +
          (α.weight i : ℝ) * t ^ α.weight i *
            (cubeBoundaryKernel α i lam r t
              (faceInsert i (boxFaceCoordinate α Q i FaceOrientation.upper) y) x -
            cubeBoundaryKernel α i lam r t
              (faceInsert i (boxFaceCoordinate α Q i FaceOrientation.lower) y) x)) *
          w y := by
  rw [integral_boxSet_eq_integral_transverse_interval α Q i _ hlocal]
  apply integral_congr_ae
  filter_upwards [] with y
  have htel := cubeCoordinate_oneDim_telescoping_faceInsert_box
    α Q i r 0 y x hlam ht
  let d : ℝ → ℝ := fun u =>
    -t * deriv (fun s : ℝ => cubeCoordinateD α i lam r s (faceInsert i u y) x) t
  have hbox :
      (∫ u in boxInterval α Q i, d u) =
        ∫ u in boxFaceCoordinate α Q i FaceOrientation.lower..
          boxFaceCoordinate α Q i FaceOrientation.upper, d u :=
    integral_boxInterval_eq_intervalIntegral α Q i d
  simp only [coordinateSplit_faceInsert]
  change (∫ u in boxInterval α Q i, d u * w y) = _
  rw [integral_mul_const]
  rw [hbox, htel]

/-- The product of the two inactive coordinate factors, expressed in literal
transverse coordinates. -/
noncomputable def cubeInactiveWeight (α : Anisotropy) (i : Fin 3)
    (lam r t : ℝ) (x : E6) (y : TransverseSpace i) : ℝ :=
  ∏ m ∈ Finset.univ.erase i,
    cubeCoordinateD α m lam r t (faceInsert i 0 y) x

/-- An inactive cubical coordinate factor is unchanged when only the active
center coordinate is varied. -/
theorem cubeCoordinateD_faceInsert_eq_of_ne
    (α : Anisotropy) (i m : Fin 3) (hmi : m ≠ i)
    (lam r t u c : ℝ) (y : TransverseSpace i) (x : E6) :
    cubeCoordinateD α m lam r t (faceInsert i u y) x =
      cubeCoordinateD α m lam r t (faceInsert i c y) x := by
  simp [cubeCoordinateD, cubeGaussianKernel, faceInsert_apply, hmi]

/-- The inactive product on an active/transverse coordinate slice is the
literal transverse weight. -/
theorem cubeInactiveWeight_faceInsert
    (α : Anisotropy) (i : Fin 3) (lam r t u : ℝ)
    (y : TransverseSpace i) (x : E6) :
    (∏ m ∈ Finset.univ.erase i,
      cubeCoordinateD α m lam r t (faceInsert i u y) x) =
      cubeInactiveWeight α i lam r t x y := by
  unfold cubeInactiveWeight
  apply Finset.prod_congr rfl
  intro m hm
  exact cubeCoordinateD_faceInsert_eq_of_ne α i m
    (Finset.mem_erase.mp hm).1 lam r t u 0 y x

/-- Reexpress the inactive product at an ambient point through its literal
transverse coordinates. -/
theorem cubeInactiveWeight_coordinateSplit
    (α : Anisotropy) (i : Fin 3) (lam r t : ℝ) (p : E3) (x : E6) :
    (∏ m ∈ Finset.univ.erase i, cubeCoordinateD α m lam r t p x) =
      cubeInactiveWeight α i lam r t x (coordinateSplit i p).2 := by
  have hjoin : p = faceInsert i (p i) (coordinateSplit i p).2 := by
    simpa [coordinateJoin, coordinateSplit] using (coordinateJoin_split i p).symm
  calc
    (∏ m ∈ Finset.univ.erase i, cubeCoordinateD α m lam r t p x) =
        ∏ m ∈ Finset.univ.erase i,
          cubeCoordinateD α m lam r t
            (faceInsert i (p i) (coordinateSplit i p).2) x :=
      congrArg (fun z : E3 ↦
        ∏ m ∈ Finset.univ.erase i, cubeCoordinateD α m lam r t z x) hjoin
    _ = cubeInactiveWeight α i lam r t x (coordinateSplit i p).2 :=
      cubeInactiveWeight_faceInsert α i lam r t (p i)
        (coordinateSplit i p).2 x

/-- Source-faithful fixed-`x` box-coordinate telescope: the active
one-dimensional identity is multiplied by the product of the two inactive
`D_m` factors and lifted through the literal box Fubini decomposition. -/
theorem cubeCoordinate_box_telescoping
    (α : Anisotropy) (Q : AnisoBox α) (i : Fin 3) {lam t : ℝ}
    (r : ℝ) (x : E6)
    (hlam : 1 ≤ lam) (ht : 0 < t)
    (hlocal : IntegrableOn
      (fun p : E3 =>
        (-t * deriv (fun s : ℝ => cubeCoordinateD α i lam r s p x) t) *
          ∏ m ∈ Finset.univ.erase i, cubeCoordinateD α m lam r t p x)
      (boxSet α Q)) :
    ∫ p in boxSet α Q,
      (-t * deriv (fun s : ℝ => cubeCoordinateD α i lam r s p x) t) *
        ∏ m ∈ Finset.univ.erase i, cubeCoordinateD α m lam r t p x =
      ∫ y in transverseRectangle α Q i,
        ((α.weight i : ℝ) / Real.pi *
            (∫ u in boxFaceCoordinate α Q i FaceOrientation.lower..
              boxFaceCoordinate α Q i FaceOrientation.upper,
              cubeCoordinateP α i lam r t (faceInsert i u y) x) +
          (α.weight i : ℝ) * t ^ α.weight i *
            (cubeBoundaryKernel α i lam r t
              (faceInsert i (boxFaceCoordinate α Q i FaceOrientation.upper) y) x -
            cubeBoundaryKernel α i lam r t
              (faceInsert i (boxFaceCoordinate α Q i FaceOrientation.lower) y) x)) *
          ∏ m ∈ Finset.univ.erase i,
            cubeCoordinateD α m lam r t (faceInsert i 0 y) x := by
  have hlocal' : IntegrableOn
      (fun p : E3 =>
        (-t * deriv (fun s : ℝ => cubeCoordinateD α i lam r s p x) t) *
          cubeInactiveWeight α i lam r t x (coordinateSplit i p).2)
      (boxSet α Q) := by
    apply hlocal.congr_fun
    · intro p _
      change
        (-t * deriv (fun s : ℝ => cubeCoordinateD α i lam r s p x) t) *
            (∏ m ∈ Finset.univ.erase i, cubeCoordinateD α m lam r t p x) =
          (-t * deriv (fun s : ℝ => cubeCoordinateD α i lam r s p x) t) *
            cubeInactiveWeight α i lam r t x (coordinateSplit i p).2
      rw [cubeInactiveWeight_coordinateSplit]
    · exact measurableSet_boxSet α Q
  have htel := weighted_cubeCoordinate_box_telescoping α Q i r x
    (cubeInactiveWeight α i lam r t x) hlam ht hlocal'
  calc
    ∫ p in boxSet α Q,
        (-t * deriv (fun s : ℝ => cubeCoordinateD α i lam r s p x) t) *
          ∏ m ∈ Finset.univ.erase i, cubeCoordinateD α m lam r t p x =
        ∫ p in boxSet α Q,
          (-t * deriv (fun s : ℝ => cubeCoordinateD α i lam r s p x) t) *
            cubeInactiveWeight α i lam r t x (coordinateSplit i p).2 := by
          apply integral_congr_ae
          filter_upwards [] with p
          rw [cubeInactiveWeight_coordinateSplit]
    _ = _ := by
      simpa only [cubeInactiveWeight] using htel

end Auto.Twisted.TransportScratch

namespace Auto.Twisted.TransportScratch

/-- A coordinate-pair factor is differentiable at every nonzero scale. -/
theorem differentiableAt_cubeCoordinateD_scale_ne_zero_scratch
    (α : Anisotropy) (i : Fin 3) {lam t : ℝ} (r : ℝ) (p : E3) (x : E6)
    (hlam : 1 ≤ lam) (ht : t ≠ 0) :
    DifferentiableAt ℝ (fun s : ℝ ↦ cubeCoordinateD α i lam r s p x) t := by
  have hwidth : cubeWidth i lam ≠ 0 :=
    (cubeWidth_pos_of_one_le i hlam).ne'
  simpa only [cubeCoordinateD_eq_scalarD] using
    (hasDerivAt_scalarD_scale (mu := cubeWidth i lam)
      (sig := cubeCenterShift i r) (n := α.weight i) (t := t)
      (p := p i) (u0 := x (i, false)) (u1 := x (i, true))
      hwidth ht).differentiableAt

/-- Positive-scale differentiability of a single coordinate-pair factor. -/
theorem differentiableAt_cubeCoordinateD_scale_scratch
    (α : Anisotropy) (i : Fin 3) {lam t : ℝ} (r : ℝ) (p : E3) (x : E6)
    (hlam : 1 ≤ lam) (ht : 0 < t) :
    DifferentiableAt ℝ (fun s : ℝ ↦ cubeCoordinateD α i lam r s p x) t := by
  exact differentiableAt_cubeCoordinateD_scale_ne_zero_scratch α i r p x hlam ht.ne'

/-- Positive-scale continuity of a single coordinate-pair factor. -/
theorem continuousAt_cubeCoordinateD_scale_scratch
    (α : Anisotropy) (i : Fin 3) {lam t : ℝ} (r : ℝ) (p : E3) (x : E6)
    (hlam : 1 ≤ lam) (ht : 0 < t) :
    ContinuousAt (fun s : ℝ ↦ cubeCoordinateD α i lam r s p x) t :=
  (differentiableAt_cubeCoordinateD_scale_scratch α i r p x hlam ht).continuousAt

/-- Positive-scale continuity of the scale derivative of a coordinate-pair
factor. -/
theorem continuousAt_cubeCoordinateDdot_scale_scratch
    (α : Anisotropy) (i : Fin 3) {lam t : ℝ} (r : ℝ) (p : E3) (x : E6)
    (hlam : 1 ≤ lam) (ht : 0 < t) :
    ContinuousAt (fun q : ℝ ↦
      deriv (fun s : ℝ ↦ cubeCoordinateD α i lam r s p x) q) t := by
  have hwidth : cubeWidth i lam ≠ 0 :=
    (cubeWidth_pos_of_one_le i hlam).ne'
  simpa only [cubeCoordinateD_eq_scalarD] using
    (continuousAt_scalarDdot_scale_scratch
      (mu := cubeWidth i lam) (sig := cubeCenterShift i r)
      (n := α.weight i) (t := t) (p := p i)
      (u0 := x (i, false)) (u1 := x (i, true)) hwidth ht.ne')

/-- The endpoint product is differentiable at every positive scale. -/
theorem differentiableAt_cubeEndpointKernel_scale_scratch
    (α : Anisotropy) {lam t : ℝ} (r : ℝ) (p : E3) (x : E6)
    (hlam : 1 ≤ lam) (ht : 0 < t) :
    DifferentiableAt ℝ (fun s : ℝ ↦ cubeEndpointKernel α lam r s p x) t := by
  simp only [cubeEndpointKernel, Fin.prod_univ_three]
  exact
    ((differentiableAt_cubeCoordinateD_scale_scratch α 0 r p x hlam ht).mul
      (differentiableAt_cubeCoordinateD_scale_scratch α 1 r p x hlam ht)).mul
      (differentiableAt_cubeCoordinateD_scale_scratch α 2 r p x hlam ht)

/-- The derivative of the endpoint product is continuous at every positive
scale.  The proof expands the literal three-factor product rule and uses the
scalar derivative formula away from scale zero. -/
theorem continuousAt_cubeEndpointKernel_deriv_scale_scratch
    (α : Anisotropy) {lam t : ℝ} (r : ℝ) (p : E3) (x : E6)
    (hlam : 1 ≤ lam) (ht : 0 < t) :
    ContinuousAt (fun q : ℝ ↦
      deriv (fun s : ℝ ↦ cubeEndpointKernel α lam r s p x) q) t := by
  let D : Fin 3 → ℝ → ℝ := fun i q ↦ cubeCoordinateD α i lam r q p x
  let d : ℝ → ℝ := fun q ↦
    (deriv (D 0) q * D 1 q + D 0 q * deriv (D 1) q) * D 2 q +
      (D 0 q * D 1 q) * deriv (D 2) q
  have hD0 : ContinuousAt (D 0) t := by
    dsimp only [D]
    exact continuousAt_cubeCoordinateD_scale_scratch α 0 r p x hlam ht
  have hD1 : ContinuousAt (D 1) t := by
    dsimp only [D]
    exact continuousAt_cubeCoordinateD_scale_scratch α 1 r p x hlam ht
  have hD2 : ContinuousAt (D 2) t := by
    dsimp only [D]
    exact continuousAt_cubeCoordinateD_scale_scratch α 2 r p x hlam ht
  have hdD0 : ContinuousAt (fun q : ℝ ↦ deriv (D 0) q) t := by
    dsimp only [D]
    exact continuousAt_cubeCoordinateDdot_scale_scratch α 0 r p x hlam ht
  have hdD1 : ContinuousAt (fun q : ℝ ↦ deriv (D 1) q) t := by
    dsimp only [D]
    exact continuousAt_cubeCoordinateDdot_scale_scratch α 1 r p x hlam ht
  have hdD2 : ContinuousAt (fun q : ℝ ↦ deriv (D 2) q) t := by
    dsimp only [D]
    exact continuousAt_cubeCoordinateDdot_scale_scratch α 2 r p x hlam ht
  have hform : ContinuousAt d t := by
    dsimp only [d]
    exact (((hdD0.mul hD1).add (hD0.mul hdD1)).mul hD2).add
      ((hD0.mul hD1).mul hdD2)
  have heq : (fun q : ℝ ↦
      deriv (fun s : ℝ ↦ cubeEndpointKernel α lam r s p x) q) =ᶠ[𝓝 t] d := by
    filter_upwards [eventually_ne_nhds ht.ne'] with q hq
    have hd0 : DifferentiableAt ℝ (D 0) q := by
      dsimp only [D]
      exact differentiableAt_cubeCoordinateD_scale_ne_zero_scratch α 0 r p x hlam hq
    have hd1 : DifferentiableAt ℝ (D 1) q := by
      dsimp only [D]
      exact differentiableAt_cubeCoordinateD_scale_ne_zero_scratch α 1 r p x hlam hq
    have hd2 : DifferentiableAt ℝ (D 2) q := by
      dsimp only [D]
      exact differentiableAt_cubeCoordinateD_scale_ne_zero_scratch α 2 r p x hlam hq
    simp only [cubeEndpointKernel, Fin.prod_univ_three]
    change deriv ((D 0 * D 1) * D 2) q = d q
    rw [deriv_mul (hd0.mul hd1) hd2, deriv_mul hd0 hd1]
    rfl
  exact hform.congr_of_eventuallyEq heq

/-- The fixed-`(p,x)` scale fundamental-theorem-of-calculus step from
Section 4: the two endpoint kernels differ by the logarithmic scale integral
of their scale derivative. -/
theorem cubeEndpointKernel_scale_FTC_scratch
    (α : Anisotropy) {lam L : ℝ} (r : ℝ) (p : E3) (x : E6)
    (hlam : 1 ≤ lam) (hL : 0 < L) :
    cubeEndpointKernel α lam r (L / 2) p x - cubeEndpointKernel α lam r L p x =
      ∫ t in L / 2..L,
        (-t * deriv (fun s : ℝ ↦ cubeEndpointKernel α lam r s p x) t) / t := by
  let K : ℝ → ℝ := fun s ↦ cubeEndpointKernel α lam r s p x
  have hhalf : 0 < L / 2 := by linarith
  have hle : L / 2 ≤ L := by linarith
  have hderiv : ∀ s ∈ Set.uIcc (L / 2) L, DifferentiableAt ℝ K s := by
    intro s hs
    rw [Set.uIcc_of_le hle] at hs
    have hspos : 0 < s := lt_of_lt_of_le hhalf hs.1
    dsimp only [K]
    exact differentiableAt_cubeEndpointKernel_scale_scratch α r p x hlam hspos
  have hcont : ContinuousOn (deriv K) (Set.uIcc (L / 2) L) := by
    intro s hs
    rw [Set.uIcc_of_le hle] at hs
    have hspos : 0 < s := lt_of_lt_of_le hhalf hs.1
    simpa only [K] using
      (continuousAt_cubeEndpointKernel_deriv_scale_scratch α r p x hlam hspos).continuousWithinAt
  have hFTC : (∫ s in L / 2..L, deriv K s) = K L - K (L / 2) :=
    intervalIntegral.integral_deriv_eq_sub hderiv hcont.intervalIntegrable
  change K (L / 2) - K L =
    ∫ t in L / 2..L, (-t * deriv K t) / t
  calc
    K (L / 2) - K L = -(K L - K (L / 2)) := by ring
    _ = -(∫ s in L / 2..L, deriv K s) := by rw [hFTC]
    _ = ∫ s in L / 2..L, -deriv K s := by
      rw [intervalIntegral.integral_neg]
    _ = ∫ s in L / 2..L, (-s * deriv K s) / s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hle] at hs
      have hspos : 0 < s := lt_of_lt_of_le hhalf hs.1
      symm
      apply (div_eq_iff hspos.ne').2
      ring

end Auto.Twisted.TransportScratch

namespace Auto.Twisted.TransportScratch

theorem continuousAt_scalarG_scale_scratch {mu sig : ℝ} {n : ℕ} {t p u : ℝ}
    (hmu : mu ≠ 0) (ht : t ≠ 0) :
    ContinuousAt (fun q : ℝ => scalarG mu sig n q p u) t := by
  have hscale : mu * t ^ n ≠ 0 :=
    mul_ne_zero hmu (pow_ne_zero n ht)
  have hpow : ContinuousAt (fun q : ℝ => q ^ n) t := continuousAt_id.pow n
  have hs : ContinuousAt (fun q : ℝ => mu * q ^ n) t :=
    continuousAt_const.mul hpow
  have hinv : ContinuousAt (fun q : ℝ => (mu * q ^ n)⁻¹) t := hs.inv₀ hscale
  have hcenter : ContinuousAt (fun q : ℝ => p + sig * q ^ n) t :=
    continuousAt_const.add (continuousAt_const.mul hpow)
  have hnum : ContinuousAt (fun q : ℝ => u - (p + sig * q ^ n)) t :=
    continuousAt_const.sub hcenter
  have hratio : ContinuousAt
      (fun q : ℝ => (u - (p + sig * q ^ n)) / (mu * q ^ n)) t := by
    change ContinuousAt
      (fun q : ℝ => (u - (p + sig * q ^ n)) * (mu * q ^ n)⁻¹) t
    convert hnum.mul hinv using 1
    funext q
    rfl
  have hexp : ContinuousAt
      (fun q : ℝ => Real.exp (-Real.pi *
        ((u - (p + sig * q ^ n)) / (mu * q ^ n)) ^ 2)) t :=
    (Real.continuous_exp.continuousAt.comp
      (continuousAt_const.mul (hratio.pow 2)))
  unfold scalarG gaussianAt kernelAt kernelDilate gaussian
  exact hinv.smul hexp

theorem differentiableAt_scalarH_scale_scratch {mu sig : ℝ} {n : ℕ} {t p u : ℝ}
    (hmu : mu ≠ 0) (ht : t ≠ 0) :
    DifferentiableAt ℝ (fun q : ℝ => scalarH mu sig n q p u) t := by
  have hscale : mu * t ^ n ≠ 0 :=
    mul_ne_zero hmu (pow_ne_zero n ht)
  unfold scalarH gaussianDerivAt kernelAt kernelDilate gaussianDeriv gaussian
  fun_prop (disch := exact hscale)

theorem continuousAt_scalarH_scale_scratch {mu sig : ℝ} {n : ℕ} {t p u : ℝ}
    (hmu : mu ≠ 0) (ht : t ≠ 0) :
    ContinuousAt (fun q : ℝ => scalarH mu sig n q p u) t :=
  (differentiableAt_scalarH_scale_scratch hmu ht).continuousAt

theorem differentiableAt_scalarZ_scale_scratch {mu sig : ℝ} {n : ℕ} {t p u : ℝ}
    (hmu : mu ≠ 0) (ht : t ≠ 0) :
    DifferentiableAt ℝ (fun q : ℝ => scalarZ mu sig n q p u) t := by
  have hscale : mu * t ^ n ≠ 0 :=
    mul_ne_zero hmu (pow_ne_zero n ht)
  have hpow : HasDerivAt (fun q : ℝ => q ^ n)
      ((n : ℝ) * t ^ (n - 1)) t := by
    simpa using hasDerivAt_pow n t
  have hs : HasDerivAt (fun q : ℝ => mu * q ^ n)
      (mu * ((n : ℝ) * t ^ (n - 1))) t := by
    convert hpow.const_mul mu using 1
  have hcenter : HasDerivAt (fun q : ℝ => p + sig * q ^ n)
      (sig * ((n : ℝ) * t ^ (n - 1))) t := by
    convert (hpow.const_mul sig).const_add p using 1
  have hnum : HasDerivAt (fun q : ℝ => u - (p + sig * q ^ n))
      (-(sig * ((n : ℝ) * t ^ (n - 1)))) t := by
    convert hcenter.const_sub u using 1
  change DifferentiableAt ℝ
    (fun q : ℝ => (u - (p + sig * q ^ n)) / (mu * q ^ n)) t
  exact hnum.differentiableAt.fun_div hs.differentiableAt hscale

theorem continuousAt_scalarZ_scale_scratch {mu sig : ℝ} {n : ℕ} {t p u : ℝ}
    (hmu : mu ≠ 0) (ht : t ≠ 0) :
    ContinuousAt (fun q : ℝ => scalarZ mu sig n q p u) t :=
  (differentiableAt_scalarZ_scale_scratch hmu ht).continuousAt

theorem continuousAt_scalarDdot_scale_scratch
    {mu sig : ℝ} {n : ℕ} {t p u0 u1 : ℝ}
    (hmu : mu ≠ 0) (ht : t ≠ 0) :
    ContinuousAt (fun q : ℝ =>
      deriv (fun s : ℝ => scalarD mu sig n s p u0 u1) q) t := by
  let d : ℝ → ℝ := fun q =>
    -(n : ℝ) / q *
      (2 * scalarD mu sig n q p u0 u1 +
        (scalarZ mu sig n q p u0 + sig / mu) * scalarH mu sig n q p u0 *
          scalarG mu sig n q p u1 +
        (scalarZ mu sig n q p u1 + sig / mu) * scalarG mu sig n q p u0 *
          scalarH mu sig n q p u1)
  have hscale : mu * t ^ n ≠ 0 :=
    mul_ne_zero hmu (pow_ne_zero n ht)
  have hform : ContinuousAt d t := by
    dsimp only [d]
    fun_prop (disch := assumption) [scalarD, scalarG, scalarH, scalarZ,
      gaussianAt, gaussianDerivAt, kernelAt, kernelDilate, gaussian, gaussianDeriv]
  have heq : (fun q : ℝ =>
      deriv (fun s : ℝ => scalarD mu sig n s p u0 u1) q) =ᶠ[𝓝 t] d := by
    filter_upwards [eventually_ne_nhds ht] with q hq
    exact (hasDerivAt_scalarD_scale hmu hq).deriv
  exact hform.congr_of_eventuallyEq heq

end Auto.Twisted.TransportScratch
