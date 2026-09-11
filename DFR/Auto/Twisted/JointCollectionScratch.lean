import Auto.Twisted.Twisted

namespace Auto.Twisted

open MeasureTheory Filter FourierTransform TopologicalSpace
open scoped BigOperators Convolution ENNReal FourierTransform LineDeriv RealInnerProductSpace Topology

noncomputable section

/-- The local cube integrand is genuinely jointly integrable over any finite
collection of box--scale cells.  This is the product-space input for the
active/passive Fubini proof of cubical Cauchy--Schwarz. -/
theorem scratch_integrable_cubeSignedInputProduct_mul_localCubeKernel_collection
    (α : Anisotropy) (S : BoxCollection α) (i : Fin 3) (lam r : ℝ)
    (F : CubeVertex → E3 → ℝ)
    (hFcont : ∀ j, Continuous (F j))
    (hFbound : ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ y, |F j y| ≤ B)
    (hlam : 1 ≤ lam) :
    Integrable (fun z : (E3 × ℝ) × E6 ↦
      cubeSignedInputProduct F z.2 *
        localCubeKernel α i lam r z.1.2 z.1.1 z.2)
      ((cubeScaleMeasure.restrict (collectionRegion α S)).prod volume) := by
  let g : (E3 × ℝ) × E6 → ℝ := fun z ↦
    cubeSignedInputProduct F z.2 *
      localCubeKernel α i lam r z.1.2 z.1.1 z.2
  have hcell (q : AnisoBox α) :
      Integrable g ((cubeScaleMeasure.restrict (boxScaleRegion α q)).prod volume) := by
    rw [cubeScaleMeasure_restrict_boxScaleRegion]
    exact integrable_cubeSignedInputProduct_mul_localCubeKernel_boxScaleCell
      α q i lam r F hFcont hFbound hlam
  letI : SFinite cubeScaleMeasure := by
    change SFinite ((volume : Measure E3).prod
      ((volume : Measure ℝ).withDensity cubeScaleDensity))
    infer_instance
  rw [Measure.restrict_prod_eq_prod_univ]
  change IntegrableOn g ((collectionRegion α S) ×ˢ (Set.univ : Set E6))
    (cubeScaleMeasure.prod volume)
  classical
  induction S using Finset.induction_on with
  | empty => simp [collectionRegion]
  | @insert q S hq ih =>
      have hregion : collectionRegion α (insert q S) =
          boxScaleRegion α q ∪ collectionRegion α S := by
        ext z
        simp [collectionRegion]
      rw [hregion, Set.union_prod]
      apply IntegrableOn.union
      · change Integrable g ((cubeScaleMeasure.prod volume).restrict
            (boxScaleRegion α q ×ˢ (Set.univ : Set E6)))
        rw [← Measure.restrict_prod_eq_prod_univ]
        exact hcell q
      · exact ih

end

end Auto.Twisted
