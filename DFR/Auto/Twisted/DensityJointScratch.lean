import Auto.Twisted.Twisted

namespace Auto.Twisted

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal RealInnerProductSpace

noncomputable section

/-- A finite collection has finite center--scale measure. -/
theorem scratch_isFiniteMeasure_cubeScaleCollection
    (α : Anisotropy) (S : BoxCollection α) :
    IsFiniteMeasure (cubeScaleMeasure.restrict (collectionRegion α S)) := by
  constructor
  rw [Measure.restrict_apply_univ]
  have hcell (q : AnisoBox α) :
      cubeScaleMeasure (boxScaleRegion α q) < ∞ := by
    rw [← Measure.restrict_apply_univ,
      cubeScaleMeasure_restrict_boxScaleRegion]
    letI : IsFiniteMeasure
        ((volume.restrict (boxSet α q)).prod
          ((volume.withDensity cubeScaleDensity).restrict (boxScaleBand q))) :=
      isFiniteMeasure_boxScaleCell α q
    exact IsFiniteMeasure.measure_univ_lt_top
  rw [collectionRegion,
    MeasureTheory.measure_biUnion_finset
      (pairwiseDisjoint_boxScaleRegion α S)
      (fun q hq ↦ measurableSet_boxScaleRegion α q)]
  exact ENNReal.sum_lt_top.mpr fun q hq ↦ hcell q

/-- The literal positive local-model density is jointly integrable over every
finite box collection. -/
theorem scratch_integrable_modelEnergyDensity_collection
    (α : Anisotropy) (S : BoxCollection α) (u : E3) :
    Integrable (fun q : (E3 × ℝ) × ModelE5 ↦
      modelEnergyDensity α u q.1.1 q.1.2 q.2)
      ((cubeScaleMeasure.restrict (collectionRegion α S)).prod
        (volume : Measure ModelE5)) := by
  let μ : Measure (E3 × ℝ) :=
    cubeScaleMeasure.restrict (collectionRegion α S)
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact scratch_isFiniteMeasure_cubeScaleCollection α S
  have hpos : ∀ᵐ pt ∂μ, 0 < pt.2 := by
    dsimp only [μ]
    filter_upwards [ae_restrict_mem (measurableSet_collectionRegion α S)]
      with pt hpt
    exact pos_of_mem_closure_collectionRegion α S (subset_closure hpt)
  have hmeas : AEStronglyMeasurable (fun q : (E3 × ℝ) × ModelE5 ↦
      modelEnergyDensity α u q.1.1 q.1.2 q.2) (μ.prod volume) :=
    aestronglyMeasurable_modelEnergyDensity α u (μ.prod volume)
  apply (integrable_prod_iff hmeas).mpr
  constructor
  · filter_upwards [hpos] with pt hpt
    exact integrable_modelEnergyDensity α u pt.1 hpt
  · let K : ℝ := (∫ x : ℝ, |conePhiPhysicalReal x|) ^ 2 *
      conePsiPhysicalRealL1
    have hconst : Integrable (fun _ : E3 × ℝ ↦ K) μ := integrable_const _
    refine hconst.congr ?_
    filter_upwards [hpos] with pt hpt
    change K = (∫ z : ModelE5,
      ‖modelEnergyDensity α u pt.1 pt.2 z‖)
    symm
    have hnonneg : ∀ z : ModelE5,
        0 ≤ modelEnergyDensity α u pt.1 pt.2 z :=
      fun z ↦ modelEnergyDensity_nonneg α u pt.1 hpt.le z
    rw [show (fun z : ModelE5 ↦
      ‖modelEnergyDensity α u pt.1 pt.2 z‖) =
        modelEnergyDensity α u pt.1 pt.2 by
      funext z
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg z)]]
    exact integral_modelEnergyDensity α u pt.1 hpt

end

end Auto.Twisted
