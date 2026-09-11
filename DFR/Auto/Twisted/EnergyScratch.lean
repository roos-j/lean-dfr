import Auto.Twisted.Twisted

namespace Auto.Twisted

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal RealInnerProductSpace

noncomputable section

/-- The first local energy is nonnegative on every finite collection. -/
theorem scratch_modelEnergyOne_nonneg
    (α : Anisotropy) (S : BoxCollection α) (u : E3)
    (f : ModelRealInput) :
    0 ≤ modelEnergyOne α S u f := by
  unfold modelEnergyOne
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (measurableSet_collectionRegion α S)] with pt hpt
  apply integral_nonneg
  intro z
  exact mul_nonneg (sq_nonneg _) (modelEnergyDensity_nonneg α u pt.1
    (pos_of_mem_closure_collectionRegion α S (subset_closure hpt)).le z)

/-- The second local energy over an arbitrary positive-scale region is
nonnegative. -/
theorem scratch_modelEnergyTwoOn_nonneg
    (α : Anisotropy) (V : Set (E3 × ℝ)) (u : E3) (f : E3 → ℝ)
    (hV : MeasurableSet V)
    (hpos : ∀ pt ∈ V, 0 < pt.2) :
    0 ≤ modelEnergyTwoOn α V u f := by
  unfold modelEnergyTwoOn
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem hV] with pt hpt
  apply integral_nonneg
  intro z
  exact mul_nonneg (sq_nonneg _) (modelEnergyDensity_nonneg α u pt.1
    (hpos pt hpt).le z)

theorem scratch_modelEnergyTwo_nonneg
    (α : Anisotropy) (S : BoxCollection α) (u : E3) (f : E3 → ℝ) :
    0 ≤ modelEnergyTwo α S u f := by
  unfold modelEnergyTwo
  apply scratch_modelEnergyTwoOn_nonneg
  · exact measurableSet_collectionRegion α S
  intro pt hpt
  exact pos_of_mem_closure_collectionRegion α S (subset_closure hpt)

end

end Auto.Twisted
