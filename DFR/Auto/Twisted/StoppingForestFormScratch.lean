import Auto.Twisted.Twisted

namespace Auto

open MeasureTheory Filter FourierTransform TopologicalSpace
open scoped BigOperators Convolution ENNReal FourierTransform LineDeriv RealInnerProductSpace Topology

noncomputable section

namespace Twisted

/-- At each stopping vector, the localized form is exactly the sum over its
maximal-root stopping trees. -/
theorem scratch_expandedModelLocalForm_stoppingLevel_eq_sum_trees_of_integrable
    {d : ℕ} (α : Anisotropy) (S : BoxCollection α) (s : Fin d → ℝ)
    (f : Fin d → E3 → ℝ) (n : Fin d → ℤ) (u : E3) (c : ℝ → ℝ)
    (F : ModelRealInput)
    (hint : Integrable (fun pt : E3 × ℝ ↦
      c pt.2 * (∫ z : ModelE5,
        modelFirstFiber α F pt.1 pt.2 z *
          modelSecondFiber α (F 3) pt.1 pt.2 z *
            modelSignedDensity α u pt.1 pt.2 z))
      (cubeScaleMeasure.restrict
        (collectionRegion α (stoppingLevel α S s f n)))) :
    expandedModelLocalForm α (stoppingLevel α S s f n) u c F =
      ∑ Q ∈ stoppingRoots α S s f n,
        expandedModelLocalForm α (stoppingTreeBoxes α S s f n Q) u c F := by
  rw [stoppingLevel_eq_biUnion_stoppingTreeBoxes] at hint ⊢
  exact expandedModelLocalForm_biUnion_eq_sum_of_integrable α
    (stoppingRoots α S s f n) (stoppingTreeBoxes α S s f n) u c F
    (pairwiseDisjoint_stoppingTreeBoxes α S s f n) hint

/-- The first energy has the same exact stopping-tree partition. -/
theorem scratch_modelEnergyOne_stoppingLevel_eq_sum_trees_of_integrable
    {d : ℕ} (α : Anisotropy) (S : BoxCollection α) (s : Fin d → ℝ)
    (f : Fin d → E3 → ℝ) (n : Fin d → ℤ) (u : E3) (F : ModelRealInput)
    (hint : Integrable (fun pt : E3 × ℝ ↦
      ∫ z : ModelE5,
        (modelFirstFiber α F pt.1 pt.2 z) ^ 2 *
          modelEnergyDensity α u pt.1 pt.2 z)
      (cubeScaleMeasure.restrict
        (collectionRegion α (stoppingLevel α S s f n)))) :
    modelEnergyOne α (stoppingLevel α S s f n) u F =
      ∑ Q ∈ stoppingRoots α S s f n,
        modelEnergyOne α (stoppingTreeBoxes α S s f n Q) u F := by
  rw [stoppingLevel_eq_biUnion_stoppingTreeBoxes] at hint ⊢
  exact modelEnergyOne_biUnion_eq_sum_of_integrable α
    (stoppingRoots α S s f n) (stoppingTreeBoxes α S s f n) u F
    (pairwiseDisjoint_stoppingTreeBoxes α S s f n) hint

/-- The second energy has the same exact stopping-tree partition. -/
theorem scratch_modelEnergyTwo_stoppingLevel_eq_sum_trees_of_integrable
    {d : ℕ} (α : Anisotropy) (S : BoxCollection α) (s : Fin d → ℝ)
    (f : Fin d → E3 → ℝ) (n : Fin d → ℤ) (u : E3) (F : E3 → ℝ)
    (hint : Integrable (fun pt : E3 × ℝ ↦
      ∫ z : ModelE5,
        (modelSecondFiber α F pt.1 pt.2 z) ^ 2 *
          modelEnergyDensity α u pt.1 pt.2 z)
      (cubeScaleMeasure.restrict
        (collectionRegion α (stoppingLevel α S s f n)))) :
    modelEnergyTwo α (stoppingLevel α S s f n) u F =
      ∑ Q ∈ stoppingRoots α S s f n,
        modelEnergyTwo α (stoppingTreeBoxes α S s f n Q) u F := by
  rw [stoppingLevel_eq_biUnion_stoppingTreeBoxes] at hint ⊢
  exact modelEnergyTwo_biUnion_eq_sum_of_integrable α
    (stoppingRoots α S s f n) (stoppingTreeBoxes α S s f n) u F
    (pairwiseDisjoint_stoppingTreeBoxes α S s f n) hint

end Twisted

end

end Auto
