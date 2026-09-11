import Auto.Twisted.Twisted

namespace Auto

open MeasureTheory Filter FourierTransform TopologicalSpace
open scoped BigOperators Convolution ENNReal FourierTransform LineDeriv RealInnerProductSpace Topology

noncomputable section

namespace Twisted

/-- Finite unions of literal box collections become ordinary unions of their
center--scale regions. -/
theorem scratch_collectionRegion_union (α : Anisotropy)
    (S T : BoxCollection α) :
    collectionRegion α (S ∪ T) =
      collectionRegion α S ∪ collectionRegion α T := by
  ext z
  constructor
  · intro hz
    rw [collectionRegion] at hz
    rcases Set.mem_iUnion.1 hz with ⟨q, hz⟩
    rcases Set.mem_iUnion.1 hz with ⟨hq, hz⟩
    rw [Finset.mem_union] at hq
    rcases hq with hq | hq
    · left
      rw [collectionRegion]
      exact Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hq, hz⟩⟩
    · right
      rw [collectionRegion]
      exact Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hq, hz⟩⟩
  · intro hz
    rw [collectionRegion]
    rcases hz with hz | hz
    · rw [collectionRegion] at hz
      rcases Set.mem_iUnion.1 hz with ⟨q, hz⟩
      rcases Set.mem_iUnion.1 hz with ⟨hq, hz⟩
      exact Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2
        ⟨Finset.mem_union_left _ hq, hz⟩⟩
    · rw [collectionRegion] at hz
      rcases Set.mem_iUnion.1 hz with ⟨q, hz⟩
      rcases Set.mem_iUnion.1 hz with ⟨hq, hz⟩
      exact Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2
        ⟨Finset.mem_union_right _ hq, hz⟩⟩

/-- Disjoint finite box collections have disjoint center--scale regions. -/
theorem scratch_disjoint_collectionRegion_of_disjoint (α : Anisotropy)
    (S T : BoxCollection α) (hST : Disjoint S T) :
    Disjoint (collectionRegion α S) (collectionRegion α T) := by
  rw [Set.disjoint_left]
  intro z hzS hzT
  rw [collectionRegion] at hzS hzT
  rcases Set.mem_iUnion.1 hzS with ⟨q, hzS⟩
  rcases Set.mem_iUnion.1 hzS with ⟨hqS, hzq⟩
  rcases Set.mem_iUnion.1 hzT with ⟨r, hzT⟩
  rcases Set.mem_iUnion.1 hzT with ⟨hrT, hzr⟩
  by_cases hqr : q = r
  · subst r
    exact (Finset.disjoint_left.1 hST hqS hrT).elim
  · exact (Set.disjoint_left.1 (boxScaleRegion_disjoint_of_ne α hqr) hzq hzr).elim

/-- The expanded local form is additive over a finite disjoint union whenever
the outer signed integrand is integrable on the union. -/
theorem scratch_expandedModelLocalForm_union_of_integrable
    (α : Anisotropy) (S T : BoxCollection α) (u : E3) (c : ℝ → ℝ)
    (f : ModelRealInput) (hST : Disjoint S T)
    (hint : Integrable (fun pt : E3 × ℝ ↦
      c pt.2 * (∫ z : ModelE5,
        modelFirstFiber α f pt.1 pt.2 z *
          modelSecondFiber α (f 3) pt.1 pt.2 z *
            modelSignedDensity α u pt.1 pt.2 z))
      (cubeScaleMeasure.restrict (collectionRegion α (S ∪ T)))) :
    expandedModelLocalForm α (S ∪ T) u c f =
      expandedModelLocalForm α S u c f +
        expandedModelLocalForm α T u c f := by
  let g : E3 × ℝ → ℝ := fun pt ↦
    c pt.2 * (∫ z : ModelE5,
      modelFirstFiber α f pt.1 pt.2 z *
        modelSecondFiber α (f 3) pt.1 pt.2 z *
          modelSignedDensity α u pt.1 pt.2 z)
  have hregion : collectionRegion α (S ∪ T) =
      collectionRegion α S ∪ collectionRegion α T :=
    scratch_collectionRegion_union α S T
  have hdisj : Disjoint (collectionRegion α S) (collectionRegion α T) :=
    scratch_disjoint_collectionRegion_of_disjoint α S T hST
  have hSint : Integrable g
      (cubeScaleMeasure.restrict (collectionRegion α S)) := by
    apply hint.mono_measure
    rw [hregion]
    exact Measure.restrict_mono (Set.subset_union_left) le_rfl
  have hTint : Integrable g
      (cubeScaleMeasure.restrict (collectionRegion α T)) := by
    apply hint.mono_measure
    rw [hregion]
    exact Measure.restrict_mono (Set.subset_union_right) le_rfl
  unfold expandedModelLocalForm
  change -(∫ pt, g pt ∂(cubeScaleMeasure.restrict
      (collectionRegion α (S ∪ T)))) =
    -(∫ pt, g pt ∂(cubeScaleMeasure.restrict (collectionRegion α S))) +
      -(∫ pt, g pt ∂(cubeScaleMeasure.restrict (collectionRegion α T)))
  rw [hregion, setIntegral_union hdisj
    (measurableSet_collectionRegion α T) hSint hTint]
  ring

/-- The expanded local form is the finite sum of its literal one-box forms
under the matching outer integrability hypothesis. -/
theorem scratch_expandedModelLocalForm_collection_eq_sum_singletons_of_integrable
    (α : Anisotropy) (S : BoxCollection α) (u : E3) (c : ℝ → ℝ)
    (f : ModelRealInput)
    (hint : Integrable (fun pt : E3 × ℝ ↦
      c pt.2 * (∫ z : ModelE5,
        modelFirstFiber α f pt.1 pt.2 z *
          modelSecondFiber α (f 3) pt.1 pt.2 z *
            modelSignedDensity α u pt.1 pt.2 z))
      (cubeScaleMeasure.restrict (collectionRegion α S))) :
    expandedModelLocalForm α S u c f =
      ∑ q ∈ S, expandedModelLocalForm α ({q} : BoxCollection α) u c f := by
  unfold expandedModelLocalForm
  simp_rw [collectionRegion_singleton]
  unfold collectionRegion
  rw [Finset.sum_neg_distrib]
  congr 1
  apply MeasureTheory.integral_biUnion_finset
  · intro q hq
    exact measurableSet_boxScaleRegion α q
  · exact pairwiseDisjoint_boxScaleRegion α S
  · intro q hq
    have hsub : boxScaleRegion α q ⊆ collectionRegion α S := by
      intro pt hpt
      unfold collectionRegion
      exact Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hq, hpt⟩⟩
    apply hint.mono_measure
    exact Measure.restrict_mono hsub le_rfl

/-- The first local energy is a finite sum of one-box energies whenever its
outer energy density is integrable over the collection. -/
theorem scratch_modelEnergyOne_collection_eq_sum_singletons_of_integrable
    (α : Anisotropy) (S : BoxCollection α) (u : E3) (f : ModelRealInput)
    (hint : Integrable (fun pt : E3 × ℝ ↦
      ∫ z : ModelE5,
        (modelFirstFiber α f pt.1 pt.2 z) ^ 2 *
          modelEnergyDensity α u pt.1 pt.2 z)
      (cubeScaleMeasure.restrict (collectionRegion α S))) :
    modelEnergyOne α S u f =
      ∑ q ∈ S, modelEnergyOne α ({q} : BoxCollection α) u f := by
  unfold modelEnergyOne
  simp_rw [collectionRegion_singleton]
  unfold collectionRegion
  apply MeasureTheory.integral_biUnion_finset
  · intro q hq
    exact measurableSet_boxScaleRegion α q
  · exact pairwiseDisjoint_boxScaleRegion α S
  · intro q hq
    have hsub : boxScaleRegion α q ⊆ collectionRegion α S := by
      intro pt hpt
      unfold collectionRegion
      exact Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hq, hpt⟩⟩
    apply hint.mono_measure
    exact Measure.restrict_mono hsub le_rfl

/-- The second local energy is a finite sum of one-box energies whenever its
outer energy density is integrable over the collection. -/
theorem scratch_modelEnergyTwo_collection_eq_sum_singletons_of_integrable
    (α : Anisotropy) (S : BoxCollection α) (u : E3) (f : E3 → ℝ)
    (hint : Integrable (fun pt : E3 × ℝ ↦
      ∫ z : ModelE5,
        (modelSecondFiber α f pt.1 pt.2 z) ^ 2 *
          modelEnergyDensity α u pt.1 pt.2 z)
      (cubeScaleMeasure.restrict (collectionRegion α S))) :
    modelEnergyTwo α S u f =
      ∑ q ∈ S, modelEnergyTwo α ({q} : BoxCollection α) u f := by
  unfold modelEnergyTwo modelEnergyTwoOn
  simp_rw [collectionRegion_singleton]
  unfold collectionRegion
  apply MeasureTheory.integral_biUnion_finset
  · intro q hq
    exact measurableSet_boxScaleRegion α q
  · exact pairwiseDisjoint_boxScaleRegion α S
  · intro q hq
    have hsub : boxScaleRegion α q ⊆ collectionRegion α S := by
      intro pt hpt
      unfold collectionRegion
      exact Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hq, hpt⟩⟩
    apply hint.mono_measure
    exact Measure.restrict_mono hsub le_rfl

/-- Exact finite-forest additivity for the expanded local form.  The proof
uses only the literal disjoint partition of boxes, so it applies directly to
the stopping trees at a fixed level. -/
theorem scratch_expandedModelLocalForm_biUnion_eq_sum_of_integrable
    {ι : Type*} (α : Anisotropy) (I : Finset ι)
    (A : ι → BoxCollection α) (u : E3) (c : ℝ → ℝ) (f : ModelRealInput)
    (hdisj : (↑I : Set ι).PairwiseDisjoint A)
    (hint : Integrable (fun pt : E3 × ℝ ↦
      c pt.2 * (∫ z : ModelE5,
        modelFirstFiber α f pt.1 pt.2 z *
          modelSecondFiber α (f 3) pt.1 pt.2 z *
            modelSignedDensity α u pt.1 pt.2 z))
      (cubeScaleMeasure.restrict (collectionRegion α (I.biUnion A)))) :
    expandedModelLocalForm α (I.biUnion A) u c f =
      ∑ i ∈ I, expandedModelLocalForm α (A i) u c f := by
  classical
  calc
    expandedModelLocalForm α (I.biUnion A) u c f =
        ∑ q ∈ I.biUnion A,
          expandedModelLocalForm α ({q} : BoxCollection α) u c f :=
      scratch_expandedModelLocalForm_collection_eq_sum_singletons_of_integrable
        α (I.biUnion A) u c f hint
    _ = ∑ i ∈ I, ∑ q ∈ A i,
          expandedModelLocalForm α ({q} : BoxCollection α) u c f :=
      Finset.sum_biUnion hdisj
    _ = ∑ i ∈ I, expandedModelLocalForm α (A i) u c f := by
      apply Finset.sum_congr rfl
      intro i hi
      symm
      apply scratch_expandedModelLocalForm_collection_eq_sum_singletons_of_integrable
      have hsub : collectionRegion α (A i) ⊆
          collectionRegion α (I.biUnion A) := by
        intro pt hpt
        rw [collectionRegion] at hpt ⊢
        rcases Set.mem_iUnion.1 hpt with ⟨q, hpt⟩
        rcases Set.mem_iUnion.1 hpt with ⟨hq, hpt⟩
        refine Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨?_, hpt⟩⟩
        exact Finset.mem_biUnion.mpr ⟨i, hi, hq⟩
      apply hint.mono_measure
      exact Measure.restrict_mono hsub le_rfl

/-- The first local energy has the same finite-forest additivity. -/
theorem scratch_modelEnergyOne_biUnion_eq_sum_of_integrable
    {ι : Type*} (α : Anisotropy) (I : Finset ι)
    (A : ι → BoxCollection α) (u : E3) (f : ModelRealInput)
    (hdisj : (↑I : Set ι).PairwiseDisjoint A)
    (hint : Integrable (fun pt : E3 × ℝ ↦
      ∫ z : ModelE5,
        (modelFirstFiber α f pt.1 pt.2 z) ^ 2 *
          modelEnergyDensity α u pt.1 pt.2 z)
      (cubeScaleMeasure.restrict (collectionRegion α (I.biUnion A)))) :
    modelEnergyOne α (I.biUnion A) u f =
      ∑ i ∈ I, modelEnergyOne α (A i) u f := by
  classical
  calc
    modelEnergyOne α (I.biUnion A) u f =
        ∑ q ∈ I.biUnion A, modelEnergyOne α ({q} : BoxCollection α) u f :=
      scratch_modelEnergyOne_collection_eq_sum_singletons_of_integrable
        α (I.biUnion A) u f hint
    _ = ∑ i ∈ I, ∑ q ∈ A i,
          modelEnergyOne α ({q} : BoxCollection α) u f :=
      Finset.sum_biUnion hdisj
    _ = ∑ i ∈ I, modelEnergyOne α (A i) u f := by
      apply Finset.sum_congr rfl
      intro i hi
      symm
      apply scratch_modelEnergyOne_collection_eq_sum_singletons_of_integrable
      have hsub : collectionRegion α (A i) ⊆
          collectionRegion α (I.biUnion A) := by
        intro pt hpt
        rw [collectionRegion] at hpt ⊢
        rcases Set.mem_iUnion.1 hpt with ⟨q, hpt⟩
        rcases Set.mem_iUnion.1 hpt with ⟨hq, hpt⟩
        refine Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨?_, hpt⟩⟩
        exact Finset.mem_biUnion.mpr ⟨i, hi, hq⟩
      apply hint.mono_measure
      exact Measure.restrict_mono hsub le_rfl

/-- The second local energy has the corresponding finite-forest additivity. -/
theorem scratch_modelEnergyTwo_biUnion_eq_sum_of_integrable
    {ι : Type*} (α : Anisotropy) (I : Finset ι)
    (A : ι → BoxCollection α) (u : E3) (f : E3 → ℝ)
    (hdisj : (↑I : Set ι).PairwiseDisjoint A)
    (hint : Integrable (fun pt : E3 × ℝ ↦
      ∫ z : ModelE5,
        (modelSecondFiber α f pt.1 pt.2 z) ^ 2 *
          modelEnergyDensity α u pt.1 pt.2 z)
      (cubeScaleMeasure.restrict (collectionRegion α (I.biUnion A)))) :
    modelEnergyTwo α (I.biUnion A) u f =
      ∑ i ∈ I, modelEnergyTwo α (A i) u f := by
  classical
  calc
    modelEnergyTwo α (I.biUnion A) u f =
        ∑ q ∈ I.biUnion A, modelEnergyTwo α ({q} : BoxCollection α) u f :=
      scratch_modelEnergyTwo_collection_eq_sum_singletons_of_integrable
        α (I.biUnion A) u f hint
    _ = ∑ i ∈ I, ∑ q ∈ A i,
          modelEnergyTwo α ({q} : BoxCollection α) u f :=
      Finset.sum_biUnion hdisj
    _ = ∑ i ∈ I, modelEnergyTwo α (A i) u f := by
      apply Finset.sum_congr rfl
      intro i hi
      symm
      apply scratch_modelEnergyTwo_collection_eq_sum_singletons_of_integrable
      have hsub : collectionRegion α (A i) ⊆
          collectionRegion α (I.biUnion A) := by
        intro pt hpt
        rw [collectionRegion] at hpt ⊢
        rcases Set.mem_iUnion.1 hpt with ⟨q, hpt⟩
        rcases Set.mem_iUnion.1 hpt with ⟨hq, hpt⟩
        refine Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨?_, hpt⟩⟩
        exact Finset.mem_biUnion.mpr ⟨i, hi, hq⟩
      apply hint.mono_measure
      exact Measure.restrict_mono hsub le_rfl

end Twisted

end

end Auto
