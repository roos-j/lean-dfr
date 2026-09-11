/- Copyright 2026 Joris Roos
License: Apache-2.0
This file is scratch work for the finite active stopping-forest form estimate.
-/

import Auto.Twisted.Twisted

namespace Auto.Twisted

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal RealInnerProductSpace

noncomputable section

/-- The stopping exponents `(4,4,4,2)` give exactly the local-size product
appearing in the local model estimate. -/
theorem scratch_sourceStopping_treeLocalSize_product
    (α : Anisotropy) (T : FiniteConvexTree α) (f : ModelRealInput) :
    (∏ j : Fin 4, treeLocalSize T (sourceStoppingExponent j) (f j)) =
      (treeLocalSize T 4 (f 0) * treeLocalSize T 4 (f 1) *
        treeLocalSize T 4 (f 2)) * treeLocalSize T 2 (f 3) := by
  simp [Fin.prod_univ_succ, sourceStoppingExponent]
  ring

/-- A single source stopping tree satisfies the local-model bound in exactly
the weighted form summed by the stopping-forest estimate. -/
theorem scratch_stoppingTree_localModel_bound_of_energyBounds
    (α : Anisotropy) (S : BoxCollection α) (hS : IsConvexCollection α S)
    (u : E3) (c : ℝ → ℝ) (f : ModelRealInput) (C₁ C₂ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (n : Fin 4 → ℤ)
    (Q : {Q : AnisoBox α // Q ∈ stoppingRoots α S sourceStoppingExponent f n})
    (hcs : |expandedModelLocalForm α
      (stoppingTree α S sourceStoppingExponent f n
        (isConvexCollection_stoppingLevel α S hS sourceStoppingExponent f n)
        Q.1 Q.2).boxes u c f| ^ 2 ≤
      modelEnergyOne α
        (stoppingTree α S sourceStoppingExponent f n
          (isConvexCollection_stoppingLevel α S hS sourceStoppingExponent f n)
          Q.1 Q.2).boxes u f *
        modelEnergyTwo α
          (stoppingTree α S sourceStoppingExponent f n
            (isConvexCollection_stoppingLevel α S hS sourceStoppingExponent f n)
            Q.1 Q.2).boxes u (f 3))
    (hE₁ : modelEnergyOne α
      (stoppingTree α S sourceStoppingExponent f n
        (isConvexCollection_stoppingLevel α S hS sourceStoppingExponent f n)
        Q.1 Q.2).boxes u f ≤
      C₁ * sourceWeight u ^ 50 *
        boxMass α
          (stoppingTree α S sourceStoppingExponent f n
            (isConvexCollection_stoppingLevel α S hS sourceStoppingExponent f n)
            Q.1 Q.2).root *
        (treeLocalSize
            (stoppingTree α S sourceStoppingExponent f n
              (isConvexCollection_stoppingLevel α S hS sourceStoppingExponent f n)
              Q.1 Q.2)
            4 (f 0) *
          treeLocalSize
            (stoppingTree α S sourceStoppingExponent f n
              (isConvexCollection_stoppingLevel α S hS sourceStoppingExponent f n)
              Q.1 Q.2)
            4 (f 1) *
          treeLocalSize
            (stoppingTree α S sourceStoppingExponent f n
              (isConvexCollection_stoppingLevel α S hS sourceStoppingExponent f n)
              Q.1 Q.2)
            4 (f 2)) ^ 2)
    (hE₂ : modelEnergyTwo α
      (stoppingTree α S sourceStoppingExponent f n
        (isConvexCollection_stoppingLevel α S hS sourceStoppingExponent f n)
        Q.1 Q.2).boxes u (f 3) ≤
      C₂ * sourceWeight u ^ 100 *
        boxMass α
          (stoppingTree α S sourceStoppingExponent f n
            (isConvexCollection_stoppingLevel α S hS sourceStoppingExponent f n)
            Q.1 Q.2).root *
        treeLocalSize
          (stoppingTree α S sourceStoppingExponent f n
            (isConvexCollection_stoppingLevel α S hS sourceStoppingExponent f n)
            Q.1 Q.2)
          2 (f 3) ^ 2) :
    |expandedModelLocalForm α
        (stoppingTreeBoxes α S sourceStoppingExponent f n Q.1) u c f| ≤
      (C₁ * C₂ + 1) * sourceWeight u ^ 75 * boxMass α Q.1 *
        (∏ j : Fin 4,
          treeLocalSize
            (stoppingTree α S sourceStoppingExponent f n
              (isConvexCollection_stoppingLevel α S hS sourceStoppingExponent f n)
              Q.1 Q.2)
            (sourceStoppingExponent j) (f j)) := by
  let T := stoppingTree α S sourceStoppingExponent f n
    (isConvexCollection_stoppingLevel α S hS sourceStoppingExponent f n)
    Q.1 Q.2
  have hmain := localModelEstimate_of_energyBounds α T u c f C₁ C₂ hC₁ hC₂
    hcs hE₁ hE₂
  calc
    |expandedModelLocalForm α
        (stoppingTreeBoxes α S sourceStoppingExponent f n Q.1) u c f| =
        |expandedModelLocalForm α T.boxes u c f| := by
      rw [stoppingTree_boxes]
    _ ≤ (C₁ * C₂ + 1) * sourceWeight u ^ 75 * boxMass α T.root *
        (treeLocalSize T 4 (f 0) * treeLocalSize T 4 (f 1) *
          treeLocalSize T 4 (f 2)) * treeLocalSize T 2 (f 3) := hmain
    _ = (C₁ * C₂ + 1) * sourceWeight u ^ 75 * boxMass α Q.1 *
        (∏ j : Fin 4, treeLocalSize T (sourceStoppingExponent j) (f j)) := by
      rw [stoppingTree_root]
      calc
        (C₁ * C₂ + 1) * sourceWeight u ^ 75 * boxMass α Q.1 *
              (treeLocalSize T 4 (f 0) * treeLocalSize T 4 (f 1) *
                treeLocalSize T 4 (f 2)) * treeLocalSize T 2 (f 3) =
            (C₁ * C₂ + 1) * sourceWeight u ^ 75 * boxMass α Q.1 *
              ((treeLocalSize T 4 (f 0) * treeLocalSize T 4 (f 1) *
                treeLocalSize T 4 (f 2)) * treeLocalSize T 2 (f 3)) := by ring
        _ = _ := by
          rw [← scratch_sourceStopping_treeLocalSize_product α T f]

/-- The finite active stopping forest converts uniform stopping-tree local
form bounds into the four-coordinate envelope sum.  The exact forest form
decomposition is kept as an explicit hypothesis, since it is the point at
which the outer model Fubini package is consumed. -/
theorem scratch_activeStoppingForest_form_bound_of_localBounds
    (α : Anisotropy) (S : BoxCollection α) (hS : IsConvexCollection α S)
    (u : E3) (c : ℝ → ℝ) (f : ModelRealInput)
    (q σ : Fin 4 → ℝ) (hq : ∀ j, 0 < q j)
    (hpos : ∀ q ∈ S, ∀ j,
      0 < stoppingData α S (sourceStoppingExponent j) (f j) q)
    (hcont : ∀ j, Continuous (f j))
    (hbound : ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ y, |f j y| ≤ B)
    (hfinite : ∀ n,
      volume (sourceStoppingDominantMaximalLevelSet α f q σ n) ≠ ∞)
    (C : ℝ) (hC : 0 ≤ C)
    (hdecomp :
      expandedModelLocalForm α S u c f =
        ∑ n ∈ activeStoppingLevels α S sourceStoppingExponent f hpos,
          ∑ Q ∈ (stoppingRoots α S sourceStoppingExponent f n).attach,
            expandedModelLocalForm α
              (stoppingTreeBoxes α S sourceStoppingExponent f n Q.1) u c f)
    (hlocal : ∀ (n : Fin 4 → ℤ)
      (Q : {Q : AnisoBox α // Q ∈ stoppingRoots α S sourceStoppingExponent f n}),
      |expandedModelLocalForm α
          (stoppingTreeBoxes α S sourceStoppingExponent f n Q.1) u c f| ≤
        C * sourceWeight u ^ 75 * boxMass α Q.1 *
          (∏ j : Fin 4,
            treeLocalSize
              (stoppingTree α S sourceStoppingExponent f n
                (isConvexCollection_stoppingLevel α S hS
                  sourceStoppingExponent f n) Q.1 Q.2)
              (sourceStoppingExponent j) (f j))) :
    |expandedModelLocalForm α S u c f| ≤
      C * sourceWeight u ^ 75 *
        (∑ j : Fin 4,
          ∑ m ∈ (activeStoppingLevels α S sourceStoppingExponent f hpos).filter
              (fun n ↦ sourceStoppingDominantIndex q σ n = j) |>.image
                (fun n ↦ n j),
            sourceStoppingDominantFiberEnvelope q σ j m *
              (volume (sourceStoppingMaximalLevelSetAt α f j m)).toReal) := by
  let L := activeStoppingLevels α S sourceStoppingExponent f hpos
  let W : ℝ := ∑ n ∈ L,
    ∑ Q ∈ (stoppingRoots α S sourceStoppingExponent f n).attach,
      boxMass α Q.1 *
        (∏ j : Fin 4,
          treeLocalSize
            (stoppingTree α S sourceStoppingExponent f n
              (isConvexCollection_stoppingLevel α S hS
                sourceStoppingExponent f n) Q.1 Q.2)
            (sourceStoppingExponent j) (f j))
  let E : ℝ := ∑ j : Fin 4,
    ∑ m ∈ L.filter (fun n ↦ sourceStoppingDominantIndex q σ n = j) |>.image
        (fun n ↦ n j),
      sourceStoppingDominantFiberEnvelope q σ j m *
        (volume (sourceStoppingMaximalLevelSetAt α f j m)).toReal
  have hW : W ≤ E := by
    dsimp only [W, E, L]
    exact sourceStoppingForestWeightedSum_le_coordinateEnvelopeSums
      α S hS f q σ hq hpos hcont hbound hfinite
  have hU : 0 ≤ sourceWeight u := sourceWeight_nonneg u
  have hfac : 0 ≤ C * sourceWeight u ^ 75 := by positivity
  have hsum :
      (∑ n ∈ L,
        ∑ Q ∈ (stoppingRoots α S sourceStoppingExponent f n).attach,
          |expandedModelLocalForm α
            (stoppingTreeBoxes α S sourceStoppingExponent f n Q.1) u c f|) ≤
        C * sourceWeight u ^ 75 * W := by
    calc
      (∑ n ∈ L,
        ∑ Q ∈ (stoppingRoots α S sourceStoppingExponent f n).attach,
          |expandedModelLocalForm α
            (stoppingTreeBoxes α S sourceStoppingExponent f n Q.1) u c f|) ≤
          ∑ n ∈ L,
            ∑ Q ∈ (stoppingRoots α S sourceStoppingExponent f n).attach,
              C * sourceWeight u ^ 75 * boxMass α Q.1 *
                (∏ j : Fin 4,
                  treeLocalSize
                    (stoppingTree α S sourceStoppingExponent f n
                      (isConvexCollection_stoppingLevel α S hS
                        sourceStoppingExponent f n) Q.1 Q.2)
                    (sourceStoppingExponent j) (f j)) := by
        apply Finset.sum_le_sum
        intro n hn
        apply Finset.sum_le_sum
        intro Q hQ
        exact hlocal n Q
      _ = C * sourceWeight u ^ 75 * W := by
        dsimp only [W]
        calc
          (∑ n ∈ L,
            ∑ Q ∈ (stoppingRoots α S sourceStoppingExponent f n).attach,
              C * sourceWeight u ^ 75 * boxMass α Q.1 *
                (∏ j : Fin 4,
                  treeLocalSize
                    (stoppingTree α S sourceStoppingExponent f n
                      (isConvexCollection_stoppingLevel α S hS
                        sourceStoppingExponent f n) Q.1 Q.2)
                    (sourceStoppingExponent j) (f j))) =
              ∑ n ∈ L,
                (C * sourceWeight u ^ 75) *
                  (∑ Q ∈ (stoppingRoots α S sourceStoppingExponent f n).attach,
                    boxMass α Q.1 *
                      (∏ j : Fin 4,
                        treeLocalSize
                          (stoppingTree α S sourceStoppingExponent f n
                            (isConvexCollection_stoppingLevel α S hS
                              sourceStoppingExponent f n) Q.1 Q.2)
                          (sourceStoppingExponent j) (f j))) := by
                apply Finset.sum_congr rfl
                intro n hn
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro Q hQ
                ring
          _ = C * sourceWeight u ^ 75 *
              (∑ n ∈ L,
                ∑ Q ∈ (stoppingRoots α S sourceStoppingExponent f n).attach,
                  boxMass α Q.1 *
                    (∏ j : Fin 4,
                      treeLocalSize
                        (stoppingTree α S sourceStoppingExponent f n
                          (isConvexCollection_stoppingLevel α S hS
                            sourceStoppingExponent f n) Q.1 Q.2)
                        (sourceStoppingExponent j) (f j))) := by
            rw [Finset.mul_sum]
  calc
    |expandedModelLocalForm α S u c f| =
        |∑ n ∈ L,
          ∑ Q ∈ (stoppingRoots α S sourceStoppingExponent f n).attach,
            expandedModelLocalForm α
              (stoppingTreeBoxes α S sourceStoppingExponent f n Q.1) u c f| := by
      rw [hdecomp]
    _ ≤ ∑ n ∈ L,
        |∑ Q ∈ (stoppingRoots α S sourceStoppingExponent f n).attach,
          expandedModelLocalForm α
            (stoppingTreeBoxes α S sourceStoppingExponent f n Q.1) u c f| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ L,
        ∑ Q ∈ (stoppingRoots α S sourceStoppingExponent f n).attach,
          |expandedModelLocalForm α
            (stoppingTreeBoxes α S sourceStoppingExponent f n Q.1) u c f| := by
      apply Finset.sum_le_sum
      intro n hn
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ C * sourceWeight u ^ 75 * W := hsum
    _ ≤ C * sourceWeight u ^ 75 * E :=
      mul_le_mul_of_nonneg_left hW hfac
    _ = C * sourceWeight u ^ 75 *
        (∑ j : Fin 4,
          ∑ m ∈ (activeStoppingLevels α S sourceStoppingExponent f hpos).filter
              (fun n ↦ sourceStoppingDominantIndex q σ n = j) |>.image
                (fun n ↦ n j),
            sourceStoppingDominantFiberEnvelope q σ j m *
              (volume (sourceStoppingMaximalLevelSetAt α f j m)).toReal) := by
      rfl

/-- The literal stopping tree attached to a source active root.  Naming it
makes the energy hypotheses in the terminal forest wrapper compact. -/
noncomputable def scratch_sourceStoppingTree
    (α : Anisotropy) (S : BoxCollection α) (hS : IsConvexCollection α S)
    (f : ModelRealInput) (n : Fin 4 → ℤ)
    (Q : {Q : AnisoBox α // Q ∈ stoppingRoots α S sourceStoppingExponent f n}) :
    FiniteConvexTree α :=
  stoppingTree α S sourceStoppingExponent f n
    (isConvexCollection_stoppingLevel α S hS sourceStoppingExponent f n)
    Q.1 Q.2

/-- The local Cauchy--Schwarz input on every tree of the source stopping
forest. -/
def scratch_sourceStoppingTreeCS
    (α : Anisotropy) (S : BoxCollection α) (hS : IsConvexCollection α S)
    (u : E3) (c : ℝ → ℝ) (f : ModelRealInput) : Prop :=
  ∀ (n : Fin 4 → ℤ)
    (Q : {Q : AnisoBox α // Q ∈ stoppingRoots α S sourceStoppingExponent f n}),
    |expandedModelLocalForm α (scratch_sourceStoppingTree α S hS f n Q).boxes u c f| ^ 2 ≤
      modelEnergyOne α (scratch_sourceStoppingTree α S hS f n Q).boxes u f *
        modelEnergyTwo α (scratch_sourceStoppingTree α S hS f n Q).boxes u (f 3)

/-- The first tree-energy conclusion, uniform over source stopping roots. -/
def scratch_sourceStoppingTreeEnergyOneBound
    (α : Anisotropy) (S : BoxCollection α) (hS : IsConvexCollection α S)
    (u : E3) (f : ModelRealInput) (C₁ : ℝ) : Prop :=
  ∀ (n : Fin 4 → ℤ)
    (Q : {Q : AnisoBox α // Q ∈ stoppingRoots α S sourceStoppingExponent f n}),
    modelEnergyOne α (scratch_sourceStoppingTree α S hS f n Q).boxes u f ≤
      C₁ * sourceWeight u ^ 50 *
        boxMass α (scratch_sourceStoppingTree α S hS f n Q).root *
        (treeLocalSize (scratch_sourceStoppingTree α S hS f n Q) 4 (f 0) *
          treeLocalSize (scratch_sourceStoppingTree α S hS f n Q) 4 (f 1) *
          treeLocalSize (scratch_sourceStoppingTree α S hS f n Q) 4 (f 2)) ^ 2

/-- The second tree-energy conclusion, uniform over source stopping roots. -/
def scratch_sourceStoppingTreeEnergyTwoBound
    (α : Anisotropy) (S : BoxCollection α) (hS : IsConvexCollection α S)
    (u : E3) (f : ModelRealInput) (C₂ : ℝ) : Prop :=
  ∀ (n : Fin 4 → ℤ)
    (Q : {Q : AnisoBox α // Q ∈ stoppingRoots α S sourceStoppingExponent f n}),
    modelEnergyTwo α (scratch_sourceStoppingTree α S hS f n Q).boxes u (f 3) ≤
      C₂ * sourceWeight u ^ 100 *
        boxMass α (scratch_sourceStoppingTree α S hS f n Q).root *
        treeLocalSize (scratch_sourceStoppingTree α S hS f n Q) 2 (f 3) ^ 2

/-- The exact four integrability obligations which instantiate the two
bounded-continuous tree-energy estimates on every source stopping tree. -/
def scratch_sourceStoppingTreeEnergyIntegrability
    (α : Anisotropy) (S : BoxCollection α) (hS : IsConvexCollection α S)
    (u : E3) (f : ModelRealInput) : Prop :=
  ∀ (n : Fin 4 → ℤ)
    (Q : {Q : AnisoBox α // Q ∈ stoppingRoots α S sourceStoppingExponent f n}),
    Integrable (modelFirstSuperpositionJoint α u f)
      ((cubeScaleMeasure.restrict
        (collectionRegion α (scratch_sourceStoppingTree α S hS f n Q).boxes)).prod
        ((volume : Measure ModelE5).prod
          ((volume : Measure ℝ).restrict (Set.Ici (1 : ℝ)))) ) ∧
    IntegrableOn (fun lam : ℝ ↦
      localCubeForm α (scratch_sourceStoppingTree α S hS f n Q).boxes 2 lam 0
        (modelFirstCubeTuple f) * lam ^ (-47 : ℝ)) (Set.Ici (1 : ℝ)) ∧
    Integrable (modelSecondSuperpositionJoint α (f 3))
      ((cubeScaleMeasure.restrict
        (collectionRegion α (scratch_sourceStoppingTree α S hS f n Q).boxes)).prod
        ((volume : Measure ModelE5).prod
          ((volume : Measure ℝ).restrict (Set.Ici (1 : ℝ)))) ) ∧
    Integrable (fun z : ℝ × ℝ ↦
      localCubeForm α (scratch_sourceStoppingTree α S hS f n Q).boxes 2 z.1 z.2
        (edgeCubeTuple (f 3)) * translationWeight z.2 ^ (-50 : ℝ) *
          z.1 ^ (-47 : ℝ))
      (((volume : Measure ℝ).restrict (Set.Ici (1 : ℝ))).prod volume)

/-- The checked tree-energy package specializes uniformly to every root of
the active source stopping forest once its four explicit integrability
conditions are provided. -/
theorem scratch_sourceStoppingTree_energyBounds_of_boundedContinuous
    (α : Anisotropy) (S : BoxCollection α) (hS : IsConvexCollection α S)
    (u : E3) (f : ModelRealInput)
    (hcont : ∀ j, Continuous (f j))
    (hbound : ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ y, |f j y| ≤ B)
    (hint : scratch_sourceStoppingTreeEnergyIntegrability α S hS u f) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      scratch_sourceStoppingTreeEnergyOneBound α S hS u f C₁ ∧
      scratch_sourceStoppingTreeEnergyTwoBound α S hS u f C₂ := by
  rcases modelEnergyOne_tree_bound_of_boundedContinuous α with ⟨C₁, hC₁, hE₁⟩
  rcases modelEnergyTwo_tree_bound_of_boundedContinuous α with ⟨C₂, hC₂, hE₂⟩
  refine ⟨C₁, C₂, hC₁, hC₂, ?_, ?_⟩
  · intro n Q
    rcases hint n Q with ⟨hfirst, hscale, hsecond, hjoint⟩
    exact hE₁ (scratch_sourceStoppingTree α S hS f n Q) u f false
      hcont hbound hfirst hscale
  · intro n Q
    rcases hint n Q with ⟨hfirst, hscale, hsecond, hjoint⟩
    exact hE₂ (scratch_sourceStoppingTree α S hS f n Q) u (f 3) false
      (hcont 3) (hbound 3) hsecond hjoint

/-- The Section 5 finite active stopping-forest form estimate.  The only
remaining analytic input is the exact outer form decomposition and the three
treewise hypotheses; the scalar stopping sum is discharged by the checked
coordinate-envelope theorem. -/
theorem scratch_activeStoppingForest_form_bound_of_energyBounds
    (α : Anisotropy) (S : BoxCollection α) (hS : IsConvexCollection α S)
    (u : E3) (c : ℝ → ℝ) (f : ModelRealInput)
    (q σ : Fin 4 → ℝ) (hq : ∀ j, 0 < q j)
    (hpos : ∀ q ∈ S, ∀ j,
      0 < stoppingData α S (sourceStoppingExponent j) (f j) q)
    (hcont : ∀ j, Continuous (f j))
    (hbound : ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ y, |f j y| ≤ B)
    (hfinite : ∀ n,
      volume (sourceStoppingDominantMaximalLevelSet α f q σ n) ≠ ∞)
    (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hdecomp :
      expandedModelLocalForm α S u c f =
        ∑ n ∈ activeStoppingLevels α S sourceStoppingExponent f hpos,
          ∑ Q ∈ (stoppingRoots α S sourceStoppingExponent f n).attach,
            expandedModelLocalForm α
              (stoppingTreeBoxes α S sourceStoppingExponent f n Q.1) u c f)
    (hcs : scratch_sourceStoppingTreeCS α S hS u c f)
    (hE₁ : scratch_sourceStoppingTreeEnergyOneBound α S hS u f C₁)
    (hE₂ : scratch_sourceStoppingTreeEnergyTwoBound α S hS u f C₂) :
    |expandedModelLocalForm α S u c f| ≤
      (C₁ * C₂ + 1) * sourceWeight u ^ 75 *
        (∑ j : Fin 4,
          ∑ m ∈ (activeStoppingLevels α S sourceStoppingExponent f hpos).filter
              (fun n ↦ sourceStoppingDominantIndex q σ n = j) |>.image
                (fun n ↦ n j),
            sourceStoppingDominantFiberEnvelope q σ j m *
              (volume (sourceStoppingMaximalLevelSetAt α f j m)).toReal) := by
  apply scratch_activeStoppingForest_form_bound_of_localBounds
    α S hS u c f q σ hq hpos hcont hbound hfinite (C₁ * C₂ + 1)
  · exact add_nonneg (mul_nonneg hC₁ hC₂) zero_le_one
  · exact hdecomp
  intro n Q
  apply scratch_stoppingTree_localModel_bound_of_energyBounds
    α S hS u c f C₁ C₂ hC₁ hC₂ n Q
  · simpa only [scratch_sourceStoppingTree] using hcs n Q
  · simpa only [scratch_sourceStoppingTree] using hE₁ n Q
  · simpa only [scratch_sourceStoppingTree] using hE₂ n Q

/-- The exact active-forest form decomposition obtained from a single outer
integrability hypothesis.  This discharges the decomposition premise of the
terminal forest estimate without any rearrangement of conditionally
integrable terms. -/
theorem scratch_expandedModelLocalForm_activeStoppingForest_eq_sum_of_integrable
    (α : Anisotropy) (S : BoxCollection α) (u : E3) (c : ℝ → ℝ)
    (f : ModelRealInput)
    (hpos : ∀ q ∈ S, ∀ j,
      0 < stoppingData α S (sourceStoppingExponent j) (f j) q)
    (hint : Integrable (fun pt : E3 × ℝ ↦
      c pt.2 * (∫ z : ModelE5,
        modelFirstFiber α f pt.1 pt.2 z *
          modelSecondFiber α (f 3) pt.1 pt.2 z *
            modelSignedDensity α u pt.1 pt.2 z))
      (cubeScaleMeasure.restrict (collectionRegion α S))) :
    expandedModelLocalForm α S u c f =
      ∑ n ∈ activeStoppingLevels α S sourceStoppingExponent f hpos,
        ∑ Q ∈ (stoppingRoots α S sourceStoppingExponent f n).attach,
          expandedModelLocalForm α
            (stoppingTreeBoxes α S sourceStoppingExponent f n Q.1) u c f := by
  classical
  let I := activeStoppingForestRoots α S sourceStoppingExponent f hpos
  let A : (Sigma fun _ : Fin 4 → ℤ ↦ AnisoBox α) → BoxCollection α :=
    fun z ↦ stoppingTreeBoxes α S sourceStoppingExponent f z.1 z.2
  have hpartition : S = I.biUnion A := by
    dsimp only [I, A]
    exact boxCollection_eq_biUnion_activeStoppingForestTreeBoxes
      α S sourceStoppingExponent f hpos
  have hint' : Integrable (fun pt : E3 × ℝ ↦
      c pt.2 * (∫ z : ModelE5,
        modelFirstFiber α f pt.1 pt.2 z *
          modelSecondFiber α (f 3) pt.1 pt.2 z *
            modelSignedDensity α u pt.1 pt.2 z))
      (cubeScaleMeasure.restrict (collectionRegion α (I.biUnion A))) := by
    rw [← hpartition]
    exact hint
  have hsum := expandedModelLocalForm_biUnion_eq_sum_of_integrable
    α I A u c f
    (by
      dsimp only [I, A]
      exact pairwiseDisjoint_activeStoppingForestTreeBoxes
        α S sourceStoppingExponent f hpos)
    hint'
  calc
    expandedModelLocalForm α S u c f =
        expandedModelLocalForm α (I.biUnion A) u c f := by rw [← hpartition]
    _ = ∑ z ∈ I, expandedModelLocalForm α (A z) u c f := hsum
    _ = ∑ n ∈ activeStoppingLevels α S sourceStoppingExponent f hpos,
        ∑ Q ∈ (stoppingRoots α S sourceStoppingExponent f n).attach,
          expandedModelLocalForm α
            (stoppingTreeBoxes α S sourceStoppingExponent f n Q.1) u c f := by
      simp only [I, A, activeStoppingForestRoots, Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro n hn
      symm
      exact Finset.sum_attach (stoppingRoots α S sourceStoppingExponent f n)
        (fun Q ↦ expandedModelLocalForm α
          (stoppingTreeBoxes α S sourceStoppingExponent f n Q) u c f)

/-- A ready-to-use finite active stopping-forest bound.  It combines the
outer-integrability decomposition, treewise local-model/energy bounds, and
the source coordinate-envelope stopping estimate. -/
theorem scratch_activeStoppingForest_form_bound_of_energyBounds_of_integrable
    (α : Anisotropy) (S : BoxCollection α) (hS : IsConvexCollection α S)
    (u : E3) (c : ℝ → ℝ) (f : ModelRealInput)
    (q σ : Fin 4 → ℝ) (hq : ∀ j, 0 < q j)
    (hpos : ∀ q ∈ S, ∀ j,
      0 < stoppingData α S (sourceStoppingExponent j) (f j) q)
    (hcont : ∀ j, Continuous (f j))
    (hbound : ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ y, |f j y| ≤ B)
    (hfinite : ∀ n,
      volume (sourceStoppingDominantMaximalLevelSet α f q σ n) ≠ ∞)
    (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hcs : scratch_sourceStoppingTreeCS α S hS u c f)
    (hE₁ : scratch_sourceStoppingTreeEnergyOneBound α S hS u f C₁)
    (hE₂ : scratch_sourceStoppingTreeEnergyTwoBound α S hS u f C₂)
    (hint : Integrable (fun pt : E3 × ℝ ↦
      c pt.2 * (∫ z : ModelE5,
        modelFirstFiber α f pt.1 pt.2 z *
          modelSecondFiber α (f 3) pt.1 pt.2 z *
            modelSignedDensity α u pt.1 pt.2 z))
      (cubeScaleMeasure.restrict (collectionRegion α S))) :
    |expandedModelLocalForm α S u c f| ≤
      (C₁ * C₂ + 1) * sourceWeight u ^ 75 *
        (∑ j : Fin 4,
          ∑ m ∈ (activeStoppingLevels α S sourceStoppingExponent f hpos).filter
              (fun n ↦ sourceStoppingDominantIndex q σ n = j) |>.image
                (fun n ↦ n j),
            sourceStoppingDominantFiberEnvelope q σ j m *
              (volume (sourceStoppingMaximalLevelSetAt α f j m)).toReal) := by
  apply scratch_activeStoppingForest_form_bound_of_energyBounds
    α S hS u c f q σ hq hpos hcont hbound hfinite C₁ C₂ hC₁ hC₂
  · exact scratch_expandedModelLocalForm_activeStoppingForest_eq_sum_of_integrable
      α S u c f hpos hint
  · exact hcs
  · exact hE₁
  · exact hE₂

/-- The fully assembled bounded-continuous Section 5 active-forest estimate.
Its sole remaining analytic assumptions are the explicit treewise energy
integrability package and the outer form integrability needed for finite
Fubini additivity. -/
theorem scratch_activeStoppingForest_form_bound_of_boundedContinuous
    (α : Anisotropy) (S : BoxCollection α) (hS : IsConvexCollection α S)
    (u : E3) (c : ℝ → ℝ) (f : ModelRealInput)
    (q σ : Fin 4 → ℝ) (hq : ∀ j, 0 < q j)
    (hpos : ∀ q ∈ S, ∀ j,
      0 < stoppingData α S (sourceStoppingExponent j) (f j) q)
    (hcont : ∀ j, Continuous (f j))
    (hbound : ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ y, |f j y| ≤ B)
    (hfinite : ∀ n,
      volume (sourceStoppingDominantMaximalLevelSet α f q σ n) ≠ ∞)
    (hcs : scratch_sourceStoppingTreeCS α S hS u c f)
    (henergy : scratch_sourceStoppingTreeEnergyIntegrability α S hS u f)
    (hint : Integrable (fun pt : E3 × ℝ ↦
      c pt.2 * (∫ z : ModelE5,
        modelFirstFiber α f pt.1 pt.2 z *
          modelSecondFiber α (f 3) pt.1 pt.2 z *
            modelSignedDensity α u pt.1 pt.2 z))
      (cubeScaleMeasure.restrict (collectionRegion α S))) :
    ∃ C : ℝ, 0 ≤ C ∧
      |expandedModelLocalForm α S u c f| ≤
        C * sourceWeight u ^ 75 *
          (∑ j : Fin 4,
            ∑ m ∈ (activeStoppingLevels α S sourceStoppingExponent f hpos).filter
                (fun n ↦ sourceStoppingDominantIndex q σ n = j) |>.image
                  (fun n ↦ n j),
              sourceStoppingDominantFiberEnvelope q σ j m *
                (volume (sourceStoppingMaximalLevelSetAt α f j m)).toReal) := by
  rcases scratch_sourceStoppingTree_energyBounds_of_boundedContinuous
    α S hS u f hcont hbound henergy with ⟨C₁, C₂, hC₁, hC₂, hE₁, hE₂⟩
  refine ⟨C₁ * C₂ + 1, add_nonneg (mul_nonneg hC₁ hC₂) zero_le_one, ?_⟩
  exact scratch_activeStoppingForest_form_bound_of_energyBounds_of_integrable
    α S hS u c f q σ hq hpos hcont hbound hfinite C₁ C₂ hC₁ hC₂
    hcs hE₁ hE₂ hint

end

end Auto.Twisted
