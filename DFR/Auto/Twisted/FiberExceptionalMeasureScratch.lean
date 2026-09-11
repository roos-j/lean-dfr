/- Copyright (c) 2026. All rights reserved.
   SPDX-License-Identifier: Apache-2.0 -/

import Auto.Twisted.Twisted

namespace Auto
namespace Twisted

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

noncomputable section

/-! ## Finite selected-rectangle measure

The stopping rectangles are globally disjoint, not merely fiberwise
disjoint.  This file turns that geometric fact into the exact finite product
measure identity needed before the monotone countable exhaustion.
-/

/-- The Lebesgue measure of a literal source dyadic interval is its declared
side length. -/
theorem scratch_measure_fiberDyadicInterval (I : FiberDyadicInterval) :
    volume (fiberDyadicInterval I) =
      ENNReal.ofReal (fiberDyadicIntervalLength I) := by
  unfold fiberDyadicInterval fiberDyadicIntervalLength
  rw [Real.volume_Ico]
  congr 1
  push_cast
  ring

/-- The product stopping rectangles inherit the fixed-fiber interval
disjointness.  This local copy makes the finite measure calculation testable
against the currently compiled public interface. -/
theorem scratch_pairwiseDisjoint_fiberDyadicSelectedRectangles
    {Z : Type*} [MeasurableSpace Z] (Zf : Set Z)
    (A : FiberDyadicInterval → Z → ℝ) (H : ℝ) :
    (Set.univ : Set FiberDyadicInterval).PairwiseDisjoint
      (fun I => fiberDyadicInterval I ×ˢ
        fiberDyadicSelectionSet Zf A H I) := by
  intro I _ J _ hne
  change Disjoint
    (fiberDyadicInterval I ×ˢ fiberDyadicSelectionSet Zf A H I)
    (fiberDyadicInterval J ×ˢ fiberDyadicSelectionSet Zf A H J)
  rw [Set.disjoint_left]
  intro yz hyI hyJ
  have hline : Disjoint (fiberDyadicInterval I) (fiberDyadicInterval J) :=
    pairwiseDisjoint_fiberDyadicSelectedIntervals Zf A H yz.2 hyI.2 hyJ.2 hne
  exact (Set.disjoint_left.mp hline) hyI.1 hyJ.1

/-- A finite family of the literal stopping rectangles has measure equal to
the sum of its product measures.  The equality uses the actual maximal
selection disjointness, rather than a subadditivity loss. -/
theorem scratch_measure_fiberDyadicExceptionalSetFinset_eq
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [SFinite μ]
    (T : Finset FiberDyadicInterval)
    (Zf : Set Z) (hZf : MeasurableSet Zf)
    (A : FiberDyadicInterval → Z → ℝ)
    (hA : ∀ I, Measurable (A I)) (H : ℝ) :
    (volume.prod μ) (fiberDyadicExceptionalSetFinset T Zf A H) =
      ∑ I ∈ T, volume (fiberDyadicInterval I) *
        μ (fiberDyadicSelectionSet Zf A H I) := by
  unfold fiberDyadicExceptionalSetFinset
  rw [measure_biUnion_finset]
  · simp only [Measure.prod_prod]
  · intro I hI J hJ hne
    exact scratch_pairwiseDisjoint_fiberDyadicSelectedRectangles Zf A H
      (Set.mem_univ I) (Set.mem_univ J) hne
  · intro I hI
    exact (measurableSet_fiberDyadicInterval I).prod
      (measurableSet_fiberDyadicSelectionSet Zf hZf A hA H I)

/-- The finite selected-length density on transverse fibers. -/
noncomputable def scratch_fiberDyadicSelectedLengthDensity
    {Z : Type*} [MeasurableSpace Z] (T : Finset FiberDyadicInterval)
    (Zf : Set Z) (A : FiberDyadicInterval → Z → ℝ) (H : ℝ) : Z → ℝ :=
  fun z => ∑ I ∈ T, fiberDyadicIntervalLength I *
    (fiberDyadicSelectionSet Zf A H I).indicator (fun _ => (1 : ℝ)) z

/-- The finite selected-length density is measurable. -/
theorem scratch_measurable_fiberDyadicSelectedLengthDensity
    {Z : Type*} [MeasurableSpace Z] (T : Finset FiberDyadicInterval)
    (Zf : Set Z) (hZf : MeasurableSet Zf)
    (A : FiberDyadicInterval → Z → ℝ)
    (hA : ∀ I, Measurable (A I)) (H : ℝ) :
    Measurable (scratch_fiberDyadicSelectedLengthDensity T Zf A H) := by
  unfold scratch_fiberDyadicSelectedLengthDensity
  apply Finset.measurable_sum
  intro I hI
  exact measurable_const.mul
    (measurable_const.indicator
      (measurableSet_fiberDyadicSelectionSet Zf hZf A hA H I))

/-- The selected-length density is pointwise nonnegative. -/
theorem scratch_fiberDyadicSelectedLengthDensity_nonneg
    {Z : Type*} [MeasurableSpace Z] (T : Finset FiberDyadicInterval)
    (Zf : Set Z) (A : FiberDyadicInterval → Z → ℝ) (H : ℝ) (z : Z) :
    0 ≤ scratch_fiberDyadicSelectedLengthDensity T Zf A H z := by
  unfold scratch_fiberDyadicSelectedLengthDensity
  apply Finset.sum_nonneg
  intro I hI
  have hlen : 0 ≤ fiberDyadicIntervalLength I :=
    (fiberDyadicIntervalLength_pos I).le
  by_cases hz : z ∈ fiberDyadicSelectionSet Zf A H I
  · simp [Set.indicator_of_mem hz, hlen]
  · simp [Set.indicator_of_notMem hz]

/-- Any integrable pointwise majorant of the finite selected-length density
controls its integral.  This is the Tonelli-facing form of the fixed-fiber
stopping estimate. -/
theorem scratch_integral_fiberDyadicSelectedLengthDensity_le
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (T : Finset FiberDyadicInterval)
    (Zf : Set Z) (hZf : MeasurableSet Zf)
    (A : FiberDyadicInterval → Z → ℝ)
    (hA : ∀ I, Measurable (A I)) (H : ℝ)
    (G : Z → ℝ) (hG : Integrable G μ)
    (hpoint : ∀ z,
      scratch_fiberDyadicSelectedLengthDensity T Zf A H z ≤ G z) :
    (∫ z, scratch_fiberDyadicSelectedLengthDensity T Zf A H z ∂μ) ≤
      ∫ z, G z ∂μ := by
  have hDmeas := scratch_measurable_fiberDyadicSelectedLengthDensity
    T Zf hZf A hA H
  have hDnon (z : Z) :
      0 ≤ scratch_fiberDyadicSelectedLengthDensity T Zf A H z :=
    scratch_fiberDyadicSelectedLengthDensity_nonneg T Zf A H z
  have hDint : Integrable (scratch_fiberDyadicSelectedLengthDensity T Zf A H) μ :=
    hG.mono' hDmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hDnon z)]
        exact hpoint z)
  exact integral_mono hDint hG hpoint

/-- On a finite transverse measure space, integrating the finite selected
length density gives the expected sum of interval lengths times fiber-set
measures. -/
theorem scratch_integral_fiberDyadicSelectedLengthDensity_eq_sum
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]
    (T : Finset FiberDyadicInterval)
    (Zf : Set Z) (hZf : MeasurableSet Zf)
    (A : FiberDyadicInterval → Z → ℝ)
    (hA : ∀ I, Measurable (A I)) (H : ℝ) :
    (∫ z, scratch_fiberDyadicSelectedLengthDensity T Zf A H z ∂μ) =
      ∑ I ∈ T, fiberDyadicIntervalLength I *
        μ.real (fiberDyadicSelectionSet Zf A H I) := by
  unfold scratch_fiberDyadicSelectedLengthDensity
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro I hI
    let S : Set Z := fiberDyadicSelectionSet Zf A H I
    have hS : MeasurableSet S :=
      measurableSet_fiberDyadicSelectionSet Zf hZf A hA H I
    have hrewrite : (fun z : Z => fiberDyadicIntervalLength I *
        S.indicator (fun _ => (1 : ℝ)) z) =
        S.indicator (fun _ => fiberDyadicIntervalLength I) := by
      funext z
      by_cases hz : z ∈ S <;> simp [S, hz]
    rw [hrewrite, integral_indicator_const _ hS]
    simp only [smul_eq_mul]
    ring
  · intro I hI
    let S : Set Z := fiberDyadicSelectionSet Zf A H I
    have hS : MeasurableSet S :=
      measurableSet_fiberDyadicSelectionSet Zf hZf A hA H I
    have hrewrite : (fun z : Z => fiberDyadicIntervalLength I *
        S.indicator (fun _ => (1 : ℝ)) z) =
        S.indicator (fun _ => fiberDyadicIntervalLength I) := by
      funext z
      by_cases hz : z ∈ S <;> simp [S, hz]
    rw [hrewrite, integrable_indicator_iff hS]
    exact integrableOn_const (measure_ne_top μ S)

/-- Membership in the nonnegative finite-fiber-mass set supplies the ordinary
Bochner integrability needed by the stopping estimate. -/
theorem scratch_mem_fiberFiniteMassSet_integrable
    {Z : Type*} [MeasurableSpace Z]
    (F : ℝ × Z → ℝ) (hF : Measurable F)
    (hF_nonneg : ∀ yz : ℝ × Z, 0 ≤ F yz)
    (z : Z)
    (hz : z ∈ fiberFiniteMassSet (fun yz : ℝ × Z => ENNReal.ofReal (F yz))) :
    Integrable (fun y : ℝ => F (y, z)) volume := by
  have hslice : Measurable (fun y : ℝ => F (y, z)) :=
    hF.comp (measurable_id.prodMk measurable_const)
  apply (lintegral_ofReal_ne_top_iff_integrable
    hslice.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => hF_nonneg (y, z))).mp
  exact ne_of_lt hz

end
end Twisted
end Auto
