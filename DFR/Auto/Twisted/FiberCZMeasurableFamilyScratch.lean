/- Copyright (c) 2026 Polona Durcik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Auto.Twisted.Twisted

/-! ### Countable measurable dyadic fiber families

This file isolates the measurability portion of the blueprint's Section 8
fiberwise Calderón--Zygmund selection.  It deliberately does not assert the
maximality or analytic estimates: its terminal is the countable-index
measurability interface needed before those arguments can be assembled. -/

namespace Auto.Twisted

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

/-- The source dyadic interval index: `(scale, translation) ∈ ℤ × ℤ`. -/
abbrev ScratchFiberDyadicIntervalIndex := ℤ × ℤ

/-- The literal half-open interval `[2^k n, 2^k(n+1))` indexed by `(k,n)`. -/
def scratchFiberDyadicInterval (I : ScratchFiberDyadicIntervalIndex) : Set ℝ :=
  Ico ((I.2 : ℝ) * (2 : ℝ) ^ I.1)
    (((I.2 + 1 : ℤ) : ℝ) * (2 : ℝ) ^ I.1)

/-- Its positive side length. -/
def scratchFiberDyadicIntervalSide (I : ScratchFiberDyadicIntervalIndex) : ℝ :=
  (2 : ℝ) ^ I.1

theorem measurableSet_scratchFiberDyadicInterval
    (I : ScratchFiberDyadicIntervalIndex) :
    MeasurableSet (scratchFiberDyadicInterval I) :=
  measurableSet_Ico

/-- A fixed dyadic interval average of a jointly measurable scalar fiber
function, written with an indicator so that its measurability is immediate
from the product-integral API. -/
noncomputable def scratchFiberDyadicIntervalAverage
    {Z : Type*} [MeasurableSpace Z] (F : ℝ × Z → ℝ)
    (I : ScratchFiberDyadicIntervalIndex) (z : Z) : ℝ :=
  (scratchFiberDyadicIntervalSide I)⁻¹ *
    ∫ y : ℝ, (scratchFiberDyadicInterval I ×ˢ Set.univ).indicator F (y, z)

/-- The indicator presentation is the source's usual set-integral average. -/
theorem scratchFiberDyadicIntervalAverage_eq_setIntegral
    {Z : Type*} [MeasurableSpace Z] (F : ℝ × Z → ℝ)
    (I : ScratchFiberDyadicIntervalIndex) (z : Z) :
    scratchFiberDyadicIntervalAverage F I z =
      (scratchFiberDyadicIntervalSide I)⁻¹ *
        ∫ y : ℝ in scratchFiberDyadicInterval I, F (y, z) := by
  unfold scratchFiberDyadicIntervalAverage
  rw [← integral_indicator (measurableSet_scratchFiberDyadicInterval I)]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ scratchFiberDyadicInterval I <;> simp [hy]

theorem measurable_scratchFiberDyadicIntervalAverage
    {Z : Type*} [MeasurableSpace Z] (F : ℝ × Z → ℝ)
    (hF : Measurable F) (I : ScratchFiberDyadicIntervalIndex) :
    Measurable (scratchFiberDyadicIntervalAverage F I) := by
  let D : Set (ℝ × Z) := scratchFiberDyadicInterval I ×ˢ Set.univ
  let G : ℝ × Z → ℝ := D.indicator F
  have hD : MeasurableSet D :=
    (measurableSet_scratchFiberDyadicInterval I).prod MeasurableSet.univ
  have hG : Measurable G := hF.indicator hD
  have hInt : Measurable (fun z : Z => ∫ y : ℝ, G (y, z)) :=
    hG.stronglyMeasurable.integral_prod_left'.measurable
  change Measurable (fun z : Z =>
    (scratchFiberDyadicIntervalSide I)⁻¹ *
      ∫ y : ℝ, G (y, z))
  exact measurable_const.mul hInt

/-- The source's proper-ancestor relation, expressed directly through literal
interval inclusion. -/
def scratchFiberDyadicProperAncestor
    (I J : ScratchFiberDyadicIntervalIndex) : Prop :=
  scratchFiberDyadicInterval I ⊂ scratchFiberDyadicInterval J

/-- The conull-fiber candidate in the source: fibers with finite nonnegative
mass.  Taking `F(y,z) = |f(y,z)|^p` (in `ℝ≥0∞`) recovers `Z_f`. -/
def scratchFiberFiniteMassSet
    {Z : Type*} [MeasurableSpace Z] (F : ℝ × Z → ℝ≥0∞) : Set Z :=
  {z | (∫⁻ y : ℝ, F (y, z)) < ∞}

theorem measurableSet_scratchFiberFiniteMassSet
    {Z : Type*} [MeasurableSpace Z] (F : ℝ × Z → ℝ≥0∞)
    (hF : Measurable F) :
    MeasurableSet (scratchFiberFiniteMassSet F) := by
  unfold scratchFiberFiniteMassSet
  exact measurableSet_lt hF.lintegral_prod_left' measurable_const

/-- For a countable index family of measurable averages, select exactly the
fibers on which `I` is above the threshold while every proper ancestor is at
most the threshold. -/
def scratchFiberDyadicSelectionSet
    {Z : Type*} [MeasurableSpace Z] (Zf : Set Z)
    (A : ScratchFiberDyadicIntervalIndex → Z → ℝ) (H : ℝ)
    (I : ScratchFiberDyadicIntervalIndex) : Set Z :=
  (Zf ∩ {z | H < A I z}) ∩
    ⋂ J : ScratchFiberDyadicIntervalIndex,
      ⋂ (_ : scratchFiberDyadicProperAncestor I J), {z | A J z ≤ H}

theorem measurableSet_scratchFiberDyadicSelectionSet
    {Z : Type*} [MeasurableSpace Z] (Zf : Set Z)
    (hZf : MeasurableSet Zf)
    (A : ScratchFiberDyadicIntervalIndex → Z → ℝ)
    (hA : ∀ I, Measurable (A I)) (H : ℝ)
    (I : ScratchFiberDyadicIntervalIndex) :
    MeasurableSet (scratchFiberDyadicSelectionSet Zf A H I) := by
  unfold scratchFiberDyadicSelectionSet
  refine (hZf.inter (measurableSet_lt measurable_const (hA I))).inter ?_
  refine MeasurableSet.iInter fun J => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_le (hA J) measurable_const

/-- The source exceptional set `B = ⋃_I (I × S_I)` for the countable dyadic
family. -/
def scratchFiberDyadicExceptionalSet
    {Z : Type*} [MeasurableSpace Z] (Zf : Set Z)
    (A : ScratchFiberDyadicIntervalIndex → Z → ℝ) (H : ℝ) : Set (ℝ × Z) :=
  ⋃ I : ScratchFiberDyadicIntervalIndex,
    scratchFiberDyadicInterval I ×ˢ scratchFiberDyadicSelectionSet Zf A H I

theorem measurableSet_scratchFiberDyadicExceptionalSet
    {Z : Type*} [MeasurableSpace Z] (Zf : Set Z)
    (hZf : MeasurableSet Zf)
    (A : ScratchFiberDyadicIntervalIndex → Z → ℝ)
    (hA : ∀ I, Measurable (A I)) (H : ℝ) :
    MeasurableSet (scratchFiberDyadicExceptionalSet Zf A H) := by
  unfold scratchFiberDyadicExceptionalSet
  refine MeasurableSet.iUnion fun I => ?_
  exact (measurableSet_scratchFiberDyadicInterval I).prod
    (measurableSet_scratchFiberDyadicSelectionSet Zf hZf A hA H I)

/-- The same exceptional set restricted to a finite family, for a finite
truncation before the countable passage. -/
def scratchFiberDyadicExceptionalSetFinset
    {Z : Type*} [MeasurableSpace Z] (T : Finset ScratchFiberDyadicIntervalIndex)
    (Zf : Set Z) (A : ScratchFiberDyadicIntervalIndex → Z → ℝ)
    (H : ℝ) : Set (ℝ × Z) :=
  ⋃ I ∈ T,
    scratchFiberDyadicInterval I ×ˢ scratchFiberDyadicSelectionSet Zf A H I

theorem measurableSet_scratchFiberDyadicExceptionalSetFinset
    {Z : Type*} [MeasurableSpace Z] (T : Finset ScratchFiberDyadicIntervalIndex)
    (Zf : Set Z) (hZf : MeasurableSet Zf)
    (A : ScratchFiberDyadicIntervalIndex → Z → ℝ)
    (hA : ∀ I, Measurable (A I)) (H : ℝ) :
    MeasurableSet (scratchFiberDyadicExceptionalSetFinset T Zf A H) := by
  unfold scratchFiberDyadicExceptionalSetFinset
  exact T.measurableSet_biUnion fun I _ =>
    (measurableSet_scratchFiberDyadicInterval I).prod
      (measurableSet_scratchFiberDyadicSelectionSet Zf hZf A hA H I)

/-- Applying the generic selection terminal to the fixed interval averages
of a jointly measurable scalar fiber function. -/
theorem measurableSet_scratchFiberDyadicExceptionalSet_of_average
    {Z : Type*} [MeasurableSpace Z] (Zf : Set Z)
    (hZf : MeasurableSet Zf) (F : ℝ × Z → ℝ)
    (hF : Measurable F) (H : ℝ) :
    MeasurableSet
      (scratchFiberDyadicExceptionalSet Zf
        (scratchFiberDyadicIntervalAverage F) H) := by
  apply measurableSet_scratchFiberDyadicExceptionalSet Zf hZf
  intro I
  exact measurable_scratchFiberDyadicIntervalAverage F hF I

/-- Fully countable measurable-family terminal: a measurable finite-mass
fiber set together with measurable fixed-interval averages yields the source
exceptional set `⋃_I (I × S_I)` as a measurable set. -/
theorem measurableSet_scratchFiberDyadicExceptionalSet_of_fiberFiniteMass
    {Z : Type*} [MeasurableSpace Z] (M : ℝ × Z → ℝ≥0∞)
    (hM : Measurable M) (F : ℝ × Z → ℝ)
    (hF : Measurable F) (H : ℝ) :
    MeasurableSet
      (scratchFiberDyadicExceptionalSet (scratchFiberFiniteMassSet M)
        (scratchFiberDyadicIntervalAverage F) H) := by
  apply measurableSet_scratchFiberDyadicExceptionalSet_of_average
  · exact measurableSet_scratchFiberFiniteMassSet M hM
  · exact hF

/-- The scalar `|f|^p` integrand in the blueprint is jointly measurable. -/
theorem measurable_scratchFiberNormRpow
    {Z : Type*} [MeasurableSpace Z] (f : ℝ × Z → ℂ)
    (hf : Measurable f) (p : ℝ) (hp : 0 ≤ p) :
    Measurable (fun yz : ℝ × Z => ‖f yz‖ ^ p) :=
  (Real.continuous_rpow_const hp).measurable.comp hf.norm

/-- Direct Section 8 specialization: the countable exceptional set based on
the fiberwise `L^p` mass and the averages of `|f|^p` is measurable. -/
theorem measurableSet_scratchFiberDyadicExceptionalSet_of_normRpow
    {Z : Type*} [MeasurableSpace Z] (f : ℝ × Z → ℂ)
    (hf : Measurable f) (p H : ℝ) (hp : 0 ≤ p) :
    MeasurableSet
      (scratchFiberDyadicExceptionalSet
        (scratchFiberFiniteMassSet
          (fun yz : ℝ × Z => ENNReal.ofReal (‖f yz‖ ^ p)))
        (scratchFiberDyadicIntervalAverage
          (fun yz : ℝ × Z => ‖f yz‖ ^ p)) H) := by
  apply measurableSet_scratchFiberDyadicExceptionalSet_of_fiberFiniteMass
  · exact (measurable_scratchFiberNormRpow f hf p hp).ennreal_ofReal
  · exact measurable_scratchFiberNormRpow f hf p hp

end

end Auto.Twisted
