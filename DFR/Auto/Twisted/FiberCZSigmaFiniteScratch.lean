import Auto.Twisted.Twisted

namespace Auto
namespace Twisted

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal

noncomputable section

/-! ## Countable disjoint unions without finite ambient measure

The transverse measure in the fiberwise Calderón--Zygmund argument is
Lebesgue measure on a plane, hence not a finite measure.  The finite-measure
terminal in the main file is still useful on local exhaustions, but the
following elementary terminal isolates the only extra fact needed to pass to
the globally countable disjoint union: each selected rectangle itself has
finite measure.
-/

theorem scratch_measureReal_iUnion_le_of_pairwise_disjoint
    {X ι : Type*} [MeasurableSpace X] [Countable ι] (μ : Measure X)
    (R : ι → Set X)
    (hRmeas : ∀ i, MeasurableSet (R i))
    (hRpair : Pairwise (Function.onFun Disjoint R))
    (hRneTop : ∀ i, μ (R i) ≠ ∞)
    (B : ℝ)
    (hfinite : ∀ T : Finset ι, (∑ i ∈ T, μ.real (R i)) ≤ B) :
    μ.real (⋃ i, R i) ≤ B := by
  change (μ (⋃ i, R i)).toReal ≤ B
  rw [measure_iUnion hRpair hRmeas, ENNReal.tsum_toReal_eq hRneTop]
  apply Real.tsum_le_of_sum_le
  · intro i
    exact ENNReal.toReal_nonneg
  · intro T
    exact hfinite T

/-- The finite selected-length Fubini identity does not need a finite
ambient transverse measure; it only needs the finitely many selected fiber
sets themselves to have finite measure. -/
theorem scratch_integral_fiberDyadicSelectedLengthDensity_eq_sum_of_measure_ne_top
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (T : Finset FiberDyadicInterval)
    (Zf : Set Z) (hZf : MeasurableSet Zf)
    (A : FiberDyadicInterval → Z → ℝ)
    (hA : ∀ I, Measurable (A I)) (H : ℝ)
    (hfinite : ∀ I ∈ T,
      μ (fiberDyadicSelectionSet Zf A H I) ≠ ∞) :
    (∫ z, fiberDyadicSelectedLengthDensity T Zf A H z ∂μ) =
      ∑ I ∈ T, fiberDyadicIntervalLength I *
        μ.real (fiberDyadicSelectionSet Zf A H I) := by
  unfold fiberDyadicSelectedLengthDensity
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
    exact integrableOn_const (hfinite I hI)

/-- The real measure of a finite selected exceptional set is its selected
length density integral under the same local finiteness hypothesis. -/
theorem scratch_measureReal_fiberDyadicExceptionalSetFinset_eq_integral_of_measure_ne_top
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [SFinite μ]
    (T : Finset FiberDyadicInterval)
    (Zf : Set Z) (hZf : MeasurableSet Zf)
    (A : FiberDyadicInterval → Z → ℝ)
    (hA : ∀ I, Measurable (A I)) (H : ℝ)
    (hfinite : ∀ I ∈ T,
      μ (fiberDyadicSelectionSet Zf A H I) ≠ ∞) :
    (volume.prod μ).real (fiberDyadicExceptionalSetFinset T Zf A H) =
      ∫ z, fiberDyadicSelectedLengthDensity T Zf A H z ∂μ := by
  change ((volume.prod μ) (fiberDyadicExceptionalSetFinset T Zf A H)).toReal = _
  rw [measure_fiberDyadicExceptionalSetFinset_eq μ T Zf hZf A hA H]
  rw [ENNReal.toReal_sum]
  · calc
      (∑ I ∈ T, (volume (fiberDyadicInterval I) *
        μ (fiberDyadicSelectionSet Zf A H I)).toReal) =
          ∑ I ∈ T, fiberDyadicIntervalLength I *
            μ.real (fiberDyadicSelectionSet Zf A H I) := by
          apply Finset.sum_congr rfl
          intro I hI
          rw [measure_fiberDyadicInterval, ENNReal.toReal_mul]
          simp only [ENNReal.toReal_ofReal (fiberDyadicIntervalLength_pos I).le]
          rfl
      _ = ∫ z, fiberDyadicSelectedLengthDensity T Zf A H z ∂μ :=
        (scratch_integral_fiberDyadicSelectedLengthDensity_eq_sum_of_measure_ne_top
          μ T Zf hZf A hA H hfinite).symm
  · intro I hI
    apply ENNReal.mul_ne_top
    · rw [measure_fiberDyadicInterval]
      exact ENNReal.ofReal_ne_top
    · exact hfinite I hI

/-- The finite selected exceptional set obeys the usual weak-one estimate
over an arbitrary sigma-finite transverse measure once its selected pieces
are locally finite. -/
theorem scratch_measureReal_fiberDyadicExceptionalSetFinset_le_inv_mul_integral
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [SFinite μ]
    (Zf : Set Z) (hZf : MeasurableSet Zf)
    (F : ℝ × Z → ℝ) (hF : Integrable F (volume.prod μ))
    (hF_nonneg : ∀ yz : ℝ × Z, 0 ≤ F yz)
    (hF_meas : Measurable F)
    (H : ℝ) (hH : 0 < H) (T : Finset FiberDyadicInterval)
    (hfiber : ∀ z ∈ Zf, Integrable (fun y : ℝ => F (y, z)) volume)
    (hfinite : ∀ I ∈ T,
      μ (fiberDyadicSelectionSet Zf (fiberDyadicIntervalAverage F) H I) ≠ ∞) :
    (volume.prod μ).real
      (fiberDyadicExceptionalSetFinset T Zf
        (fiberDyadicIntervalAverage F) H) ≤
      H⁻¹ * ∫ yz, F yz ∂(volume.prod μ) := by
  rw [scratch_measureReal_fiberDyadicExceptionalSetFinset_eq_integral_of_measure_ne_top
    μ T Zf hZf (fiberDyadicIntervalAverage F)
    (fun I => measurable_fiberDyadicIntervalAverage F hF_meas I) H hfinite]
  exact integral_fiberDyadicSelectedLengthDensity_le_inv_mul_integral μ Zf hZf
    F hF hF_nonneg hF_meas H hH T hfiber

/-- Countable selected rectangles have the source weak-one measure bound over
the non-finite transverse Lebesgue space.  The supplied local-finiteness
premise is exactly what makes the `toReal` countable-additivity step valid. -/
theorem scratch_measureReal_fiberDyadicExceptionalSet_le_inv_mul_integral
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [SFinite μ]
    (Zf : Set Z) (hZf : MeasurableSet Zf)
    (F : ℝ × Z → ℝ) (hF : Integrable F (volume.prod μ))
    (hF_nonneg : ∀ yz : ℝ × Z, 0 ≤ F yz)
    (hF_meas : Measurable F)
    (H : ℝ) (hH : 0 < H)
    (hfiber : ∀ z ∈ Zf, Integrable (fun y : ℝ => F (y, z)) volume)
    (hfinite : ∀ I : FiberDyadicInterval,
      μ (fiberDyadicSelectionSet Zf (fiberDyadicIntervalAverage F) H I) ≠ ∞) :
    (volume.prod μ).real
      (fiberDyadicExceptionalSet Zf (fiberDyadicIntervalAverage F) H) ≤
      H⁻¹ * ∫ yz, F yz ∂(volume.prod μ) := by
  classical
  let R : FiberDyadicInterval → Set (ℝ × Z) := fun I =>
    fiberDyadicInterval I ×ˢ
      fiberDyadicSelectionSet Zf (fiberDyadicIntervalAverage F) H I
  have hRmeas (I : FiberDyadicInterval) : MeasurableSet (R I) := by
    dsimp [R]
    exact (measurableSet_fiberDyadicInterval I).prod
      (measurableSet_fiberDyadicSelectionSet Zf hZf
        (fiberDyadicIntervalAverage F)
        (fun J => measurable_fiberDyadicIntervalAverage F hF_meas J) H I)
  have hRpair : Pairwise (Function.onFun Disjoint R) := by
    intro I J hIJ
    exact pairwiseDisjoint_fiberDyadicSelectedRectangles Zf
      (fiberDyadicIntervalAverage F) H (Set.mem_univ I) (Set.mem_univ J) hIJ
  have hRneTop (I : FiberDyadicInterval) :
      (volume.prod μ) (R I) ≠ ∞ := by
    dsimp [R]
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top
      (by rw [measure_fiberDyadicInterval]; exact ENNReal.ofReal_ne_top)
      (hfinite I)
  have hrect (I : FiberDyadicInterval) :
      (volume.prod μ).real (R I) =
        fiberDyadicIntervalLength I *
          μ.real (fiberDyadicSelectionSet Zf
            (fiberDyadicIntervalAverage F) H I) := by
    change ((volume.prod μ) (R I)).toReal = _
    dsimp [R]
    rw [Measure.prod_prod, measure_fiberDyadicInterval, ENNReal.toReal_mul]
    simp only [ENNReal.toReal_ofReal (fiberDyadicIntervalLength_pos I).le]
    rfl
  have hpartial (T : Finset FiberDyadicInterval) :
      (∑ I ∈ T, (volume.prod μ).real (R I)) ≤
        H⁻¹ * ∫ yz, F yz ∂(volume.prod μ) := by
    calc
      (∑ I ∈ T, (volume.prod μ).real (R I)) =
          ∑ I ∈ T, fiberDyadicIntervalLength I *
            μ.real (fiberDyadicSelectionSet Zf
              (fiberDyadicIntervalAverage F) H I) := by
            apply Finset.sum_congr rfl
            intro I hI
            exact hrect I
      _ = ∫ z, fiberDyadicSelectedLengthDensity T Zf
          (fiberDyadicIntervalAverage F) H z ∂μ :=
        (scratch_integral_fiberDyadicSelectedLengthDensity_eq_sum_of_measure_ne_top
          μ T Zf hZf (fiberDyadicIntervalAverage F)
          (fun I => measurable_fiberDyadicIntervalAverage F hF_meas I) H
          (fun I _ => hfinite I)).symm
      _ = (volume.prod μ).real
          (fiberDyadicExceptionalSetFinset T Zf
            (fiberDyadicIntervalAverage F) H) :=
        (scratch_measureReal_fiberDyadicExceptionalSetFinset_eq_integral_of_measure_ne_top
          μ T Zf hZf (fiberDyadicIntervalAverage F)
          (fun I => measurable_fiberDyadicIntervalAverage F hF_meas I) H
          (fun I _ => hfinite I)).symm
      _ ≤ H⁻¹ * ∫ yz, F yz ∂(volume.prod μ) :=
        scratch_measureReal_fiberDyadicExceptionalSetFinset_le_inv_mul_integral
          μ Zf hZf F hF hF_nonneg hF_meas H hH T hfiber
          (fun I _ => hfinite I)
  unfold fiberDyadicExceptionalSet
  change (volume.prod μ).real (⋃ I, R I) ≤ _
  exact scratch_measureReal_iUnion_le_of_pairwise_disjoint
    (volume.prod μ) R hRmeas hRpair hRneTop
    (H⁻¹ * ∫ yz, F yz ∂(volume.prod μ)) hpartial

/-- Every individual selected transverse fiber set has finite measure when
the underlying nonnegative fiber field is globally integrable.  This supplies
the local-finiteness premise of the sigma-finite countable-union terminal. -/
theorem scratch_measure_fiberDyadicSelectionSet_ne_top_of_integrable
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [SFinite μ]
    (Zf : Set Z) (F : ℝ × Z → ℝ)
    (hF : Integrable F (volume.prod μ))
    (hF_nonneg : ∀ yz : ℝ × Z, 0 ≤ F yz)
    (H : ℝ) (hH : 0 < H) (I : FiberDyadicInterval) :
    μ (fiberDyadicSelectionSet Zf (fiberDyadicIntervalAverage F) H I) ≠ ∞ := by
  let D : Set (ℝ × Z) := fiberDyadicInterval I ×ˢ Set.univ
  let G : ℝ × Z → ℝ := D.indicator F
  have hD : MeasurableSet D :=
    (measurableSet_fiberDyadicInterval I).prod MeasurableSet.univ
  have hG : Integrable G (volume.prod μ) := by
    dsimp [G]
    exact hF.indicator hD
  let A : Z → ℝ := fiberDyadicIntervalAverage F I
  have hA : Integrable A μ := by
    change Integrable (fun z : Z =>
      (fiberDyadicIntervalLength I)⁻¹ * ∫ y : ℝ, G (y, z)) μ
    exact hG.integral_prod_right.const_mul _
  let Q : Z → ℝ := fun z => H⁻¹ * A z
  have hQ : Integrable Q μ := hA.const_mul H⁻¹
  have hQnonneg (z : Z) : 0 ≤ Q z := by
    dsimp [Q, A]
    apply mul_nonneg
    · exact inv_nonneg.mpr hH.le
    · apply mul_nonneg
      · exact inv_nonneg.mpr (fiberDyadicIntervalLength_pos I).le
      · apply integral_nonneg
        intro y
        dsimp [G, D]
        by_cases hy : y ∈ fiberDyadicInterval I <;>
          simp [hy, hF_nonneg (y, z)]
  let S : Set Z := fiberDyadicSelectionSet Zf (fiberDyadicIntervalAverage F) H I
  have hS : ∀ z ∈ S, 1 ≤ Q z := by
    intro z hz
    have hlt : H < fiberDyadicIntervalAverage F I z := hz.1.2
    have hdiv : 1 < fiberDyadicIntervalAverage F I z / H :=
      (one_lt_div hH).mpr hlt
    have heq : fiberDyadicIntervalAverage F I z / H = Q z := by
      dsimp [Q, A]
      field_simp
    exact hdiv.le.trans_eq heq
  have hmeasure : μ S ≤ ENNReal.ofReal (∫ z, Q z ∂μ) :=
    hQ.measure_le_integral (Filter.Eventually.of_forall hQnonneg) hS
  exact ne_of_lt (hmeasure.trans_lt ENNReal.ofReal_lt_top)

/-- The countable stopping exceptional-set weak bound in the form usable for
Lebesgue measure on the transverse variables. -/
theorem scratch_measureReal_fiberDyadicExceptionalSet_le_inv_mul_integral_of_integrable
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [SFinite μ]
    (Zf : Set Z) (hZf : MeasurableSet Zf)
    (F : ℝ × Z → ℝ) (hF : Integrable F (volume.prod μ))
    (hF_nonneg : ∀ yz : ℝ × Z, 0 ≤ F yz)
    (hF_meas : Measurable F)
    (H : ℝ) (hH : 0 < H)
    (hfiber : ∀ z ∈ Zf, Integrable (fun y : ℝ => F (y, z)) volume) :
    (volume.prod μ).real
      (fiberDyadicExceptionalSet Zf (fiberDyadicIntervalAverage F) H) ≤
      H⁻¹ * ∫ yz, F yz ∂(volume.prod μ) := by
  apply scratch_measureReal_fiberDyadicExceptionalSet_le_inv_mul_integral
    μ Zf hZf F hF hF_nonneg hF_meas H hH hfiber
  intro I
  exact scratch_measure_fiberDyadicSelectionSet_ne_top_of_integrable
    μ Zf F hF hF_nonneg H hH I

end
end Twisted
end Auto
