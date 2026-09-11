import Auto.Twisted.Twisted

namespace Auto

open MeasureTheory Filter FourierTransform TopologicalSpace
open scoped BigOperators Convolution ENNReal FourierTransform LineDeriv RealInnerProductSpace Topology

noncomputable section

namespace Twisted

/-- The two local-energy bounds with powers `50` and `100` give the source
local-model estimate with translation power `75`.  All analytic content stays
in the two displayed energy hypotheses; this lemma only records their exact
positive algebraic synthesis. -/
theorem scratch_localModelEstimate_of_energyBounds
    (α : Anisotropy) (T : FiniteConvexTree α) (u : E3) (c : ℝ → ℝ)
    (f : ModelRealInput) (C₁ C₂ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hcs : |expandedModelLocalForm α T.boxes u c f| ^ 2 ≤
      modelEnergyOne α T.boxes u f * modelEnergyTwo α T.boxes u (f 3))
    (hE₁ : modelEnergyOne α T.boxes u f ≤
      C₁ * sourceWeight u ^ 50 * boxMass α T.root *
        (treeLocalSize T 4 (f 0) * treeLocalSize T 4 (f 1) *
          treeLocalSize T 4 (f 2)) ^ 2)
    (hE₂ : modelEnergyTwo α T.boxes u (f 3) ≤
      C₂ * sourceWeight u ^ 100 * boxMass α T.root *
        treeLocalSize T 2 (f 3) ^ 2) :
    |expandedModelLocalForm α T.boxes u c f| ≤
      (C₁ * C₂ + 1) * sourceWeight u ^ 75 * boxMass α T.root *
        (treeLocalSize T 4 (f 0) * treeLocalSize T 4 (f 1) *
          treeLocalSize T 4 (f 2)) * treeLocalSize T 2 (f 3) := by
  let P : ℝ := treeLocalSize T 4 (f 0) * treeLocalSize T 4 (f 1) *
    treeLocalSize T 4 (f 2)
  let M : ℝ := treeLocalSize T 2 (f 3)
  let A : ℝ := sourceWeight u ^ 25 * √(boxMass α T.root) * P
  let B : ℝ := sourceWeight u ^ 50 * √(boxMass α T.root) * M
  have hU : 0 ≤ sourceWeight u := sourceWeight_nonneg u
  have hmass : 0 ≤ boxMass α T.root := (boxMass_pos α T.root).le
  have hP : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg
      (mul_nonneg (treeLocalSize_four_nonneg T (f 0))
        (treeLocalSize_four_nonneg T (f 1)))
      (treeLocalSize_four_nonneg T (f 2))
  have hM : 0 ≤ M := by
    dsimp [M]
    exact treeLocalSize_two_nonneg T (f 3)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hA_sq : A ^ 2 = sourceWeight u ^ 50 * boxMass α T.root * P ^ 2 := by
    dsimp [A]
    rw [mul_pow, mul_pow, ← pow_mul, show 25 * 2 = 50 by norm_num,
      Real.sq_sqrt hmass]
  have hB_sq : B ^ 2 = sourceWeight u ^ 100 * boxMass α T.root * M ^ 2 := by
    dsimp [B]
    rw [mul_pow, mul_pow, ← pow_mul, show 50 * 2 = 100 by norm_num,
      Real.sq_sqrt hmass]
  have hbound₁ : modelEnergyOne α T.boxes u f ≤ C₁ * A ^ 2 := by
    rw [hA_sq]
    calc
      modelEnergyOne α T.boxes u f ≤
          C₁ * sourceWeight u ^ 50 * boxMass α T.root * P ^ 2 := by
            simpa only [P] using hE₁
      _ = C₁ * (sourceWeight u ^ 50 * boxMass α T.root * P ^ 2) := by ring
  have hbound₂ : modelEnergyTwo α T.boxes u (f 3) ≤ C₂ * B ^ 2 := by
    rw [hB_sq]
    calc
      modelEnergyTwo α T.boxes u (f 3) ≤
          C₂ * sourceWeight u ^ 100 * boxMass α T.root * M ^ 2 := by
            simpa only [M] using hE₂
      _ = C₂ * (sourceWeight u ^ 100 * boxMass α T.root * M ^ 2) := by ring
  have hmain := abs_le_of_square_energy_bounds hcs
    (modelEnergyOne_nonneg α T.boxes u f)
    (modelEnergyTwo_nonneg α T.boxes u (f 3)) hA hB hC₁ hC₂ hbound₁ hbound₂
  calc
    |expandedModelLocalForm α T.boxes u c f| ≤ (C₁ * C₂ + 1) * A * B := hmain
    _ = (C₁ * C₂ + 1) * sourceWeight u ^ 75 * boxMass α T.root * P * M := by
      dsimp [A, B]
      calc
        (C₁ * C₂ + 1) *
            (sourceWeight u ^ 25 * √(boxMass α T.root) * P) *
            (sourceWeight u ^ 50 * √(boxMass α T.root) * M) =
            (C₁ * C₂ + 1) *
              (sourceWeight u ^ 25 * sourceWeight u ^ 50) *
              (√(boxMass α T.root) * √(boxMass α T.root)) * P * M := by ring
        _ = _ := by
          rw [← pow_add, show 25 + 50 = 75 by norm_num,
            Real.mul_self_sqrt hmass]
    _ = _ := by rfl

end Twisted

end

end Auto
