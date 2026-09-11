import Auto.Twisted.Twisted
import LeanSpherical.Auto.Spherical.PowerWeights

namespace Auto.Twisted

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal

noncomputable section

#check Auto.Spherical.PowerWeights.exists_lacunaryCZDyadicCube_continuous_decay_decomposition
#check Auto.Spherical.PowerWeights.exists_lacunaryCZDyadicCube_finite_decomposition
#check Auto.Spherical.PowerWeights.lacunaryCZDyadicCubeBadAtom
#check Auto.Spherical.PowerWeights.lacunaryCZDyadicCubeGoodPart
#check Auto.Spherical.PowerWeights.lacunaryCZDyadicCubeCenter
#check Auto.Spherical.PowerWeights.lacunaryCZDyadicCubeRadius

/-- Sanity check: the existing finite Euclidean CZ package specializes
directly to the one-dimensional fiber space used by the twisted argument. -/
theorem scratch_exists_fiberDyadic_cube_CZ
    (f : FiberDyadicLine → ℂ) (lambda : ℝ)
    (hlambda : 0 < lambda) (hcont : Continuous f) (hf : Integrable f volume)
    (hzero : Tendsto f (cocompact FiberDyadicLine) (nhds 0)) :
    ∃ U : Finset (Auto.Spherical.PowerWeights.LacunaryCZDyadicCubeIndex 1),
      (↑U : Set (Auto.Spherical.PowerWeights.LacunaryCZDyadicCubeIndex 1)).PairwiseDisjoint
        Auto.Spherical.PowerWeights.lacunaryCZDyadicCube ∧
      (∀ q ∈ U, Auto.Spherical.PowerWeights.lacunaryCZDyadicCubeIsBad f (lambda / 2) q) ∧
      (∀ x : FiberDyadicLine,
        x ∉ ⋃ q ∈ U, Auto.Spherical.PowerWeights.lacunaryCZDyadicCube q → ‖f x‖ ≤ lambda) ∧
      (∀ q ∈ U, ‖Auto.Spherical.PowerWeights.lacunaryCZDyadicCubeAverage f q‖ ≤
        (2 : ℝ) ^ 1 * (lambda / 2)) ∧
      (∀ x : FiberDyadicLine,
        ‖Auto.Spherical.PowerWeights.lacunaryCZDyadicCubeGoodPart f U x‖ ≤
          (2 : ℝ) ^ 1 * (lambda / 2)) ∧
      (∀ q ∈ U, Integrable
        (Auto.Spherical.PowerWeights.lacunaryCZDyadicCubeBadAtom f q) volume) ∧
      (∀ q ∈ U, (∫ x,
        Auto.Spherical.PowerWeights.lacunaryCZDyadicCubeBadAtom f q x) = 0) ∧
      (∀ q ∈ U, ∀ x : FiberDyadicLine,
        Auto.Spherical.PowerWeights.lacunaryCZDyadicCubeBadAtom f q x ≠ 0 →
          ‖x - Auto.Spherical.PowerWeights.lacunaryCZDyadicCubeCenter q‖ ≤
            Auto.Spherical.PowerWeights.lacunaryCZDyadicCubeRadius q) ∧
      (∀ x : FiberDyadicLine, f x =
        Auto.Spherical.PowerWeights.lacunaryCZDyadicCubeGoodPart f U x +
        ∑ q ∈ U, Auto.Spherical.PowerWeights.lacunaryCZDyadicCubeBadAtom f q x) ∧
      Integrable (Auto.Spherical.PowerWeights.lacunaryCZDyadicCubeGoodPart f U) volume ∧
      (∫ x, ‖Auto.Spherical.PowerWeights.lacunaryCZDyadicCubeGoodPart f U x‖ ^ 2) ≤
        (3 * ((2 : ℝ) ^ 1 * (lambda / 2))) * ∫ x, ‖f x‖ ∧
      (∑ q ∈ U, ∫ x,
        ‖Auto.Spherical.PowerWeights.lacunaryCZDyadicCubeBadAtom f q x‖) ≤
        2 * ∫ x, ‖f x‖ ∧
      (∑ q ∈ U, ((2 : ℝ) ^ q.scale) ^ 1) ≤
        (lambda / 2)⁻¹ * ∫ x, ‖f x‖ ∧
      (∑ q ∈ U,
        (Auto.Spherical.PowerWeights.lacunaryCZDyadicCubeRadius q) ^ 1) ≤
        (1 : ℝ) ^ 1 * ((lambda / 2)⁻¹ * ∫ x, ‖f x‖) := by
  simpa using
    (Auto.Spherical.PowerWeights.exists_lacunaryCZDyadicCube_continuous_decay_decomposition
      (d := 1) f lambda hlambda hcont hf hzero)

end

end Auto.Twisted
