import Auto.Twisted.Twisted
import Mathlib.Algebra.Module.ZLattice.Summable

namespace Auto.Twisted

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal RealInnerProductSpace Topology

noncomputable section

/-- The standard integer lattice in the three frequency coordinates. -/
def scratch_standardModeLattice : Submodule ℤ E3 :=
  Submodule.span ℤ (Set.range (PiLp.basisFun 2 ℝ (Fin 3)))

local instance : DiscreteTopology scratch_standardModeLattice := by
  change DiscreteTopology (Submodule.span ℤ
    (Set.range (PiLp.basisFun 2 ℝ (Fin 3))))
  infer_instance

local instance : IsZLattice ℝ scratch_standardModeLattice := by
  change IsZLattice ℝ (Submodule.span ℤ
    (Set.range (PiLp.basisFun 2 ℝ (Fin 3))))
  infer_instance

theorem scratch_standardModeLattice_rank :
    Module.finrank ℤ scratch_standardModeLattice = 3 := by
  rw [ZLattice.rank ℝ]
  exact finrank_euclideanSpace_fin

theorem scratch_summable_standardMode_norm_inv :
    Summable (fun z : scratch_standardModeLattice ↦
      if z = 0 then (1 : ℝ) else ‖(z : E3)‖⁻¹ ^ (10 : ℕ)) := by
  have hbase := ZLattice.summable_norm_pow_inv scratch_standardModeLattice 10 (by
    rw [scratch_standardModeLattice_rank]
    norm_num)
  have hdelta : Summable (fun z : scratch_standardModeLattice ↦
      if z = 0 then (1 : ℝ) else 0) := by
    apply summable_of_hasFiniteSupport
    rw [Function.HasFiniteSupport]
    refine (Set.finite_singleton (0 : scratch_standardModeLattice)).subset ?_
    intro z hz
    rw [Set.mem_singleton_iff]
    by_contra hzero
    simpa [Function.mem_support, hzero] using hz
  refine (hdelta.add hbase).congr ?_
  intro z
  by_cases hz : z = 0
  · simp [hz]
  · simp [hz]

theorem scratch_summable_standardMode_one_add_norm_inv :
    Summable (fun z : scratch_standardModeLattice ↦
      (1 + ‖(z : E3)‖)⁻¹ ^ (10 : ℕ)) := by
  apply scratch_summable_standardMode_norm_inv.of_nonneg_of_le
  · intro z
    positivity
  · intro z
    by_cases hz : z = 0
    · subst z
      simp
    · rw [if_neg hz]
      have hnorm : 0 < ‖(z : E3)‖ := by
        apply norm_pos_iff.mpr
        intro hzero
        apply hz
        exact Subtype.ext hzero
      have hinv : (1 + ‖(z : E3)‖)⁻¹ ≤ ‖(z : E3)‖⁻¹ := by
        exact (inv_le_inv₀ (by linarith) hnorm).mpr (by linarith)
      exact pow_le_pow_left₀ (by positivity) hinv _

theorem scratch_norm_le_coordinate_l1 (x : E3) :
    ‖x‖ ≤ |x 0| + |x 1| + |x 2| := by
  have hdir (i : Fin 3) : ‖Anisotropy.coordinateDirection i‖ = 1 := by
    simpa only [Anisotropy.coordinateDirection] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one i
  have hdecomp : x =
      x 0 • Anisotropy.coordinateDirection 0 +
        x 1 • Anisotropy.coordinateDirection 1 +
          x 2 • Anisotropy.coordinateDirection 2 := by
    ext i
    fin_cases i <;> simp [coordinateDirection_apply]
  calc
    ‖x‖ = ‖x 0 • Anisotropy.coordinateDirection 0 +
        x 1 • Anisotropy.coordinateDirection 1 +
          x 2 • Anisotropy.coordinateDirection 2‖ := congrArg norm hdecomp
    _ ≤
        ‖x 0 • Anisotropy.coordinateDirection 0‖ +
          ‖x 1 • Anisotropy.coordinateDirection 1‖ +
            ‖x 2 • Anisotropy.coordinateDirection 2‖ := by
      exact norm_add_le_of_le (norm_add_le _ _) (le_refl _)
    _ = |x 0| + |x 1| + |x 2| := by
      simp only [norm_smul, hdir, mul_one, Real.norm_eq_abs]

theorem scratch_one_add_norm_le_sourceWeight (x : E3) :
    1 + ‖x‖ ≤ sourceWeight x := by
  unfold sourceWeight
  linarith [scratch_norm_le_coordinate_l1 x]

theorem scratch_summable_standardMode_sourceWeight_inv :
    Summable (fun z : scratch_standardModeLattice ↦
      (sourceWeight (z : E3))⁻¹ ^ (10 : ℕ)) := by
  apply scratch_summable_standardMode_one_add_norm_inv.of_nonneg_of_le
  · intro z
    positivity
  · intro z
    have hweight : 1 + ‖(z : E3)‖ ≤ sourceWeight (z : E3) :=
      scratch_one_add_norm_le_sourceWeight (z : E3)
    have hposNorm : 0 < 1 + ‖(z : E3)‖ := by positivity
    have hposWeight : 0 < sourceWeight (z : E3) := by
      unfold sourceWeight
      positivity
    have hinv : (sourceWeight (z : E3))⁻¹ ≤ (1 + ‖(z : E3)‖)⁻¹ := by
      exact (inv_le_inv₀ hposWeight hposNorm).mpr hweight
    exact pow_le_pow_left₀ (by positivity) hinv _

end

end Auto.Twisted
