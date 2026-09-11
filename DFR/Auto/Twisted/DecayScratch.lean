import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Topology.Order.Compact
import DFR.Auto.Twisted.Twisted

open Filter TopologicalSpace
open scoped Topology

noncomputable section

#check pow_le_pow_right₀
#check Continuous.exists_forall_ge'
#check Real.rpow_natCast

def g (x : ℝ) : ℝ := Real.exp (-Real.pi * x ^ 2)

example (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, (1 + |x|) ^ n * g x ≤ C := by
  let F : ℝ → ℝ := fun x ↦ (1 + |x|) ^ n * g x
  have hg0 : Tendsto (fun x : ℝ ↦ g x) (cocompact ℝ) (𝓝 0) := by
    simpa [g, Real.rpow_zero] using
      (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact Real.pi_pos (0 : ℝ))
  have hgn : Tendsto (fun x : ℝ ↦ |x| ^ n * g x) (cocompact ℝ) (𝓝 0) := by
    simpa [g, Real.rpow_natCast] using
      (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact Real.pi_pos (n : ℝ))
  have hq : Tendsto (fun x : ℝ ↦ (2 : ℝ) ^ n * (g x + |x| ^ n * g x))
      (cocompact ℝ) (𝓝 0) := by
    convert (tendsto_const_nhds.mul (hg0.add hgn)) using 1 <;> norm_num
  have hnonneg (x : ℝ) : 0 ≤ F x := by
    exact mul_nonneg (pow_nonneg (by positivity) _) (Real.exp_pos _).le
  have hupper (x : ℝ) : F x ≤ (2 : ℝ) ^ n * (g x + |x| ^ n * g x) := by
    dsimp [F, g]
    have hp : (1 + |x|) ^ n ≤ (2 : ℝ) ^ (n - 1) * (1 ^ n + |x| ^ n) :=
      add_pow_le zero_le_one (abs_nonneg x) n
    have hpow : (2 : ℝ) ^ (n - 1) ≤ (2 : ℝ) ^ n := by
      exact pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (Nat.sub_le n 1)
    calc
      (1 + |x|) ^ n * Real.exp (-Real.pi * x ^ 2) ≤
          ((2 : ℝ) ^ (n - 1) * (1 ^ n + |x| ^ n)) *
            Real.exp (-Real.pi * x ^ 2) := by gcongr
      _ ≤ ((2 : ℝ) ^ n * (1 ^ n + |x| ^ n)) *
            Real.exp (-Real.pi * x ^ 2) := by gcongr
      _ = (2 : ℝ) ^ n *
          (Real.exp (-Real.pi * x ^ 2) + |x| ^ n * Real.exp (-Real.pi * x ^ 2)) := by
        ring
  have hlim : Tendsto F (cocompact ℝ) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hq
      (Filter.Eventually.of_forall hnonneg) (Filter.Eventually.of_forall hupper)
  have hFzero : F 0 = 1 := by simp [F, g]
  have hev : ∀ᶠ x in cocompact ℝ, F x ≤ F 0 := by
    rw [hFzero]
    exact hlim.eventually (Iic_mem_nhds (by norm_num))
  have hcont : Continuous F := by
    dsimp [F, g]
    fun_prop
  rcases hcont.exists_forall_ge' 0 hev with ⟨x0, hmax⟩
  exact ⟨F x0, hnonneg x0, fun x ↦ hmax x⟩
