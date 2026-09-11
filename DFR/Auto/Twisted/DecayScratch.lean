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

namespace Auto
namespace Twisted

/-- A sixfold product selecting a Gaussian or derivative-Gaussian in each
literal cube coordinate.  This is scratch notation for the pointwise
remainder estimates. -/
def scratchCubeKernelProduct (α : Anisotropy) (choose : Fin 3 × Bool → Bool)
    (lam r t : ℝ) (p : E3) (x : E6) : ℝ :=
  ∏ q : Fin 3 × Bool,
    if choose q then
      cubeGaussianDerivKernel α lam r t p q.1 (x q)
    else cubeGaussianKernel α lam r t p q.1 (x q)

theorem scratchCubeKernelProduct_domination (α : Anisotropy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (choose : Fin 3 × Bool → Bool)
      (lam r t : ℝ) (p : E3) (x : E6), 1 ≤ lam → 0 < t →
      |scratchCubeKernelProduct α choose lam r t p x| ≤
        C ^ 6 * lam ^ 36 * translationWeight r ^ 20 * cubeBracketWeight α t p x := by
  rcases cubeGaussian_sixfold_domination α with ⟨C, hC, hdom⟩
  refine ⟨C, hC, ?_⟩
  intro choose lam r t p x hlam ht
  unfold scratchCubeKernelProduct
  rw [Finset.abs_prod]
  exact hdom choose lam r t p x hlam ht

theorem scratch_cubeEndpointKernel_eq_product (α : Anisotropy)
    (lam r t : ℝ) (p : E3) (x : E6) :
    cubeEndpointKernel α lam r t p x =
      scratchCubeKernelProduct α (fun _ ↦ false) lam r t p x := by
  unfold cubeEndpointKernel cubeCoordinateD scratchCubeKernelProduct
  rw [Fintype.prod_prod_type]
  simp_rw [Fintype.prod_bool]
  apply Finset.prod_congr rfl
  intro i hi
  simp
  ring

theorem scratch_cubeEndpointKernel_eq_coordinate_mul_erase (α : Anisotropy)
    (i : Fin 3) (lam r t : ℝ) (p : E3) (x : E6) :
    cubeEndpointKernel α lam r t p x =
      cubeGaussianKernel α lam r t p i (x (i, false)) *
        cubeGaussianKernel α lam r t p i (x (i, true)) *
          ∏ m ∈ Finset.univ.erase i, cubeCoordinateD α m lam r t p x := by
  unfold cubeEndpointKernel cubeCoordinateD
  rw [← Finset.mul_prod_erase Finset.univ
    (fun m ↦ cubeGaussianKernel α lam r t p m (x (m, false)) *
      cubeGaussianKernel α lam r t p m (x (m, true))) (Finset.mem_univ i)]

theorem scratch_cubeEndpointKernel_domination (α : Anisotropy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam r t : ℝ) (p : E3) (x : E6),
      1 ≤ lam → 0 < t →
      |cubeEndpointKernel α lam r t p x| ≤
        C ^ 6 * lam ^ 36 * translationWeight r ^ 20 * cubeBracketWeight α t p x := by
  rcases scratchCubeKernelProduct_domination α with ⟨C, hC, hdom⟩
  refine ⟨C, hC, ?_⟩
  intro lam r t p x hlam ht
  rw [scratch_cubeEndpointKernel_eq_product]
  exact hdom (fun _ ↦ false) lam r t p x hlam ht

theorem scratch_cubeKernelProduct_deriv_false_eq (α : Anisotropy)
    (i : Fin 3) (lam r t : ℝ) (p : E3) (x : E6) :
    scratchCubeKernelProduct α (fun q ↦ decide (q = (i, false))) lam r t p x =
      cubeGaussianDerivKernel α lam r t p i (x (i, false)) *
        cubeGaussianKernel α lam r t p i (x (i, true)) *
          ∏ m ∈ Finset.univ.erase i, cubeCoordinateD α m lam r t p x := by
  unfold scratchCubeKernelProduct cubeCoordinateD
  rw [Fintype.prod_prod_type]
  let A : Fin 3 → ℝ := fun j ↦
    ∏ b : Bool, if decide ((j, b) = (i, false)) then
      cubeGaussianDerivKernel α lam r t p j (x (j, b))
    else cubeGaussianKernel α lam r t p j (x (j, b))
  change (∏ j : Fin 3, A j) = _
  rw [← Finset.mul_prod_erase Finset.univ A (Finset.mem_univ i)]
  have hAi : A i =
      cubeGaussianDerivKernel α lam r t p i (x (i, false)) *
        cubeGaussianKernel α lam r t p i (x (i, true)) := by
    dsimp [A]
    simp
    ring
  rw [hAi]
  congr 1
  apply Finset.prod_congr rfl
  intro m hm
  have hmi : m ≠ i := (Finset.mem_erase.mp hm).1
  dsimp [A]
  simp [hmi]
  ring

theorem scratch_cubeKernelProduct_deriv_true_eq (α : Anisotropy)
    (i : Fin 3) (lam r t : ℝ) (p : E3) (x : E6) :
    scratchCubeKernelProduct α (fun q ↦ decide (q = (i, true))) lam r t p x =
      cubeGaussianKernel α lam r t p i (x (i, false)) *
        cubeGaussianDerivKernel α lam r t p i (x (i, true)) *
          ∏ m ∈ Finset.univ.erase i, cubeCoordinateD α m lam r t p x := by
  unfold scratchCubeKernelProduct cubeCoordinateD
  rw [Fintype.prod_prod_type]
  let A : Fin 3 → ℝ := fun j ↦
    ∏ b : Bool, if decide ((j, b) = (i, true)) then
      cubeGaussianDerivKernel α lam r t p j (x (j, b))
    else cubeGaussianKernel α lam r t p j (x (j, b))
  change (∏ j : Fin 3, A j) = _
  rw [← Finset.mul_prod_erase Finset.univ A (Finset.mem_univ i)]
  have hAi : A i =
      cubeGaussianKernel α lam r t p i (x (i, false)) *
        cubeGaussianDerivKernel α lam r t p i (x (i, true)) := by
    dsimp [A]
    simp
    ring
  rw [hAi]
  congr 1
  apply Finset.prod_congr rfl
  intro m hm
  have hmi : m ≠ i := (Finset.mem_erase.mp hm).1
  dsimp [A]
  simp [hmi]
  ring

theorem scratch_cubeFaceKernel_eq_three_products (α : Anisotropy)
    (i : Fin 3) (lam r t : ℝ) (p : E3) (x : E6) :
    cubeFaceKernel α i lam r t p x =
      cubeWidth i lam / (2 * Real.pi) *
        (scratchCubeKernelProduct α (fun q ↦ decide (q = (i, false))) lam r t p x +
          scratchCubeKernelProduct α (fun q ↦ decide (q = (i, true))) lam r t p x) -
      cubeCenterShift i r * scratchCubeKernelProduct α (fun _ ↦ false) lam r t p x := by
  rw [scratch_cubeKernelProduct_deriv_false_eq,
    scratch_cubeKernelProduct_deriv_true_eq,
    ← scratch_cubeEndpointKernel_eq_product,
    scratch_cubeEndpointKernel_eq_coordinate_mul_erase]
  unfold cubeFaceKernel cubeBoundaryKernel cubeCoordinateD
  ring

example {L R K P : ℝ} (hL : 1 ≤ L) (hR : 1 ≤ R)
    (hK : 0 ≤ K) (hP : 0 ≤ P) :
    L * P * (K + K) + R * K ≤ (2 * P + 1) * L * R * K := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hR),
    mul_nonneg (sub_nonneg.mpr hL) hK,
    mul_nonneg (sub_nonneg.mpr hR) hK,
    mul_nonneg hP hK]

theorem scratch_cubeFaceKernel_domination (α : Anisotropy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin 3) (lam r t : ℝ) (p : E3) (x : E6),
      1 ≤ lam → 0 < t →
      |cubeFaceKernel α i lam r t p x| ≤
        C * lam ^ 37 * translationWeight r ^ 21 * cubeBracketWeight α t p x := by
  rcases scratchCubeKernelProduct_domination α with ⟨C, hC, hdom⟩
  let P : ℝ := |(2 * Real.pi)⁻¹|
  have hP : 0 ≤ P := abs_nonneg _
  have hcoef : 0 ≤ 2 * P + 1 := by nlinarith
  refine ⟨(2 * P + 1) * C ^ 6, mul_nonneg hcoef (pow_nonneg hC _), ?_⟩
  intro i lam r t p x hlam ht
  let R : ℝ := translationWeight r
  let K : ℝ := C ^ 6 * lam ^ 36 * R ^ 20 * cubeBracketWeight α t p x
  let Pfalse : ℝ := scratchCubeKernelProduct α
    (fun q ↦ decide (q = (i, false))) lam r t p x
  let Ptrue : ℝ := scratchCubeKernelProduct α
    (fun q ↦ decide (q = (i, true))) lam r t p x
  let Pall : ℝ := scratchCubeKernelProduct α (fun _ ↦ false) lam r t p x
  have hRone : 1 ≤ R := by
    dsimp [R, translationWeight]
    linarith [abs_nonneg r]
  have hR : 0 ≤ R := le_trans (by norm_num) hRone
  have hlam0 : 0 ≤ lam := le_trans (by norm_num) hlam
  have hW : 0 ≤ cubeBracketWeight α t p x :=
    cubeBracketWeight_nonneg α ht.le p x
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg hC _) (pow_nonneg hlam0 _))
        (pow_nonneg hR _)) hW
  have hfalse : |Pfalse| ≤ K := by
    dsimp [Pfalse]
    simpa only [K, R] using
      hdom (fun q ↦ decide (q = (i, false))) lam r t p x hlam ht
  have htrue : |Ptrue| ≤ K := by
    dsimp [Ptrue]
    simpa only [K, R] using
      hdom (fun q ↦ decide (q = (i, true))) lam r t p x hlam ht
  have hall : |Pall| ≤ K := by
    dsimp [Pall]
    simpa only [K, R] using hdom (fun _ ↦ false) lam r t p x hlam ht
  have hwidth0 : 0 ≤ cubeWidth i lam := (cubeWidth_pos_of_one_le i hlam).le
  have hwidth : cubeWidth i lam ≤ lam := by
    fin_cases i <;> simp [cubeWidth, hlam]
  have hscale : |cubeWidth i lam / (2 * Real.pi)| ≤ lam * P := by
    calc
      |cubeWidth i lam / (2 * Real.pi)| =
          cubeWidth i lam * |(2 * Real.pi)⁻¹| := by
            rw [div_eq_mul_inv, abs_mul, abs_of_nonneg hwidth0]
      _ ≤ lam * |(2 * Real.pi)⁻¹| :=
        mul_le_mul_of_nonneg_right hwidth (abs_nonneg _)
      _ = lam * P := rfl
  have hshift : |cubeCenterShift i r| ≤ R := by
    dsimp [R]
    fin_cases i
    · change |0| ≤ translationWeight r
      unfold translationWeight
      simp only [abs_zero]
      linarith [abs_nonneg r]
    · change |0| ≤ translationWeight r
      unfold translationWeight
      simp only [abs_zero]
      linarith [abs_nonneg r]
    · change |r| ≤ translationWeight r
      unfold translationWeight
      linarith [abs_nonneg r]
  have hsum : |Pfalse| + |Ptrue| ≤ K + K := add_le_add hfalse htrue
  have hterm1 : |cubeWidth i lam / (2 * Real.pi)| *
      (|Pfalse| + |Ptrue|) ≤ lam * P * (K + K) := by
    exact mul_le_mul hscale hsum (by positivity)
      (mul_nonneg hlam0 hP)
  have hterm2 : |cubeCenterShift i r| * |Pall| ≤ R * K := by
    exact mul_le_mul hshift hall (abs_nonneg _) hR
  have hcoefbound :
      lam * P * (K + K) + R * K ≤ (2 * P + 1) * lam * R * K := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlam) (sub_nonneg.mpr hRone),
      mul_nonneg (sub_nonneg.mpr hlam) hK,
      mul_nonneg (sub_nonneg.mpr hRone) hK,
      mul_nonneg hP hK]
  have hdecomp : cubeFaceKernel α i lam r t p x =
      cubeWidth i lam / (2 * Real.pi) * (Pfalse + Ptrue) -
        cubeCenterShift i r * Pall := by
    dsimp [Pfalse, Ptrue, Pall]
    exact scratch_cubeFaceKernel_eq_three_products α i lam r t p x
  calc
    |cubeFaceKernel α i lam r t p x| =
        |cubeWidth i lam / (2 * Real.pi) * (Pfalse + Ptrue) -
          cubeCenterShift i r * Pall| := by rw [hdecomp]
    _ ≤ |cubeWidth i lam / (2 * Real.pi)| * (|Pfalse| + |Ptrue|) +
          |cubeCenterShift i r| * |Pall| := by
      calc
        _ ≤ |cubeWidth i lam / (2 * Real.pi) * (Pfalse + Ptrue)| +
            |cubeCenterShift i r * Pall| := by
              simpa using (abs_sub_le
                (cubeWidth i lam / (2 * Real.pi) * (Pfalse + Ptrue)) 0
                (cubeCenterShift i r * Pall))
        _ = |cubeWidth i lam / (2 * Real.pi)| * |Pfalse + Ptrue| +
            |cubeCenterShift i r| * |Pall| := by rw [abs_mul, abs_mul]
        _ ≤ _ := by gcongr; exact abs_add_le _ _
    _ ≤ lam * P * (K + K) + R * K := add_le_add hterm1 hterm2
    _ ≤ (2 * P + 1) * lam * R * K := hcoefbound
    _ = ((2 * P + 1) * C ^ 6) * lam ^ 37 * translationWeight r ^ 21 *
          cubeBracketWeight α t p x := by
      dsimp [K, R]
      ring

end Twisted
end Auto

namespace Auto
namespace Twisted

/-! ### Patch-ready remainder-kernel majorants

This block depends only on the already-exported sixfold Gaussian estimate
`cubeGaussian_sixfold_domination`, the literal cube kernels, and elementary
ordered-ring algebra.  The two final theorems are intended to be copied into
`Twisted.lean` unchanged. -/

/-- The six literal Gaussian slots, with a Boolean choosing the derivative in
each slot. -/
private def cubeGaussianProduct (α : Anisotropy) (choose : Fin 3 × Bool → Bool)
    (lam r t : ℝ) (p : E3) (x : E6) : ℝ :=
  ∏ q : Fin 3 × Bool,
    if choose q then
      cubeGaussianDerivKernel α lam r t p q.1 (x q)
    else cubeGaussianKernel α lam r t p q.1 (x q)

private theorem cubeGaussianProduct_domination (α : Anisotropy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (choose : Fin 3 × Bool → Bool)
      (lam r t : ℝ) (p : E3) (x : E6), 1 ≤ lam → 0 < t →
      |cubeGaussianProduct α choose lam r t p x| ≤
        C ^ 6 * lam ^ 36 * translationWeight r ^ 20 * cubeBracketWeight α t p x := by
  rcases cubeGaussian_sixfold_domination α with ⟨C, hC, hdom⟩
  refine ⟨C, hC, ?_⟩
  intro choose lam r t p x hlam ht
  unfold cubeGaussianProduct
  rw [Finset.abs_prod]
  exact hdom choose lam r t p x hlam ht

private theorem cubeEndpointKernel_eq_gaussianProduct (α : Anisotropy)
    (lam r t : ℝ) (p : E3) (x : E6) :
    cubeEndpointKernel α lam r t p x =
      cubeGaussianProduct α (fun _ ↦ false) lam r t p x := by
  unfold cubeEndpointKernel cubeCoordinateD cubeGaussianProduct
  rw [Fintype.prod_prod_type]
  simp_rw [Fintype.prod_bool]
  apply Finset.prod_congr rfl
  intro i hi
  simp
  ring

private theorem cubeEndpointKernel_eq_coordinate_mul_erase (α : Anisotropy)
    (i : Fin 3) (lam r t : ℝ) (p : E3) (x : E6) :
    cubeEndpointKernel α lam r t p x =
      cubeGaussianKernel α lam r t p i (x (i, false)) *
        cubeGaussianKernel α lam r t p i (x (i, true)) *
          ∏ m ∈ Finset.univ.erase i, cubeCoordinateD α m lam r t p x := by
  unfold cubeEndpointKernel cubeCoordinateD
  rw [← Finset.mul_prod_erase Finset.univ
    (fun m ↦ cubeGaussianKernel α lam r t p m (x (m, false)) *
      cubeGaussianKernel α lam r t p m (x (m, true))) (Finset.mem_univ i)]

private theorem cubeGaussianProduct_deriv_false_eq (α : Anisotropy)
    (i : Fin 3) (lam r t : ℝ) (p : E3) (x : E6) :
    cubeGaussianProduct α (fun q ↦ decide (q = (i, false))) lam r t p x =
      cubeGaussianDerivKernel α lam r t p i (x (i, false)) *
        cubeGaussianKernel α lam r t p i (x (i, true)) *
          ∏ m ∈ Finset.univ.erase i, cubeCoordinateD α m lam r t p x := by
  unfold cubeGaussianProduct cubeCoordinateD
  rw [Fintype.prod_prod_type]
  let A : Fin 3 → ℝ := fun j ↦
    ∏ b : Bool, if decide ((j, b) = (i, false)) then
      cubeGaussianDerivKernel α lam r t p j (x (j, b))
    else cubeGaussianKernel α lam r t p j (x (j, b))
  change (∏ j : Fin 3, A j) = _
  rw [← Finset.mul_prod_erase Finset.univ A (Finset.mem_univ i)]
  have hAi : A i =
      cubeGaussianDerivKernel α lam r t p i (x (i, false)) *
        cubeGaussianKernel α lam r t p i (x (i, true)) := by
    dsimp [A]
    simp
    ring
  rw [hAi]
  congr 1
  apply Finset.prod_congr rfl
  intro m hm
  have hmi : m ≠ i := (Finset.mem_erase.mp hm).1
  dsimp [A]
  simp [hmi]
  ring

private theorem cubeGaussianProduct_deriv_true_eq (α : Anisotropy)
    (i : Fin 3) (lam r t : ℝ) (p : E3) (x : E6) :
    cubeGaussianProduct α (fun q ↦ decide (q = (i, true))) lam r t p x =
      cubeGaussianKernel α lam r t p i (x (i, false)) *
        cubeGaussianDerivKernel α lam r t p i (x (i, true)) *
          ∏ m ∈ Finset.univ.erase i, cubeCoordinateD α m lam r t p x := by
  unfold cubeGaussianProduct cubeCoordinateD
  rw [Fintype.prod_prod_type]
  let A : Fin 3 → ℝ := fun j ↦
    ∏ b : Bool, if decide ((j, b) = (i, true)) then
      cubeGaussianDerivKernel α lam r t p j (x (j, b))
    else cubeGaussianKernel α lam r t p j (x (j, b))
  change (∏ j : Fin 3, A j) = _
  rw [← Finset.mul_prod_erase Finset.univ A (Finset.mem_univ i)]
  have hAi : A i =
      cubeGaussianKernel α lam r t p i (x (i, false)) *
        cubeGaussianDerivKernel α lam r t p i (x (i, true)) := by
    dsimp [A]
    simp
    ring
  rw [hAi]
  congr 1
  apply Finset.prod_congr rfl
  intro m hm
  have hmi : m ≠ i := (Finset.mem_erase.mp hm).1
  dsimp [A]
  simp [hmi]
  ring

private theorem cubeFaceKernel_eq_threeGaussianProducts (α : Anisotropy)
    (i : Fin 3) (lam r t : ℝ) (p : E3) (x : E6) :
    cubeFaceKernel α i lam r t p x =
      cubeWidth i lam / (2 * Real.pi) *
        (cubeGaussianProduct α (fun q ↦ decide (q = (i, false))) lam r t p x +
          cubeGaussianProduct α (fun q ↦ decide (q = (i, true))) lam r t p x) -
      cubeCenterShift i r * cubeGaussianProduct α (fun _ ↦ false) lam r t p x := by
  rw [cubeGaussianProduct_deriv_false_eq,
    cubeGaussianProduct_deriv_true_eq,
    ← cubeEndpointKernel_eq_gaussianProduct,
    cubeEndpointKernel_eq_coordinate_mul_erase]
  unfold cubeFaceKernel cubeBoundaryKernel cubeCoordinateD
  ring

/-- The endpoint kernel is bounded by the sixfold bracket weight, with the
four scaled slots contributing `λ^36` and the two translated slots
contributing `R(r)^20`. -/
theorem cubeEndpointKernel_domination (α : Anisotropy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam r t : ℝ) (p : E3) (x : E6),
      1 ≤ lam → 0 < t →
      |cubeEndpointKernel α lam r t p x| ≤
        C ^ 6 * lam ^ 36 * translationWeight r ^ 20 * cubeBracketWeight α t p x := by
  rcases cubeGaussianProduct_domination α with ⟨C, hC, hdom⟩
  refine ⟨C, hC, ?_⟩
  intro lam r t p x hlam ht
  rw [cubeEndpointKernel_eq_gaussianProduct]
  exact hdom (fun _ ↦ false) lam r t p x hlam ht

/-- The complete kernel in one face integral has the source remainder
exponents `λ^37 R(r)^21` against the sixfold bracket weight. -/
theorem cubeFaceKernel_domination (α : Anisotropy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin 3) (lam r t : ℝ) (p : E3) (x : E6),
      1 ≤ lam → 0 < t →
      |cubeFaceKernel α i lam r t p x| ≤
        C * lam ^ 37 * translationWeight r ^ 21 * cubeBracketWeight α t p x := by
  rcases cubeGaussianProduct_domination α with ⟨C, hC, hdom⟩
  let P : ℝ := |(2 * Real.pi)⁻¹|
  have hP : 0 ≤ P := abs_nonneg _
  have hcoef : 0 ≤ 2 * P + 1 := by nlinarith
  refine ⟨(2 * P + 1) * C ^ 6, mul_nonneg hcoef (pow_nonneg hC _), ?_⟩
  intro i lam r t p x hlam ht
  let R : ℝ := translationWeight r
  let K : ℝ := C ^ 6 * lam ^ 36 * R ^ 20 * cubeBracketWeight α t p x
  let Pfalse : ℝ := cubeGaussianProduct α
    (fun q ↦ decide (q = (i, false))) lam r t p x
  let Ptrue : ℝ := cubeGaussianProduct α
    (fun q ↦ decide (q = (i, true))) lam r t p x
  let Pall : ℝ := cubeGaussianProduct α (fun _ ↦ false) lam r t p x
  have hRone : 1 ≤ R := by
    dsimp [R, translationWeight]
    linarith [abs_nonneg r]
  have hR : 0 ≤ R := le_trans (by norm_num) hRone
  have hlam0 : 0 ≤ lam := le_trans (by norm_num) hlam
  have hW : 0 ≤ cubeBracketWeight α t p x :=
    cubeBracketWeight_nonneg α ht.le p x
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg hC _) (pow_nonneg hlam0 _))
        (pow_nonneg hR _)) hW
  have hfalse : |Pfalse| ≤ K := by
    dsimp [Pfalse]
    simpa only [K, R] using
      hdom (fun q ↦ decide (q = (i, false))) lam r t p x hlam ht
  have htrue : |Ptrue| ≤ K := by
    dsimp [Ptrue]
    simpa only [K, R] using
      hdom (fun q ↦ decide (q = (i, true))) lam r t p x hlam ht
  have hall : |Pall| ≤ K := by
    dsimp [Pall]
    simpa only [K, R] using hdom (fun _ ↦ false) lam r t p x hlam ht
  have hwidth0 : 0 ≤ cubeWidth i lam := (cubeWidth_pos_of_one_le i hlam).le
  have hwidth : cubeWidth i lam ≤ lam := by
    fin_cases i <;> simp [cubeWidth, hlam]
  have hscale : |cubeWidth i lam / (2 * Real.pi)| ≤ lam * P := by
    calc
      |cubeWidth i lam / (2 * Real.pi)| =
          cubeWidth i lam * |(2 * Real.pi)⁻¹| := by
            rw [div_eq_mul_inv, abs_mul, abs_of_nonneg hwidth0]
      _ ≤ lam * |(2 * Real.pi)⁻¹| :=
        mul_le_mul_of_nonneg_right hwidth (abs_nonneg _)
      _ = lam * P := rfl
  have hshift : |cubeCenterShift i r| ≤ R := by
    dsimp [R]
    fin_cases i
    · change |0| ≤ translationWeight r
      unfold translationWeight
      simp only [abs_zero]
      linarith [abs_nonneg r]
    · change |0| ≤ translationWeight r
      unfold translationWeight
      simp only [abs_zero]
      linarith [abs_nonneg r]
    · change |r| ≤ translationWeight r
      unfold translationWeight
      linarith [abs_nonneg r]
  have hsum : |Pfalse| + |Ptrue| ≤ K + K := add_le_add hfalse htrue
  have hterm1 : |cubeWidth i lam / (2 * Real.pi)| *
      (|Pfalse| + |Ptrue|) ≤ lam * P * (K + K) := by
    exact mul_le_mul hscale hsum (by positivity)
      (mul_nonneg hlam0 hP)
  have hterm2 : |cubeCenterShift i r| * |Pall| ≤ R * K := by
    exact mul_le_mul hshift hall (abs_nonneg _) hR
  have hcoefbound :
      lam * P * (K + K) + R * K ≤ (2 * P + 1) * lam * R * K := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlam) (sub_nonneg.mpr hRone),
      mul_nonneg (sub_nonneg.mpr hlam) hK,
      mul_nonneg (sub_nonneg.mpr hRone) hK,
      mul_nonneg hP hK]
  have hdecomp : cubeFaceKernel α i lam r t p x =
      cubeWidth i lam / (2 * Real.pi) * (Pfalse + Ptrue) -
        cubeCenterShift i r * Pall := by
    dsimp [Pfalse, Ptrue, Pall]
    exact cubeFaceKernel_eq_threeGaussianProducts α i lam r t p x
  calc
    |cubeFaceKernel α i lam r t p x| =
        |cubeWidth i lam / (2 * Real.pi) * (Pfalse + Ptrue) -
          cubeCenterShift i r * Pall| := by rw [hdecomp]
    _ ≤ |cubeWidth i lam / (2 * Real.pi)| * (|Pfalse| + |Ptrue|) +
          |cubeCenterShift i r| * |Pall| := by
      calc
        _ ≤ |cubeWidth i lam / (2 * Real.pi) * (Pfalse + Ptrue)| +
            |cubeCenterShift i r * Pall| := by
              simpa using (abs_sub_le
                (cubeWidth i lam / (2 * Real.pi) * (Pfalse + Ptrue)) 0
                (cubeCenterShift i r * Pall))
        _ = |cubeWidth i lam / (2 * Real.pi)| * |Pfalse + Ptrue| +
            |cubeCenterShift i r| * |Pall| := by rw [abs_mul, abs_mul]
        _ ≤ _ := by gcongr; exact abs_add_le _ _
    _ ≤ lam * P * (K + K) + R * K := add_le_add hterm1 hterm2
    _ ≤ (2 * P + 1) * lam * R * K := hcoefbound
    _ = ((2 * P + 1) * C ^ 6) * lam ^ 37 * translationWeight r ^ 21 *
          cubeBracketWeight α t p x := by
      dsimp [K, R]
      ring

end Twisted
end Auto
