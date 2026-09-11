import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

universe u

namespace Scratch

open MeasureTheory FiniteDimensional Filter TopologicalSpace
open scoped Topology

noncomputable section

theorem uniform_second_decay
    {D E V : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
    [SMulCommClass ℝ ℂ V]
    (F : SchwartzMap (D × E) V) (r n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : D × E,
      ‖iteratedFDeriv ℝ n F z‖ ≤ C / (1 + ‖z.2‖) ^ r := by
  let C : ℝ := 2 ^ r *
    (Finset.Iic (r, n)).sup (fun q ↦ SchwartzMap.seminorm ℂ q.1 q.2) F
  have hC : 0 ≤ C := by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
      (m := (r, n)) le_rfl le_rfl F (0 : D × E)
    have hnonneg : 0 ≤ (1 + ‖(0 : D × E)‖) ^ r *
        ‖iteratedFDeriv ℝ n F (0 : D × E)‖ :=
      mul_nonneg (pow_nonneg (by positivity) _) (norm_nonneg _)
    exact hnonneg.trans (by simpa [C] using h)
  refine ⟨C, hC, fun z ↦ ?_⟩
  apply (le_div_iff₀ (by positivity)).mpr
  rw [mul_comm]
  calc
    (1 + ‖z.2‖) ^ r * ‖iteratedFDeriv ℝ n F z‖ ≤
        (1 + ‖z‖) ^ r * ‖iteratedFDeriv ℝ n F z‖ := by
      gcongr
      rw [Prod.norm_def]
      exact le_max_right _ _
    _ ≤ C := by
      simpa [C] using (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
        (m := (r, n)) le_rfl le_rfl F z)

theorem weighted_second_decay
    {D E V : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
    [SMulCommClass ℝ ℂ V]
    (F : SchwartzMap (D × E) V) (k r n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : D × E,
      ‖z.1‖ ^ k * ‖iteratedFDeriv ℝ n F z‖ ≤ C / (1 + ‖z.2‖) ^ r := by
  let C : ℝ := 2 ^ (k + r) *
    (Finset.Iic (k + r, n)).sup (fun q ↦ SchwartzMap.seminorm ℂ q.1 q.2) F
  have hC : 0 ≤ C := by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
      (m := (k + r, n)) le_rfl le_rfl F (0 : D × E)
    have hnonneg : 0 ≤ (1 + ‖(0 : D × E)‖) ^ (k + r) *
        ‖iteratedFDeriv ℝ n F (0 : D × E)‖ :=
      mul_nonneg (pow_nonneg (by positivity) _) (norm_nonneg _)
    exact hnonneg.trans (by simpa [C] using h)
  refine ⟨C, hC, fun z ↦ ?_⟩
  apply (le_div_iff₀ (by positivity)).mpr
  have hz1 : ‖z.1‖ ≤ 1 + ‖z‖ := by
    rw [Prod.norm_def]
    exact le_trans (le_max_left _ _) (by linarith [norm_nonneg z])
  have hz2 : 1 + ‖z.2‖ ≤ 1 + ‖z‖ := by
    rw [Prod.norm_def]
    gcongr
    exact le_max_right _ _
  calc
    (‖z.1‖ ^ k * ‖iteratedFDeriv ℝ n F z‖) * (1 + ‖z.2‖) ^ r =
        (‖z.1‖ ^ k * (1 + ‖z.2‖) ^ r) * ‖iteratedFDeriv ℝ n F z‖ := by ring
    _ ≤ ((1 + ‖z‖) ^ k * (1 + ‖z‖) ^ r) * ‖iteratedFDeriv ℝ n F z‖ := by
      gcongr
    _ = (1 + ‖z‖) ^ (k + r) * ‖iteratedFDeriv ℝ n F z‖ := by rw [← pow_add]
    _ ≤ C := by
      simpa [C] using (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
        (m := (k + r, n)) le_rfl le_rfl F z)

theorem integrable_second_weight
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] (C : ℝ) :
    Integrable (fun v : E ↦ C / (1 + ‖v‖) ^ (Module.finrank ℝ E + 1)) μ := by
  have hr : (Module.finrank ℝ E : ℝ) < (↑(Module.finrank ℝ E + 1) : ℝ) := by
    exact_mod_cast Nat.lt_succ_self (Module.finrank ℝ E)
  have h := (integrable_one_add_norm (E := E) (μ := μ) hr).const_mul C
  convert h using 1
  ext v
  rw [Real.rpow_neg (by positivity), ← Real.rpow_natCast]
  ring

noncomputable def fiberFDeriv
    {D E V : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
    [SMulCommClass ℝ ℂ V]
    (F : SchwartzMap (D × E) V) : SchwartzMap (D × E) (D →L[ℝ] V) :=
  (SchwartzMap.fderivCLM ℂ (D × E) V F).postcompCLM
    ((ContinuousLinearMap.compL ℝ D (D × E) V).flip (ContinuousLinearMap.inl ℝ D E))

@[simp]
theorem fiberFDeriv_apply
    {D E V : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
    [SMulCommClass ℝ ℂ V]
    (F : SchwartzMap (D × E) V) (z : D × E) (h : D) :
    fiberFDeriv F z h = fderiv ℝ F z (h, 0) := by
  rfl

theorem hasFDerivAt_fiber_slice
    {D E V : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
    [SMulCommClass ℝ ℂ V]
    (F : SchwartzMap (D × E) V) (u : D) (v : E) :
    HasFDerivAt (fun x : D ↦ F (x, v)) (fiberFDeriv F (u, v)) u := by
  have hlin : HasFDerivAt (fun x : D ↦ (x, v))
      (ContinuousLinearMap.inl ℝ D E) u := by
    simpa [ContinuousLinearMap.inl_apply] using
      ((ContinuousLinearMap.inl ℝ D E).hasFDerivAt (x := u) |>.add_const (0, v))
  convert (F.hasFDerivAt (u, v)).comp u hlin using 1
  · rfl
  · ext h
    rfl

noncomputable def fixedFiber
    {D E V : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
    [SMulCommClass ℝ ℂ V]
    (F : SchwartzMap (D × E) V) (u : D) : SchwartzMap E V := by
  let L := ContinuousLinearMap.inr ℝ D E
  have hL : Function.Injective L := by
    intro v w h
    change (0, v) = (0, w) at h
    exact Prod.ext_iff.mp h |>.2
  let hAnti := (L.toLinearMap.injective_iff_antilipschitz).mp hL
  exact SchwartzMap.compCLMOfAntilipschitz ℂ L.hasTemperateGrowth
    (Classical.choose_spec hAnti).2 (F.compSubConstCLM ℂ (-(u, 0)))

@[simp]
theorem fixedFiber_apply
    {D E V : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
    [SMulCommClass ℝ ℂ V]
    (F : SchwartzMap (D × E) V) (u : D) (v : E) :
    fixedFiber F u v = F (u, v) := by
  simp [fixedFiber]

noncomputable def fiberIntegral
    {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
    [SMulCommClass ℝ ℂ V]
    (μ : Measure E) (F : SchwartzMap (D × E) V) : D → V :=
  fun u ↦ ∫ v, F (u, v) ∂μ

theorem fiberIntegral_hasFDerivAt
    {D E V : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
    [SMulCommClass ℝ ℂ V]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    (F : SchwartzMap (D × E) V) (u : D) :
    HasFDerivAt (fiberIntegral μ F)
      (∫ v, fiberFDeriv F (u, v) ∂μ) u := by
  obtain ⟨C, hC, hdecay⟩ :=
    uniform_second_decay (fiberFDeriv F) (Module.finrank ℝ E + 1) 0
  let bound : E → ℝ := fun v ↦ C / (1 + ‖v‖) ^ (Module.finrank ℝ E + 1)
  have hF_meas : ∀ᶠ x in 𝓝 u, AEStronglyMeasurable (fun v ↦ F (x, v)) μ :=
    Filter.Eventually.of_forall fun x ↦ by
      simpa only [← fixedFiber_apply] using
        ((fixedFiber F x).integrable (μ := μ)).aestronglyMeasurable
  have hF_int : Integrable (fun v ↦ F (u, v)) μ := by
    simpa only [← fixedFiber_apply] using (fixedFiber F u).integrable (μ := μ)
  have hF'_meas : AEStronglyMeasurable (fun v ↦ fiberFDeriv F (u, v)) μ := by
    simpa only [← fixedFiber_apply] using
      ((fixedFiber (fiberFDeriv F) u).integrable (μ := μ)).aestronglyMeasurable
  have hbound : ∀ᵐ v ∂μ, ∀ x ∈ Set.univ,
      ‖fiberFDeriv F (x, v)‖ ≤ bound v :=
    Filter.Eventually.of_forall fun v x _ ↦ by
      simpa only [bound, norm_iteratedFDeriv_zero] using hdecay (x, v)
  have hbound_int : Integrable bound μ := by
    simpa only [bound] using integrable_second_weight (μ := μ) C
  have hdiff : ∀ᵐ v ∂μ, ∀ x ∈ Set.univ,
      HasFDerivAt (fun y : D ↦ F (y, v)) (fiberFDeriv F (x, v)) x :=
    Filter.Eventually.of_forall fun v x _ ↦ hasFDerivAt_fiber_slice F x v
  change HasFDerivAt (fun x : D ↦ ∫ v : E, F (x, v) ∂μ)
    (∫ v, fiberFDeriv F (u, v) ∂μ) u
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ)
    univ_mem hF_meas hF_int hF'_meas hbound hbound_int hdiff

theorem fiberIntegral_contDiff_nat
    {D E V : Type u}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
    [SMulCommClass ℝ ℂ V]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    (F : SchwartzMap (D × E) V) (n : ℕ) :
    ContDiff ℝ n (fiberIntegral μ F) := by
  induction n generalizing V with
  | zero =>
      apply contDiff_zero.2
      have hd : Differentiable ℝ (fiberIntegral μ F) :=
        fun u ↦ (fiberIntegral_hasFDerivAt F u).differentiableAt
      exact hd.continuous
  | succ n ih =>
      apply (contDiff_succ_iff_hasFDerivAt (n := n)).2
      refine ⟨fiberIntegral μ (fiberFDeriv F), ?_, ?_⟩
      · exact ih (fiberFDeriv F)
      · intro u
        exact fiberIntegral_hasFDerivAt F u

theorem fiberIntegral_smooth
    {D E V : Type u}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
    [SMulCommClass ℝ ℂ V]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    (F : SchwartzMap (D × E) V) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fiberIntegral μ F) := by
  rw [contDiff_infty]
  intro n
  exact fiberIntegral_contDiff_nat F n

theorem fiberIntegral_decay_zero
    {D E V : Type u}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
    [SMulCommClass ℝ ℂ V]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    (F : SchwartzMap (D × E) V) (k : ℕ) :
    ∃ C : ℝ, ∀ u : D,
      ‖u‖ ^ k * ‖fiberIntegral μ F u‖ ≤ C := by
  let r : ℕ := Module.finrank ℝ E + 1
  obtain ⟨C, hC, hdecay⟩ := weighted_second_decay F k r 0
  let major : E → ℝ := fun v ↦ C / (1 + ‖v‖) ^ r
  have hmajor : Integrable major μ := by
    simpa only [major, r] using integrable_second_weight (μ := μ) C
  refine ⟨∫ v, major v ∂μ, fun u ↦ ?_⟩
  have hFu : Integrable (fun v : E ↦ F (u, v)) μ := by
    simpa only [← fixedFiber_apply] using (fixedFiber F u).integrable (μ := μ)
  have hnorm : Integrable (fun v : E ↦ ‖u‖ ^ k * ‖F (u, v)‖) μ :=
    hFu.norm.const_mul _
  calc
    ‖u‖ ^ k * ‖fiberIntegral μ F u‖ = ‖u‖ ^ k * ‖∫ v : E, F (u, v) ∂μ‖ := rfl
    _ ≤ ‖u‖ ^ k * ∫ v : E, ‖F (u, v)‖ ∂μ := by
      gcongr
      exact norm_integral_le_integral_norm _
    _ = ∫ v : E, ‖u‖ ^ k * ‖F (u, v)‖ ∂μ := by
      rw [integral_const_mul]
    _ ≤ ∫ v, major v ∂μ := by
      apply integral_mono hnorm hmajor
      intro v
      simpa only [major, norm_iteratedFDeriv_zero] using hdecay (u, v)

theorem fiberIntegral_decay
    {D E V : Type u}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
    [SMulCommClass ℝ ℂ V]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    (F : SchwartzMap (D × E) V) (k n : ℕ) :
    ∃ C : ℝ, ∀ u : D,
      ‖u‖ ^ k * ‖iteratedFDeriv ℝ n (fiberIntegral μ F) u‖ ≤ C := by
  induction n generalizing V with
  | zero =>
      simpa only [norm_iteratedFDeriv_zero] using fiberIntegral_decay_zero F k
  | succ n ih =>
      obtain ⟨C, hC⟩ := ih (V := D →L[ℝ] V) (fiberFDeriv F)
      refine ⟨C, fun u ↦ ?_⟩
      rw [← norm_iteratedFDeriv_fderiv]
      have heq : fderiv ℝ (fiberIntegral μ F) =
          fiberIntegral μ (fiberFDeriv F) := by
        funext u
        exact (fiberIntegral_hasFDerivAt F u).fderiv
      rw [heq]
      exact hC u

noncomputable def schwartzIteratedFDeriv
    {X V : Type u}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (n : ℕ) → SchwartzMap X V → SchwartzMap X (X [×n]→L[ℝ] V)
  | 0, F =>
      F.postcompCLM
        (LinearIsometryEquiv.toContinuousLinearEquiv
          (continuousMultilinearCurryFin0 ℝ X V).symm).toContinuousLinearMap
  | n + 1, F =>
      (SchwartzMap.fderivCLM ℝ X (X [×n]→L[ℝ] V)
        (schwartzIteratedFDeriv n F)).postcompCLM
        (LinearIsometryEquiv.toContinuousLinearEquiv
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ X) V).symm).toContinuousLinearMap

theorem schwartzIteratedFDeriv_apply
    {X V : Type u}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (F : SchwartzMap X V) (x : X) :
    schwartzIteratedFDeriv n F x = iteratedFDeriv ℝ n F x := by
  induction n generalizing V x with
  | zero =>
      ext m
      simp [schwartzIteratedFDeriv, iteratedFDeriv_zero_apply]
  | succ n ih =>
      have hfun : (schwartzIteratedFDeriv n F : X → X [×n]→L[ℝ] V) =
          iteratedFDeriv ℝ n F := by
        funext y
        exact ih F y
      rw [iteratedFDeriv_succ_eq_comp_left]
      simp only [schwartzIteratedFDeriv, SchwartzMap.postcompCLM_apply,
        SchwartzMap.fderivCLM_apply, hfun]
      rfl

abbrev E3 := EuclideanSpace ℝ (Fin 3)

def coordinateDirection (i : Fin 3) : E3 :=
  WithLp.toLp 2 fun j ↦ if j = i then 1 else 0

def coordinateProjection (i : Fin 3) : E3 →L[ℝ] ℝ where
  toFun := fun x ↦ x i
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro c x
    rfl
  cont := PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 ↦ ℝ) i

@[simp]
theorem coordinateProjection_apply (i : Fin 3) (x : E3) :
    coordinateProjection i x = x i := rfl

@[simp]
theorem coordinateDirection_apply (i j : Fin 3) :
    coordinateDirection i j = if j = i then 1 else 0 := rfl

def basisCoordinateDirection (i : Fin 3) : E3 :=
  EuclideanSpace.basisFun (Fin 3) ℝ i

@[simp]
theorem basisCoordinateDirection_apply (i j : Fin 3) :
    basisCoordinateDirection i j = if j = i then 1 else 0 := by
  simp [basisCoordinateDirection]

noncomputable def shiftedCoordinate (i : Fin 3) : E3 × E3 →L[ℝ] E3 :=
  ContinuousLinearMap.snd ℝ E3 E3 +
    ((coordinateProjection i ∘L ContinuousLinearMap.fst ℝ E3 E3).smulRight
      (basisCoordinateDirection i))

@[simp]
theorem shiftedCoordinate_apply (i : Fin 3) (z : E3 × E3) :
    shiftedCoordinate i z = z.2 + z.1 i • basisCoordinateDirection i := by
  simp [shiftedCoordinate]

noncomputable def shiftedProductMap : E3 × E3 →L[ℝ] (E3 × E3) × (E3 × E3) :=
  ((ContinuousLinearMap.snd ℝ E3 E3).prod (shiftedCoordinate 0)).prod
    ((shiftedCoordinate 1).prod (shiftedCoordinate 2))

@[simp]
theorem shiftedProductMap_apply (z : E3 × E3) :
    shiftedProductMap z =
      ((z.2, shiftedCoordinate 0 z), (shiftedCoordinate 1 z, shiftedCoordinate 2 z)) := by
  simp [shiftedProductMap]

theorem shiftedProductMap_injective : Function.Injective shiftedProductMap := by
  intro z w h
  have hbase : z.2 = w.2 := by
    have h' := congrArg (fun q : (E3 × E3) × (E3 × E3) ↦ q.1.1) h
    simpa only [shiftedProductMap_apply] using h'
  have hshift : ∀ i : Fin 3, shiftedCoordinate i z = shiftedCoordinate i w := by
    intro i
    fin_cases i
    · have h' := congrArg (fun q : (E3 × E3) × (E3 × E3) ↦ q.1.2) h
      change shiftedCoordinate 0 z = shiftedCoordinate 0 w
      simpa only [shiftedProductMap_apply] using h'
    · have h' := congrArg (fun q : (E3 × E3) × (E3 × E3) ↦ q.2.1) h
      change shiftedCoordinate 1 z = shiftedCoordinate 1 w
      simpa only [shiftedProductMap_apply] using h'
    · have h' := congrArg (fun q : (E3 × E3) × (E3 × E3) ↦ q.2.2) h
      change shiftedCoordinate 2 z = shiftedCoordinate 2 w
      simpa only [shiftedProductMap_apply] using h'
  apply Prod.ext
  · ext i
    have hi := congrArg (fun q : E3 ↦ q i) (hshift i)
    rw [shiftedCoordinate_apply, shiftedCoordinate_apply, hbase] at hi
    apply add_left_cancel (a := z.2 i)
    simpa [basisCoordinateDirection_apply] using hi
  · exact hbase

noncomputable def coordinateShear (i : Fin 3) : E3 × ℝ →L[ℝ] E3 × ℝ :=
  (ContinuousLinearMap.fst ℝ E3 ℝ -
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateDirection i) ∘L
        ContinuousLinearMap.snd ℝ E3 ℝ)).prod
    (ContinuousLinearMap.snd ℝ E3 ℝ)

@[simp]
theorem coordinateShear_apply (i : Fin 3) (z : E3 × ℝ) :
    coordinateShear i z = (z.1 - z.2 • coordinateDirection i, z.2) := by
  simp [coordinateShear]

theorem coordinateShear_injective (i : Fin 3) : Function.Injective (coordinateShear i) := by
  intro z w h
  have hsecond : z.2 = w.2 := by
    simpa only [coordinateShear_apply] using congrArg Prod.snd h
  apply Prod.ext
  · have hfirst := congrArg Prod.fst h
    have hfirst' : z.1 - w.2 • coordinateDirection i =
        w.1 - w.2 • coordinateDirection i := by
      simpa only [coordinateShear_apply, hsecond] using hfirst
    calc
      z.1 = (z.1 - w.2 • coordinateDirection i) + w.2 • coordinateDirection i :=
        (sub_add_cancel _ _).symm
      _ = (w.1 - w.2 • coordinateDirection i) + w.2 • coordinateDirection i := by
        rw [hfirst']
      _ = w.1 := sub_add_cancel _ _
  · exact hsecond

end

end Scratch

#check MeasureTheory.Integrable.mono
#check MeasureTheory.Integrable.mono'
#check MeasureTheory.Measurable.aestronglyMeasurable
#check MeasureTheory.AEStronglyMeasurable.mul
#check MeasureTheory.Integrable.const_mul
#check MeasureTheory.Integrable.norm
#check MeasureTheory.Integrable.bdd_mul
#check WithSeminorms.continuous_normedSpace_rng
#check MeasureTheory.memLp_top_of_bound
#check MeasureTheory.MemLp.toLp
#check MeasureTheory.MemLp.coeFn_toLp
#check MeasureTheory.Lp.toTemperedDistribution_apply
#check FourierTransform.fourierInv_apply
#check SchwartzMap.fourierInv_apply
