import DFR.Auto.Twisted.Twisted

namespace Auto.Twisted

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal RealInnerProductSpace

noncomputable section

/-- Joint continuity of the sixfold comparison weight in center and spatial
variables at one positive scale. -/
theorem scratch_continuous_cubeBracketWeight_center_space
    (α : Anisotropy) {t : ℝ} (ht : 0 < t) :
    Continuous (fun z : E3 × E6 ↦ cubeBracketWeight α t z.1 z.2) := by
  unfold cubeBracketWeight bracketKernelAt kernelAt kernelDilate
  apply continuous_finsetProd
  intro q _
  have hx : Continuous (fun z : E3 × E6 ↦ z.2 q) :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 × Bool ↦ ℝ) q).comp
      continuous_snd
  have hp : Continuous (fun z : E3 × E6 ↦ z.1 q.1) :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 ↦ ℝ) q.1).comp
      continuous_fst
  have harg : Continuous (fun z : E3 × E6 ↦
      (z.2 q - z.1 q.1) / t ^ α.weight q.1) :=
    (hx.sub hp).div_const _
  have hprod : Continuous (fun z : E3 × E6 ↦
      (t ^ α.weight q.1)⁻¹ * bracketKernel
        ((z.2 q - z.1 q.1) / t ^ α.weight q.1)) :=
    (continuous_const : Continuous (fun _ : E3 × E6 ↦
      (t ^ α.weight q.1)⁻¹)).mul (continuous_bracketKernel.comp harg)
  simpa only [smul_eq_mul] using hprod

/-- On a finite center box, the positive sixfold comparison weight is jointly
integrable in the center and all six spatial variables. -/
theorem scratch_integrable_cubeBracketWeight_center_space
    (α : Anisotropy) (q : AnisoBox α) {t : ℝ} (ht : 0 < t) :
    Integrable (fun z : E3 × E6 ↦ cubeBracketWeight α t z.1 z.2)
      ((volume.restrict (boxSet α q)).prod volume) := by
  letI : IsFiniteMeasure (volume.restrict (boxSet α q)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr (volume_boxSet_ne_top α q)
  have hmeas : AEStronglyMeasurable
      (fun z : E3 × E6 ↦ cubeBracketWeight α t z.1 z.2)
      ((volume.restrict (boxSet α q)).prod volume) :=
    (scratch_continuous_cubeBracketWeight_center_space α ht).aestronglyMeasurable
  refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
  · filter_upwards [] with p
    exact integrable_cubeBracketWeight α ht p
  · have hconst : (fun p : E3 ↦
        ∫ x : E6, ‖cubeBracketWeight α t p x‖) =
          fun _ ↦ (2 / 9 : ℝ) ^ 6 := by
      funext p
      rw [show (fun x : E6 ↦ ‖cubeBracketWeight α t p x‖) =
        cubeBracketWeight α t p by
          funext x
          rw [Real.norm_eq_abs, abs_of_nonneg]
          exact cubeBracketWeight_nonneg α ht.le p x]
      exact integral_cubeBracketWeight α ht p
    rw [hconst]
    exact integrable_const _

end

end Auto.Twisted
