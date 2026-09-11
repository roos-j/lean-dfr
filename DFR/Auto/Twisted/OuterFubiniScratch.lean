import Auto.Twisted.Twisted

namespace Auto.Twisted

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal RealInnerProductSpace

noncomputable section

/-- Transport the jointly integrable local cube integrand through the
active/passive measurable equivalence and then apply product Fubini. -/
theorem scratch_integral_localCubeIntegrand_centerActivePassive_fubini
    (α : Anisotropy) (i : Fin 3) (lam r : ℝ)
    (F : CubeVertex → E3 → ℝ) (μz : Measure (E3 × ℝ)) [SFinite μz]
    (hjoint : Integrable (fun zx : (E3 × ℝ) × E6 ↦
      cubeSignedInputProduct F zx.2 *
        localCubeKernel α i lam r zx.1.2 zx.1.1 zx.2) (μz.prod volume)) :
    (∫ zx : (E3 × ℝ) × E6,
      cubeSignedInputProduct F zx.2 *
        localCubeKernel α i lam r zx.1.2 zx.1.1 zx.2 ∂(μz.prod volume)) =
      ∫ w : (E3 × ℝ) × (TransverseSpace i × TransverseSpace i),
        ∫ v : ℝ × ℝ,
          cubeSignedInputProduct F
              ((cubeCenterActivePassiveSplit i).symm (w, v)).2 *
            localCubeKernel α i lam r
              ((cubeCenterActivePassiveSplit i).symm (w, v)).1.2
              ((cubeCenterActivePassiveSplit i).symm (w, v)).1.1
              ((cubeCenterActivePassiveSplit i).symm (w, v)).2
          ∂((volume : Measure ℝ).prod volume)
        ∂(μz.prod ((volume : Measure (TransverseSpace i)).prod volume)) := by
  let g : (E3 × ℝ) × E6 → ℝ := fun zx ↦
    cubeSignedInputProduct F zx.2 *
      localCubeKernel α i lam r zx.1.2 zx.1.1 zx.2
  let e := cubeCenterActivePassiveSplit i
  let μw : Measure ((E3 × ℝ) × (TransverseSpace i × TransverseSpace i)) :=
    μz.prod ((volume : Measure (TransverseSpace i)).prod volume)
  let μv : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume
  have hmp : MeasurePreserving e (μz.prod volume) (μw.prod μv) := by
    simpa only [e, μw, μv, Measure.volume_eq_prod] using
      cubeCenterActivePassiveSplit_measurePreserving i μz
  have htrans : Integrable (fun q :
      ((E3 × ℝ) × (TransverseSpace i × TransverseSpace i)) × (ℝ × ℝ) ↦
        g (e.symm q)) (μw.prod μv) := by
    exact (MeasurePreserving.symm e hmp).integrable_comp_of_integrable hjoint
  calc
    (∫ zx : (E3 × ℝ) × E6, g zx ∂(μz.prod volume)) =
        ∫ q : ((E3 × ℝ) × (TransverseSpace i × TransverseSpace i)) × (ℝ × ℝ),
          g (e.symm q) ∂(μw.prod μv) := by
      exact (MeasurePreserving.symm e hmp).integral_comp
        e.symm.measurableEmbedding g |>.symm
    _ = ∫ w : (E3 × ℝ) × (TransverseSpace i × TransverseSpace i),
        ∫ v : ℝ × ℝ, g (e.symm (w, v)) ∂μv ∂μw :=
      MeasureTheory.integral_prod _ htrans
    _ = _ := by rfl

end

end Auto.Twisted
