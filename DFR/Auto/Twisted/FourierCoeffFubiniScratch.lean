/- Copyright (c) 2026. All rights reserved. -/
import Auto.Twisted.Twisted
import Mathlib.Analysis.Fourier.AddCircleMulti

namespace Auto
namespace Twisted

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal Topology

noncomputable section

def fubini_unitIoc : Set ℝ := Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)

def fubini_unitIocCube : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ (fun _ : Fin 3 ↦ fubini_unitIoc)

theorem fubini_unitIoc_measurable : MeasurableSet fubini_unitIoc := measurableSet_Ioc

theorem fubini_unitIocCube_measurable : MeasurableSet fubini_unitIocCube := by
  unfold fubini_unitIocCube
  exact MeasurableSet.univ_pi fun _ ↦ fubini_unitIoc_measurable

/-- First literal Fubini split for the half-open unit cube.  The remaining
two-coordinate split will be applied to the `Fin 2` tail. -/
theorem scratch_integral_fin3_unitIocCube_eq_first_split
    (F : (Fin 3 → ℝ) → ℂ) (hF : IntegrableOn F fubini_unitIocCube) :
    ∫ u in fubini_unitIocCube, F u =
      ∫ x : ℝ, ∫ r : Fin 2 → ℝ,
        F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).symm (x, r))
          ∂Measure.pi (fun _ ↦
            volume.restrict fubini_unitIoc)
          ∂(volume.restrict fubini_unitIoc) := by
  let μ : Fin 3 → Measure ℝ := fun _ ↦ volume.restrict fubini_unitIoc
  have hμ : volume.restrict fubini_unitIocCube = Measure.pi μ := by
    unfold fubini_unitIocCube μ
    rw [volume_pi, Measure.restrict_pi_pi]
  have hFpi : Integrable F (Measure.pi μ) := by
    simpa only [IntegrableOn, hμ] using hF
  let e₃ := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0
  let hmp₃ : MeasurePreserving e₃ (Measure.pi μ)
      ((μ 0).prod (Measure.pi fun j ↦ μ ((0 : Fin 3).succAbove j))) :=
    measurePreserving_piFinSuccAbove μ 0
  have hF₃ : Integrable (fun q : ℝ × (Fin 2 → ℝ) ↦ F (e₃.symm q))
      ((μ 0).prod (Measure.pi fun j ↦ μ ((0 : Fin 3).succAbove j))) := by
    exact hmp₃.symm.integrable_comp_of_integrable hFpi
  change ∫ u, F u ∂volume.restrict fubini_unitIocCube = _
  rw [hμ]
  calc
    ∫ u, F u ∂Measure.pi μ =
        ∫ q : ℝ × (Fin 2 → ℝ), F (e₃.symm q)
          ∂((μ 0).prod (Measure.pi fun j ↦ μ ((0 : Fin 3).succAbove j))) := by
      symm
      exact hmp₃.symm.integral_comp' F
    _ = ∫ x : ℝ, ∫ r : Fin 2 → ℝ, F (e₃.symm (x, r))
          ∂Measure.pi (fun j ↦ μ ((0 : Fin 3).succAbove j)) ∂μ 0 := by
      exact MeasureTheory.integral_prod _ hF₃
    _ = _ := by rfl

/-- The two-coordinate product-measure Fubini step, stated separately so
the `Fin 3` calculation can use it almost everywhere in its outer variable. -/
theorem scratch_integral_fin2_pi_eq_iterated
    (μ : Fin 2 → Measure ℝ) [∀ j, SigmaFinite (μ j)]
    (G : (Fin 2 → ℝ) → ℂ) (hG : Integrable G (Measure.pi μ)) :
    ∫ r, G r ∂Measure.pi μ =
      ∫ y : ℝ, ∫ z : ℝ, G ![y, z] ∂μ 1 ∂μ 0 := by
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)
  let hmp : MeasurePreserving e (Measure.pi μ) ((μ 0).prod (μ 1)) :=
    measurePreserving_piFinTwo μ
  have hG' : Integrable (fun q : ℝ × ℝ ↦ G (e.symm q)) ((μ 0).prod (μ 1)) := by
    exact hmp.symm.integrable_comp_of_integrable hG
  calc
    ∫ r, G r ∂Measure.pi μ = ∫ q : ℝ × ℝ, G (e.symm q) ∂((μ 0).prod (μ 1)) := by
      symm
      exact hmp.symm.integral_comp' G
    _ = ∫ y : ℝ, ∫ z : ℝ, G (e.symm (y, z)) ∂μ 1 ∂μ 0 := by
      exact MeasureTheory.integral_prod _ hG'
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      apply integral_congr_ae
      filter_upwards [] with z
      congr 1

/-- Full literal three-coordinate Fubini formula for the half-open unit cube.
All measure changes are explicit: restriction becomes a product of restricted
Lebesgue measures, followed by the finite-coordinate measurable equivalences. -/
theorem scratch_integral_fin3_unitIocCube_eq_iterated
    (F : (Fin 3 → ℝ) → ℂ) (hF : IntegrableOn F fubini_unitIocCube) :
    ∫ u in fubini_unitIocCube, F u =
      ∫ x in fubini_unitIoc,
        ∫ y in fubini_unitIoc,
          ∫ z in fubini_unitIoc, F ![x, y, z] := by
  let μ : Fin 3 → Measure ℝ := fun _ ↦ volume.restrict fubini_unitIoc
  let e₃ := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0
  let μtail : Fin 2 → Measure ℝ := fun j ↦ μ ((0 : Fin 3).succAbove j)
  have hμ : volume.restrict fubini_unitIocCube = Measure.pi μ := by
    unfold fubini_unitIocCube μ
    rw [volume_pi, Measure.restrict_pi_pi]
  have hFpi : Integrable F (Measure.pi μ) := by
    simpa only [IntegrableOn, hμ] using hF
  have hmp₃ : MeasurePreserving e₃ (Measure.pi μ) ((μ 0).prod (Measure.pi μtail)) := by
    exact measurePreserving_piFinSuccAbove μ 0
  have hF₃ : Integrable (fun q : ℝ × (Fin 2 → ℝ) ↦ F (e₃.symm q))
      ((μ 0).prod (Measure.pi μtail)) := by
    exact hmp₃.symm.integrable_comp_of_integrable hFpi
  change ∫ u, F u ∂volume.restrict fubini_unitIocCube = _
  rw [hμ]
  calc
    ∫ u, F u ∂Measure.pi μ =
        ∫ q : ℝ × (Fin 2 → ℝ), F (e₃.symm q) ∂((μ 0).prod (Measure.pi μtail)) := by
      symm
      exact hmp₃.symm.integral_comp' F
    _ = ∫ x : ℝ, ∫ r : Fin 2 → ℝ, F (e₃.symm (x, r))
          ∂Measure.pi μtail ∂μ 0 := by
      exact MeasureTheory.integral_prod _ hF₃
    _ = ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
          F (e₃.symm (x, ![y, z])) ∂μtail 1 ∂μtail 0 ∂μ 0 := by
      apply integral_congr_ae
      filter_upwards [hF₃.prod_right_ae] with x hx
      exact scratch_integral_fin2_pi_eq_iterated μtail
        (fun r ↦ F (e₃.symm (x, r))) hx
    _ = ∫ x in fubini_unitIoc,
          ∫ y in fubini_unitIoc,
            ∫ z in fubini_unitIoc, F ![x, y, z] := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with y
      apply integral_congr_ae
      filter_upwards [] with z
      congr 1
      ext j
      fin_cases j <;> rfl

/-- The cyclic coordinate permutation which changes the standard Fubini
order `(0,1,2)` into the order `(1,2,0)`. -/
noncomputable def fubini_rotateCoordinates :
    (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin 3 ↦ ℝ)
    ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))

theorem fubini_rotateCoordinates_apply (x y z : ℝ) :
    fubini_rotateCoordinates ![x, y, z] = ![z, x, y] := by
  ext j
  fin_cases j <;> rfl

/-- The same literal Fubini formula in the order `(1,2,0)`.  This is the
order in which a first-coordinate Fourier coefficient becomes the innermost
integral. -/
theorem scratch_integral_fin3_unitIocCube_eq_iterated_120
    (F : (Fin 3 → ℝ) → ℂ) (hF : IntegrableOn F fubini_unitIocCube) :
    ∫ u in fubini_unitIocCube, F u =
      ∫ y in fubini_unitIoc,
        ∫ z in fubini_unitIoc,
          ∫ x in fubini_unitIoc, F ![x, y, z] := by
  let μ : Fin 3 → Measure ℝ := fun _ ↦ volume.restrict fubini_unitIoc
  have hμ : volume.restrict fubini_unitIocCube = Measure.pi μ := by
    unfold fubini_unitIocCube μ
    rw [volume_pi, Measure.restrict_pi_pi]
  have hFpi : Integrable F (Measure.pi μ) := by
    simpa only [IntegrableOn, hμ] using hF
  let e := fubini_rotateCoordinates
  have hmp : MeasurePreserving e (Measure.pi μ) (Measure.pi μ) := by
    exact measurePreserving_piCongrLeft μ
      ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have hFcomp : Integrable (F ∘ e) (Measure.pi μ) :=
    hmp.integrable_comp_of_integrable hFpi
  have hFcompOn : IntegrableOn (F ∘ e) fubini_unitIocCube := by
    simpa only [IntegrableOn, hμ] using hFcomp
  calc
    ∫ u in fubini_unitIocCube, F u = ∫ u in fubini_unitIocCube, F (e u) := by
      change ∫ u, F u ∂volume.restrict fubini_unitIocCube =
        ∫ u, F (e u) ∂volume.restrict fubini_unitIocCube
      rw [hμ]
      symm
      exact hmp.integral_comp' F
    _ = ∫ x in fubini_unitIoc,
          ∫ y in fubini_unitIoc,
            ∫ z in fubini_unitIoc, (F ∘ e) ![x, y, z] :=
      scratch_integral_fin3_unitIocCube_eq_iterated (F ∘ e) hFcompOn
    _ = ∫ y in fubini_unitIoc,
          ∫ z in fubini_unitIoc,
            ∫ x in fubini_unitIoc, F ![x, y, z] := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with y
      apply integral_congr_ae
      filter_upwards [] with z
      rw [Function.comp_apply, fubini_rotateCoordinates_apply]

end
end Twisted
end Auto
