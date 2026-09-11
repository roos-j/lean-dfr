import Auto.Twisted.Twisted

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

namespace Auto
namespace Twisted

/-- Real scalar multiplication commutes exactly with each one-coordinate
model convolution. -/
theorem scratch_ModelCoordinateConvolution_smul
    (i : Fin 3) (a : ℝ) (f : E3 → ℝ) (k : ℝ → ℝ)
    (s : ℝ) (x : E3) :
    ModelCoordinateConvolution i (a • f) k s x =
      a * ModelCoordinateConvolution i f k s x := by
  unfold ModelCoordinateConvolution
  rw [show (fun r : ℝ ↦ (a • f) (x - r • Anisotropy.coordinateDirection i) *
      kernelDilate k s r) =
      fun r ↦ a * (f (x - r • Anisotropy.coordinateDirection i) *
        kernelDilate k s r) by
      funext r
      simp only [Pi.smul_apply, smul_eq_mul]
      ring, integral_const_mul]

/-- Independently rescale the four real Schwartz inputs of the model form. -/
noncomputable def scratch_modelInputRescale
    (a : Fin 4 → ℝ) (F : ModelSchwartzInput) : ModelSchwartzInput :=
  fun j ↦ a j • F j

@[simp] theorem scratch_modelInputRescale_apply
    (a : Fin 4 → ℝ) (F : ModelSchwartzInput) (j : Fin 4) (x : E3) :
    scratch_modelInputRescale a F j x = a j * F j x := by
  simp [scratch_modelInputRescale]

/-- The pointwise spatial model integrand is four-linear in independently
rescaled inputs. -/
theorem scratch_ModelSpatialIntegrand_rescale
    (α : Anisotropy) (u : E3) (a : Fin 4 → ℝ)
    (F : ModelSchwartzInput) (t : ℝ) (x : E3) :
    ModelSpatialIntegrand α u (scratch_modelInputRescale a F) t x =
      (∏ j : Fin 4, a j) * ModelSpatialIntegrand α u F t x := by
  have hcomp (j : Fin 4) :
      ((scratch_modelInputRescale a F j : SchwartzMap E3 ℝ) : E3 → ℝ) =
        a j • ((F j : SchwartzMap E3 ℝ) : E3 → ℝ) := by
    funext y
    simp [scratch_modelInputRescale]
  unfold ModelSpatialIntegrand
  rw [hcomp 0, hcomp 1, hcomp 2, hcomp 3,
    scratch_ModelCoordinateConvolution_smul,
    scratch_ModelCoordinateConvolution_smul,
    scratch_ModelCoordinateConvolution_smul]
  simp only [Pi.smul_apply, smul_eq_mul, Fin.prod_univ_four]
  ring

/-- The spatial profile inherits the same four-linear rescaling law. -/
theorem scratch_ModelSpatialProfile_rescale
    (α : Anisotropy) (u : E3) (a : Fin 4 → ℝ)
    (F : ModelSchwartzInput) (t : ℝ) :
    ModelSpatialProfile α u (scratch_modelInputRescale a F) t =
      (∏ j : Fin 4, a j) * ModelSpatialProfile α u F t := by
  unfold ModelSpatialProfile
  rw [show (fun x : E3 ↦ ModelSpatialIntegrand α u
      (scratch_modelInputRescale a F) t x) =
      fun x ↦ (∏ j : Fin 4, a j) * ModelSpatialIntegrand α u F t x by
        funext x
        exact scratch_ModelSpatialIntegrand_rescale α u a F t x,
      integral_const_mul]

/-- The full real Schwartz model form is exactly four-linear under
independent scalar rescaling. -/
theorem scratch_ModelFullForm_rescale
    (α : Anisotropy) (u : E3) (c : ℝ → ℝ)
    (a : Fin 4 → ℝ) (F : ModelSchwartzInput) :
    ModelFullForm α u c (scratch_modelInputRescale a F) =
      (∏ j : Fin 4, a j) * ModelFullForm α u c F := by
  unfold ModelFullForm
  rw [show (fun t : ℝ ↦ c t * ModelSpatialProfile α u
      (scratch_modelInputRescale a F) t) =
      fun t ↦ (∏ j : Fin 4, a j) *
        (c t * ModelSpatialProfile α u F t) by
        funext t
        rw [scratch_ModelSpatialProfile_rescale]
        ring,
      integral_const_mul]

/-- Independent rescaling at the raw real-input level used by finite model
forests. -/
def scratch_modelRealInputRescale
    (a : Fin 4 → ℝ) (f : ModelRealInput) : ModelRealInput :=
  fun j ↦ a j • f j

@[simp] theorem scratch_modelRealInputRescale_apply
    (a : Fin 4 → ℝ) (f : ModelRealInput) (j : Fin 4) (x : E3) :
    scratch_modelRealInputRescale a f j x = a j * f j x := by
  simp [scratch_modelRealInputRescale]

/-- The first fiber is trilinear in its three real input branches. -/
theorem scratch_modelFirstFiber_rescale
    (α : Anisotropy) (a : Fin 4 → ℝ) (f : ModelRealInput)
    (p : E3) (t : ℝ) (z : ModelE5) :
    modelFirstFiber α (scratch_modelRealInputRescale a f) p t z =
      (a 0 * a 1 * a 2) * modelFirstFiber α f p t z := by
  unfold modelFirstFiber
  rw [show (fun v : ℝ ↦
      scratch_modelRealInputRescale a f 0 (modelPoint (z 0) (z 1) v) *
      scratch_modelRealInputRescale a f 1 (modelPoint (z 2) (z 1) v) *
      scratch_modelRealInputRescale a f 2 (modelPoint (z 0) (z 3) v) *
      gaussianDerivAt (t ^ α.weight 2) (p 2) v) =
      fun v ↦ (a 0 * a 1 * a 2) *
        (f 0 (modelPoint (z 0) (z 1) v) *
        f 1 (modelPoint (z 2) (z 1) v) *
        f 2 (modelPoint (z 0) (z 3) v) *
        gaussianDerivAt (t ^ α.weight 2) (p 2) v) by
      funext v
      simp only [scratch_modelRealInputRescale_apply]
      ring, integral_const_mul]

/-- The second fiber is linear in the fourth real input branch. -/
theorem scratch_modelSecondFiber_smul
    (α : Anisotropy) (a : ℝ) (f : E3 → ℝ)
    (p : E3) (t : ℝ) (z : ModelE5) :
    modelSecondFiber α (a • f) p t z =
      a * modelSecondFiber α f p t z := by
  unfold modelSecondFiber
  rw [show (fun v : ℝ ↦
      (a • f) (modelPoint (z 0) (z 1) v) *
        gaussianDerivAt (t ^ α.weight 2)
          (p 2 + z 4 * t ^ α.weight 2) v) =
      fun v ↦ a * (f (modelPoint (z 0) (z 1) v) *
        gaussianDerivAt (t ^ α.weight 2)
          (p 2 + z 4 * t ^ α.weight 2) v) by
      funext v
      simp only [Pi.smul_apply, smul_eq_mul]
      ring, integral_const_mul]

/-- The finite expanded local form has the expected four-linear scaling
law, without any auxiliary integrability premise. -/
theorem scratch_expandedModelLocalForm_rescale
    (α : Anisotropy) (S : BoxCollection α) (u : E3) (c : ℝ → ℝ)
    (a : Fin 4 → ℝ) (f : ModelRealInput) :
    expandedModelLocalForm α S u c (scratch_modelRealInputRescale a f) =
      (∏ j : Fin 4, a j) * expandedModelLocalForm α S u c f := by
  unfold expandedModelLocalForm
  rw [show (fun pt : E3 × ℝ ↦ c pt.2 * (∫ z : ModelE5,
      modelFirstFiber α (scratch_modelRealInputRescale a f) pt.1 pt.2 z *
        modelSecondFiber α (scratch_modelRealInputRescale a f 3) pt.1 pt.2 z *
          modelSignedDensity α u pt.1 pt.2 z)) =
      fun pt ↦ (∏ j : Fin 4, a j) *
        (c pt.2 * (∫ z : ModelE5,
          modelFirstFiber α f pt.1 pt.2 z *
            modelSecondFiber α (f 3) pt.1 pt.2 z *
              modelSignedDensity α u pt.1 pt.2 z)) by
      funext pt
      rw [show (fun z : ModelE5 ↦
        modelFirstFiber α (scratch_modelRealInputRescale a f) pt.1 pt.2 z *
          modelSecondFiber α (scratch_modelRealInputRescale a f 3) pt.1 pt.2 z *
            modelSignedDensity α u pt.1 pt.2 z) =
          fun z ↦ (a 0 * a 1 * a 2 * a 3) *
            (modelFirstFiber α f pt.1 pt.2 z *
              modelSecondFiber α (f 3) pt.1 pt.2 z *
                modelSignedDensity α u pt.1 pt.2 z) by
          funext z
          rw [scratch_modelFirstFiber_rescale,
            show scratch_modelRealInputRescale a f 3 = a 3 • f 3 by
              funext y
              simp [scratch_modelRealInputRescale],
            scratch_modelSecondFiber_smul]
          ring,
        integral_const_mul]
      simp only [Fin.prod_univ_four]
      ring,
    integral_const_mul]
  ring

/-- Rescaling commutes with the coercion from a real Schwartz tuple to the
finite-forest input tuple. -/
theorem scratch_InitialModelRealInput_rescale
    (a : Fin 4 → ℝ) (F : InitialModelSchwartzInput) :
    InitialModelRealInput (scratch_modelInputRescale a F) =
      scratch_modelRealInputRescale a (InitialModelRealInput F) := by
  funext j x
  simp [scratch_modelInputRescale, scratch_modelRealInputRescale,
    InitialModelRealInput]

/-- The finite forest form has the same rescaling law when presented by a
real Schwartz tuple. -/
theorem scratch_expandedModelLocalForm_initial_rescale
    (α : Anisotropy) (S : BoxCollection α) (u : E3) (c : ℝ → ℝ)
    (a : Fin 4 → ℝ) (F : InitialModelSchwartzInput) :
    expandedModelLocalForm α S u c
      (InitialModelRealInput (scratch_modelInputRescale a F)) =
      (∏ j : Fin 4, a j) *
        expandedModelLocalForm α S u c (InitialModelRealInput F) := by
  rw [scratch_InitialModelRealInput_rescale]
  exact scratch_expandedModelLocalForm_rescale α S u c a
    (InitialModelRealInput F)

end Twisted
end Auto
