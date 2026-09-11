import Auto.Twisted.Twisted

namespace Auto.Twisted

open MeasureTheory Filter FourierTransform TopologicalSpace
open scoped BigOperators Convolution ENNReal FourierTransform LineDeriv RealInnerProductSpace Topology

noncomputable section

/-- The five real variables `(x₁,x₂,y₁,y₂,r)` in the local model form. -/
abbrev ModelE5 := EuclideanSpace ℝ (Fin 5)

/-- Assemble three scalar coordinates into the ambient source space. -/
noncomputable def modelPoint (a b c : ℝ) : E3 :=
  WithLp.toLp 2 fun i ↦
    if i = 0 then a else if i = 1 then b else c

@[simp] theorem modelPoint_zero (a b c : ℝ) : modelPoint a b c 0 = a := by
  simp [modelPoint]

@[simp] theorem modelPoint_one (a b c : ℝ) : modelPoint a b c 1 = b := by
  simp [modelPoint]

@[simp] theorem modelPoint_two (a b c : ℝ) : modelPoint a b c 2 = c := by
  simp [modelPoint]

/-- The source's translated low-frequency kernel `φ_{s,a}`. -/
def modelPhiAt (s a x : ℝ) : ℝ := kernelAt conePhiPhysicalReal s a x

/-- The translated annular kernel `ψ_{s,a}`. -/
def modelPsiAt (s a x : ℝ) : ℝ := kernelAt conePsiPhysicalReal s a x

/-- The third-coordinate convolution kernel occurring before the first local
Cauchy--Schwarz step. -/
noncomputable def modelThirdKernel (u s p y : ℝ) : ℝ :=
  kernelAt
    (fun w : ℝ ↦ ∫ z : ℝ, gaussianDeriv z * conePsiPhysicalReal (w - z + u))
    s p y

/-- The fixed-scale local model integrand, written with the original
third-coordinate convolution kernel from Definition `def:model`. -/
noncomputable def modelLocalIntegrand
    (α : Anisotropy) (u : E3) (f : Fin 4 → E3 → ℂ) (p : E3) (t : ℝ)
    (x₁ x₂ y₁ y₂ x₃ y₃ : ℝ) : ℂ :=
  f 0 (modelPoint x₁ x₂ x₃) *
  f 1 (modelPoint y₁ x₂ x₃) *
  f 2 (modelPoint x₁ y₂ x₃) *
  f 3 (modelPoint x₁ x₂ y₃) *
  (modelPhiAt (t ^ α.weight 0)
    (p 0 + t ^ α.weight 0 * u 0) x₁ : ℂ) *
  (gaussianAt (t ^ α.weight 0) (p 0) y₁ : ℂ) *
  (modelPhiAt (t ^ α.weight 1)
    (p 1 + t ^ α.weight 1 * u 1) x₂ : ℂ) *
  (gaussianAt (t ^ α.weight 1) (p 1) y₂ : ℂ) *
  (gaussianDerivAt (t ^ α.weight 2) (p 2) x₃ : ℂ) *
  (modelThirdKernel (u 2) (t ^ α.weight 2) (p 2) y₃ : ℂ)

/-- The real inputs used for the local-tree and energy estimates. -/
abbrev ModelRealInput := Fin 4 → E3 → ℝ

/-- The first, three-input fiber transform in the local Cauchy--Schwarz
factorization.  The five-vector has coordinates `(x₁,x₂,y₁,y₂,r)`. -/
noncomputable def modelFirstFiber (α : Anisotropy) (f : ModelRealInput)
    (p : E3) (t : ℝ) (z : ModelE5) : ℝ :=
  ∫ v : ℝ,
    f 0 (modelPoint (z 0) (z 1) v) *
    f 1 (modelPoint (z 2) (z 1) v) *
    f 2 (modelPoint (z 0) (z 3) v) *
    gaussianDerivAt (t ^ α.weight 2) (p 2) v

/-- The second, one-input fiber transform in the local Cauchy--Schwarz
factorization. -/
noncomputable def modelSecondFiber (α : Anisotropy) (f : E3 → ℝ)
    (p : E3) (t : ℝ) (z : ModelE5) : ℝ :=
  ∫ v : ℝ,
    f (modelPoint (z 0) (z 1) v) *
      gaussianDerivAt (t ^ α.weight 2)
        (p 2 + z 4 * t ^ α.weight 2) v

/-- The signed five-variable density obtained by opening the translated
third-coordinate convolution. -/
def modelSignedDensity (α : Anisotropy) (u : E3)
    (p : E3) (t : ℝ) (z : ModelE5) : ℝ :=
  modelPhiAt (t ^ α.weight 0)
    (p 0 + t ^ α.weight 0 * u 0) (z 0) *
  gaussianAt (t ^ α.weight 0) (p 0) (z 2) *
  modelPhiAt (t ^ α.weight 1)
    (p 1 + t ^ α.weight 1 * u 1) (z 1) *
  gaussianAt (t ^ α.weight 1) (p 1) (z 3) *
  conePsiPhysicalReal (z 4 + u 2)

/-- The positive measure density used by the two local energies. -/
def modelEnergyDensity (α : Anisotropy) (u : E3)
    (p : E3) (t : ℝ) (z : ModelE5) : ℝ :=
  |modelPhiAt (t ^ α.weight 0)
    (p 0 + t ^ α.weight 0 * u 0) (z 0)| *
  gaussianAt (t ^ α.weight 0) (p 0) (z 2) *
  |modelPhiAt (t ^ α.weight 1)
    (p 1 + t ^ α.weight 1 * u 1) (z 1)| *
  gaussianAt (t ^ α.weight 1) (p 1) (z 3) *
  |conePsiPhysicalReal (z 4 + u 2)|

theorem modelEnergyDensity_nonneg (α : Anisotropy) (u p : E3) {t : ℝ}
    (ht : 0 ≤ t) (z : ModelE5) : 0 ≤ modelEnergyDensity α u p t z := by
  have hg0 : 0 ≤ gaussianAt (t ^ α.weight 0) (p 0) (z 2) := by
    unfold gaussianAt kernelAt kernelDilate
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg ht _)) (gaussian_nonneg _)
  have hg1 : 0 ≤ gaussianAt (t ^ α.weight 1) (p 1) (z 3) := by
    unfold gaussianAt kernelAt kernelDilate
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg ht _)) (gaussian_nonneg _)
  unfold modelEnergyDensity
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (abs_nonneg _) hg0)
        (abs_nonneg _)) hg1)
    (abs_nonneg _)

/-- Taking absolute values of the signed local density gives exactly the
positive density defining the two energies. -/
theorem abs_modelSignedDensity (α : Anisotropy) (u p : E3) {t : ℝ}
    (ht : 0 ≤ t) (z : ModelE5) :
    |modelSignedDensity α u p t z| = modelEnergyDensity α u p t z := by
  have hg0 : 0 ≤ gaussianAt (t ^ α.weight 0) (p 0) (z 2) := by
    unfold gaussianAt kernelAt kernelDilate
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg ht _)) (gaussian_nonneg _)
  have hg1 : 0 ≤ gaussianAt (t ^ α.weight 1) (p 1) (z 3) := by
    unfold gaussianAt kernelAt kernelDilate
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg ht _)) (gaussian_nonneg _)
  unfold modelSignedDensity modelEnergyDensity
  repeat' rw [abs_mul]
  rw [abs_of_nonneg hg0, abs_of_nonneg hg1]

/-- The localized real model form after its Fubini expansion.  The equality
with the convolution presentation is established as part of localization. -/
noncomputable def expandedModelLocalForm (α : Anisotropy) (S : BoxCollection α)
    (u : E3) (c : ℝ → ℝ) (f : ModelRealInput) : ℝ :=
  -(∫ pt : E3 × ℝ,
    c pt.2 * (∫ z : ModelE5,
      modelFirstFiber α f pt.1 pt.2 z *
        modelSecondFiber α (f 3) pt.1 pt.2 z *
          modelSignedDensity α u pt.1 pt.2 z)
    ∂(cubeScaleMeasure.restrict (collectionRegion α S)))

/-- The first local energy. -/
noncomputable def modelEnergyOne (α : Anisotropy) (S : BoxCollection α)
    (u : E3) (f : ModelRealInput) : ℝ :=
  ∫ pt : E3 × ℝ,
    (∫ z : ModelE5,
      (modelFirstFiber α f pt.1 pt.2 z) ^ 2 *
        modelEnergyDensity α u pt.1 pt.2 z)
    ∂(cubeScaleMeasure.restrict (collectionRegion α S))

/-- The second local energy on an arbitrary measurable center--scale set. -/
noncomputable def modelEnergyTwoOn (α : Anisotropy) (V : Set (E3 × ℝ))
    (u : E3) (f : E3 → ℝ) : ℝ :=
  ∫ pt : E3 × ℝ,
    (∫ z : ModelE5,
      (modelSecondFiber α f pt.1 pt.2 z) ^ 2 *
        modelEnergyDensity α u pt.1 pt.2 z)
    ∂(cubeScaleMeasure.restrict V)

/-- The second local energy over a finite box collection. -/
noncomputable def modelEnergyTwo (α : Anisotropy) (S : BoxCollection α)
    (u : E3) (f : E3 → ℝ) : ℝ :=
  modelEnergyTwoOn α (collectionRegion α S) u f

end

end Auto.Twisted
