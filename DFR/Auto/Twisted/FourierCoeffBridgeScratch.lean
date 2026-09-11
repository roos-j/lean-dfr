/- Copyright (c) 2026. All rights reserved. -/
import Auto.Twisted.Twisted
import Auto.Twisted.FourierOneDimScratch
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Scratch interface from the unit-torus localized symbol to its raw cube model

The endpoint issue is deliberately isolated by using the open fundamental
cube.  It is invisible to the Haar integral and is the right starting point
for the subsequent coordinatewise integration-by-parts argument.
-/

namespace Auto
namespace Twisted

open MeasureTheory Filter FourierTransform TopologicalSpace
open scoped BigOperators Convolution ENNReal FourierTransform NNReal Topology

noncomputable section

/-- The open representative of the unit fundamental cube.  We use this
representative to invoke the literal `(-4,4)^3` formula, then return to the
half-open cube used by `mFourierCoeff`. -/
def scratch_unitOpenCube : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ (fun _ : Fin 3 ↦ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ))

/-- The half-open representative selected by the torus Fourier-coefficient
API. -/
def scratch_unitIocCube : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ (fun _ : Fin 3 ↦ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))

theorem scratch_unitOpenCube_measurable : MeasurableSet scratch_unitOpenCube := by
  unfold scratch_unitOpenCube
  exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo

theorem scratch_unitIocCube_measurable : MeasurableSet scratch_unitIocCube := by
  unfold scratch_unitIocCube
  exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioc

/-- The endpoint convention for the unit cube is invisible to Lebesgue
measure.  This is the measure-theoretic mechanism which makes the raw
scale-eight identity applicable to the `mFourierCoeff` integral. -/
theorem scratch_unitOpenCube_ae_eq_unitIocCube :
    scratch_unitOpenCube =ᵐ[volume] scratch_unitIocCube := by
  unfold scratch_unitOpenCube scratch_unitIocCube
  rw [volume_pi]
  exact Measure.pi_Ioo_ae_eq_pi_Ioc

/-- On the open unit fundamental cube, the periodized unit-torus symbol is
literally the localized raw symbol on `(-4,4)^3`, after the scale-eight
coordinate change. -/
theorem scratch_unitTorusLocalizedSymbol_coe_scaled_openCube
    (α : Anisotropy) (m : E3 → ℂ) (i : Fin 3) (t : ℝ)
    (u : Fin 3 → ℝ)
    (hu : ∀ j : Fin 3, u j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    unitTorusLocalizedSymbol α m i t (fun j ↦ (u j : UnitAddCircle)) =
      localizedSymbolRaw α m i t (8 * u 0) (8 * u 1) (8 * u 2) := by
  have hu₀ : 8 * u 0 ∈ Set.Ico (-4 : ℝ) 4 := by
    constructor <;> nlinarith [(hu 0).1, (hu 0).2]
  have hu₁ : 8 * u 1 ∈ Set.Ico (-4 : ℝ) 4 := by
    constructor <;> nlinarith [(hu 1).1, (hu 1).2]
  have hu₂ : 8 * u 2 ∈ Set.Ico (-4 : ℝ) 4 := by
    constructor <;> nlinarith [(hu 2).1, (hu 2).2]
  have hpoint : (fun j ↦ (u j : UnitAddCircle)) =
      unitTorusPoint (8 * u 0) (8 * u 1) (8 * u 2) := by
    unfold unitTorusPoint
    funext j
    change (u j : UnitAddCircle) =
      ((![8 * u 0 / 8, 8 * u 1 / 8, 8 * u 2 / 8] j : ℝ) : UnitAddCircle)
    have hvec : (![8 * u 0 / 8, 8 * u 1 / 8, 8 * u 2 / 8] : Fin 3 → ℝ) = u := by
      funext k
      fin_cases k <;> simp
    rw [hvec]
  rw [hpoint]
  exact unitTorusLocalizedSymbol_coe_div α m i t hu₀ hu₁ hu₂

/-- On the half-open Fourier fundamental cube, the unit-torus localized
symbol agrees almost everywhere with the literal raw symbol after `x = 8u`.
The number `8` remains explicit for the later Jacobian calculation. -/
theorem scratch_ae_unitTorusLocalizedSymbol_coe_scaled
    (α : Anisotropy) (m : E3 → ℂ) (i : Fin 3) (t : ℝ) :
    ∀ᵐ u : Fin 3 → ℝ ∂volume.restrict scratch_unitIocCube,
      unitTorusLocalizedSymbol α m i t (fun j ↦ (u j : UnitAddCircle)) =
        localizedSymbolRaw α m i t (8 * u 0) (8 * u 1) (8 * u 2) := by
  rw [← Measure.restrict_congr_set scratch_unitOpenCube_ae_eq_unitIocCube]
  refine ae_restrict_of_forall_mem scratch_unitOpenCube_measurable fun u hu ↦ ?_
  apply scratch_unitTorusLocalizedSymbol_coe_scaled_openCube
  intro j
  exact hu j (Set.mem_univ j)

/-- The existing multivariate Fourier coefficient API reduces the coefficient
of the unit-torus localized symbol to the unit fundamental cube.  Together
with `scratch_unitTorusLocalizedSymbol_coe_scaled_openCube`, this is the
measure-theoretic entry point for the raw compact cube calculation. -/
theorem scratch_mFourierCoeff_unitTorusLocalizedSymbol_eq_unitCube
    (α : Anisotropy) (m : E3 → ℂ) (i : Fin 3) (t : ℝ)
    (ν : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν =
      ∫ u : Fin 3 → ℝ in
        {u : Fin 3 → ℝ | ∀ j : Fin 3,
          u j ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)},
        UnitAddTorus.mFourier (-ν) (fun j ↦ (u j : UnitAddCircle)) •
          unitTorusLocalizedSymbol α m i t (fun j ↦ (u j : UnitAddCircle)) := by
  have hendpoint : -(1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  simpa only [hendpoint] using
    UnitAddTorus.mFourierCoeff_eq_integral
      (unitTorusLocalizedSymbol α m i t) ν (fun _ : Fin 3 ↦ -(1 / 2 : ℝ))

/-- Exact raw-cube version of the unit-torus coefficient formula.  It has not
yet changed variables to `x = 8u`; that next step is where the explicit
Jacobian `8⁻³` must be introduced. -/
theorem scratch_mFourierCoeff_unitTorusLocalizedSymbol_eq_raw_unitCube
    (α : Anisotropy) (m : E3 → ℂ) (i : Fin 3) (t : ℝ)
    (ν : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff (unitTorusLocalizedSymbol α m i t) ν =
      ∫ u : Fin 3 → ℝ in scratch_unitIocCube,
        UnitAddTorus.mFourier (-ν) (fun j ↦ (u j : UnitAddCircle)) •
          localizedSymbolRaw α m i t (8 * u 0) (8 * u 1) (8 * u 2) := by
  rw [scratch_mFourierCoeff_unitTorusLocalizedSymbol_eq_unitCube]
  have hcube : scratch_unitIocCube =
      {u : Fin 3 → ℝ | ∀ j : Fin 3,
        u j ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)} := by
    ext u
    simp [scratch_unitIocCube, Set.pi]
  rw [← hcube]
  change ∫ u : Fin 3 → ℝ in scratch_unitIocCube,
      UnitAddTorus.mFourier (-ν) (fun j ↦ (u j : UnitAddCircle)) •
        unitTorusLocalizedSymbol α m i t (fun j ↦ (u j : UnitAddCircle)) = _
  refine setIntegral_congr_ae scratch_unitIocCube_measurable ?_
  refine (ae_restrict_iff' scratch_unitIocCube_measurable).mp ?_
  filter_upwards [scratch_ae_unitTorusLocalizedSymbol_coe_scaled α m i t] with u hu
  rw [hu]

/-- Differentiation preserves vanishing on an open set.  We state this for
iterated real derivatives because it supplies all four zero boundary terms
in the later coordinatewise integration-by-parts step. -/
theorem scratch_iteratedDeriv_eq_zero_on_open
    (f : ℝ → ℂ) (U : Set ℝ) (hU : IsOpen U)
    (hzero : ∀ x ∈ U, f x = 0) :
    ∀ n : ℕ, ∀ x ∈ U, iteratedDeriv n f x = 0 := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simpa using hzero x hx
  | succ n hn =>
      intro x hx
      rw [iteratedDeriv_succ]
      apply deriv_zero_of_frequently_const
      have hmem : ∀ᶠ y in 𝓝 x, y ∈ U := hU.mem_nhds hx
      have hmem' : ∀ᶠ y in 𝓝[≠] x, y ∈ U :=
        hmem.filter_mono nhdsWithin_le_nhds
      exact (hmem'.mono fun y hy ↦ hn y hy).frequently

/-- A globally smooth function which vanishes outside the open unit core has
all of its iterated derivatives vanishing at both endpoints of that core.
This turns compact support into the four periodic boundary identities needed
by the one-dimensional Fourier integration-by-parts lemma. -/
theorem scratch_iteratedDeriv_eq_zero_unitBoundary_of_contDiff
    (N k : ℕ) (f : ℝ → ℂ) (hf : ContDiff ℝ N f) (hk : k ≤ N)
    (hzero : ∀ x : ℝ, (1 / 2 : ℝ) < |x| → f x = 0) :
    iteratedDeriv k f (-(1 / 2 : ℝ)) = 0 ∧
      iteratedDeriv k f (1 / 2 : ℝ) = 0 := by
  let U : Set ℝ := {x : ℝ | (1 / 2 : ℝ) < |x|}
  have hU : IsOpen U := by
    exact isOpen_lt continuous_const continuous_abs
  have hzeroU : ∀ x ∈ U, f x = 0 := by
    intro x hx
    exact hzero x hx
  have hiter : ∀ x ∈ U, iteratedDeriv k f x = 0 :=
    scratch_iteratedDeriv_eq_zero_on_open f U hU hzeroU k
  have hcont : Continuous (iteratedDeriv k f) :=
    hf.continuous_iteratedDeriv k (by exact_mod_cast hk)
  have hclosed : IsClosed ((iteratedDeriv k f) ⁻¹' ({0} : Set ℂ)) :=
    isClosed_singleton.preimage hcont
  have hsubset : U ⊆ (iteratedDeriv k f) ⁻¹' ({0} : Set ℂ) := by
    intro x hx
    simpa using hiter x hx
  have hpos : (1 / 2 : ℝ) ∈ closure U := by
    have hIoi : Set.Ioi (1 / 2 : ℝ) ⊆ U := by
      intro x hx
      exact lt_of_lt_of_le hx (le_abs_self x)
    apply (closure_mono hIoi)
    rw [closure_Ioi]
    exact Set.mem_Ici.mpr le_rfl
  have hneg : (-(1 / 2 : ℝ)) ∈ closure U := by
    have hIio : Set.Iio (-(1 / 2 : ℝ)) ⊆ U := by
      intro x hx
      change x < -(1 / 2 : ℝ) at hx
      have hminus : (1 / 2 : ℝ) < -x := by linarith
      exact lt_of_lt_of_le hminus (neg_le_abs x)
    apply (closure_mono hIio)
    rw [closure_Iio]
    exact Set.mem_Iic.mpr le_rfl
  have hclosure : closure U ⊆ (iteratedDeriv k f) ⁻¹' ({0} : Set ℂ) :=
    closure_minimal hsubset hclosed
  constructor
  · simpa using hclosure hneg
  · simpa using hclosure hpos

/-- Smoothness of a scale-eight raw coordinate slice.  This is the
calculus input for applying four integrations by parts in a single Fourier
coordinate after the other two are frozen. -/
theorem scratch_contDiff_raw_first_scaled
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (y z : ℝ) :
    ContDiff ℝ 110 (fun x : ℝ ↦
      localizedSymbolRaw α m i t (8 * x) y z) := by
  change ContDiff ℝ 110
    (localizedSymbol α m i t ∘ fun x : ℝ ↦ frequencyAssemble3 (8 * x) y z)
  let L : ℝ →L[ℝ] E3 :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (Anisotropy.coordinateDirection 0)
  have hslice : (fun x : ℝ ↦ frequencyAssemble3 (8 * x) y z) =
      fun x : ℝ ↦ L (8 * x) + frequencyAssemble3 0 y z := by
    funext x
    ext j
    fin_cases j <;>
      simp [L, frequencyAssemble3_apply, coordinateDirection_apply]
  rw [hslice]
  apply (localizedSymbol_contDiff α M m hm i ht).comp
  fun_prop

/-- The first raw coordinate slice is identically zero outside the scale-eight
unit interval.  The deliberately stronger source support threshold `3` makes
this immediate once `|x| ≥ 1/2`. -/
theorem scratch_raw_first_scaled_eq_zero_of_abs_ge_half
    (α : Anisotropy) (m : E3 → ℂ) (i : Fin 3) (t y z x : ℝ)
    (hx : (1 / 2 : ℝ) ≤ |x|) :
    localizedSymbolRaw α m i t (8 * x) y z = 0 := by
  apply localizedSymbolRaw_eq_zero_of_coordinate_large α m i 0 t
  change 3 ≤ |8 * x|
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
  nlinarith

/-- Every derivative through the available localized-symbol smoothness order
vanishes at both endpoints of a scale-eight raw first-coordinate slice. -/
theorem scratch_iteratedDeriv_raw_first_scaled_unitBoundary
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (y z : ℝ) (k : ℕ) (hk : k ≤ 110) :
    iteratedDeriv k (fun x : ℝ ↦
      localizedSymbolRaw α m i t (8 * x) y z) (-(1 / 2 : ℝ)) = 0 ∧
      iteratedDeriv k (fun x : ℝ ↦
        localizedSymbolRaw α m i t (8 * x) y z) (1 / 2 : ℝ) = 0 := by
  apply scratch_iteratedDeriv_eq_zero_unitBoundary_of_contDiff 110 k
  · exact scratch_contDiff_raw_first_scaled α M m hm i ht y z
  · exact hk
  · intro x hx
    exact scratch_raw_first_scaled_eq_zero_of_abs_ge_half α m i t y z x (le_of_lt hx)

/-- Four integrations by parts in the first scale-eight raw coordinate.
The conclusion is deliberately an exact `fourierCoeffOn` estimate: it is the
one-dimensional core of the future three-dimensional coefficient-decay
argument, before Fubini chooses a large coordinate of the lattice mode. -/
theorem scratch_norm_fourierCoeffOn_raw_first_scaled_le_of_fourth_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t) (y z C : ℝ)
    (n : ℤ) (hn : n ≠ 0)
    (hbound : ∀ x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
      ‖iteratedDeriv 4 (fun r : ℝ ↦
        localizedSymbolRaw α m i t (8 * r) y z) x‖ ≤ C) :
    ‖fourierCoeffOn (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
      (fun r : ℝ ↦ localizedSymbolRaw α m i t (8 * r) y z) n‖ ≤
      (2 * Real.pi * |(n : ℝ)|)⁻¹ ^ 4 * C := by
  let f : ℝ → ℂ := fun r ↦ localizedSymbolRaw α m i t (8 * r) y z
  have hf : ContDiff ℝ 110 f :=
    scratch_contDiff_raw_first_scaled α M m hm i ht y z
  have hderiv (r : ℕ) (hr : r < 110) (x : ℝ) :
      HasDerivAt (iteratedDeriv r f) (iteratedDeriv (r + 1) f x) x := by
    rw [iteratedDeriv_succ]
    exact (hf.differentiable_iteratedDeriv r (by exact_mod_cast hr)).differentiableAt.hasDerivAt
  have hboundary (r : ℕ) (hr : r ≤ 110) :
      iteratedDeriv r f (1 / 2 : ℝ) = iteratedDeriv r f (-(1 / 2 : ℝ)) := by
    rcases scratch_iteratedDeriv_raw_first_scaled_unitBoundary
      α M m hm i ht y z r hr with ⟨hleft, hright⟩
    change iteratedDeriv r f (1 / 2 : ℝ) = iteratedDeriv r f (-(1 / 2 : ℝ))
    rw [hleft, hright]
  have hmain := scratch_norm_fourierCoeffOn_le_of_four_deriv_bound
    (a := -(1 / 2 : ℝ)) (b := 1 / 2) (C := C)
    (f0 := f) (f1 := iteratedDeriv 1 f) (f2 := iteratedDeriv 2 f)
    (f3 := iteratedDeriv 3 f) (f4 := iteratedDeriv 4 f)
    (by norm_num : -(1 / 2 : ℝ) < 1 / 2) hn
    (by
      intro x hx
      simpa using hderiv 0 (by norm_num) x)
    (by
      intro x hx
      exact hderiv 1 (by norm_num) x)
    (by
      intro x hx
      exact hderiv 2 (by norm_num) x)
    (by
      intro x hx
      exact hderiv 3 (by norm_num) x)
    ((hf.continuous_iteratedDeriv 1 (by norm_num)).intervalIntegrable _ _)
    ((hf.continuous_iteratedDeriv 2 (by norm_num)).intervalIntegrable _ _)
    ((hf.continuous_iteratedDeriv 3 (by norm_num)).intervalIntegrable _ _)
    ((hf.continuous_iteratedDeriv 4 (by norm_num)).intervalIntegrable _ _)
    (by simpa using hboundary 0 (by norm_num))
    (hboundary 1 (by norm_num))
    (hboundary 2 (by norm_num))
    (hboundary 3 (by norm_num))
    (by simpa [f] using hbound)
  change ‖fourierCoeffOn (by norm_num : -(1 / 2 : ℝ) < 1 / 2) f n‖ ≤
    (2 * Real.pi * |(n : ℝ)|)⁻¹ ^ 4 * C
  convert hmain using 1 <;> norm_num

/-- A nested raw-cube Fourier coefficient, with the first coordinate already
packaged as `fourierCoeffOn`.  The pending Fubini bridge identifies this
literal iterated integral with `mFourierCoeff` of the periodized symbol. -/
noncomputable def scratch_nestedRawUnitFourierCoeff
    (α : Anisotropy) (m : E3 → ℂ) (i : Fin 3) (t : ℝ)
    (ν : Fin 3 → ℤ) : ℂ :=
  ∫ y in (-(1 / 2 : ℝ))..(1 / 2),
    fourier (-ν 1) (y : UnitAddCircle) *
      ∫ z in (-(1 / 2 : ℝ))..(1 / 2),
        fourier (-ν 2) (z : UnitAddCircle) *
          fourierCoeffOn (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
            (fun x : ℝ ↦ localizedSymbolRaw α m i t
              (8 * x) (8 * y) (8 * z)) (ν 0)

/-- The exact nested coefficient has fourth-order decay in any chosen
nonzero coordinate, provided the corresponding fourth raw derivative is
uniformly bounded on the unit cube.  This is the Fubini-ready multivariate
form of the four-IBP estimate. -/
theorem scratch_norm_nestedRawUnitFourierCoeff_le_of_first_fourth_bound
    (α : Anisotropy) (M : ℝ) (m : E3 → ℂ)
    (hm : Anisotropy.IsAnisotropicMultiplier α M m)
    (i : Fin 3) {t : ℝ} (ht : 0 < t)
    (ν : Fin 3 → ℤ) (hν : ν 0 ≠ 0) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
      ∀ y ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
      ∀ z ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        ‖iteratedDeriv 4 (fun r : ℝ ↦ localizedSymbolRaw α m i t
          (8 * r) (8 * y) (8 * z)) x‖ ≤ C) :
    ‖scratch_nestedRawUnitFourierCoeff α m i t ν‖ ≤
      (2 * Real.pi * |((ν 0 : ℤ) : ℝ)|)⁻¹ ^ 4 * C := by
  let B : ℝ := (2 * Real.pi * |((ν 0 : ℤ) : ℝ)|)⁻¹ ^ 4 * C
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity) hC
  unfold scratch_nestedRawUnitFourierCoeff
  calc
    ‖∫ y in (-(1 / 2 : ℝ))..(1 / 2),
        fourier (-ν 1) (y : UnitAddCircle) *
          ∫ z in (-(1 / 2 : ℝ))..(1 / 2),
            fourier (-ν 2) (z : UnitAddCircle) *
              fourierCoeffOn (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
                (fun x : ℝ ↦ localizedSymbolRaw α m i t
                  (8 * x) (8 * y) (8 * z)) (ν 0)‖ ≤
        B * |(1 / 2 : ℝ) - (-(1 / 2 : ℝ))| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      have hy' : y ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
        simpa only [Set.uIoc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)] using hy
      have hyfourier : ‖fourier (-ν 1) (y : UnitAddCircle)‖ = 1 := Circle.norm_coe _
      rw [norm_mul, hyfourier, one_mul]
      calc
        ‖∫ z in (-(1 / 2 : ℝ))..(1 / 2),
            fourier (-ν 2) (z : UnitAddCircle) *
              fourierCoeffOn (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
                (fun x : ℝ ↦ localizedSymbolRaw α m i t
                  (8 * x) (8 * y) (8 * z)) (ν 0)‖ ≤
            B * |(1 / 2 : ℝ) - (-(1 / 2 : ℝ))| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro z hz
          have hz' : z ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
            simpa only [Set.uIoc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)] using hz
          have hzfourier : ‖fourier (-ν 2) (z : UnitAddCircle)‖ = 1 := Circle.norm_coe _
          rw [norm_mul, hzfourier, one_mul]
          change ‖fourierCoeffOn (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
            (fun x : ℝ ↦ localizedSymbolRaw α m i t
              (8 * x) (8 * y) (8 * z)) (ν 0)‖ ≤ B
          exact scratch_norm_fourierCoeffOn_raw_first_scaled_le_of_fourth_bound
            α M m hm i ht (8 * y) (8 * z) C (ν 0) hν
            (fun x hx ↦ hbound x hx y hy' z hz')
        _ = B := by norm_num
    _ = B := by norm_num

end
end Twisted
end Auto
