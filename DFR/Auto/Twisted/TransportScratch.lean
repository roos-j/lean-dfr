import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped RealInnerProductSpace

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev E6 := WithLp 2 (E3 × E3)
abbrev E9p := WithLp 2 (E6 × E3)
abbrev E9 := EuclideanSpace ℝ (Fin 9)

noncomputable def split6Hilbert :
    WithLp 2 (Fin 3 ⊕ Fin 3 → ℝ) ≃ₗᵢ[ℝ] E6 :=
  PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin 3 ⊕ Fin 3 => ℝ)

noncomputable def idx9 : Fin 9 ≃ Fin 3 ⊕ (Fin 3 ⊕ Fin 3) :=
  (finSumFinEquiv (m := 3) (n := 6)).symm.trans
    (Equiv.sumCongr (Equiv.refl _) (finSumFinEquiv (m := 3) (n := 3)).symm)

def frequencyIndexPermutation : Fin 9 ≃ Fin 9 where
  toFun i :=
    match i.1 with
    | 0 => 3
    | 1 => 7
    | 2 => 2
    | 3 => 4
    | 4 => 5
    | 5 => 6
    | 6 => 8
    | 7 => 0
    | _ => 1
  invFun i :=
    match i.1 with
    | 0 => 7
    | 1 => 8
    | 2 => 2
    | 3 => 0
    | 4 => 3
    | 5 => 4
    | 6 => 5
    | 7 => 1
    | _ => 6
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl


noncomputable def split6 : E6 ≃ₗᵢ[ℝ]
    WithLp 2 (E3 × E3) := LinearIsometryEquiv.refl ℝ E6

noncomputable def e9_to_freqHilbert : E9 ≃ₗᵢ[ℝ] E9p :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ idx9).trans
    ((PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin 3 ⊕ (Fin 3 ⊕ Fin 3) => ℝ)).trans
      ((LinearIsometryEquiv.withLpProdCongr 2
        (LinearIsometryEquiv.refl ℝ E3)
        (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin 3 ⊕ Fin 3 => ℝ))).trans
          (LinearIsometryEquiv.withLpProdComm 2 ℝ E3 E6)))

noncomputable def splitToE9 : WithLp 2 (E3 × E6) ≃ₗᵢ[ℝ] E9 :=
  (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ E3)
    split6Hilbert.symm).trans
      ((PiLp.sumPiLpEquivProdLpPiLp 2
        (fun _ : Fin 3 ⊕ (Fin 3 ⊕ Fin 3) => ℝ)).symm.trans
          (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ idx9.symm))

noncomputable def reassemblyHilbert : E9 ≃ₗᵢ[ℝ] E9p :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ frequencyIndexPermutation).trans
    e9_to_freqHilbert

noncomputable def rawFrequencyEquiv : E9p ≃ᵐ ((E3 × E3) × E3) :=
  (MeasurableEquiv.toLp 2 (E6 × E3)).symm.trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.toLp 2 (E3 × E3)).symm (MeasurableEquiv.refl E3))

noncomputable def rawFrequencyCLE : E9p ≃L[ℝ] ((E3 × E3) × E3) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E6 E3).trans
    (ContinuousLinearEquiv.prodCongr
      (WithLp.prodContinuousLinearEquiv 2 ℝ E3 E3)
      (ContinuousLinearEquiv.refl ℝ E3))

noncomputable def frequencyReassemblyCLE :
    (E3 × E6) ≃L[ℝ] ((E3 × E3) × E3) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E3 E6).symm.trans
    ((splitToE9.toContinuousLinearEquiv.trans
      reassemblyHilbert.toContinuousLinearEquiv).trans rawFrequencyCLE)

noncomputable def assemble3 (a b c : ℝ) : E3 :=
  WithLp.toLp 2 ![a, b, c]

@[simp] theorem assemble3_apply (a b c : ℝ) (i : Fin 3) :
    assemble3 a b c i = ![a, b, c] i := rfl

theorem frequencyReassemblyCLE_apply (η : E3) (r : E6) :
    frequencyReassemblyCLE (η, r) =
      ((assemble3 (η 0) (r.fst 0) (r.fst 1),
        assemble3 (r.fst 2) (η 1) (r.snd 0)),
        assemble3 (r.snd 1) (r.snd 2) (η 2)) := by
  apply Prod.ext
  · apply Prod.ext
    · ext i
      fin_cases i <;> rfl
    · ext i
      fin_cases i <;> rfl
  · ext i
    fin_cases i <;> rfl

theorem rawFrequencyEquiv_measurePreserving :
    MeasurePreserving rawFrequencyEquiv volume volume := by
  exact (WithLp.volume_preserving_symm_measurableEquiv_toLp_prod E6 E3).trans
    (MeasurePreserving.prod
      (WithLp.volume_preserving_symm_measurableEquiv_toLp_prod E3 E3)
      (MeasurePreserving.id volume))

theorem reassemblyHilbert_measurePreserving :
    MeasurePreserving reassemblyHilbert volume volume :=
  reassemblyHilbert.measurePreserving

theorem frequencyReassembly_measurePreserving :
    MeasurePreserving frequencyReassemblyCLE volume volume := by
  have h1 : MeasurePreserving (WithLp.toLp 2)
      (volume : Measure (E3 × E6)) (volume : Measure (WithLp 2 (E3 × E6))) :=
    WithLp.volume_preserving_toLp (U := E3) (V := E6)
  have h2 : MeasurePreserving splitToE9
      (volume : Measure (WithLp 2 (E3 × E6))) (volume : Measure E9) :=
    splitToE9.measurePreserving
  have h3 : MeasurePreserving reassemblyHilbert
      (volume : Measure E9) (volume : Measure E9p) :=
    reassemblyHilbert.measurePreserving
  have h4 : MeasurePreserving rawFrequencyEquiv
      (volume : Measure E9p) (volume : Measure ((E3 × E3) × E3)) :=
    rawFrequencyEquiv_measurePreserving
  have h := h4.comp (h3.comp (h2.comp h1))
  convert h using 1
  ext z <;> rfl

#check e9_to_freqHilbert
#check finSumFinEquiv
#check e9_to_freqHilbert.measurePreserving
#check WithLp.volume_preserving_symm_measurableEquiv_toLp_prod
#check WithLp.prodContinuousLinearEquiv
#check LinearIsometryEquiv.piLpCongrLeft
#check MeasurePreserving.comp
#check MeasurePreserving.trans
#check integral_prod
#check MeasureTheory.integral_prod
#check MeasureTheory.integral_integral_swap
#check MeasurePreserving.integral_comp
#check ContinuousLinearEquiv.toHomeomorph
#check Homeomorph.measurableEmbedding
#check MeasurePreserving.integrable_comp_of_integrable
#check MeasureTheory.integral_mul_left
#check MeasureTheory.integral_mul_right
#check MeasureTheory.integral_smul
#check Circle.norm_coe
#check AddChar.map_add_eq_mul
#check Real.fourierChar
#check Circle.smul_def
#check Real.fourierChar_apply
#check Circle.coe_mul
