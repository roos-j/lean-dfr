/- Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Auto.Twisted.Twisted
import LeanSpherical.Auto.LpSpaceFacts

namespace Auto
namespace Twisted

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

/-- A scalar `L^p` function is normed by Schwartz test functions.  This is
the density/duality step needed to turn a finite-model form estimate into an
actual output estimate once preliminary finite-scale integrability has given
the `MemLp` premise. -/
theorem scratch_lpNorm_le_of_schwartz_test_pairing_bound
    {p K : ℝ} (hp : 1 < p) (hK : 0 ≤ K) {y : E3 → ℂ}
    (hy : MemLp y (ENNReal.ofReal p) volume)
    (hSchwartz : ∀ g : SchwartzMap E3 ℂ,
      ‖∫ x : E3, y x * g x‖ ≤
        K * lpNorm (g : E3 → ℂ) (ENNReal.ofReal p.conjExponent) volume) :
    lpNorm y (ENNReal.ofReal p) volume ≤ K := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hp.le⟩
  letI : Fact (1 ≤ ENNReal.ofReal p.conjExponent) :=
    ⟨Auto.LpSpaceFacts.one_le_ofReal_conjExponent p hp⟩
  letI : ENNReal.HolderConjugate (ENNReal.ofReal p)
      (ENNReal.ofReal p.conjExponent) :=
    Auto.LpSpaceFacts.ofReal_holderConjugate p hp
  let Φ : Lp ℂ (ENNReal.ofReal p.conjExponent) volume →L[ℂ] ℂ :=
    (ContinuousLinearMap.lpPairing volume (ENNReal.ofReal p)
      (ENNReal.ofReal p.conjExponent) (ContinuousLinearMap.mul ℂ ℂ))
      (hy.toLp y)
  have hnorm_toLp (g : SchwartzMap E3 ℂ) :
      ‖g.toLp (ENNReal.ofReal p.conjExponent) volume‖ =
        lpNorm (g : E3 → ℂ) (ENNReal.ofReal p.conjExponent) volume := by
    rw [SchwartzMap.norm_toLp,
      toReal_eLpNorm g.continuous.aestronglyMeasurable]
  have hPhi_schwartz (g : SchwartzMap E3 ℂ) :
      ‖Φ (g.toLp (ENNReal.ofReal p.conjExponent) volume)‖ ≤
        K * ‖g.toLp (ENNReal.ofReal p.conjExponent) volume‖ := by
    have hraw : Φ (g.toLp (ENNReal.ofReal p.conjExponent) volume) =
        ∫ x : E3, y x * g x := by
      rw [show Φ =
        (ContinuousLinearMap.lpPairing volume (ENNReal.ofReal p)
          (ENNReal.ofReal p.conjExponent) (ContinuousLinearMap.mul ℂ ℂ))
          (hy.toLp y) by rfl,
        Auto.LpSpaceFacts.lpPairing_apply_toLp_eq_integral hy]
      apply integral_congr_ae
      filter_upwards [g.coeFn_toLp (ENNReal.ofReal p.conjExponent) volume]
        with x hx
      rw [hx]
    rw [hraw, hnorm_toLp]
    exact hSchwartz g
  have hPhi (g : Lp ℂ (ENNReal.ofReal p.conjExponent) volume) :
      ‖Φ g‖ ≤ K * ‖g‖ := by
    refine (SchwartzMap.denseRange_toLpCLM (E := E3) (F := ℂ)
      (p := ENNReal.ofReal p.conjExponent) ENNReal.ofReal_ne_top).induction_on
      g ?_ ?_
    · exact isClosed_le Φ.continuous.norm
        (continuous_const.mul continuous_id.norm)
    · intro g
      simpa only [SchwartzMap.toLpCLM_apply] using hPhi_schwartz g
  refine Auto.LpSpaceFacts.lpNorm_le_of_simple_test_pairing_bound hp hK hy ?_
  intro g
  have hraw : Φ (g : Lp ℂ (ENNReal.ofReal p.conjExponent) volume) =
      ∫ x : E3, y x *
        (g : Lp ℂ (ENNReal.ofReal p.conjExponent) volume) x := by
    rw [show Φ =
      (ContinuousLinearMap.lpPairing volume (ENNReal.ofReal p)
        (ENNReal.ofReal p.conjExponent) (ContinuousLinearMap.mul ℂ ℂ))
        (hy.toLp y) by rfl,
      Auto.LpSpaceFacts.lpPairing_apply_toLp_eq_integral hy]
  rw [← hraw]
  exact hPhi (g : Lp ℂ (ENNReal.ofReal p.conjExponent) volume)

end
end Twisted
end Auto
