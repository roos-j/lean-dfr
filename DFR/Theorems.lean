/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

public import DFR.Defs
public import Mathlib
import DFR.Auto.Reduction.Reduction

/-!

# Main theorem

Here we state the main theorem of the paper.
The proofs are in the `Auto` folder.

-/

public section

namespace DFR

open MeasureTheory ENNReal SchwartzMap Topology Filter

/-- **Main theorem.** The three-simplex Hilbert transform along the moment curve
is bounded `L^{p_1} × L^{p_2} × L^{p_3} → L^p` for `p ∈ (1, 4/3)` and `p_1, p_2, p_3 ∈ (1,4)`
such that `1/p_1 + 1/p_2 + 1/p_3 = 1/p`.

**Implementation notes:**
- We use a vector `q` to represent the exponent triple `(p_1, p_2, p_3)`.
- Consistent with usual Lean convention we use zero indexing.
- We formulate the bound as an a priori estimate on Schwartz functions as is common practice.
-/
theorem main_result {p : ℝ≥0∞} (hp : 1 < p ∧ p < 4 / 3)
    {q : Fin 3 → ℝ≥0∞} (hq : ∀ i, 1 < q i ∧ q i < 4) (hpq : (q 0)⁻¹ + (q 1)⁻¹ + (q 2)⁻¹ = p⁻¹) :
    ∃ C : ℝ, ∀ f : Fin 3 → 𝓢(ℝ^3, ℂ),
      eLpNorm (T (fun i ↦ f i)) p ≤ (ENNReal.ofReal C) * ∏ i, eLpNorm (f i) (q i) :=
  Auto.main_result hp hq hpq

end DFR

end
