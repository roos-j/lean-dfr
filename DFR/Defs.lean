/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!

# Main definitions

Here we state the definitions needed to formulate the main theorems.

-/

@[expose] public noncomputable section

namespace DFR

open MeasureTheory Topology Filter

variable {n : ℕ}

/-- Real Euclidean space `R^n` -/
scoped notation:max "ℝ^" n:max => EuclideanSpace ℝ (Fin n)

/-- `i`th standard unit vector -/
abbrev unitVector (i : Fin n) : ℝ^n := EuclideanSpace.single i (1 : ℝ)

@[inherit_doc unitVector]
scoped notation "𝐞" => unitVector

/-- Truncated three-simplex Hilbert transform along the moment curve of `f` at `x`. -/
def T_trunc (f : Fin 3 → ℝ^3 → ℂ) (x : ℝ^3) (ε : ℝ) : ℂ :=
  ∫ t in {t : ℝ | ε < |t|}, (∏ i : Fin 3, f i (x + (t ^ (i.val + 1)) • 𝐞 i)) / t

/-- Three-simplex Hilbert transform along the moment curve `T f (x)` as principal-value.

**Note:** The (trivial) fact that the principal value limit exists when `f` are Schwartz functions
is proved as the automatically generated lemma `Auto.tendsto_T_trunc`.
-/
def T (f : Fin 3 → ℝ^3 → ℂ) (x : ℝ^3) : ℂ := limUnder (𝓝[>] 0) (T_trunc f x)

end DFR

end
