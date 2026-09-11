/- Copyright (c) 2026 Polona Durcik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Auto.Twisted.Twisted
import LeanSpherical.Auto.Spherical.PowerWeights

/-! ### One-dimensional geometry of the public dyadic CZ package

This is an audit-only bridge for the `d = 1` stopping cubes from
`PowerWeights`.  In that API, the named cube center is the lower endpoint;
the actual midpoint and half-side used by the interval-tail package are
defined below. -/

namespace Auto.Twisted

open MeasureTheory Filter Set
open Auto.Spherical.PowerWeights
open scoped BigOperators ENNReal

noncomputable section

abbrev FiberCZCubeIndex := LacunaryCZDyadicCubeIndex 1

/-- The lower endpoint of a one-dimensional literal CZ dyadic cube. -/
noncomputable def scratch_fiberCZCubeLo (q : FiberCZCubeIndex) : ℝ :=
  (q.translation 0 : ℝ) * (2 : ℝ) ^ q.scale

/-- Half the side length of a one-dimensional literal CZ dyadic cube. -/
noncomputable def scratch_fiberCZCubeHalfSide (q : FiberCZCubeIndex) : ℝ :=
  ((2 : ℝ) ^ q.scale) / 2

/-- The genuine midpoint of a one-dimensional literal CZ dyadic cube. -/
noncomputable def scratch_fiberCZCubeMidpoint (q : FiberCZCubeIndex) : ℝ :=
  scratch_fiberCZCubeLo q + scratch_fiberCZCubeHalfSide q

private theorem scratch_realToFiberDyadicLine_coordinate_zero (x : ℝ) :
    WithLp.ofLp (realToFiberDyadicLine x) (0 : Fin 1) = x := by
  simp [realToFiberDyadicLine, MeasurableEquiv.piUnique]

/-- The literal `d = 1` cube is exactly the expected half-open real interval. -/
theorem scratch_realToFiber_mem_fiberCZCube_iff
    (q : FiberCZCubeIndex) (x : ℝ) :
    realToFiberDyadicLine x ∈ lacunaryCZDyadicCube q ↔
      x ∈ Ico (scratch_fiberCZCubeLo q)
        (scratch_fiberCZCubeLo q + 2 * scratch_fiberCZCubeHalfSide q) := by
  unfold lacunaryCZDyadicCube
  rw [Set.mem_preimage, Set.mem_pi]
  simp only [Set.mem_univ, forall_true_left]
  constructor
  · intro h
    have h0 := h 0
    rw [scratch_realToFiberDyadicLine_coordinate_zero] at h0
    change x ∈ Ico (scratch_fiberCZCubeLo q)
      (scratch_fiberCZCubeLo q + 2 * scratch_fiberCZCubeHalfSide q)
    convert h0 using 1
    all_goals
      unfold scratch_fiberCZCubeLo scratch_fiberCZCubeHalfSide
      push_cast
      ring_nf
  · intro h i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [scratch_realToFiberDyadicLine_coordinate_zero]
    change x ∈ Ico (scratch_fiberCZCubeLo q)
      (scratch_fiberCZCubeLo q + 2 * scratch_fiberCZCubeHalfSide q) at h
    convert h using 1
    all_goals
      unfold scratch_fiberCZCubeLo scratch_fiberCZCubeHalfSide
      push_cast
      ring_nf

/-- The library's named cube center is its lower endpoint in dimension one. -/
theorem scratch_lacunaryCZDyadicCubeCenter_eq_realToFiber_lo
    (q : FiberCZCubeIndex) :
    lacunaryCZDyadicCubeCenter q =
      realToFiberDyadicLine (scratch_fiberCZCubeLo q) := by
  ext i
  fin_cases i
  simp [lacunaryCZDyadicCubeCenter, scratch_fiberCZCubeLo,
    realToFiberDyadicLine, MeasurableEquiv.piUnique]

/-- In dimension one the library's enclosing radius is the full side length. -/
theorem scratch_lacunaryCZDyadicCubeRadius_eq_two_halfSide
    (q : FiberCZCubeIndex) :
    lacunaryCZDyadicCubeRadius q = 2 * scratch_fiberCZCubeHalfSide q := by
  unfold lacunaryCZDyadicCubeRadius scratch_fiberCZCubeHalfSide
  norm_num
  ring_nf

theorem scratch_fiberCZCubeHalfSide_pos (q : FiberCZCubeIndex) :
    0 < scratch_fiberCZCubeHalfSide q := by
  unfold scratch_fiberCZCubeHalfSide
  positivity

/-- A literal dyadic cell lies in the closed ball about its true midpoint
with radius half its side length. -/
theorem scratch_mem_fiberCZCube_midpoint_halfSide
    (q : FiberCZCubeIndex) {x : ℝ}
    (hx : realToFiberDyadicLine x ∈ lacunaryCZDyadicCube q) :
    |x - scratch_fiberCZCubeMidpoint q| ≤ scratch_fiberCZCubeHalfSide q := by
  rw [scratch_realToFiber_mem_fiberCZCube_iff] at hx
  rcases hx with ⟨hlo, hhi⟩
  apply abs_le.2
  constructor <;>
    unfold scratch_fiberCZCubeMidpoint <;>
    linarith

/-- The open midpoint interval is contained in the literal half-open cube.
This is the direction that transports pairwise disjointness. -/
theorem scratch_midpoint_openInterval_subset_fiberCZCube
    (q : FiberCZCubeIndex) :
    Ioo (scratch_fiberCZCubeMidpoint q - scratch_fiberCZCubeHalfSide q)
      (scratch_fiberCZCubeMidpoint q + scratch_fiberCZCubeHalfSide q) ⊆
      realToFiberDyadicLine ⁻¹' lacunaryCZDyadicCube q := by
  intro x hx
  change realToFiberDyadicLine x ∈ lacunaryCZDyadicCube q
  rw [scratch_realToFiber_mem_fiberCZCube_iff]
  rcases hx with ⟨hlo, hhi⟩
  constructor
  · unfold scratch_fiberCZCubeMidpoint at hlo
    linarith
  · unfold scratch_fiberCZCubeMidpoint at hhi
    linarith

/-- The public atom-support statement has exactly the closed-midpoint-ball
form consumed by the Section 8 scale-tail lemma. -/
theorem scratch_fiberCZBadAtom_support_midpoint_halfSide
    (f : FiberDyadicLine → ℂ) (q : FiberCZCubeIndex) {x : ℝ}
    (hx : lacunaryCZDyadicCubeBadAtom f q (realToFiberDyadicLine x) ≠ 0) :
    |x - scratch_fiberCZCubeMidpoint q| ≤ scratch_fiberCZCubeHalfSide q := by
  apply scratch_mem_fiberCZCube_midpoint_halfSide q
  exact lacunaryCZDyadicCubeBadAtom_support f q hx

/-- Pairwise disjoint literal cubes induce pairwise disjoint open midpoint
intervals, while the atom support remains allowed to meet their endpoints. -/
theorem scratch_pairwiseDisjoint_fiberCZCube_midpoint_openIntervals
    (U : Finset FiberCZCubeIndex)
    (hdisj : (↑U : Set FiberCZCubeIndex).PairwiseDisjoint
      lacunaryCZDyadicCube) :
    (↑U : Set FiberCZCubeIndex).PairwiseDisjoint
      (fun q => Ioo (scratch_fiberCZCubeMidpoint q - scratch_fiberCZCubeHalfSide q)
        (scratch_fiberCZCubeMidpoint q + scratch_fiberCZCubeHalfSide q)) := by
  intro q hq r hr hqr
  change Disjoint
    (Ioo (scratch_fiberCZCubeMidpoint q - scratch_fiberCZCubeHalfSide q)
      (scratch_fiberCZCubeMidpoint q + scratch_fiberCZCubeHalfSide q))
    (Ioo (scratch_fiberCZCubeMidpoint r - scratch_fiberCZCubeHalfSide r)
      (scratch_fiberCZCubeMidpoint r + scratch_fiberCZCubeHalfSide r))
  rw [Set.disjoint_left]
  intro x hxq hxr
  have hxq' : realToFiberDyadicLine x ∈ lacunaryCZDyadicCube q :=
    scratch_midpoint_openInterval_subset_fiberCZCube q hxq
  have hxr' : realToFiberDyadicLine x ∈ lacunaryCZDyadicCube r :=
    scratch_midpoint_openInterval_subset_fiberCZCube r hxr
  exact (Set.disjoint_left.1 (hdisj hq hr hqr)) hxq' hxr'

end

end Auto.Twisted
