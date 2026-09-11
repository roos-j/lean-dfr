# Formalization status

## Main theorem overview

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
not started | arXiv:2008.10140v2, Theorem 5 | Task 1: trilinear smoothing inequality | 2026-09-10T09:42:06.7141336-04:00
not started | Task 2 blueprint pending | Task 2: 3d smoothing inequality | 2026-09-10T09:42:06.7141336-04:00
in progress | blueprints/task_3_twisted_blueprint.tex, Theorem `thm:main` | Task 3: anisotropic twisted paraproduct; source audit and forward dependency plan | 2026-09-10T18:55:25-07:00
not started | Task 4 blueprint pending | Task 4: main theorem via Reduction | 2026-09-10T09:42:06.7141336-04:00

## Proof ledger

No mathematical statements or proofs have been translated during setup.
After reading each available source, expand that task into substantial steps in
forward dependency order before implementing it. Task 4 follows all of Tasks 1-3.
Place any justified reusable-prerequisite sections before the consuming proof rows.

### Task 3 — anisotropic twisted paraproduct

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | blueprints/task_3_twisted_blueprint.tex, Sections 1–10 and proof of `thm:main` | Source audit: target, all internal declarations, external analytic inputs, and proof dependency order read | 2026-09-10T19:00:32-07:00
complete | `def:anisotropy`, lines 57–79 | `Auto.Anisotropy` with `homogeneousDimension`, diagonal `dilate`/`dilateLinear`, radius, inverse/composition, determinant, and homogeneous-radius identities | 2026-09-10T19:11:05-07:00
complete | `def:schwartz` and `lem:schwartz`, lines 177–278 | Mathlib wrappers for products, translations, coordinate derivatives, Fourier/inverse Fourier, convolution, density; injective affine pullbacks; external products; fixed fibers; generic Schwartz-preserving fiber integration with uniform absolute bounds; and coordinate convolution by a linear shear are kernel-checked | 2026-09-10T20:01:00-07:00
complete | `def:multiplier` and `lem:pairing`, lines 101–151 | The translated product `P_f` is a Schwartz fiber integral through the stated injective map; the defining multiplier integral is absolutely convergent; the bounded measurable symbol is represented by its `L^∞` regular tempered distribution; and the literal E9 frequency representation is proved via an explicit measure-preserving diagonal/remainder reassembly and an absolutely integrable Fourier/Fubini calculation. | 2026-09-10T21:00:41-07:00
not started | `def:gaussian`–`lem:domination`, lines 297–430 | Fixed Gaussian/bracket kernels, infinite-product bump/cutoffs, and domination/superposition estimates | 2026-09-10T19:09:03-07:00
not started | Section 3, `def:tree`–`lem:bl` (lines 433–733) | Anisotropic dyadic geometry, local sizes, boundary packing, and cube/edge Brascamp--Lieb estimates | 2026-09-10T19:00:32-07:00
not started | Section 4, `def:cube`–`prop:edge_tree` (lines 736–1373) | Cubical local forms; differential telescoping, boundary cancellation, remainders, and full/edge tree estimates | 2026-09-10T19:00:32-07:00
not started | Section 5, `def:model`–`cor:local_model` (lines 1376–1819) | Model form localization, local/global energy identities, and local model bound | 2026-09-10T19:00:32-07:00
not started | Sections 6–7, `ext:maximal`–`thm:initial_model` (lines 1822–2213) | Maximal/stopping-time machinery, finite-forest estimate, truncation convergence, and initial model exponent range | 2026-09-10T19:00:32-07:00
not started | Section 8, `def:fiber_maximal`–`thm:extended_model` (lines 2216–2722) | Fiberwise Calderón--Zygmund decomposition, weak extension, multilinear interpolation bridge, exponent simplex, extended model range | 2026-09-10T19:00:32-07:00
not started | Section 9, `def:permuted_model`–`thm:cone` (lines 2725–3040) | Coordinate permutation, cone localization, derivative/Fourier-series control, and multiplier-to-model decomposition | 2026-09-10T19:00:32-07:00
not started | `thm:main`, lines 153–161 and proof lines 3041–3071 | Apply all three permuted model estimates to the cone expansion and sum Fourier modes | 2026-09-10T19:00:32-07:00

## Verification

Setup build: lake build passed (3345 jobs), 2026-09-10T09:46:43.7252496-04:00. Both DFR and the new
Auto.SmoothingIneq2D.Smoothing2D module were covered. Existing dependency linter warnings remain.
Axiom audits: not applicable yet; there are no completed Auto targets.
Reduction gate: closed.

## Continuation

Task 1 starter: DFR/Auto/SmoothingIneq2D/Smoothing2D.lean.
Next: assign Task 1, read Theorem 5 and its proof, and record the source dependency
plan. Tasks 2-4 have no blueprints yet. Exported theorem interfaces: none.

Task 3 active owner: Codex root task3-20260910-1855. Source:
blueprints/task_3_twisted_blueprint.tex, Theorem `thm:main`; target module:
DFR/Auto/Twisted/Twisted.lean. The task-scoped directory has been created at that
exact prescribed path. `Auto.Anisotropy`, `homogeneousDimension`, `dilate`,
`dilateLinear`, `radius`, `derivativeWeight`, `coordinateDirection`, and
`IsAnisotropicMultiplier` are present.  The Task 3 Schwartz toolkit now contains
the direct Mathlib wrappers, injective affine pullback, external product,
fixed-fibre declarations, and a generic fixed-fiber integral preserving
`SchwartzMap`, with smoothness, weighted derivative decay, and the blueprint's
uniform absolute fiber integral bound. Coordinate convolution is next. The latest
direct source check passed at 2026-09-10T19:57:50-07:00. The forward source order is: analytic base;
dyadic geometry and local sizes; cubical telescoping/tree estimates; model form and
energies; stopping-time initial range; fiberwise extension/interpolation; cone
decomposition; main theorem. The blueprint's explicitly external ingredients are
one-dimensional Hardy--Littlewood maximal/differentiation and multilinear
Marcinkiewicz interpolation; their exact Lean coverage has been audited. The pinned
`lean_spherical` modules provide only unary/linear maximal, Marcinkiewicz,
Mikhlin, and interpolation results, not the required tree estimate or multilinear
interpolation bridge. Potential reusable foundational declarations are recorded in
the task work notes; no dependency theorem is claimed as a direct solution.

Skill copies: SHA-256 verified against installed editions (Codex: 6 files; Claude: 5).
Git diff --check passed; automation/raw.md is ignored.
The initial broad Mathlib import build was stopped during starter compilation;
the final starter uses Mathlib.Analysis.Normed.Module.Basic and the full build passed.

## Current verification policy

2026-09-10T09:58:01.5996155-04:00 - Auto is excluded from lakefile.toml by explicit user instruction. The setup build above is historical evidence only. Current lake build passed (3343 jobs) for configured targets; it does not check Auto. Owned Auto sources require separate direct lake env lean checks. Both vendored skill editions and their bootstrap references now follow this policy.
Task 1 source study is underway; no mathematical declarations have been added or proved. Theorem 5 and portions of Section 3 have been read; the full proof/dependency audit remains unfinished.

2026-09-10T09:58:47.5716059-04:00 - Task 1 paused by explicit user request after the Auto build-inclusion instruction cleanup. No Lean source edits or proofs were made. Source study remains incomplete; resume with the full Section 3 dependency audit only when directed. Documentation diff check passed.

2026-09-10T18:23:34.428125-04:00 - Layout correction: task files use the existing DFR/Auto task directories. Source paths in this record have been updated; proof statuses and historical verification timestamps are unchanged. Each branch retains only its own preexisting mathematical content.
