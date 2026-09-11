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
complete | `def:gaussian`–`lem:domination`, lines 297–430 | Exact Gaussian/Fourier/derivative and scaled-kernel identities; exact bracket mass `2/9`; direct source-compatible bump data; `\Psi`, `c_\Psi`, `\Phi`, and their real-even Schwartz kernels. All three Gaussian-domination clauses now check: scale and translation bracket bounds, the literal four normalized-Gaussian superposition (including its positive scale-interval lower bound), and both translated `\psi` decay/L¹ identities. | 2026-09-10T22:45:38-07:00
complete | Section 3, `def:tree`–`lem:bl` (lines 433–733) | Literal boxes/faces, finite convex trees, boundary packing, local sizes, six-coordinate cube measures, and exact full-cube and edge Brascamp--Lieb estimates are kernel-checked and consumed by the later tree estimates. | 2026-09-11T06:06:05-07:00
complete | Section 4, `def:cube`–`prop:edge_tree` (lines 736–1375) | Literal local/endpoint/face/remainder forms and coordinate copies; exact scalar, fixed-box, and scale FTC telescopes; joint collection center--scale--space integrability; closure-based local-size kernel bounds; bounded-continuous one-box/tree telescopes; the exact `λ^37 R(r)^21` remainder and normalization bounds; literal active/passive transport, Fubini, cubical Cauchy--Schwarz, and copied-form positivity; and the exact full-cube and edge-tree conclusions (including both edge cancellations) are kernel-checked. Direct `lake env lean DFR/Auto/Twisted/Twisted.lean` check passes. | 2026-09-11T04:03:42-07:00
in progress | Section 5, `def:model`–`cor:local_model` (lines 1376–1819) | Literal local Cauchy--Schwarz, collection/forest additivity, exact full-cube and edge-tree comparison interfaces, scalar superposition masses, coordinate reordering, and tree-energy transport are kernel-checked. The formerly conditional fixed-scale localization now has unconditional expanded-kernel and center-expanded integrability, two-shear Fubini, and the exact signed spatial-profile identity; the model third kernel has proved first absolute moment and a uniform pointwise bound. The remaining model-range bridge is the faithful two-index spatial/scale exhaustion and the global initial estimate. | 2026-09-11T08:12:19-07:00
in progress | Sections 6–7, `ext:maximal`–`thm:initial_model` (lines 1822–2213) | Literal stopping ancestors, active-level and active-forest partitions, two/fourth anisotropic maximal comparisons, finite root packing, dyadic layer-cake, dominant-coordinate reindexing, and the finite active stopping-forest form bound are kernel-checked. Truncation/exhaustion, scalar maximal distribution estimates, and initial model-range assembly remain. | 2026-09-11T06:06:05-07:00
in progress | Section 8, `def:fiber_maximal`–`thm:extended_model` (lines 2216–2722) | The reciprocal region, capped-sum construction, interpolation simplex, and barycentric identities are kernel-checked. Fiberwise Calderón--Zygmund decomposition, weak extension, interpolation bridge, and extended model range remain. | 2026-09-11T06:06:05-07:00
in progress | Section 9, `def:permuted_model`–`thm:cone` (lines 2725–3040) | Coordinate permutations and source-weight invariance are kernel-checked; standard mode-lattice reciprocal-decay summability is now formalized. Cone localization, uniform symbol derivative/Fourier-series control, and multiplier-to-model decomposition remain. | 2026-09-11T06:06:05-07:00
not started | `thm:main`, lines 153–161 and proof lines 3041–3071 | Apply all three permuted model estimates to the cone expansion and sum Fourier modes | 2026-09-10T19:00:32-07:00

## Verification

Setup build: lake build passed (3345 jobs), 2026-09-10T09:46:43.7252496-04:00. Both DFR and the new
Auto.SmoothingIneq2D.Smoothing2D module were covered. Existing dependency linter warnings remain.
Axiom audits: not applicable yet; there are no completed Auto targets.
Reduction gate: closed.

Task 3 direct source check: `lake env lean -o DFR/Auto/Twisted/Twisted.olean
DFR/Auto/Twisted/Twisted.lean` passed at 2026-09-11T08:05:55-07:00 after the
fixed-scale localization and model-kernel first-moment/boundedness additions.
Existing linter warnings only; no `sorry`, `admit`, or added axioms in the owned
source. The audited localization and kernel terminals use only `propext`,
`Classical.choice`, and `Quot.sound`.

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
