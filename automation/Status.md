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
in progress | Sections 6–7, `ext:maximal`–`thm:initial_model` (lines 1822–2213) | Literal stopping ancestors, active-level and active-forest partitions, two/fourth anisotropic maximal comparisons, finite root packing, dyadic layer-cake, dominant-coordinate reindexing, and the finite active stopping-forest form bound are kernel-checked. The strict real full-model bound is now assembled: compact-scale full-slab integrability, the two-index exhaustion, explicit stopping-distribution powers, four-linear `L^q` normalization, zero-input branches, and a constant uniform over translation/coefficient/input give the real strict range. The actual complex model form is identified with its exact 32-term real/imaginary expansion for arbitrary measurable complex unit coefficients, and the literal complex active-coordinate form now transports exactly to it under every source coordinate permutation. Both give uniform complex strict-range terminals. Continuous `L^p` extension remains. | 2026-09-11T11:13:51-07:00
in progress | Section 8, `def:fiber_maximal`–`thm:extended_model` (lines 2216–2722) | The reciprocal region, capped-sum construction, interpolation simplex, real truncated operator, Fubini/Young--Hölder and weak-maximal packages, kernel majorants, mean-zero cancellation, and finite positive interval-tail package are kernel-checked. The finite `p>1` tail package is canonical: it proves the exact scalar `α⁻¹/72` scale integral, the `Mr²/|x-c|²` cancellation tail, a one-dimensional strong dyadic maximal `MemLp` interface, and the finite pairwise-disjoint interval-tail cutoff/Hölder terminal for actual scale-integrated bad fibers. The source fiber grid is aligned exactly with the public one-dimensional dyadic cubes; its parent containment/strictness, laminarity, index injectivity, parent-average bound, stopping maximality, `(H,2H]` selected-average range, selected-fiber disjointness, finite selected-rectangle measure identity, selected-length density/Fubini bound, and countable exceptional-set weak bound are canonical. The countable exceptional estimate now applies over the sigma-finite transverse Lebesgue space by deriving finite selected-fiber mass from global integrability. Literal coordinate convolution and the actual finite-scale operator are additive in a selected slot under explicit line/scale integrability; the bounded-input Young estimate needs only measurability; and measurable linewise active-kernel bracket domination is canonical. The measurable one-fiber Calderón--Zygmund decomposition, its general operator weak extension, the genuine four-vertex multilinear interpolation bridge, and the extended model range remain. | 2026-09-11T15:41:41-07:00
in progress | Section 9, `def:permuted_model`–`thm:cone` (lines 2725–3040) | Coordinate permutations and source-weight invariance are kernel-checked; the strict real model estimate is transported uniformly to every active coordinate with its corresponding `2/4` stopping thresholds. The exact `ν/8` mode parameter, its source-weight comparison, and the degree-110 coefficient/degree-100 model `tsum` consumer are formalized. The source-compatible auxiliary cone localization divides out passive Gaussians exactly on cone factors, is compactly supported away from the singular origin, and its cutoff and localized symbol are globally smooth through order 110. The full coordinate-to-Fréchet derivative comparison and Leibniz package yields the uniform global `C*M` localized-symbol derivative bound through order 110. Its fixed-support period-eight extension is constructed coordinate by coordinate, transferred continuously to the standard unit three-torus, and identified exactly with the original symbol on the fundamental cube. The canonical Fourier package now gives all-coordinate degree-110 coefficient decay, scale measurability after zero extension, strict-range summability of the actual mode forms, pointwise torus/fundamental-cube Fourier reconstruction, and the exact fixed-scale global third-cone/mode form reconstruction. The remaining Section 9 step is the full three-cone/form-decomposition assembly at the extended range, including the joint scale interchange. | 2026-09-11T15:41:41-07:00
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

Task 3 direct source check: `lake env lean -o DFR/Auto/Twisted/Twisted.olean
DFR/Auto/Twisted/Twisted.lean` passed at 2026-09-11T10:07:48-07:00 after the
strict real initial-range integration (`initialModelFullForm_bound`). `git diff
--check` and the owned-source `sorry`/`admit` scan were clean. Its dedicated
axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean -o DFR/Auto/Twisted/Twisted.olean
DFR/Auto/Twisted/Twisted.lean` passed at 2026-09-11T10:20:40-07:00 after
integrating the Section 8 real truncated-operator and fixed-scale
Young--Hölder package. `git diff --check` and the owned-source `sorry` scan
were clean. The audited terminal `eLpNorm_modelFixedOperatorFormIntegrand_le`
uses only `propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean -o DFR/Auto/Twisted/Twisted.olean
DFR/Auto/Twisted/Twisted.lean` passed at 2026-09-11T10:25:00-07:00 after
integrating the active-coordinate strict initial-range estimate
(`activeModelFullForm_bound_weight100`). `git diff --check` and the
owned-source `sorry`/`admit` scan were clean. Its terminal axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean -o DFR/Auto/Twisted/Twisted.olean
DFR/Auto/Twisted/Twisted.lean` passed at 2026-09-11T10:30:02-07:00 after
integrating the coordinate dyadic-maximal and literal bracket-convolution weak
`(1,1)` terminals. `git diff --check` and the owned-source `sorry` scan were
clean. The three terminal axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean -o DFR/Auto/Twisted/Twisted.olean
DFR/Auto/Twisted/Twisted.lean` passed at 2026-09-11T10:34:32-07:00 after
integrating the uniform active-coordinate strict range and the literal
`ν/8` lattice-mode summation bridge. `git diff --check` and the owned-source
`sorry`/`admit` scan were clean. The audited terminals use only `propext`,
`Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean -o DFR/Auto/Twisted/Twisted.olean
DFR/Auto/Twisted/Twisted.lean` passed at 2026-09-11T11:05:15-07:00 after
integrating the literal complex model bridge and the Section 8 kernel-majorant
terminals. `git diff --check` and the owned-source `sorry`/`admit` scan were
clean. Axiom audits of `exists_uniform_LiteralModelFullForm_bound_weight100`
and `kernelDilate_ModelThirdKernel_sourceWeight_bracket_majorant` report only
`propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean -o DFR/Auto/Twisted/Twisted.olean
DFR/Auto/Twisted/Twisted.lean` passed at 2026-09-11T11:13:51-07:00 after
integrating the literal complex active-coordinate transport and uniform bound.
`git diff --check` and the owned-source `sorry`/`admit` scan were clean. Axiom
audits of `LiteralActiveModelFullForm_permute_to_third` and
`exists_uniform_LiteralActiveModelFullForm_bound_weight100` report only
`propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean -o DFR/Auto/Twisted/Twisted.olean
DFR/Auto/Twisted/Twisted.lean` passed at 2026-09-11T11:34:57-07:00 after
integrating the active-kernel convolution domination and genuine scaled spatial
derivative package. `git diff --check` and the owned-source `sorry`/`admit`
scan were clean. Axiom audits of the public active kernel majorant,
dyadic-convolution, and derivative-majorant terminals report only `propext`,
`Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean -o DFR/Auto/Twisted/Twisted.olean
DFR/Auto/Twisted/Twisted.lean` passed at 2026-09-11T11:52:07-07:00 after
integrating the mean-zero bad-fiber cancellation-under-the-integral package.
`git diff --check` and the owned-source `sorry`/`admit` scan were clean. Axiom
audits of the exact centering identity and active-kernel bad-fiber terminal
report only `propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean -o DFR/Auto/Twisted/Twisted.olean
DFR/Auto/Twisted/Twisted.lean` passed at 2026-09-11T12:01:02-07:00 after
integrating the auxiliary cone-localization package. `git diff --check` and
the owned-source `sorry`/`admit` scan were clean. Audits of the exact
passive-Gaussian cancellation, compact support, derivative-bound, and global
localized-symbol smoothness terminals report only `propext`,
`Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean -o DFR/Auto/Twisted/Twisted.olean
DFR/Auto/Twisted/Twisted.lean` passed at 2026-09-11T12:09:23-07:00 after
integrating the coordinate-to-Fréchet derivative comparison and the global
localized-symbol derivative package. `git diff --check` and the owned-source
`sorry`/`admit` scan were clean. Audits of the full rescaled-multiplier and
localized-symbol derivative terminals report only `propext`,
`Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean -o DFR/Auto/Twisted/Twisted.olean
DFR/Auto/Twisted/Twisted.lean` passed at 2026-09-11T12:11:33-07:00 after
integrating the exact passive-Gaussian cone-factor identities and the compact
support bridge for the localized complex symbol. `git diff --check` and the
owned-source `sorry`/`admit` scan were clean. Their axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean -o /private/tmp/Twisted-interval-tail-root-check.olean
DFR/Auto/Twisted/Twisted.lean` passed at 2026-09-11T12:19:37-07:00 after
integrating the interval-radius bad-fiber first-moment, cancellation, and
finite positive-tail (L^1) package. `git diff --check` and the owned-source
`sorry`/`admit` scan were clean. The interval-tail terminal audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean -o DFR/Auto/Twisted/Twisted.olean
DFR/Auto/Twisted/Twisted.lean` passed at 2026-09-11T12:36:00-07:00 after
integrating the coordinatewise period-eight localized-symbol extension, its
continuous unit-three-torus form, and the fundamental-cube identification.
`git diff --check` and the owned-source `sorry`/`admit` scan were clean. The
periodization terminals audit only `propext`, `Classical.choice`, and
`Quot.sound`.

Task 3 direct source check: `lake env lean -o
/private/tmp/Twisted-mode-bridge-root-check.olean DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T12:51:53-07:00 after integrating the exact literal
third-active spatial/Fourier mode bridge and its conditional
`multiplierForm` version. `git diff --check` and the owned-source
`sorry`/`admit` scan were clean. The independent terminal audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean -o
/private/tmp/Twisted-section8-tail-root-check.olean DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T13:17:40-07:00 after integrating the finite Section 8
scale-tail and `p>1` cutoff/Hölder package. `git diff --check` and the
owned-source `sorry`/`admit` scan were clean. The independent audit of all
seven public terminals—including `badFiber_scaleTail_le_intervalTail`—reports
only `propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean -o
/private/tmp/Twisted-selection-fourier-root-check.olean DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T13:57:26-07:00 after integrating the exact source-fiber
dyadic-grid alignment and selected-interval maximality/disjointness package,
and the raw-cube/torus Fourier coefficient bridge with first-coordinate
fourth-order decay. `git diff --check` and the owned-source
`sorry`/`admit`/`axiom` scan were clean. The fixed-fiber key-terminal audit
reports only `propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean -o
/private/tmp/Twisted-countable-exceptional-check.olean DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T15:02:56-07:00 after integrating the countable
selected-rectangle exceptional-set bound, finite-fiber-mass integrability
bridge, and complete degree-110 Fourier coefficient/reconstruction package.
`git diff --check` and the owned-source `sorry`/`admit`/`axiom` scan were
clean. The independently audited Fourier terminals use only `propext`,
`Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean -o
/private/tmp/Twisted-measurable-bracket-check.olean DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T15:41:41-07:00 after integrating the sigma-finite
selected-exceptional bound, actual good--bad operator additivity, measurable
bounded-input coordinate Young bound, measurable linewise bracket domination,
and fixed-scale third-cone/mode reconstruction. `git diff --check` and the
owned-source `sorry`/`admit`/`axiom` scan were clean; only pre-existing linter
warnings occurred during the direct source check.

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
