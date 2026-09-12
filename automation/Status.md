# Formalization status

## Main theorem overview

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
not started | arXiv:2008.10140v2, Theorem 5 | Task 1: trilinear smoothing inequality | 2026-09-10T09:42:06.7141336-04:00
not started | Task 2 blueprint pending | Task 2: 3d smoothing inequality | 2026-09-10T09:42:06.7141336-04:00
in progress | blueprints/task_3_twisted_blueprint.tex, Theorem `thm:main` | Task 3: anisotropic twisted paraproduct; Sections 1-4 and 9's analytic inputs complete, Section 8 fiberwise Calderón--Zygmund frontier active | 2026-09-11T19:17:00-07:00
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
in progress | Sections 6–7, `ext:maximal`–`thm:initial_model` (lines 1822–2213) | Literal stopping ancestors, active-level and active-forest partitions, two/fourth anisotropic maximal comparisons, finite root packing, dyadic layer-cake, dominant-coordinate reindexing, and the finite active stopping-forest form bound are kernel-checked. The strict real full-model bound is now assembled: compact-scale full-slab integrability, the two-index exhaustion, explicit stopping-distribution powers, four-linear `L^q` normalization, zero-input branches, and a constant uniform over translation/coefficient/input give the real strict range. The actual complex model form is identified with its exact 32-term real/imaginary expansion for arbitrary measurable complex unit coefficients, and the literal complex active-coordinate form now transports exactly to it under every source coordinate permutation. Both give uniform complex strict-range terminals. The real strict-range form bound is now recovered from the complex one by complexifying real Schwartz data, and cutting the coefficient to a finite positive scale interval gives the exact finite-scale form estimate. The `L^p` duality bridge is canonical: an `L^p` function is normed by Schwartz test pairings (via the pinned `LeanSpherical.Auto.LpSpaceFacts` `lpPairing`/dense-range machinery), and `L¹ ∩ L^∞` interpolation supplies `MemLp` at every finite exponent above one. Applying these to the actual truncated operator now yields the source's duality step itself: the four Schwartz slots are assembled from a zeroth test function and the three operator inputs, a complex Schwartz pairing splits into its two real pairings without loss, and `lpNorm_ModelTruncatedOperator_le_of_strict_range` gives `‖U^{a,b}_{u,c}(f)‖_{R_0} ≤ C·U(u)^100·∏_j ‖f_j‖_{P_j}` with `R_0` conjugate to the zeroth exponent, uniformly in the truncation and coefficient. The Fubini joint-integrability premise is now discharged outright: on a compact positive scale interval the pairing integrand is dominated by `|f_0(x)|` times a scale-uniform kernel-mass constant, which is integrable against the finite logarithmic scale measure. Both analytic premises of the duality step are now discharged. The source's coordinate-decay observation is canonical: a coordinate convolution is controlled by any bound valid along that coordinate line alone, translating a Schwartz input along coordinate `i` preserves its order-ten bracket decay in every other coordinate uniformly along the line, and the reciprocal three-coordinate order-twenty bracket product dominates the radial majorant, hence is integrable on `E3`. These give a scale-uniform integrable majorant for the model integrand, hence integrability and uniform boundedness of the truncated operator, hence its `MemLp` membership at every finite exponent above one. `lpNorm_ModelTruncatedOperator_le_of_realSchwartz` is therefore the unconditional source estimate `‖U^{a,b}_{u,c}(f)‖_{R_0} ≤ C·U(u)^100·∏_j‖f_j‖_{P_j}` on Schwartz data. The fiberwise good-part estimate is also integrated over the transverse variables by Tonelli, giving the source's global `‖g_m‖_P^P ≤ (2H)^{P/p-1}‖f_m‖_p^p` for the canonical stopping data (finite-`p`-mass fibers and `|f|^p` dyadic averages); fibers of infinite mass need no exclusion because the majorant is already infinite there. The estimate is then transported to the ambient space `E3` through the measure-preserving coordinate split, giving the source's good-part bound in the ambient variables with the canonical ambient stopping data. The good part's Chebyshev budget at the base exponent is canonical, together with the source's arithmetic that makes it level-independent: with height `H = λ/A` and the exponent identity `δ·R_0 = R_0 - 1`, the budget collapses to `2^{R_0-1}·A`. The third display of `lem:fiber_kernel` is also canonical: a coordinate convolution against the active model kernel is dominated by the coordinate maximal function with the source's `U(u)^{10}` weight and a scale-uniform constant, obtained by chaining the bracket majorant with the one-dimensional radial-bracket shell decomposition. The compact truncation is also removed from the scale integral: the logarithmic scale measure is identified with the explicit density `dt/t` in set-integral form, and the truncated integral is dominated by the full positive-scale tail of its absolute value, uniformly in the truncation. The model integrand's passive-slot factorization is canonical: bounds on the two slots other than the Calderón--Zygmund slot pull out of the integrand, leaving that slot's coordinate convolution, for every choice of active slot. Integrating it over the scale interval gives the source's estimate of the truncated operator by the two passive constants times the active slot's full positive-scale tail, uniformly in the truncation. The active convolution is also identified with the source's fiber-line integral: translating along the active coordinate shifts only the active component of the coordinate split, and reflecting the line variable leaves the full real integral unchanged, so a field pulled back through the split convolves exactly as `∫ g(y,z)·(κ)_s(x_m - y) dy`. With the selected bad field in the active slot this makes the slot's absolute scale tail literally `selectedFiberScaleTail`: the convolution is the finite sum of the atoms' fiber-line integrals, and the triangle inequality plus finite interchange of the atom sum with the scale integral give the source's tail. Chaining this with the scale-integrated passive factorization proves `eq:cz_bad_pointwise` in operator form: with the selected bad field in the Calderón--Zygmund slot, the truncated operator is dominated by the two passive constants times the source's selected scale tail, uniformly in the truncation. The weak-one bookkeeping is matched to it by a weighted consumer: the source's exterior bad bound carries the passive maximal functions as an `x`-dependent weight, so the tail entering the three-piece inclusion is the weighted tail. That tail's budget is now canonical: a three-factor Hölder package at output exponent one, and the Chebyshev step bounding the exterior weighted level set by the product of the tail's own `L^p` norm and the two passive maximal `L^{P_j}` norms. `eq:cz_bad_pointwise` is now stated in the source's own form: the passive slots contribute their coordinate maximal functions evaluated at the same point, so the exterior bad bound is literally `∏_{j≠m}M^{(j)}f_j(x)` times the selected scale tail. The three budgets are now assembled: `eq:one_fiber` holds in finite-family form, with the exceptional-set measure, the Chebyshev good budget at the base exponent, and the Hölder budget for the weighted bad tail all in their canonical source shapes. Two of the three budgets are already level-independent at the source's stopping height `H = λ/A`: the good one by the exponent identity, and now the exceptional one, where the selected-length estimate `|E| ≤ 2H^{-1}` collapses `λ|E|` to `2A`. The tail budget's fiberwise `p = 1` input is also canonical: the source's `h_m(·,z)` has mass exactly `intervalTailMass` times the selected total length, and that countable total length obeys the stopping bound `H^{-1}∫|f(y,z)|dy` by passing the finite selected-length estimate through the subtype index. Integrating that fiberwise mass over the transverse variables gives the source's global tail bound `‖h_m‖_1 ≤ intervalTailMass·H^{-1}‖f_m‖_1`, restated in the `eLpNorm` shape the weighted budget consumes. The stopping height's two opposite appearances — `H^{1/p}` in the bad-atom mass and `H^{-1/p}` in the tail norm — are proved to cancel, which is the source's reason the bad contribution is level-independent. The passive factors' estimate `‖M^{(j)}f‖_p ≤ C_p‖f‖_p` of `def:fiber_maximal` is now available in the `eLpNorm` shape the three-factor Hölder step consumes, derived from the already-canonical ambient lintegral bound. The three normalized budgets also combine: once each piece is bounded by a multiple of `𝒜_u`, the three-piece inclusion yields the source's single level-independent constant. The countable passage's analytic core is also proved: a uniform level-set bound for a sequence transfers to any almost-everywhere limit with no loss in the level, since a strict inequality at the limit is already strict along the tail. Its hypothesis is supplied by the source's own observation that at most one selected atom is nonzero at each point: a finite family containing that point's index already reproduces the countable bad field, so along any exhausting sequence the finite bad fields are eventually constant, hence convergent. | 2026-09-11T22:06:11-07:00
in progress | Section 8, `def:fiber_maximal`–`thm:extended_model` (lines 2216–2722) | The reciprocal region, capped-sum construction, interpolation simplex, real truncated operator, Fubini/Young--Hölder and weak-maximal packages, kernel majorants, mean-zero cancellation, and finite positive interval-tail package are kernel-checked. The finite `p>1` tail package is canonical: it proves the exact scalar `α⁻¹/72` scale integral, the `Mr²/|x-c|²` cancellation tail, a one-dimensional strong dyadic maximal `MemLp` interface, and the finite pairwise-disjoint interval-tail cutoff/Hölder terminal for actual scale-integrated bad fibers. The literal selected dyadic grid is now also canonically adapted to that midpoint/radius tail interface, including centered-open containment and selected-family pairwise disjointness. The source fiber grid is aligned exactly with the public one-dimensional dyadic cubes; its parent containment/strictness, laminarity, index injectivity, parent-average bound, stopping maximality, `(H,2H]` selected-average range, selected-fiber disjointness, finite selected-rectangle measure identity, selected-length density/Fubini bound, and countable exceptional-set weak bound are canonical. The countable exceptional estimate now applies over the sigma-finite transverse Lebesgue space by deriving finite selected-fiber mass from global integrability. Literal coordinate convolution and the actual finite-scale operator are additive in a selected slot under explicit line/scale integrability; the bounded-input Young estimate needs only measurability; and measurable linewise active-kernel bracket domination is canonical. The countable doubled-radius interval-tail package now proves the source's `p = 1` clause of `lem:interval_tails` with its exact mass. One-dimensional dyadic differentiation is proved from Mathlib's uniformly-locally-doubling density theorem, together with the scale-`k` dyadic cell containing a point, its midpoint/radius closed-ball identification, and the exact average comparison. The source's stopping existence (`A_J(z) → 0` on growing ancestors, hence every above-height cell lies in a maximal selected one) and the Jensen/Hölder cell bound `|f_I(z)| ≤ A_I(z)^{1/p}` are canonical. All three source good-part clauses of `lem:fiber_cz` are now canonical: the almost-everywhere stopping bound `|g| ≤ (2H)^{1/p}`, the `p`-mass comparison `‖g‖_p ≤ ‖f‖_p` via countable additivity over the disjoint selected cells, and the interpolated fiberwise `‖g‖_P^P ≤ (2H)^{P/p-1}‖f‖_p^p` for finite `P ≥ p`. The remaining Section 8 steps are the transverse Tonelli integration of the good-part bounds, the one-fiber weak extension `lem:one_fiber`, the genuine four-vertex multilinear interpolation bridge, and the extended model range. | 2026-09-11T19:17:00-07:00
in progress | Section 9, `def:permuted_model`–`thm:cone` (lines 2725–3040) | Coordinate permutations and source-weight invariance are kernel-checked; the strict real model estimate is transported uniformly to every active coordinate with its corresponding `2/4` stopping thresholds. The exact `ν/8` mode parameter, its source-weight comparison, and the degree-110 coefficient/degree-100 model `tsum` consumer are formalized. The source-compatible auxiliary cone localization divides out passive Gaussians exactly on cone factors, is compactly supported away from the singular origin, and its cutoff and localized symbol are globally smooth through order 110. The full coordinate-to-Fréchet derivative comparison and Leibniz package yields the uniform global `C*M` localized-symbol derivative bound through order 110. Its fixed-support period-eight extension is constructed coordinate by coordinate, transferred continuously to the standard unit three-torus, and identified exactly with the original symbol on the fundamental cube. The canonical Fourier package now gives all-coordinate degree-110 coefficient decay, scale measurability after zero extension, strict-range summability of the actual mode forms, pointwise torus/fundamental-cube Fourier reconstruction, and the exact fixed-scale global third-cone/mode form reconstruction. The remaining Section 9 step is the full three-cone/form-decomposition assembly at the extended range, including the joint scale interchange. | 2026-09-11T15:41:41-07:00
not started | `thm:main`, lines 153–161 and proof lines 3041–3071 | Apply all three permuted model estimates to the cone expansion and sum Fourier modes | 2026-09-10T19:00:32-07:00
complete | continuation checkpoint | Resumption audit: the previously unverified selected-atom scale-tail bridge (`selectedFiber_finset_fiberCZBadAtom_scaleTail_holder_cutoff_le`) now passes the direct source check and its axiom audit. The strict finite-scale duality bridge (`StrictOperatorExtensionScratch`) and the cone-symbol multiplier certificate (`ThirdConeMultiplierScratch`) remain scratch-only. | 2026-09-11T19:03:07-07:00

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

Task 3 direct source check: `lake env lean -o
/private/tmp/Twisted-selected-tail-bridge-check.olean DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T17:49:37-07:00 after integrating the literal
selected-dyadic midpoint/radius adapter for the finite interval-tail
cutoff/Hölder estimate. `git diff --check` and the owned-source
`sorry`/`admit`/`axiom` scan were clean; only pre-existing linter warnings
occurred during the direct source check.

Task 3 direct source check: `lake env lean -o
/private/tmp/Twisted-finite-selected-operator-check.olean DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T18:03:57-07:00 after integrating the bounded-measurable
finite selected fiber good/bad fields, their literal cancellation and pointwise
bounds, and the exact finite-scale truncated-operator split. `git diff --check`
and the owned-source `sorry`/`admit`/`axiom` scan were clean; only pre-existing
linter warnings occurred during the direct source check.

Task 3 direct source check: `lake env lean -o DFR/Auto/Twisted/Twisted.olean
DFR/Auto/Twisted/Twisted.lean` passed at 2026-09-11T18:47:00-07:00 on resumption,
before any new edits, confirming the paused checkpoint's unverified
selected-atom scale-tail bridge. `#print axioms` on
`selectedFiber_finset_fiberCZBadAtom_scaleTail_holder_cutoff_le` and
`ModelTruncatedOperator_fiberCZ_weakOne_of_selectedFiberScaleTail_coordinateFiberGoodBad_data`
reports only `propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T18:55:00-07:00 after promoting the countable
doubled-radius interval-tail package (reused from
`CountableIntervalTailCandidate.lean`) and the new one-dimensional dyadic
differentiation package. `git diff --check` and the owned-source
`sorry`/`admit` scan were clean. Axiom audits of
`integrable_intervalTailTsum`, `integral_intervalTailTsum`,
`ae_le_of_forall_fiberDyadicAverage_le`, and
`setAverage_closedBall_eq_fiberDyadicAverage` report only `propext`,
`Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T19:03:07-07:00 after promoting the source stopping-existence
lemma and the Jensen/Hölder dyadic-cell bound. `git diff --check` and the
owned-source `sorry`/`admit` scan were clean. Axiom audits of
`fiberDyadicAverage_le_of_forall_not_mem_selected`,
`abs_fiberDyadicIntervalAverage_le_rpow`,
`fiberDyadicProperAncestor_scale_lt`, and `fiberDyadicIndexAt_eq_of_mem`
report only `propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T19:17:00-07:00 after promoting the three source good-part
clauses of `lem:fiber_cz`. `git diff --check` and the owned-source
`sorry`/`admit` scan were clean. Axiom audits of
`ae_abs_fiberDyadicCountableGoodField_le`,
`lintegral_rpow_fiberDyadicCountableGoodField_le`, and
`lintegral_rpow_fiberDyadicCountableGoodField_le_exponent` report only
`propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T19:26:29-07:00 after adding the pinned dependency import
`LeanSpherical.Auto.LpSpaceFacts` and promoting the real-form/`L^p`-duality
block. `git diff --check` and the owned-source `sorry`/`admit` scan were clean.
Axiom audits of
`exists_uniform_real_ModelScaleIntervalTruncation_bound_from_strict_weight100`,
`lpNorm_le_of_schwartz_test_pairing_bound`, and `memLp_of_one_and_top` report
only `propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T19:35:13-07:00 after promoting the Schwartz test-pairing
block and the `L^{R_0}` operator bound of the duality step. `git diff --check`
and the owned-source `sorry`/`admit` scan were clean. Axiom audits of
`norm_integral_ModelTruncatedOperator_mul_schwartz_le` and
`lpNorm_ModelTruncatedOperator_le_of_strict_range` report only `propext`,
`Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T19:43:23-07:00 after promoting the compact-scale Fubini
premise for the truncated pairing integrand. `git diff --check` and the
owned-source `sorry`/`admit` scan were clean. The axiom audit of
`integrable_modelTruncatedOperatorPairingIntegrand` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T19:51:39-07:00 after promoting the coordinate-decay block
for the truncated operator. `git diff --check` and the owned-source
`sorry`/`admit` scan were clean. Axiom audits of
`abs_ModelCoordinateConvolution_le_of_line_bound`,
`exists_realSchwartz_line_bracket_bound`, and
`integrable_prod_coordinate_bracket_twenty` report only `propext`,
`Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T20:01:50-07:00 after promoting the scale-uniform majorant,
the operator's integrability and uniform bound, its `MemLp` membership, and the
resulting unconditional strict-range output estimate. `git diff --check` and the
owned-source `sorry`/`admit` scan were clean. Axiom audits of
`exists_integrable_majorant_modelTruncatedOperatorIntegrand`,
`integrable_ModelTruncatedOperator_of_realSchwartz`,
`memLp_complexified_ModelTruncatedOperator_of_realSchwartz`, and
`lpNorm_ModelTruncatedOperator_le_of_realSchwartz` report only `propext`,
`Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T20:07:40-07:00 after promoting the canonical stopping-data
abbreviation and the transverse Tonelli integration of the good-part estimate.
`git diff --check` and the owned-source `sorry`/`admit` scan were clean. The
axiom audit of `lintegral_prod_rpow_fiberDyadicCountableGoodField_le` reports
only `propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T20:13:04-07:00 after promoting the ambient transport of the
good-part estimate through the measure-preserving coordinate split.
`git diff --check` and the owned-source `sorry`/`admit` scan were clean. The
axiom audit of
`lintegral_rpow_coordinateFiberDyadicCountableGoodField_le` reports only
`propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T20:18:58-07:00 after promoting the good-part Chebyshev
budget and its level-independent normalization. `git diff --check` and the
owned-source `sorry`/`admit` scan were clean. Axiom audits of
`weakOne_good_budget_of_lintegral_le` and
`weakOne_good_budget_normalization` report only `propext`, `Classical.choice`,
and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T20:24:30-07:00 after promoting the maximal domination of
the active coordinate convolution. `git diff --check` and the owned-source
`sorry`/`admit` scan were clean. The axiom audit of
`abs_activeModelCoordinateConvolution_le_coordinateDyadicBallMaximal` reports
only `propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T20:30:40-07:00 after promoting the scale-density
identification and the truncation-free scale-tail bound. `git diff --check` and
the owned-source `sorry`/`admit` scan were clean. The axiom audit of
`abs_integral_modelScaleInterval_le_scaleTail` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T20:37:09-07:00 after promoting the active-kernel slot
identities and the passive-slot factorization of the model integrand.
`git diff --check` and the owned-source `sorry`/`admit` scan were clean. The
axiom audit of `abs_modelTruncatedOperatorIntegrand_le_passive` reports only
`propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T20:42:45-07:00 after promoting the scale-integrated passive
factorization. `git diff --check` and the owned-source `sorry`/`admit` scan were
clean. The axiom audit of
`abs_ModelTruncatedOperator_le_passive_mul_scaleTail` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T20:47:54-07:00 after promoting the active-coordinate split
shift, the line-reflection identity, and the fiber-line form of the coordinate
convolution. `git diff --check` and the owned-source `sorry`/`admit` scan were
clean. The axiom audits of
`ModelCoordinateConvolution_coordinateSplit_eq_fiberLine` and
`coordinateSplit_sub_smul_coordinateDirection` report only `propext`,
`Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T20:53:09-07:00 after promoting the identification of the
bad slot's absolute scale tail with `selectedFiberScaleTail`. `git diff --check`
and the owned-source `sorry`/`admit` scan were clean. The axiom audit of
`integral_scaleTail_coordinateFiberBadField_le_selectedFiberScaleTail` reports
only `propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T20:59:40-07:00 after promoting the operator form of
`eq:cz_bad_pointwise`. `git diff --check` and the owned-source `sorry`/`admit`
scan were clean. The axiom audit of
`abs_ModelTruncatedOperator_bad_le_passive_mul_selectedFiberScaleTail` reports
only `propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T21:04:43-07:00 after promoting the weighted weak-one
consumer. `git diff --check` and the owned-source `sorry`/`admit` scan were
clean. The axiom audit of
`ModelTruncatedOperator_fiberCZ_weakOne_of_weighted_selectedFiberScaleTail`
reports only `propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T21:10:16-07:00 after promoting the three-factor Hölder
package and the weighted-tail Chebyshev budget. `git diff --check` and the
owned-source `sorry`/`admit` scan were clean. Axiom audits of
`eLpNorm_threefold_product_le` and `weakOne_weighted_tail_budget` report only
`propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T21:16:18-07:00 after promoting `eq:cz_bad_pointwise` with
the source's maximal-function weight. `git diff --check` and the owned-source
`sorry`/`admit` scan were clean. The axiom audit of
`abs_ModelTruncatedOperator_bad_le_maximalWeight_mul_selectedFiberScaleTail`
reports only `propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T21:22:42-07:00 after promoting the finite-family form of
`eq:one_fiber`. `git diff --check` and the owned-source `sorry`/`admit` scan
were clean. The axiom audit of
`ModelTruncatedOperator_weakOne_finite_of_canonical_budgets` reports only
`propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T21:27:46-07:00 after promoting the level-independent
exceptional budget. `git diff --check` and the owned-source `sorry`/`admit`
scan were clean. Axiom audits of `weakOne_exception_budget_normalization` and
`weakOne_exception_budget_of_measureReal_le` report only `propext`,
`Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T21:33:05-07:00 after promoting the fiberwise selected-tail
mass identity and the countable selected-length bound. `git diff --check` and
the owned-source `sorry`/`admit` scan were clean. Axiom audits of
`integral_selectedFiber_intervalTailTsum` and `tsum_selectedFiber_length_le`
report only `propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T21:38:45-07:00 after promoting the global tail mass bound.
`git diff --check` and the owned-source `sorry`/`admit` scan were clean. The
axiom audit of `integral_prod_selectedTail_le` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T21:43:34-07:00 after promoting the tail-budget
normalization and the `eLpNorm` form of the global tail mass. `git diff --check`
and the owned-source `sorry`/`admit` scan were clean. Axiom audits of
`weakOne_tail_budget_normalization` and `eLpNorm_one_selectedTail_le` report
only `propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T21:49:33-07:00 after promoting the `eLpNorm` form of the
coordinate maximal theorem. `git diff --check` and the owned-source
`sorry`/`admit` scan were clean. The axiom audit of
`eLpNorm_coordinateDyadicBallMaximal_le` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T21:54:21-07:00 after promoting the combination of the
three normalized budgets. `git diff --check` and the owned-source
`sorry`/`admit` scan were clean. The axiom audit of
`weakOne_combine_normalized_budgets` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T22:00:37-07:00 after promoting the almost-everywhere limit
transfer for weak-type bounds. `git diff --check` and the owned-source
`sorry`/`admit` scan were clean. The axiom audit of `weakBound_of_ae_tendsto`
reports only `propext`, `Classical.choice`, and `Quot.sound`.

Task 3 direct source check: `lake env lean` on `DFR/Auto/Twisted/Twisted.lean`
passed at 2026-09-11T22:06:11-07:00 after promoting the finite-to-countable
exhaustion of the selected bad fields. `git diff --check` and the owned-source
`sorry`/`admit` scan were clean. Axiom audits of
`fiberCZBadField_eq_countableBadField_of_mem` and
`tendsto_fiberCZBadField_countableBadField` report only `propext`,
`Classical.choice`, and `Quot.sound`.

## Continuation

Task 1 starter: DFR/Auto/SmoothingIneq2D/Smoothing2D.lean.
Next: assign Task 1, read Theorem 5 and its proof, and record the source dependency
plan. Tasks 2-4 have no blueprints yet. Exported theorem interfaces: none.

Task 3 owner: Claude root task3-20260911-1842 (reassigned 2026-09-11T18:42:00-07:00 after the previous owner's user-requested pause). Source:
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

## Task 3 next step (2026-09-11T19:26:29-07:00)

Reused pinned-dependency declarations (audited, allowed axioms only):
`Auto.LpSpaceFacts.memLp_of_power_interpolation`,
`Auto.LpSpaceFacts.lpNorm_le_of_simple_test_pairing_bound`,
`Auto.LpSpaceFacts.lpPairing_apply_toLp_eq_integral`,
`Auto.LpSpaceFacts.one_le_ofReal_conjExponent`,
`Auto.LpSpaceFacts.ofReal_holderConjugate`, plus Mathlib's
`SchwartzMap.denseRange_toLpCLM` and
`IsUnifLocDoublingMeasure.ae_tendsto_average`.

Frontier: `lem:one_fiber`, specifically its pointwise bad-part estimate
`eq:cz_bad_pointwise`. Available in consumed form: the exceptional-set measure
bound, the selected bad-atom scale tail, the good-part Chebyshev budget with its
level-independent normalization, the base strong estimate (unconditional on
Schwartz data), `lem:fiber_cz` fiberwise/globally/ambiently, the maximal
domination of `lem:fiber_kernel`, and the truncation-free scale-tail bound.
`eq:one_fiber` is proved in finite-family form with all three budgets
normalized and combined; the countable passage has both its analytic core (weak
bounds transfer to an almost-everywhere limit) and its hypothesis at the level of
the bad fields (finite families exhaust the countable one, eventually constant at
each point). Next: transport that pointwise convergence through the truncated
operator — the operator is linear in the Calderón--Zygmund slot and the
finite-scale integrand is dominated uniformly, so dominated convergence applies —
to obtain `eq:one_fiber` for the countable family, completing `lem:one_fiber`.
Then: the
four-vertex multilinear Marcinkiewicz bridge (`ext:interpolation`),
`thm:extended_model`, the Section 9 three-cone assembly, and `thm:main`.
