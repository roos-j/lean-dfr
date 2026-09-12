# Source discrepancies

No mathematical source audit has been performed during setup.
No discrepancies recorded. Add timestamped source locations, differences, and
resolutions here as required by the autoformalize skill.

2026-09-10T18:23:34.428125-04:00 - Repository layout error: setup created a root Auto directory despite existing DFR/Auto task directories. Corrected task locations, verification commands, agent entry point, and both vendored skills/bootstrap guides. Files are relocated without replacing their contents. Main and Tasks 2-4 receive only their original starter and instruction corrections, never Task 1 formalization work.

2026-09-10T19:00:32-07:00 - Task 3 source audit, `blueprints/task_3_twisted_blueprint.tex`, proof of `thm:cone` at lines 3036--3037: the prose cites only `lem:model_convergence` when identifying the scale limits of all three active-coordinate model forms. That lemma is stated for active coordinate 3; lines 2753--2794 (`lem:permutation`) are also required for coordinates 1 and 2. Resolution: preserve the theorem statement and insert the verified coordinate-permutation bridge in the Lean dependency order before the cone-decomposition proof.

2026-09-10T19:29:44-07:00 - Task 3 source convention, `lem:schwartz`, lines 191--278: the blueprint writes Euclidean-coordinate derivative and weight estimates, while Mathlib's `SchwartzMap` uses Fréchet derivatives and its raw product carrier has the max product norm.  In finite dimension these norms and derivative presentations are equivalent, but not definitionally equal.  Resolution: keep the source statements unchanged and make each needed finite-dimensional/product-norm comparison explicit; do not treat the two formulations as definitional identities.

2026-09-10T20:16:00-07:00 - Task 3 library representation gap, `def:multiplier` and `lem:pairing`, lines 101--151: Mathlib's `Function.HasTemperateGrowth.toTemperedDistribution` requires global `ContDiff ℝ ∞`, while the source permits a multiplier that is only smooth off the origin and merely measurable at the origin. Resolution: use the available `L^∞` (`p = ⊤`) embedding instead: the source's global order-zero bound gives `m : Lp ℂ ⊤ volume`, whose regular tempered distribution has the required action. Its inverse Fourier transform and the literal multiplier integral are now kernel-checked equal; the multiplier hypothesis was not strengthened.

2026-09-10T21:10:01-07:00 - Task 3 `def:bumps`, lines 308--386: neither Mathlib nor the pinned dependency library provides the source's literal infinite convolution-product construction together with its smooth-limit theorem. Resolution: implement a direct even `ContDiffBump` with inner radius `1/2` and outer radius `1`, then define the spatial bump by inverse Fourier transformation. This preserves every downstream-used cutoff property (real/even/Schwartz, `0 ≤ b ≤ 1`, support in `[-1,1]`, and plateau on `[-1/2,1/2]`); no equality to the source's particular infinite product is asserted.

2026-09-10T22:40:34-07:00 - Task 3 `lem:domination`, equation `eq:superposition`, lines 413--415: an initial in-progress Lean definition used the preliminary spatial bump `B = F^{-1}b` in the two low-frequency slots. The blueprint instead uses `varphi = F^{-1}Phi`. Resolution: replace those slots with the already formalized real kernel `conePhiPhysicalReal`; its order-fifty Schwartz decay is used in the completed superposition argument. No theorem statement was weakened or changed.

2026-09-11T21:04:43-07:00 - Task 3 Lean-interface gap (not a source discrepancy),
`lem:one_fiber`, `eq:cz_bad_pointwise`, blueprint lines 2495--2500: the
previously canonical weak-one consumer
`ModelTruncatedOperator_fiberCZ_weakOne_of_selectedFiberScaleTail_coordinateFiberGoodBad_data`
takes its exterior bad bound as the bare `selectedFiberScaleTail`. The source's
bound carries the two passive coordinate maximal functions as an `x`-dependent
weight, which cannot be pulled out of the later spatial integration. Resolution:
the general assembly `ModelTruncatedOperator_fiberCZ_weakOne_of_good_bad_data`
already accepts an arbitrary exterior tail, so a weighted consumer
`ModelTruncatedOperator_fiberCZ_weakOne_of_weighted_selectedFiberScaleTail` was
added and is the one matching `eq:cz_bad_pointwise`. The narrower consumer is
preserved; no source statement changed.

2026-09-11T22:29:17-07:00 - Task 3 dependency audit (not a source discrepancy),
`ext:interpolation`, blueprint lines 2538--2558: the pinned `lean_spherical`
checkout provides only unary Marcinkiewicz interpolation
(`Auto.Spherical.Auxiliary.marcinkiewicz_*`, including the off-diagonal
source/output two-pair forms in `MSSBase` and `AHRSUpperBounds`) and a finite-sum
bilinear geometric-mean bound
(`AHRSUpperBounds.norm_bilinear_finset_sum_le_interpolate`). None of these is the
four-vertex trilinear Marcinkiewicz theorem the source cites; the unary theorems
interpolate one exponent pair, while `ext:interpolation` interpolates a
three-dimensional reciprocal simplex. Resolution: develop the multilinear
theorem inside the task folder as the local instructions require, reusing the
unary machinery and Mathlib's weighted geometric-mean inequalities where they
apply. No source statement changed; the suggested "derive it from the existing
interpolation machinery" route is recorded as not directly available.

2026-09-11T23:05:00-07:00 - Task 3 dependency audit, refinement of the
2026-09-11T22:29:17-07:00 entry, `ext:interpolation`: the suggested route of
iterating the pinned dependency's unary (including off-diagonal source/output
two-pair) Marcinkiewicz theorems slot by slot does not reach the source's target.
Fixing two slots makes the trilinear operator linear in the third, so an edge of
the simplex can be crossed by a unary theorem; but the source's four vertices are
`b` and `b + b_0 e_m` for `m = 1,2,3`, and the target `b + b_0(ϑ_1,ϑ_2,ϑ_3)` is
interior to a genuinely three-dimensional tetrahedron. Reaching it would require
weak bounds at points such as `b + b_0 ϑ_1 e_1 + b_0 e_2`, which are not among
the hypotheses and are not produced by any single-slot interpolation of them.
Resolution: the four-vertex trilinear theorem is being developed directly. Its
finite-layer decomposition, trilinear expansion, four-vertex geometric mean,
two-sided geometric summability, and vertex-combination step are proved; the
remaining obstacle is the weak-to-strong passage, which needs a Lorentz-type
pairing because weak-`L^{r_a}` bounds are not summable by the triangle
inequality. No source statement changed.

2026-09-12T00:15:00-07:00 - Task 3 structural finding (not a source
discrepancy), `ext:interpolation`.  Two updates to the 2026-09-11T23:05:00-07:00
entry.

First, the weak-to-strong passage recorded there as the remaining obstacle is
resolved and no longer needs a Lorentz-type pairing.  Level-set bounds at two
exponents straddling the target integrate against `r t^{r-1}` after splitting
the level axis where the two bounds agree, and the resulting constant is the
weighted geometric mean of the two weak constants.  The exponent ordering this
needs is available: `lem:exponent_simplex` gives `0 < beta_0 < b_0 < 1/4`, the
three shifted vertices have output exponent exactly `1`, the base vertex has
`1/(1-b_0)`, and the target `1/(1-beta_0)` lies strictly between them.

Second, a genuine obstruction to the naive assembly is now identified, and it is
not the one previously recorded.  The four-fold weighted geometric mean of the
per-layer endpoint constants collapses exactly to the product of the
target-exponent layer sizes `N_{j,k} = 2^k mu_j(S_{j,k})^{1/p_j}`, with the pure
powers of the dyadic level cancelling identically.  But summing that product
over the multi-index `k` in `Z^3` by the triangle inequality would require
`sum_k N_{j,k}` to be controlled by `||f_j||_{p_j}`, whereas the layer machinery
supplies only `sum_k N_{j,k}^{p_j} <= ||f_j||_{p_j}^{p_j}`.  For `p_j > 1` no
such control exists, since `l^{p_j}` is not contained in `l^1`.  The exact
geometric mean at the weights `eq:weights` is therefore not summable over the
multi-indices, and the assembly must instead perturb the weights: the target is
interior to the tetrahedron, so the weights admit small independent
perturbations in three directions, each purchasing a factor `2^{k_j delta}` of
one sign or the other, and taking the minimum over the perturbations yields the
geometric decay that makes the sum over `Z^3` converge.  This is what the
already-proved two-sided geometric summability
(`summable_min_two_rpow`) is for.  No source statement changed.

2026-09-12T00:55:00-07:00 - Task 3 structural finding (not a source
discrepancy), `ext:interpolation` applied in `thm:extended_model`: an input-class
mismatch between the external hypothesis and its application.

`ext:interpolation` is stated for a trilinear operator on complex simple
functions of finite measure support: both its weak endpoint hypotheses and its
strong conclusion are quantified over that class. The endpoint bounds this
development supplies for the model operator — the base strong bound from
`thm:initial_model` via duality, and the three weak bounds from
`lem:one_fiber` — are established for Schwartz inputs. Neither class contains
the other: a nonzero simple function is not Schwartz, and a nonzero Schwartz
function is not simple.

Consequently the external theorem does not apply to the model operator as a
direct instantiation. Two transfers are needed: the weak endpoint bounds must
be moved from the Schwartz class to the simple-function class in order to
satisfy the hypothesis, and the strong conclusion must be moved back from the
simple-function class to the Schwartz class in order to be used. The source
performs the corresponding step itself at the end of the proof of
`thm:extended_model` ("take the scale limit for Schwartz inputs by
Lemma `lem:model_convergence`, then use density"), and its own statement of
`ext:interpolation` carries the clause "the map extends to these `L^p` spaces
when initially defined on their dense simple-function subspaces".

Recorded as the remaining structural gap between the external hypothesis as
stated and its use. The exponent-level side conditions are all discharged
(vertex exponents exceed one, reciprocal vectors affinely independent, output
reciprocals and weights matching the convex combinations), and simple functions
of finite measure support are confirmed to lie in every endpoint `L^q`, so the
hypothesis's quantifiers are over a class on which all endpoint norms are
finite. No source statement changed, and no additional hypothesis has been
assumed to paper over the mismatch.

2026-09-12T04:22:00-07:00 - Task 3 structural finding (not a source
discrepancy), `thm:cone`: the cone-symbol multiplier certificate needs a
direction-sensitive Leibniz rule that the pinned Mathlib does not provide.

The mode-symbol certificate was obtained cheaply because the mode symbol is a
scale-independent profile precomposed with the anisotropic dilation, so its
derivatives follow from the chain rule for a linear map. The cone symbol does
not have that shape: it is the multiplier `m` itself multiplied by the cone
cutoffs at dilated coordinates, and `m` is not precomposed with the dilation.
Its derivative bound therefore requires the Leibniz expansion the source
performs, distributing each derivative between `m` and the cutoffs.

The obstacle is that `eq:symbol`, as formalized in `IsAnisotropicMultiplier`,
bounds only *coordinate-direction evaluations*
`||(iteratedFDeriv k m xi) (fun r => coordinateDirection (sigma r))||`, with a
bound depending on the anisotropic weight of the particular direction sequence
`sigma`. The pinned Mathlib supplies only the norm-based product inequality
`norm_iteratedFDeriv_mul_le`, whose right side involves the full operator norms
`||iteratedFDeriv i m xi||`. Those operator norms are not what the hypothesis
gives, and passing from coordinate evaluations to operator norms collapses the
anisotropy: bounding a multilinear map by its values on basis tuples replaces
the sharp exponent `rho^{-alpha . sigma}` by a maximum over all direction
sequences, which is too lossy to reassemble the required `sigma`-specific
bound after the product.

What is needed is the direction-sensitive rule
`d^k(fg)(v_1..v_k) = sum over subsets S of [k] of d^{|S|}f(v_S) * d^{k-|S|}g(v_{S^c})`,
each term of which is again a coordinate-direction evaluation and so matches
the hypothesis exactly. This is not in the pinned Mathlib and would have to be
proved by induction on the order, with the Finset-subset reindexing that
entails.

Recorded as the remaining obstacle for the cone-symbol certificate. The
mode-symbol certificate is complete and the one-mode bridge is unconditional;
the cone symbol's vanishing at the origin, support confinement, and
infinite-order vanishing off the support are also proved, so only the
derivative bound is outstanding. No source statement changed.

2026-09-12T04:27:00-07:00 - Task 3, correction to the 2026-09-12T04:22:00-07:00
entry: the direction-sensitive Leibniz rule is **not** required for the
cone-symbol certificate. The previous entry was too pessimistic.

The cone symbol has the same precomposition shape as the mode symbol, once the
right intermediate function is named. Writing
`G_t(eta) = m(D_t^{-1} eta) * coneCutoff(eta)` — which is exactly the shape of
the already-formalized `localizedSymbol` — one has
`thirdConeFrequencySymbol alpha m t = G_t . D_t`, because
`m(D_t^{-1}(D_t xi)) = m(xi)`. The chain rule for the dilation therefore
applies here as well, and it is the chain rule that carries the direction
sensitivity: an ordered coordinate derivative of the composite is
`t^{alpha . sigma}` times the same derivative of `G_t`.

Consequently the bound needed on `G_t` is only a *direction-insensitive*
operator-norm bound `||iteratedFDeriv k G_t eta|| <= C M`, uniform in `eta` and
in `t`. That is precisely what `exists_localizedSymbol_derivative_bound`
already proves for the localized symbol, by the Leibniz argument the source
performs — so the Leibniz work is done in the file, not missing from Mathlib.
Its constant is visibly independent of the scale (it is built from the
cutoff derivative bound and combinatorial factors only), although the
statement as written existentially quantifies the constant after fixing the
scale and so does not expose that independence.

Remaining work for this certificate is therefore: introduce the cone analogue
of the localized symbol with the cone cutoffs actually used by
`thirdConeFrequencySymbol`, obtain the scale-uniform operator-norm derivative
bound for it along the existing lines, and then transport through the dilation
exactly as was done for the mode symbol. No new Mathlib infrastructure is
needed. No source statement changed.

## Higher-order unification against an uncurried symbol is expensive

Composing a jointly continuous function of scale and frequency with the map
fixing the frequency — to get continuity in the scale alone — exhausted the
elaborator's budget outright, even though every ingredient elaborates in under
a second on its own. The cost is the higher-order unification: matching a
composition against a lambda in which the large symbol definition appears
forces the elaborator to unfold that definition while it still has
metavariables to solve.

The fix is to name the intermediate step. The symbol is definitionally a fixed
profile precomposed with the dilation; rewriting along that equation first, and
only then composing, elaborates immediately, because the composition is then
matched against a small term. Where a definition is large, prefer rewriting
along its characterizing equation over relying on definitional unfolding inside
unification.

## A duplicated library lemma

A nonnegativity lemma for the `L^p` norm was proved here from the definition
before checking whether the library already had it. It does — under the obvious
name — and the search that missed it looked only in the definition file rather
than the companion file where the simp lemmas live.

The cost was small, but the habit matters: for a fact this generic, search the
whole library by name pattern before proving it. The redundant copy is left in
place rather than removed, since removing a promoted declaration would mean
rewriting history in a file that is only ever appended to; later uses should
prefer the library lemma.
