# Task 3 formalization status

Per-label status for `blueprints/task_3_twisted_blueprint.tex`.
Narrative commentary lives in `StatusLog.md`.

Entry shape: `\label{Manuscript label}: [Status] (Lean: [lean name]) (timestamp)`.
Definitions use `Todo` / `Completed`; theorems use `Todo` /
`Statement completed` / `Proof completed`.

The development itself is `DFR/Auto/Twisted/Twisted.lean`, which is sorry-free
and whose declarations audit to `propext, Classical.choice, Quot.sound` only.
Per-section modules restate that section's labelled results in the
blueprint's wording; the top-level module is `DFR/Auto/Twisted.lean`.

Every Lean name below has been confirmed to elaborate against the corpus.
`External` marks the two `exttheorem` environments, which the manuscript
quotes without proof; these are carried as hypotheses by design.

## Section 1: Conventions and the main statement
Lean file: DFR/Auto/Twisted/ConventionsAndMainStatement/ConventionsAndMainStatement.lean

### Definitions
\label{def:anisotropy}: Completed (Lean: Auto.Twisted.Anisotropy) (2026-09-12T14:22-0700)
\label{def:multiplier}: Completed (Lean: Auto.Twisted.Anisotropy.IsAnisotropicMultiplier) (2026-09-12T14:22-0700)

### Theorems
\label{lem:pairing}: Proof completed (Lean: Auto.Twisted.lem_pairing_integrable) (2026-09-12T14:22-0700)
\label{lem:pairing}: Proof completed (Lean: Auto.Twisted.lem_pairing_eq_frequencyForm) (2026-09-12T14:22-0700)
\label{thm:main}: Proof completed (Lean: Auto.Twisted.thm_main, Auto.Twisted.anisotropicParaproduct_unconditional, Auto.Twisted.anisotropicParaproduct_of_interpolation). Now unconditional: ext:interpolation is proved, so thm_main carries no hypothesis beyond the exponent conditions. (2026-09-18T09:30-0700)

`thm:main` is proved from `ext:interpolation` alone, which is the manuscript's
own single external input.  The chain is:
`exists_exponentSimplex_base` (`lem:exponent_simplex`) supplies a base point for
each coordinate relabeling, `exists_abs_ModelFullForm_le_extended`
(`thm:extended_model`) supplies the real full-scale model bound there,
`exists_uniform_LiteralActiveModelFullForm_bound_of_real` complexifies it and
carries it to every active coordinate, `coneModeFullForm_eq_
LiteralActiveModelFullForm` (`lem:permutation`) identifies the cone mode forms
with active-coordinate model forms, and `thm:cone` sums the modes.  The Lean
hypothesis `hU : FourVertexMarcinkiewiczUniform volume` is `ext:interpolation`.

## Section 2: Function spaces and fixed bumps
Lean file: DFR/Auto/Twisted/FunctionSpacesAndFixedBumps/FunctionSpacesAndFixedBumps.lean

### Definitions
\label{def:schwartz}: Completed (Lean: Auto.Schwartz3) (2026-09-12T14:22-0700)
\label{def:gaussian}: Completed (Lean: Auto.gaussian) (2026-09-12T14:22-0700)
\label{def:bumps}: Completed (Lean: Auto.standardFrequencyBump, Auto.conePsi, Auto.conePhi) (2026-09-12T14:22-0700)

### Theorems
\label{lem:schwartz}: Proof completed (Lean: Auto.schwartz_memLp) (2026-09-12T14:22-0700)
\label{lem:bumps}: Proof completed (Lean: Auto.cPsi_pos, Auto.conePhi_eq_cPsi_of_abs_le_one, Auto.standardFrequencyBump_eq_one_of_abs_le_half) (2026-09-12T14:22-0700)
\label{lem:domination}: Proof completed (Lean: Auto.gaussianSuperposition_domination) (2026-09-12T14:22-0700)

## Section 3: Dyadic geometry and local sizes
Lean file: DFR/Auto/Twisted/DyadicGeometryAndLocalSizes/DyadicGeometryAndLocalSizes.lean

### Definitions
\label{def:tree}: Completed (Lean: Auto.AnisoBox, Auto.BoxCollection) (2026-09-12T14:22-0700)
\label{def:faces}: Completed (Lean: Auto.boxFaceCoordinate, Auto.boxFaceSet, Auto.boxFaceArea) (2026-09-12T14:22-0700)
\label{def:size}: Completed (Lean: Auto.treeLocalSize) (2026-09-12T14:22-0700)

### Theorems
\label{lem:geometry}: Proof completed (Lean: Auto.card_boxChildren, Auto.volume_root_eq_sum_volume_leaves) (2026-09-12T14:22-0700)
\label{lem:size}: Proof completed (Lean: Auto.cubeBracketAverage_le_treeLocalSize_product_of_mem_closure) (2026-09-12T14:22-0700)
\label{lem:bl}: Proof completed (Lean: Auto.cubeEdgeBracketAverage_le_product_secondMoments) (2026-09-12T14:22-0700)

## Section 4: Cubical telescoping with boundary terms
Lean file: DFR/Auto/Twisted/CubicalTelescopingWithBoundaryTerms/CubicalTelescopingWithBoundaryTerms.lean

### Definitions
\label{def:cube}: Completed (Lean: Auto.localCubeForm) (2026-09-12T14:22-0700)
\label{def:boundary}: Completed (Lean: Auto.cubeBoundaryFaceForm, Auto.cubeTreeRemainder) (2026-09-12T14:22-0700)

### Theorems
\label{lem:local_integrability}: Proof completed (Lean: Auto.integrable_cubeBracketWeight_center_space) (2026-09-12T14:22-0700)
\label{lem:oned_telescoping}: Proof completed (Lean: Auto.cubeCoordinate_oneDim_telescoping) (2026-09-12T14:22-0700)
\label{lem:telescoping_identity}: Proof completed (Lean: Auto.cubeCoordinate_box_telescoping_weighted) (2026-09-12T14:22-0700)
\label{lem:face_cancellation}: Proof completed (Lean: Auto.cubeTreeBoxBoundaryForm_eq_cubeBoundaryFaceForm) (2026-09-12T14:22-0700)
\label{lem:remainder}: Proof completed (Lean: Auto.abs_cubeTreeRemainder_le_of_uniform_bounds) (2026-09-12T14:22-0700)
\label{cor:remainder_norms}: Proof completed (Lean: Auto.cubeTreeRemainder_bound_of_boundedContinuous) (2026-09-12T14:22-0700)
\label{lem:cube_cs}: Proof completed (Lean: Auto.fullCubeTreeEstimate_of_boundedContinuousCubeCS) (2026-09-12T14:22-0700)
\label{prop:cube_tree}: Proof completed (Lean: Auto.fullCubeTreeEstimate_of_boundedContinuous) (2026-09-12T14:22-0700)
\label{prop:edge_tree}: Proof completed (Lean: Auto.edgeTreeEstimate_of_boundedContinuous) (2026-09-12T14:22-0700)

## Section 5: The model form and its localization
Lean file: DFR/Auto/Twisted/TheModelFormAndItsLocalization/TheModelFormAndItsLocalization.lean

### Definitions
\label{def:model}: Completed (Lean: Auto.Twisted.ModelSpatialIntegrand) (2026-09-12T14:22-0700)
\label{def:local_model}: Completed (Lean: Auto.expandedModelLocalForm) (2026-09-12T14:22-0700)

### Theorems
\label{lem:localization}: Proof completed (Lean: Auto.expandedModelLocalForm_eq_neg_jointIntegral_of_integrable) (2026-09-12T14:22-0700)
\label{lem:local_cs}: Proof completed (Lean: Auto.expandedModelLocalForm_cauchySchwarz_of_boundedContinuous) (2026-09-12T14:22-0700)
\label{lem:local_energies}: Completed (Lean: Auto.modelEnergyOne, Auto.modelEnergyTwo) (2026-09-12T14:22-0700)
\label{lem:global_energy}: Proof completed (Lean: Auto.modelEnergyTwoOn_eq_jointIntegral_of_integrable) (2026-09-12T14:22-0700)
\label{cor:local_model}: Proof completed (Lean: Auto.stoppingTree_localModel_bound_of_energyBounds) (2026-09-12T14:22-0700)

## Section 6: Stopping time and the initial exponent range
Lean file: DFR/Auto/Twisted/StoppingTimeAndTheInitialExponentRange/StoppingTimeAndTheInitialExponentRange.lean

### Definitions
\label{def:stopping}: Completed (Lean: Auto.sourceStoppingTree, Auto.sourceStoppingMaximal) (2026-09-12T14:22-0700)

### Theorems
\label{ext:maximal}: Proof completed (Lean: Auto.Twisted.ext_maximal_strong_type, Auto.Twisted.ext_maximal_lebesgue_differentiation, Auto.Twisted.ext_maximal_dyadic_differentiation, Auto.Twisted.ext_maximal_fiber_strong_type, Auto.Twisted.ext_maximal_fiber_differentiation) (2026-09-13T20:05-0700)

`ext:maximal` is quoted by the manuscript as an external result; it is proved here.
The strong `(q,q)` bound is for the blueprint's own operator, the supremum over all
positive radii: `lineMaximalRaw_le_two_mul_dyadicBallMaximalRaw` compares it with the
dyadic-radius maximal function of `lean_spherical` at the cost of a factor two, since
`Int.log 2 r + 1` gives a dyadic radius in `[r, 2r)`.  Lebesgue differentiation is
Mathlib's Besicovitch--Vitali theorem read along `r → 0⁺`; the dyadic form follows
because the standard dyadic interval of scale `k` containing `x` lies in the ball of
radius `2^k` about `x`, of exactly twice its measure.  The fiber statements are the
one-dimensional ones applied to each fiber, together with the repository's
`coordinateDyadicBallMaximal_lintegral_bound` for the fiber maximal estimate.
\label{lem:maximal_size}: Proof completed (Lean: Auto.boxLocalSize_two_le_anisotropicMaximalTwo) (2026-09-12T14:22-0700)
\label{lem:stopping}: Proof completed (Lean: Auto.sourceStoppingTree_energyBounds_of_boundedContinuous) (2026-09-12T14:22-0700)
\label{lem:forest_bound}: Proof completed (Lean: Auto.sourceStoppingForestWeightedSum_le_maximalLevelSum) (2026-09-12T14:22-0700)
\label{lem:model_convergence}: Proof completed (Lean: Auto.tendsto_expandedModelLocalForm_centerExhaustion_restrictScale) (2026-09-12T14:22-0700)
\label{thm:initial_model}: Proof completed (Lean: Auto.exists_uniform_initialModelFullForm_bound_weight100) (2026-09-12T14:22-0700)

## Section 7: Fiberwise Calderon-Zygmund decomposition
Lean file: DFR/Auto/Twisted/FiberwiseCalderonZygmundDecomposition/FiberwiseCalderonZygmundDecomposition.lean

### Definitions
\label{def:fiber_maximal}: Completed (Lean: Auto.coordinateDyadicBallMaximal) (2026-09-12T14:22-0700)
\label{def:weak_norm}: Completed (Lean: Auto.Twisted.weakNorm) (2026-09-12T14:22-0700)

### Theorems
\label{lem:fiber_kernel}: Proof completed (Lean: Auto.abs_activeModelCoordinateConvolution_le_coordinateDyadicBallMaximal) (2026-09-12T14:22-0700)
\label{lem:fiber_cz}: Proof completed (Lean: Auto.lintegral_prod_rpow_fiberDyadicCountableGoodField_le) (2026-09-12T14:22-0700)
\label{lem:interval_tails}: Proof completed (Lean: Auto.Twisted.lpNorm_finset_double_intervalTails_le_of_radius_sum, Auto.integral_finset_double_intervalTails_le_of_radius_sum) (2026-09-12T18:55-0700)
\label{lem:one_fiber}: Proof completed (Lean: Auto.Twisted.ModelTruncatedOperator_weakNorm_le_one_fiber_unbounded) (2026-09-13T17:40-0700)
\label{ext:interpolation}: Proof completed (Lean: Auto.Twisted.fourVertexMarcinkiewiczUniformMeasurable_of_sigmaFinite, Auto.Twisted.fourVertexMarcinkiewiczUniformMeasurable_volume_E3, Auto.Twisted.fourVertexMarcinkiewicz_of_measurable). The recorded predicates were adjusted to carry the operator measurability hypothesis, which is necessary (see ErrorReport) and is discharged at the one use site by Auto.Twisted.measurable_ModelTruncatedOperator_of_measurable; sigma-finiteness of Lebesgue measure on E3 is automatic. thm:main is now unconditional: Auto.Twisted.anisotropicParaproduct_unconditional. (2026-09-14T01:05-0700)
\label{lem:exponent_simplex}: Proof completed (Lean: Auto.Twisted.affineIndependent_exponentSimplex_vertices) (2026-09-12T14:22-0700)
\label{thm:extended_model}: Proof completed (Lean: Auto.Twisted.exists_abs_ModelFullForm_le_extended) (2026-09-13T13:20-0700)

`ext:interpolation` remains External, and the entry records what is and is not
proved about it, since a substantial amount now is.

Proved unconditionally, from the four endpoint hypotheses alone:
`weakNorm_le_of_four_weakNorm` combines the four endpoint weak bounds into one at
any interior exponent, with the geometric-mean constant;
`lintegral_rpow_le_of_symmetric_weight_pair` upgrades that to the *strong* `L^R`
bound, losslessly, at every weight vector whose exponent is `R`, by placing two
weight vectors symmetrically about it;
`exists_straddling_output_exponents` shows the affine independence forces the
target output exponent to be strictly straddled by two of the four, which is what
makes the weak-to-strong passage applicable at all; and
`weakNorm_interior_le_of_indicator_inputs` proves the theorem's own conclusion,
with its own constant `∏_a A_a^{ϑ_a}` and no slack, on inputs that are constant
multiples of indicators — the restricted weak type of the interpolated point.

Not proved: the passage from those inputs to general simple functions.  The
obstruction is recorded in StatusLog.md with an explicit witness.  Decomposing
the inputs into dyadic bands and bounding each term of the trilinear expansion
separately cannot work: for three equal inputs with `M` bands, the `k`-th of
measure `2^{-pk}/M`, the `M` diagonal terms each have target size `M^{-1/R}`, so
the sum of the term bounds is `M^{1-1/R}`, which diverges, while the truth is
bounded.  The same example localises the loss — the `ℓ^R` sum of the same bounds
is `1` — so it is the triangle inequality `‖∑_k W_k‖_R ≤ ∑_k ‖W_k‖_R` that is
lossy, and no per-term bound can repair it.  What is needed is to apply the
endpoint hypotheses to groups of bands rather than to single bands;
`trilinearOnSimple_expand_three_general` is the expansion over arbitrary finite
decompositions that such a grouping requires, and
`lintegral_rpow_enorm_high_le`, `lintegral_rpow_enorm_low_le`,
`sum_measure_dyadicLevelSet_le` and `sum_triple_dyadicLevelSet_le` are the
estimates a grouping would consume.

The blocker has since been identified precisely, and is recorded in
ErrorReport.md under "Missing prerequisite: the real interpolation method".  The
level split with a tent share (`exists_normalized_lattice_tent`,
`sum_tent_levels_le`) together with the two-sided summation bound
(`exists_sum_min_two_geometric_bound`) gives weak type at the interior exponent,
and that is sharp for the route: off balance the level-set bound is
`D₁(k₀) τ^{-r₁} + D₂(k₀) τ^{-r₂}`, and the two integrability constraints on `k₀`
meet exactly at the balance, where the bound is `τ^{-R}` and the strong-norm
integral diverges logarithmically.  Closing the gap classically needs the `ℓ^s`
aggregation of the real interpolation method, which converts the divergent `ℓ¹`
sum of the layer bounds into a convergent `ℓ^R` one.  Mathlib has no Lorentz
spaces, no `K`- or `J`-functionals and no real interpolation functor, and the
pinned `lean_spherical` supplies only the complex method.

`lem:one_fiber` is proved for the truncated operator at the manuscript's own
constant `A_u = C_1U(u)^{100}`: the three budgets are discharged at the
canonical stopping data, combined into the weak-`L^R` bound, and the input
norms are restored by rescaling.  The exponent conditions match the source
(`R^{-1} = p^{-1} + Σ_{j≠m}P_j^{-1}`, `1 ≤ p ≤ P_m`, `1 ≤ R`), and the
starting estimate is not assumed but derived from `thm:initial_model`.

`ModelTruncatedOperator_weakNorm_le_one_fiber_explicit` proves it for pointwise
bounded inputs whose distinguished slot is integrable on each finite-mass fiber;
`ModelTruncatedOperator_weakNorm_le_one_fiber_unbounded` removes both hypotheses,
which is the manuscript's approximation step.  Simple approximants
(`SimpleFunc.approxOn`) are bounded, of finite-measure support, converge pointwise,
and are dominated by twice the limit, so every side condition holds for them and
each input norm costs a factor two; the weak bound then survives the
almost-everywhere limit
(`ae_tendsto_ModelTruncatedOperator_of_ae_tendsto_all_dominated`,
`weakNorm_le_of_ae_tendsto`).  The dominated convergence there needs no uniform sup
bound: on the compact scale range the bracket profile at the largest scale dominates
every model kernel, and Hoelder against the input's line restriction — in `L^{P_j}`
at almost every point — makes the majorant constant in the scale.

`thm:extended_model` is the interpolation assembly, which consumes
`ext:interpolation` as a hypothesis by design, the manuscript supplying no
proof of it.

`ext:interpolation` is recorded with the manuscript's trilinearity hypothesis.  An
earlier version of `FourVertexMarcinkiewicz` and `FourVertexMarcinkiewiczUniform`
quantified over every operator `T`, dropping the "Let `T` be a trilinear operator"
with which the source opens; that made the recorded hypothesis strictly stronger
than the manuscript's, and Marcinkiewicz interpolation is false without such
structure.  `TrilinearOnSimple` supplies it, and
`trilinearOnSimple_ModelTruncatedOperator` discharges it where the hypothesis is
consumed, from `ModelTruncatedOperator_replace_add_of_bounded` and
`ModelTruncatedOperator_replace_smul`.

`ext:interpolation` is recorded in two readings.  `FourVertexMarcinkiewicz`
fixes the operator and then produces the constant, so it permits the constant to
depend on the operator.  `FourVertexMarcinkiewiczUniform` produces the constant
from the exponent vectors and the weights alone, and then serves every choice of
endpoint constants and every operator; that is the source's own wording
("with constant depending only on the exponent vectors and the weights") and it
is what `thm:extended_model` needs, since its constant has to be uniform in the
mode `u` while the operators `U^{a,b}_{u,c}` differ exactly in `u` and `c`.
`fourVertexMarcinkiewicz_of_uniform` shows the uniform reading implies the
per-operator one, so nothing that consumed the earlier form is affected.

`exists_ModelTruncatedOperator_extended_strong_bound` is equation
`eq:extended_operator_bound`: the three shifted-vertex weak endpoints
(`weakNorm_ModelTruncatedOperator_simplexVertex_succ`, obtained from
`lem:one_fiber` at `p = P_m^{(m)}`) together with the base vertex
(`simplexWeakEndpoint_zero_of_strong`) are fed to
`exists_strong_bound_at_simplex_interior_uniform`, and the factor `U(u)^{100}`
common to the four endpoint constants is pulled out of the weighted product
because the weights sum to one.

`exists_ModelTruncatedOperator_extended_strong_bound_unconditional` discharges the
base vertex on the interpolation's own class:
`exists_lpNorm_ModelTruncatedOperator_le_of_simpleFunc` reads the strict-range
output estimate for bounded measurable fields
(`lintegral_rpow_ModelTruncatedOperator_le_of_boundedMeasurable`, itself the
duality step applied to `thm:initial_model` and mollified to non-Schwartz inputs)
at simple inputs of finite-measure support, which are bounded and lie in every
`L^{P_j}`.  Nothing is left as a hypothesis there beyond the exponent conditions
and `ext:interpolation`.

`exists_abs_formPairing_ModelTruncatedOperator_le_extended` is the closing Hoelder
display: `R^{-1} + p_0^{-1} = 1` turns the operator bound into
`|∫ f_0 U^{a,b}_{u,c}(f_1,f_2,f_3)| ≤ C U(u)^{100} ∏_{j=0}^3 ‖f_j‖_{p_j}`, uniform
in the mode, the coefficient and the truncation.

`exists_ModelTruncatedOperator_extended_strong_bound_boundedMeasurable` removes the
restriction to simple inputs.  `ext:interpolation` delivers the strong bound on
simple functions of finite-measure support; `SimpleFunc.approxOn` approximates each
slot pointwise, keeping the sup bound and the `L^{p_j}` norm up to a factor two,
and Fatou (`lintegral_rpow_ModelTruncatedOperator_le_of_ae_tendsto_all`) carries the
bound to the limit with the constant enlarged by `2^3`.  Schwartz tuples are in
that class.

`exists_abs_ModelFullForm_le_extended` is `thm:extended_model` for the real
full-scale model form: the interval form is bounded uniformly in the truncation by
`abs_ModelScaleIntervalTruncation_le_of_extended_operator_bound`, and the scale
truncations converge to the full form by
`tendsto_ModelScaleTruncation_of_realSchwartz` (`lem:model_convergence`).  It is the
exact analogue of `exists_uniform_initialModelFullForm_bound_weight100`, at the
extended exponents instead of the strict initial range.

What remains is the passage from the real full-scale model form to
`UniformConeModeFormBound`: complexification, `lem:permutation` to reach every
active coordinate, and the mode-sum bookkeeping.  The corresponding chain already
exists for the initial range, starting from
`exists_uniform_initialModelFullForm_bound_weight100`; it is stated there in terms
of the strict-range hypothesis `hqs`, so it has to be re-derived taking the form
bound itself as input.

## Section 8: Cone decomposition and the multiplier theorem
Lean file: DFR/Auto/Twisted/ConeDecompositionMultiplierTheorem/ConeDecompositionMultiplierTheorem.lean

### Definitions
\label{def:permuted_model}: Completed (Lean: Auto.activeModelScaleTruncation) (2026-09-12T14:22-0700)
\label{def:localized_symbol}: Completed (Lean: Auto.Twisted.unitTorusLocalizedSymbol) (2026-09-12T14:22-0700)
\label{def:fourier_coefficients}: Completed (Lean: UnitAddTorus.mFourierCoeff [Mathlib]) (2026-09-12T14:22-0700)

### Theorems
\label{lem:permutation}: Proof completed (Lean: Auto.Twisted.lem_permutation) (2026-09-12T14:47-0700)
\label{lem:calderon}: Proof completed (Lean: Auto.Twisted.lem_calderon_cone_identity) (2026-09-12T14:47-0700)
\label{lem:symbol_derivatives}: Proof completed (Lean: Auto.Twisted.lem_symbol_derivatives) (2026-09-12T14:47-0700)
\label{lem:fourier_series}: Proof completed (Lean: Auto.Twisted.lem_fourier_series_coefficient_decay) (2026-09-12T14:47-0700)
\label{thm:cone}: Proof completed (Lean: Auto.Twisted.thm_cone) (2026-09-12T14:47-0700)
