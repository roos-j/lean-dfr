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
\label{def:anisotropy}: Completed (Lean: Auto.Anisotropy) (2026-09-12T14:22-0700)
\label{def:multiplier}: Completed (Lean: Auto.Anisotropy.IsAnisotropicMultiplier) (2026-09-12T14:22-0700)

### Theorems
\label{lem:pairing}: Proof completed (Lean: Auto.Twisted.lem_pairing_integrable) (2026-09-12T14:22-0700)
\label{lem:pairing}: Proof completed (Lean: Auto.Twisted.lem_pairing_eq_frequencyForm) (2026-09-12T14:22-0700)
\label{thm:main}: Statement completed (Lean: Auto.Twisted.thm_main) (2026-09-12T14:22-0700)

`thm:main` is proved from the hypothesis `UniformConeModeFormBound`, which
carries `thm:extended_model`.  Discharging that hypothesis is the remaining
work; until then the Lean statement has an assumption the manuscript does not,
so the status is `Statement completed` rather than `Proof completed`.

## Section 2: Function spaces and fixed bumps
Lean file: DFR/Auto/Twisted/Twisted.lean

### Definitions
\label{def:schwartz}: Completed (Lean: Auto.Schwartz3) (2026-09-12T14:22-0700)
\label{def:gaussian}: Completed (Lean: Auto.gaussian) (2026-09-12T14:22-0700)
\label{def:bumps}: Completed (Lean: Auto.standardFrequencyBump, Auto.conePsi, Auto.conePhi) (2026-09-12T14:22-0700)

### Theorems
\label{lem:schwartz}: Proof completed (Lean: Auto.schwartz_memLp) (2026-09-12T14:22-0700)
\label{lem:bumps}: Proof completed (Lean: Auto.cPsi_pos, Auto.conePhi_eq_cPsi_of_abs_le_one, Auto.standardFrequencyBump_eq_one_of_abs_le_half) (2026-09-12T14:22-0700)
\label{lem:domination}: Proof completed (Lean: Auto.gaussianSuperposition_domination) (2026-09-12T14:22-0700)

## Section 3: Dyadic geometry and local sizes
Lean file: DFR/Auto/Twisted/Twisted.lean

### Definitions
\label{def:tree}: Completed (Lean: Auto.AnisoBox, Auto.BoxCollection) (2026-09-12T14:22-0700)
\label{def:faces}: Completed (Lean: Auto.boxFaceCoordinate, Auto.boxFaceSet, Auto.boxFaceArea) (2026-09-12T14:22-0700)
\label{def:size}: Completed (Lean: Auto.treeLocalSize) (2026-09-12T14:22-0700)

### Theorems
\label{lem:geometry}: Proof completed (Lean: Auto.card_boxChildren, Auto.volume_root_eq_sum_volume_leaves) (2026-09-12T14:22-0700)
\label{lem:size}: Proof completed (Lean: Auto.cubeBracketAverage_le_treeLocalSize_product_of_mem_closure) (2026-09-12T14:22-0700)
\label{lem:bl}: Proof completed (Lean: Auto.cubeEdgeBracketAverage_le_product_secondMoments) (2026-09-12T14:22-0700)

## Section 4: Cubical telescoping with boundary terms
Lean file: DFR/Auto/Twisted/Twisted.lean

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
Lean file: DFR/Auto/Twisted/Twisted.lean

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
Lean file: DFR/Auto/Twisted/Twisted.lean

### Definitions
\label{def:stopping}: Completed (Lean: Auto.sourceStoppingTree, Auto.sourceStoppingMaximal) (2026-09-12T14:22-0700)

### Theorems
\label{ext:maximal}: External (Lean: Mathlib Hardy-Littlewood maximal theory via LeanSpherical.Auto.HardyLittlewoodMaximal) (2026-09-12T14:22-0700)
\label{lem:maximal_size}: Proof completed (Lean: Auto.boxLocalSize_two_le_anisotropicMaximalTwo) (2026-09-12T14:22-0700)
\label{lem:stopping}: Proof completed (Lean: Auto.sourceStoppingTree_energyBounds_of_boundedContinuous) (2026-09-12T14:22-0700)
\label{lem:forest_bound}: Proof completed (Lean: Auto.sourceStoppingForestWeightedSum_le_maximalLevelSum) (2026-09-12T14:22-0700)
\label{lem:model_convergence}: Proof completed (Lean: Auto.tendsto_expandedModelLocalForm_centerExhaustion_restrictScale) (2026-09-12T14:22-0700)
\label{thm:initial_model}: Proof completed (Lean: Auto.exists_uniform_initialModelFullForm_bound_weight100) (2026-09-12T14:22-0700)

## Section 7: Fiberwise Calderon-Zygmund decomposition
Lean file: DFR/Auto/Twisted/Twisted.lean

### Definitions
\label{def:fiber_maximal}: Completed (Lean: Auto.coordinateDyadicBallMaximal) (2026-09-12T14:22-0700)
\label{def:weak_norm}: Completed (Lean: Auto.Twisted.weakNorm) (2026-09-12T14:22-0700)

### Theorems
\label{lem:fiber_kernel}: Proof completed (Lean: Auto.abs_activeModelCoordinateConvolution_le_coordinateDyadicBallMaximal) (2026-09-12T14:22-0700)
\label{lem:fiber_cz}: Proof completed (Lean: Auto.lintegral_prod_rpow_fiberDyadicCountableGoodField_le) (2026-09-12T14:22-0700)
\label{lem:interval_tails}: Proof completed (Lean: Auto.Twisted.lpNorm_finset_double_intervalTails_le_of_radius_sum, Auto.integral_finset_double_intervalTails_le_of_radius_sum) (2026-09-12T18:55-0700)
\label{lem:one_fiber}: Statement completed (Lean: Auto.Twisted.ModelTruncatedOperator_weakNorm_one_le_of_countable_stopping_data) (2026-09-12T16:16-0700)
\label{ext:interpolation}: External (Lean: Auto.Twisted.FourVertexMarcinkiewicz) (2026-09-12T14:22-0700)
\label{lem:exponent_simplex}: Proof completed (Lean: Auto.Twisted.affineIndependent_exponentSimplex_vertices) (2026-09-12T14:22-0700)
\label{thm:extended_model}: Statement completed (Lean: Auto.Twisted.exists_strong_bound_at_simplex_interior) (2026-09-12T14:22-0700)

`lem:one_fiber` is proved from level-wise stopping data: given, at each level,
data whose exceptional, good and bad budgets hold there, the weak bound
follows.  All three budgets now exist in the countable form the source uses, as
does the good budget for the operator, so what the statement still assumes is
the source's normalisation -- the choice of constant making each budget's mass
at most one.  `thm:extended_model` is the interpolation assembly, which
consumes `ext:interpolation` as a hypothesis by design, the manuscript
supplying no proof of it.

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
