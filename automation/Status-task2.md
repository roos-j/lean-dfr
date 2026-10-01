# Formalization status

## Task 2 fine-grained ledger, in strict forward reasoning order

### Part I -- ambient layer: definitions and elementary estimates

status | source item | Lean name
--- | --- | ---
proved | `def:fourier`, the Fourier convention on `R^3` | Mathlib's `𝓕`, fixed by the inner product and Lebesgue measure on `Auto.E3`
proved | `def:dyadic-envelope`, the dyadic envelope `Dyad` | `Auto.Dyad`
proved | `def:dyadic-envelope`, `max 1 s <= Dyad s < 2 max 1 s`, positivity | `Auto.dyad_bounds`, `Auto.dyad_pos`, `Auto.dyad_eq_zpow`
proved | `def:averages`, the monomial curves `t -> t^n e_n` | `Auto.expo`, `Auto.basisVec`, `Auto.curve`
proved | `def:averages`, the product shift | `Auto.prodShift`
proved | `def:averages`, the normalized average `A_N` | `Auto.A`
proved | `def:averages`, the upper-half average `Atilde_N` | `Auto.Atilde`
proved | `def:averages`, continuity of the averages of continuous data | `Auto.continuous_A`, `Auto.continuous_Atilde`
proved | `def:dilation`, the anisotropic dilation and its linear form | `Auto.D`, `Auto.Dlin`
proved | `def:dilation`, `det D_rho = rho^6` | `Auto.det_Dlin`
proved | `lem:scaling`, change of variables for `D_rho` | `Auto.lintegral_comp_D`
proved | `lem:scaling`, the dilation `S_rho` and the scaling identities for the averages | `Auto.S`, `Auto.A_S_D`, `Auto.Atilde_S_D`, `Auto.eLpNorm_S`
proved | `lem:scaling`, exponent cancellation for the endpoint estimate | `Auto.scale_factor_cancel`
proved | `lem:scaling`, exponent cancellation for the primitive estimate | `Auto.scale_factor_cancel'`
proved | `lem:trivial-holder`, the trivial Hoelder estimate for `A_N` | `Auto.eLpNorm_A_le`
proved | `lem:subunit-power`, subadditivity of `x -> x^q` for `q <= 1` | `Auto.add_rpow_le_of_le_one`
proved | `lem:cutoff-boundary`, a `C^1` cutoff vanishes at both endpoints | `Auto.cutoff_boundary`
proved | `lem:weighted-primitive-identity`, integration by parts against `psi` | `Auto.weighted_primitive_identity`
proved | `lem:dyadic-decomposition`, the weighted average `A_psi` and its decomposition | `Auto.Apsi`
proved | `def:projection`, the fixed cutoff `eta` and its inverse transform | `Auto.eta`, `Auto.etaKer`
proved | `def:projection`, the projection kernel `k_R` | `Auto.projKernel`
proved | `def:projection`, `P_R` as convolution in one coordinate | `Auto.P`
proved | `def:projection`, `Q_R = I - P_{4R}` | `Auto.Q`
proved | `lem:projection-properties`, `k_R` integrable, `L^1` norm `etaKerL1` | `Auto.projKernel_integrable`, `Auto.projKernel_L1`
proved | `lem:projection-properties`, the multiplier description of `P_R` | `Auto.fourier_P`
proved | `lem:projection-properties`, pointwise and `L^p` bounds for `P_R` | `Auto.norm_P_le`, `Auto.eLpNorm_P_le`
proved | `lem:projection-properties`, `P_R` and `Q_R` preserve `Nice` | `Auto.nice_P`, `Auto.nice_Q`
proved | `lem:projection-properties`, `Q_R f = f` off the low band | `Auto.Q_eq_self_of_fourier_support`
proved | `lem:projection-properties`, the Fourier support of `Q_R f` | `Auto.support_fourier_Q`
proved | `def:adjoint`, the four-linear form and the adjoint `A_N^{*j}` | `Auto.Astar`
proved | `lem:adjoint-identity`, the adjoint identity | `Auto.adjoint_identity`
proved | auxiliary, the class `Nice`, a dense linear subspace of every `L^p` | `Auto.Nice`, `Auto.nice_smul_add`, `Auto.nice_dense`
proved | auxiliary, the smooth truncating cutoffs | `Auto.cutoffBump`, `Auto.cutoff`

### Part II -- row 1: `lem:scalar-strip`, `lem:lebesgue-strip`, `thm:gm-internal`, `thm:quasi-interpolation`

status | source item | Lean name
--- | --- | ---
proved | harmonic measure of the strip, the two densities | `Auto.poissonStrip`
proved | positivity, continuity, integrability of the densities | `Auto.poissonStrip_pos`, `Auto.continuous_poissonStrip`, `Auto.integrable_poissonStrip`
proved | the masses `int w_0 = 1-theta` and `int w_1 = theta` | `Auto.integral_poissonStrip_one`, `Auto.integral_poissonStrip_neg_one`
proved | the strip Poisson kernel and its translation invariance | `Auto.stripKernel`, `Auto.im_stripKernel_eq`
proved | harmonicity of the strip Poisson integral | `Auto.differentiableOn_stripPoissonIntegral`
proved | the boundary limit of the Poisson integral | `Auto.tendsto_poissonAverage_strip`
proved | the reflection `z -> 1 - conj z` exchanging the edges | `Auto.stripReflect`
proved | Phragmen-Lindeloef for the strip, growth `exp(B exp(c abs Im z))`, `c < pi` | `Auto.norm_le_of_boundary_lt_strip`
proved | the Poisson majorant for `log norm H` | `Auto.norm_le_exp_re_stripPoissonIntegral`
proved | weighted Jensen for `exp`, by the tangent line | `Auto.exp_integral_le_integral_exp_weighted`
proved | Hirschman's lemma in regularized form | `Auto.norm_le_geom_mean_strip`
proved | removal of the regularization `eps` | `Auto.integrable_abs_log_shift`, `Auto.tendsto_integral_rpow_shift`
proved | **`lem:scalar-strip`** | `Auto.norm_le_geom_mean_strip_zero`
proved | `lem:scalar-strip` under a uniform bound, in `ENNReal` form | `Auto.norm_le_geom_mean_strip_bdd`, `Auto.enorm_le_geom_mean_strip`
proved | the normalized harmonic measures as probability densities | `Auto.hmLeft`, `Auto.lintegral_hmLeft`, `Auto.lintegral_hmRight`
proved | Jensen against a probability density, replacing Minkowski | `Auto.rpow_lintegral_mul_le`
proved | the edge estimate, by Jensen then Tonelli | `Auto.lintegral_edge_mean_le`
proved | prerequisite: **Stein interpolation for analytic families**, subunit exponents allowed | `Auto.eLpNorm_le_of_analyticFamily`
proved | the exponent path `a_i(z)` and its real part | `Auto.interpExp`, `Auto.interpExp_re`, `Auto.interpExp_at_eq_one`
proved | the phase `ph` with the convention `ph 0 = 0` | `Auto.ph`, `Auto.ph_mul_norm`
proved | the analytic family `F_i(z,x)`, entire in `z` | `Auto.anFam`, `Auto.differentiable_anFam`
proved | `F_i(theta) = f_i` | `Auto.anFam_at`
proved | the edge norms `norm F_i(l+it) = norm f_i ^ (p_i/p_{i,l})` | `Auto.eLpNorm_anFam_left`, `Auto.eLpNorm_anFam_right`
proved | **`lem:lebesgue-strip`** with the conclusion of **`thm:gm-internal`** | `Auto.interpolate_of_analyticFamily`
proved | the dense class closed under the analytic family | `Auto.Ccs`, `Auto.ccs_anFam`, `Auto.continuous_anFam`
proved | Cauchy's estimate: a value bound gives a derivative bound | `Auto.norm_deriv_le_of_bounded_on_ball`
proved | measurability of the parameter derivative of an entire family | `Auto.aestronglyMeasurable_deriv_at`
proved | holomorphy of an integral of a holomorphic family with a uniform bound | `Auto.differentiableAt_integral_of_bounded`
proved | the family is bounded on a disc about an interior point of the strip | `Auto.exists_disc_bound`, `Auto.norm_anFam_le`
proved | holomorphy of `z -> P_{4R}(F_j(z))` | `Auto.differentiableAt_P_anFam`
proved | holomorphy of `z -> Tproj(F(z))(y)` | `Auto.differentiableAt_Tproj_anFam`
proved | continuity of `z -> Tproj(F(z))(y)` on the closed strip | `Auto.continuousAt_Tproj_anFam`
proved | boundedness of the composed family on the closed strip | `Auto.exists_bound_Tproj_anFam`
proved | joint measurability of the composed family on the two edges | `Auto.aestronglyMeasurable_Tproj_anFam`
proved | the interpolation bound on compactly supported triples | `Auto.interpolate_Tproj`
proved | Fatou for `eLpNorm` along a pointwise convergent sequence | `Auto.eLpNorm_le_of_tendsto`
proved | truncation, and pointwise convergence of `Tproj` under it | `Auto.trunc`, `Auto.tendsto_Tproj_trunc`
proved | **`thm:quasi-interpolation`** for the operator that consumes it | `Auto.interpolate_Tproj_nice`

### Part III -- row 2: the six-dimensional lift and `prop:restricted-improving-vertex`

status | source item | Lean name
--- | --- | ---
proved | `def:real-lift`, the ambient space of the lift | `Auto.E6`, `Auto.basisVec6`
proved | `def:real-lift`, the three lifted curves in three disjoint blocks | `Auto.liftCurve1`, `Auto.liftCurve2`, `Auto.liftCurve3`, `Auto.liftCurve`
proved | `def:real-lift`, continuity of the lifted curves | `Auto.continuous_liftCurve`
proved | `def:real-lift`, the lifted average `L_N` | `Auto.Llift`
proved | `def:real-lift`, the dimension constants `D = 6`, `D* = 10`, `D' = 4` | `Auto.liftDims`
proved | `lem:fibre-separation`, separation inside a measurable fibre | `Auto.exists_separated_subset`
proved | `lem:lossless-refinements`, splitting an integral at a threshold | `Auto.lintegral_le_setLIntegral_thresh`
proved | `lem:lossless-refinements`, the deletion step | `Auto.refinement_step`
proved | the incidence integral of the lifted operator | `Auto.incid`
proved | the adjoint identity used between deletions | `Auto.incid_shift`
proved | monotonicity of the incidence in the four sets | `Auto.incid_mono`
proved | the incidence at a point is the measure of the fibre of the move | `Auto.moveFibre`, `Auto.lintegral_indicator_move`
proved | `lem:real-flow-jacobian`, the degree-two diagonal block and its determinant | `Auto.flowBlock2`, `Auto.det_flowBlock2`
proved | `lem:real-flow-jacobian`, the degree-three diagonal block and its determinant | `Auto.flowBlock3`, `Auto.det_flowBlock3`
proved | `lem:real-flow-jacobian`, the full block diagonal derivative matrix | `Auto.flowMatrix`
proved | `lem:real-flow-jacobian`, `det = 12 (u-v)(a-b)(a-c)(b-c)` | `Auto.det_flowMatrix`
proved | `lem:real-flow-jacobian`, the Jacobian in absolute value | `Auto.abs_det_flowMatrix`, `Auto.abs_det_flow`
proved | `lem:real-flow-jacobian`, the degree-two block is injective off its diagonal | `Auto.flowBlock2_injective`
proved | `lem:real-flow-jacobian`, the three moment relations of the degree-three block | `Auto.flowBlock3_relations`, `Auto.flowBlock3_coeff`
proved | `lem:real-flow-jacobian`, the degree-three block determines `b` and the pair `(a+c, ac)` | `Auto.flowBlock3_pair`
proved | the area formula with bounded multiplicity | `Auto.lintegral_abs_det_fderiv_le_card_mul_image`
proved | the fibre integration step of the Jacobian | `Auto.exists_separated_lintegral_ge`
proved | the induction atom of the tower | `Auto.mul_measure_le_setLIntegral`
proved | the descent projection and `proj6 (Gamma_i t) = curve i t` | `Auto.blockLast`, `Auto.proj6`, `Auto.proj6_liftCurve`
proved | the descent identity `L_N(lifted data) = A_N` | `Auto.Llift_comp_proj`
proved | the tower move, for the measure of the tower | `Auto.measure_prod_ge_of_fibres`
proved | the tower move, for a weighted integral over the tower | `Auto.lintegral_prod_ge_of_fibres`
proved | Fubini transport: peeling one coordinate of `Fin (n+1) -> R` | `Auto.measurePreserving_piFinSucc`
proved | Fubini transport: the lift is measure-preservingly `R x (Fin 5 -> R)` | `Auto.measurePreserving_E6_prod`
proved | `lem:real-flow-jacobian`, adjoining one parameter to a tower | `Auto.towerCons`, `Auto.preimage_towerCons`
proved | `lem:real-flow-jacobian`, one move of the tower, for its measure | `Auto.measure_towerCons_ge`
proved | `lem:real-flow-jacobian`, one move of the tower, for a weighted integral | `Auto.lintegral_towerCons_ge`
proved | `lem:real-flow-jacobian`, the six-level tower has measure at least the product of the six fibre bounds | `Auto.measure_tower6_ge`
proved | `lem:lossless-refinements`, the forward incidence density carried by `E0` | `Auto.incidFwd`, `Auto.measurable_incid_integrand`
proved | `lem:lossless-refinements`, the incidence integral is the integral of the forward density over `E0` | `Auto.incid_eq_setLIntegral_incidFwd`
proved | `lem:lossless-refinements`, the `j`-th adjoint incidence density carried by `E j` | `Auto.incidAdj`
proved | `lem:lossless-refinements`, **the adjoint identity in the form used between deletions** | `Auto.incid_eq_setLIntegral_incidAdj`
proved | `lem:lossless-refinements`, measurability of the four incidence densities | `Auto.measurable_incidFwd`, `Auto.measurable_incidAdj`
proved | `lem:lossless-refinements`, the `j`-th adjoint density does not see the `j`-th set | `Auto.incidAdj_update`
proved | **`lem:lossless-refinements`, one deletion from `E0`** | `Auto.refinement_delete_fwd`
proved | **`lem:lossless-refinements`, one deletion from `E j`** | `Auto.refinement_delete_adj`
proved | **`lem:lossless-refinements`, one full stage: four deletions costing a factor `2^4`** | `Auto.refinement_stage`
proved | patch 1 `def:refinements`, the refinement tower: the stage iterated to depth `r`, every stage carrying the pointwise bounds of its own starting configuration (was blocked; unblocked by patch 1) | `Auto.one_le_pow_sixteen`, `Auto.refinement_tower`
proved | patch 1 `lem:nonempty`, every set of every stage has measure at least `B / N`, hence is nonempty | `Auto.indicator_one_le_one`, `Auto.incidFwd_le`, `Auto.incidAdj_le`, `Auto.incid_le_volume_fwd`, `Auto.incid_le_volume_adj`, `Auto.volume_ge_of_incid_ge`, `Auto.nonempty_of_incid_ge`
proved | one move of the tower on the lift's coordinate space | `Auto.measure_piTower_ge`
proved | transport of a measure from the lift to its coordinate space | `Auto.measure_E6_preimage`
proved | transport of a weighted integral from the lift to its coordinate space | `Auto.lintegral_E6_preimage`
proved | `lem:real-flow-jacobian`, the flow in coordinates and on the lift | `Auto.flowPi`, `Auto.flowMap`
proved | `lem:real-flow-jacobian`, the derivative of the flow as a continuous linear map | `Auto.flowDeriv`
proved | `lem:real-flow-jacobian`, the determinant of a matrix acting on the lift | `Auto.det_toEuclideanLin`
proved | `lem:real-flow-jacobian`, `det DPhi = 12 (t1-t2)(t3-t4)(t3-t5)(t4-t5)` | `Auto.det_flowDeriv`, `Auto.abs_det_flowDeriv`
proved | `lem:real-flow-jacobian`, `HasFDerivAt` for the flow, in coordinates | `Auto.hasFDerivAt_flowPi`
proved | `lem:real-flow-jacobian`, `HasFDerivAt` for the flow on the lift | `Auto.hasFDerivAt_flowMap`
proved | two reals are determined by their sum, product and order | `Auto.pair_eq_of_sum_prod`
proved | the flow is injective where the Jacobian's factors are nonzero and the outer pair is ordered | `Auto.flowMap_injOn`, `Auto.flowMap_injOn'`
proved | **`lem:real-flow-jacobian`, the multiplicity bound as a two-piece measurable injective cover** | `Auto.flowMap_injective_cover`
proved | patch 1, the incidence densities as measures of fibres | `Auto.lintegral_eq_volume_fibre`, `Auto.measurableSet_fwdFibre`, `Auto.measurableSet_adjFibre`, `Auto.incidFwd_eq_volume`, `Auto.incidAdj_eq_volume`
proved | patch 1 `lem:transition`, the four labels uniformly, with `Γ 0 = 0`: the fibre of the move leaving `a` has measure the density of `a`, and lands in the set of any other label | `Auto.curve4`, `Auto.cfg4`, `Auto.dens4`, `Auto.transSet`, `Auto.mem_cfg4_of_mem_transSet`, `Auto.transSet_zero`, `Auto.transSet_succ`, `Auto.measurableSet_transSet`, `Auto.volume_transSet_zero`, `Auto.volume_transSet_succ`, `Auto.volume_transSet_ge_of_tower`
proved | patch 1 `def:itinerary`, `lem:parity`, the incidence count `n_i(w) + [w_0=i] + [w_6=i] = 2 #{l : w_l = i}` and its parity consequence | `Auto.IsItinerary`, `Auto.numTouch`, `Auto.numOcc`, `Auto.numTouch_add_ends`, `Auto.numTouch_mod_two`, `Auto.ends_of_numTouch_odd`, `Auto.not_ends_at_two`
proved | patch 1 `def:three-itineraries`, `lem:itineraries-admissible`, the three words, their block assignments of sizes `(1,2,3)`, and which moves touch `E_0` | `Auto.word3`, `Auto.word1`, `Auto.word2`, `Auto.word3_isItinerary`, `Auto.word1_isItinerary`, `Auto.word2_isItinerary`, `Auto.word_ends`, `Auto.word3_numTouch`, `Auto.word1_numTouch`, `Auto.word3_touches_zero`, `Auto.word1_touches_zero`, `Auto.word2_not_touches_zero`, `Auto.word2_nonzero_moves`, `Auto.blk3`, `Auto.blk1`, `Auto.blk2`, `Auto.blkCard`, `Auto.blk3_card`, `Auto.blk1_card`, `Auto.blk2_card`
proved | patch 1 `lem:levels`, a level is consumed exactly at a move `a -> b` with `a < b`; the three level tables run `60` down to `57` | `Auto.levels`, `Auto.levels_word3`, `Auto.levels_word1`, `Auto.levels_word2`, `Auto.levels_word3_ge`, `Auto.levels_word1_ge`, `Auto.levels_word2_ge`
proved | patch 1 `def:flow`, `lem:tower`, the parameter tower: the point after `l` moves lies in the set of the label `w l` at level `r - l`, each fibre has measure at least that label's density, and the flow lands in the terminal set | `Auto.flowPt`, `Auto.flowFibre`, `Auto.tower_subset_zero`, `Auto.cfg4_subset_zero`, `Auto.flowPt_mem`, `Auto.volume_flowFibre_ge`, `Auto.flowPt_six_mem`
proved | patch 1 `lem:jacobian` for `w^(3)`: the flow is the translate of `Auto.flowMap3`, block diagonal, with `|det| = 12 |u-v| |a-b| |a-c| |b-c|` | `Auto.flowPi3`, `Auto.flowMatrix3`, `Auto.det_flowMatrix3`, `Auto.abs_det_flowMatrix3`, `Auto.flowMap3`, `Auto.flowDeriv3`, `Auto.det_flowDeriv3`, `Auto.abs_det_flowDeriv3`, `Auto.hasFDerivAt_flowPi3`, `Auto.hasFDerivAt_flowMap3`, `Auto.flowPt_word3`, `Auto.flowPt_word3_eq`
proved | patch 1 `lem:jacobian` for `w^(1)`: the same block structure with block `3` at the moves `0, 3, 4`, and the same Jacobian | `Auto.flowPi1`, `Auto.flowMatrix1`, `Auto.det_flowMatrix1`, `Auto.abs_det_flowMatrix1`, `Auto.flowMap1`, `Auto.flowDeriv1`, `Auto.det_flowDeriv1`, `Auto.abs_det_flowDeriv1`, `Auto.hasFDerivAt_flowPi1`, `Auto.hasFDerivAt_flowMap1`, `Auto.flowPt_word1`, `Auto.flowPt_word1_eq`
proved | patch 1 `lem:jacobian` for `w^(2)`: the second flow map, **block lower triangular but not diagonal**, with the same Jacobian | `Auto.flowPi2`, `Auto.flowMatrix2`, `Auto.flowMatrix2_not_blockDiagonal`, `Auto.det_flowMatrix2`, `Auto.abs_det_flowMatrix2`, `Auto.flowMap2`, `Auto.flowDeriv2`, `Auto.det_flowDeriv2`, `Auto.abs_det_flowDeriv2`, `Auto.hasFDerivAt_flowPi2`, `Auto.hasFDerivAt_flowMap2`, `Auto.flowPt_word2`, `Auto.flowPt_word2_eq`
proved | patch 1 `lem:multiplicity`, at most two preimages: each of the three flows is injective on each of two measurable pieces, split by the order of the outer pair of the degree-three block; for `w^(2)` the parameters are recovered in the visiting order `1, 3, 2` | `Auto.flowMap3_coord`, `Auto.flowMap1_coord`, `Auto.flowMap2_coord`, `Auto.flowMap3_injOn`, `Auto.flowMap3_injOn'`, `Auto.flowMap3_injective_cover`, `Auto.flowMap1_injOn`, `Auto.flowMap1_injOn'`, `Auto.flowMap1_injective_cover`, `Auto.flowMap2_injOn`, `Auto.flowMap2_injOn'`, `Auto.flowMap2_injective_cover`
proved | patch 1, the parameter set of the tower as a subset of the lift, its measurability, and the area bound with the factor `1/2` | `Auto.toSeq`, `Auto.continuous_curve4`, `Auto.continuous_toSeq_apply`, `Auto.continuous_flowPt`, `Auto.flowParamSet`, `Auto.measurableSet_flowParamSet`, `Auto.lintegral_abs_det_le_two_mul`, `Auto.injOn_const_add`
proved | patch 1 `lem:real-flow-jacobian-fixed`, **the corrected statement of `lem:real-flow-jacobian`**, items (i)-(iv) for each of the three words | `Auto.real_flow_jacobian_word3`, `Auto.real_flow_jacobian_word1`, `Auto.real_flow_jacobian_word2`
proved | patch 1 `lem:integrated`, one fibre integration: separating the new parameter from the at most two earlier ones of its block costs only a power of two | `Auto.lintegral_prod_dist_ge`
proved | patch 1 `lem:integrated`, the six successive fibre integrations: one move of the tower with the outer variable weighted, and the six of them composed | `Auto.mul_lintegral_le_setLIntegral`, `Auto.lintegral_prod_ge_of_fibres'`, `Auto.lintegral_towerCons_ge'`, `Auto.lintegral_towerCons_ge_mul`, `Auto.lintegral_tower6_ge`
proved | patch 1 `lem:integrated`, the exponent bookkeeping `m_l <= 2` and `sum_l (m_l + 1) = D* = 10`, for each of the three block assignments | `Auto.mCount`, `Auto.mCount_le_two_word3`, `Auto.mCount_le_two_word1`, `Auto.mCount_le_two_word2`, `Auto.sum_mCount_word3`, `Auto.sum_mCount_word1`, `Auto.sum_mCount_word2`, `Auto.mCount_word3_values`, `Auto.mCount_word1_values`, `Auto.mCount_word2_values`
proved | patch 1 `lem:integrated`, the constants: the per-step `2^{-9}`, the six steps `2^{-54}`, `c_*^{10} = 2^{-2400}`, the total `2^{-2455}`, and the exponent trade `(prod alpha_i)^10 <= prod alpha_i^{e_i}` | `Auto.step_const_ge`, `Auto.six_step_const`, `Auto.cstar_pow_ten`, `Auto.two_pow_const`, `Auto.prod_alpha_pow_ge`, `Auto.prod_alpha_pow_ge'`
proved | patch 1 `lem:integrated`, the lift as the six-fold product of the line, and the transport of sets and weighted integrals | `Auto.e6ToProd`, `Auto.measurePreserving_e6ToProd`, `Auto.measure_e6ToProd_preimage`, `Auto.lintegral_e6ToProd_preimage`
proved | patch 1 `lem:integrated`, each fibre reads only the earlier parameters | `Auto.flowPt_congr`, `Auto.flowFibre_congr`, `Auto.seqOf`, `Auto.seqOf_e6ToProd`
proved | patch 1 `lem:integrated`, the parameter set of the flow presented as the nested tower of its six fibres | `Auto.towA1`, `Auto.towA2`, `Auto.towA3`, `Auto.towA4`, `Auto.towA5`, `Auto.towA6`, `Auto.flowTower`, `Auto.preimage_flowTower`
proved | patch 1 `lem:integrated`, the Jacobian of `w^(3)` as the product of the six per-move Vandermonde factors | `Auto.jg1`, `Auto.jg2`, `Auto.jg3`, `Auto.jg4`, `Auto.jg5`, `Auto.jg6`, `Auto.jacWeight3_le`
proved | patch 1 `lem:integrated`, measurability in the tower coordinates and of the five intermediate towers | `Auto.continuous_seqOf_apply`, `Auto.continuous_flowPt_seqOf`, `Auto.towCond`, `Auto.measurableSet_towCond`, `Auto.flowTower_eq`, `Auto.measurableSet_flowTower`, `Auto.towerCons5_eq`, `Auto.towerCons4_eq`, `Auto.towerCons3_eq`, `Auto.towerCons2_eq`, `Auto.measurableSet_towerCons5`, `Auto.measurableSet_towerCons4`, `Auto.measurableSet_towerCons3`, `Auto.measurableSet_towerCons2`, `Auto.measurableSet_towA`
proved | **patch 1 `lem:integrated` for `w^(3)`: the six steps composed, transported to the lift, and the area bound** | `Auto.lintegral_jacWeight3_flowTower_ge`, `Auto.lintegral_absDet_flowParamSet_ge`, `Auto.ndSet3`, `Auto.measurableSet_ndSet3`, `Auto.absDet_flowDeriv3_eq_zero`, `Auto.lintegral_absDet_eq_ndSet3`, `Auto.measure_terminal_ge_word3`
proved | **patch 1 `lem:integrated` for `w^(1)` and `w^(2)`**, completing the patch for all three terminal indices | `Auto.kg1`-`Auto.kg6`, `Auto.jacWeight1_le`, `Auto.lintegral_jacWeight1_flowTower_ge`, `Auto.lintegral_absDet1_flowParamSet_ge`, `Auto.ndSet1`, `Auto.measurableSet_ndSet1`, `Auto.absDet_flowDeriv1_eq_zero`, `Auto.lintegral_absDet1_eq_ndSet1`, `Auto.measure_terminal_ge_word1`, `Auto.mg1`-`Auto.mg6`, `Auto.jacWeight2_le`, `Auto.lintegral_jacWeight2_flowTower_ge`, `Auto.lintegral_absDet2_flowParamSet_ge`, `Auto.ndSet2`, `Auto.measurableSet_ndSet2`, `Auto.absDet_flowDeriv2_eq_zero`, `Auto.lintegral_absDet2_eq_ndSet2`, `Auto.measure_terminal_ge_word2`
proved | `prop:restricted-improving-vertex`, six successive fibre integrations, exponent `10 = 1+3+6`: the product of the six per-step bounds, for each of the three words | `Auto.lintegral_jacWeight3_flowTower_ge`, `Auto.lintegral_jacWeight1_flowTower_ge`, `Auto.lintegral_jacWeight2_flowTower_ge`, `Auto.sum_mCount_word3`, `Auto.sum_mCount_word1`, `Auto.sum_mCount_word2`
proved | **`prop:restricted-improving-vertex`, the image measure bound `\|E_{j'}\| >= c (alpha_0 alpha_1 alpha_2 alpha_3 N)^10`**, for each of the three words | `Auto.prod_six_word3_ge`, `Auto.prod_six_word1_ge`, `Auto.prod_six_word2_ge`, `Auto.ofReal_prod_six`, `Auto.measure_terminal_ge_symmetric_word3`, `Auto.measure_terminal_ge_symmetric_word1`, `Auto.measure_terminal_ge_symmetric_word2`
proved | **`prop:restricted-improving-vertex`, the symmetric restricted inequality `K^60 <= C N^{-10} \|E_0\|^10 \|E_j\|^30 \|E_{j'}\|^11 \|E_k\|^10`** | `Auto.K_le_of_alpha_le_one`, `Auto.alpha_prod_mul`, `Auto.K_pow_sixty_le_of_symmetric`
proved | `prop:restricted-improving-vertex`, the cutoff box in the unused coordinates and the inner box | `Auto.boxSet`, `Auto.innerBox`
proved | `prop:restricted-improving-vertex`, every translation of the average keeps the inner box inside the cutoff box | `Auto.mem_boxSet_of_innerBox`
proved | `prop:restricted-improving-vertex`, the lift of a function on `R^3` | `Auto.liftFun`
proved | **`prop:restricted-improving-vertex`, on the inner box the lifted average is the original average** | `Auto.Llift_liftFun`
proved | the coordinate permutation splitting the lift into used and unused coordinates | `Auto.coordPerm`, `Auto.coordEquiv`, `Auto.splitE6`
proved | the split is measure preserving | `Auto.measurePreserving_splitE6`
proved | the block projection and the cutoff box read off the two halves of the split | `Auto.proj6_eq_splitE6`, `Auto.boxSet_eq_preimage`
proved | **`prop:restricted-improving-vertex`, the factor `N^{D'}`: the cutoff box has measure `8 N^4`** | `Auto.volume_unusedBox`
proved | `prop:restricted-improving-vertex`, the exponent arithmetic giving `N^{-1/10}`: `-1/6 + 4(1/p - 1/q) = -1/10` with `1/p = 17/20`, `1/q = 5/6` | `Auto.descent_exponent`, `Auto.exponent_arithmetic`
proved | `prop:restricted-improving-vertex`, the restricted weak bound from the dual pairing: testing on the level sets | `Auto.wnorm_le_of_setLIntegral`
proved | `prop:restricted-improving-vertex`, the measure of a lifted set: lifting multiplies by the cutoff box `8 N^4` | `Auto.volume_lifted_set`
proved | `prop:restricted-improving-vertex`, the measure of a lifted set inside the inner box: the factor is `N^4` | `Auto.innerUnusedBox`, `Auto.innerBox_eq_preimage`, `Auto.volume_innerUnusedBox`, `Auto.volume_lifted_inner`
proved | `prop:restricted-improving-vertex`, integrating a function of the used coordinates over a lifted set; measurability of `proj6` and of the boxes | `Auto.measurable_toLp3`, `Auto.lintegral_lifted_inner`, `Auto.measurable_proj6`, `Auto.measurableSet_innerBox`, `Auto.measurableSet_boxSet`
proved | **`prop:restricted-improving-vertex`, the incidence integral of lifted data**: it is the incidence integral on `R^3` times the measure of the inner box in the unused coordinates | `Auto.indicator_lifted_shift`, `Auto.incid_lifted`
proved | `prop:restricted-improving-vertex`, the six fibre bounds along the tower, and the image measure bound from the refinement tower alone, for all three words | `Auto.flowPt_mem_succ`, `Auto.towA_fibre_bounds`, `Auto.dens4_ofReal`, `Auto.measure_terminal_ge_of_tower_word3`, `Auto.measure_terminal_ge_of_tower_word1`, `Auto.measure_terminal_ge_of_tower_word2`
proved | `prop:restricted-improving-vertex`, the average of indicators as a fibre measure, and the pairing with a test set as the incidence integral on `R^3` | `Auto.ofReal_prodShiftR_indicator`, `Auto.enorm_A_indicators`, `Auto.lintegral_enorm_A_eq`
proved | **`prop:restricted-improving-vertex`, the symmetric inequality assembled on the lift**: the refinement tower with densities `K / |E_i|`, the itinerary `w^(3)`, and the area formula give `2^{-19} N^{10} K^{60} <= |E_0|^{10} |E_j|^{30} |E_2|^{11} |E_k|^{10}` | `Auto.prod_three_perm`, `Auto.K_pow_sixty_incid_word3`
proved | `prop:restricted-improving-vertex`, the descent identity: the incidence integral of the lift is the pairing of the average on `R^3` with the test set, times `N^5`; the average of indicators has modulus at most one, so that pairing is finite | `Auto.incid_lift_eq`, `Auto.indicator_one_le_one3`, `Auto.enorm_A_indicators_le_one`, `Auto.lintegral_enorm_A_ne_top`
proved | **`prop:restricted-improving-vertex`, the statement**: `RestrictedWeak (A N)` at the improving vertex with constant `C N^{-1/10}` -- the assembly of the rows above (ledger row added 2026-09-14, previously omitted) | `Auto.enn_le_of_mul_le_mul`, `Auto.enn_le_mul_of_inv_mul_le`, `Auto.lintegral_enorm_A_pow_sixty_le`, `Auto.measurable_prod_indicator_shift`, `Auto.measurable_enorm_A_indicators`, `Auto.lintegral_enorm_A_le_volume`, `Auto.volume_level_A_ne_top`, `Auto.improvingConst`, `Auto.improvingExp`, `Auto.prod_improvingExp`, **`Auto.restrictedWeak_A_improving`**
proved | `prop:restricted-improving-vertex`, the proposition for **every** choice of the distinct pair `j, j'`: the three itineraries of patch 1 give the three terminal indices, and the statement is stated with `j'` a parameter | `Auto.K_pow_sixty_incid_of_word`, `Auto.K_pow_sixty_incid_word3`, `Auto.K_pow_sixty_incid_word1`, `Auto.K_pow_sixty_incid_word2`, `Auto.K_pow_sixty_incid`

### Part IV -- row 3: `lem:finite-marcinkiewicz`, `cor:kosz-53-internal`, `cor:kosz-subunit-internal`

status | source item | Lean name
--- | --- | ---
proved | `lem:finite-marcinkiewicz`, the dyadic level sets and their disjointness | `Auto.dyadicLevel`, `Auto.dyadicLevel_disjoint`, `Auto.measurableSet_dyadicLevel`
proved | `lem:finite-marcinkiewicz`, every point of positivity lies in one level set | `Auto.mem_dyadicLevel`, `Auto.iUnion_dyadicLevel`
proved | **`lem:finite-marcinkiewicz`, the dyadic sum and the integral are comparable** | `Auto.tsum_dyadic_le_lintegral`, `Auto.lintegral_le_tsum_dyadic`
proved | **`lem:finite-marcinkiewicz`, the finite cone split of the exponent lattice** | `Auto.maxCone`, `Auto.iUnion_maxCone`
proved | `lem:finite-marcinkiewicz`, the ratio along an extremal ray is less than one | `Auto.two_rpow_neg_lt_one`, `Auto.ofReal_two_rpow_neg_lt_one`
proved | **`lem:finite-marcinkiewicz`, geometric summation along each extremal ray** | `Auto.tsum_two_rpow_neg_mul`, `Auto.tsum_two_rpow_neg_mul_ne_top`
proved | `lem:finite-marcinkiewicz`, the four nonnegative parts of a complex input, each dominated by its modulus | `Auto.cpart`, `Auto.cpart_nonneg`, `Auto.cpart_le_norm`, `Auto.measurable_cpart`
proved | `lem:finite-marcinkiewicz`, recovery of the input from its four parts | `Auto.max_sub_max_neg`, `Auto.cpart_recombine`
proved | **`lem:finite-marcinkiewicz`, the monotone approximation by nonnegative simple functions** | `Auto.exists_monotone_simple_approx`
proved | `lem:finite-marcinkiewicz`, the weak `L^q` quasi-norm and its basic properties | `Auto.wnorm`, `Auto.le_wnorm`, `Auto.wnorm_le`, `Auto.wnorm_mono`
proved | `lem:finite-marcinkiewicz`, Chebyshev: a strong estimate implies the weak one | `Auto.wnorm_le_eLpNorm`
proved | `lem:finite-marcinkiewicz`, algebraic trilinearity and the vanishing of a zero slot | `Auto.Trilin`, `Auto.Trilin.update_zero`
proved | **`lem:finite-marcinkiewicz`, expansion by trilinearity over a finite sum in one slot** | `Auto.Trilin.finset_sum`
proved | `lem:finite-marcinkiewicz`, the split of the half line at a level | `Auto.Ioi_zero_split`, `Auto.Ioc_disjoint_Ioi_zero`
proved | `lem:finite-marcinkiewicz`, the Lebesgue integral of a real power on each of the two pieces | `Auto.lintegral_rpow_Ioc`, `Auto.lintegral_rpow_Ioi`
proved | `lem:finite-marcinkiewicz`, the weak bound cleared of its denominator, and the layer cake integrand | `Auto.meas_rpow_le_of_wnorm`, `Auto.meas_mul_rpow_le_of_wnorm`
proved | `lem:finite-marcinkiewicz`, the layer cake formula for the `L^q` integral | `Auto.lintegral_enorm_rpow_eq`
proved | **`lem:finite-marcinkiewicz`, the distributional upgrade with an `L^infinity` upper endpoint** | `Auto.eLpNorm_le_of_wnorm_of_bdd`
proved | **`lem:finite-marcinkiewicz`, the distributional upgrade between two finite endpoints, at a free splitting level** | `Auto.lintegral_enorm_rpow_le_of_wnorm_pair`
proved | `lem:finite-marcinkiewicz`, the interpolation relation between the three output exponents | `Auto.interp_relation`, `Auto.interp_theta_mem`
proved | **`lem:finite-marcinkiewicz`, the optimal splitting level, giving the product of endpoint powers** | `Auto.exists_split_level`
proved | **`lem:finite-marcinkiewicz`, the distributional upgrade between two finite endpoints** | `Auto.eLpNorm_le_of_wnorm_pair`
proved | `lem:finite-marcinkiewicz`, finiteness and nonvanishing of the products of powers | `Auto.rpow_ne_zero_of_ne_zero`, `Auto.rpow_ne_top_of_ne_top`, `Auto.prod_ne_zero_of_ne_zero`, `Auto.prod_ne_top_of_ne_top`
proved | `lem:finite-marcinkiewicz`, the interpolated product of the measures of the input sets | `Auto.prod_rpow_interp`
proved | **`lem:finite-marcinkiewicz`, the distributional upgrade in the shape a restricted estimate produces** | `Auto.eLpNorm_le_of_wnorm_pair_prod`
proved | `lem:finite-marcinkiewicz`, the `L^infinity` upper endpoint in the shape a restricted estimate produces | `Auto.eLpNorm_le_of_wnorm_of_bdd_prod`
proved | `lem:finite-marcinkiewicz`, restricted weak, strong and `L^infinity` estimates in set form | `Auto.indicators`, `Auto.RestrictedWeak`, `Auto.RestrictedStrong`, `Auto.RestrictedBdd`
proved | **`lem:finite-marcinkiewicz`, restricted strong estimates at interior points of a two-vertex segment** | `Auto.restrictedStrong_of_restrictedWeak_pair`, `Auto.restrictedStrong_of_restrictedWeak_bdd`
proved | `lem:finite-marcinkiewicz`, a quantity below two bounds is below their weighted geometric mean | `Auto.le_geom_mean_of_le`
proved | `lem:finite-marcinkiewicz`, a restricted strong estimate implies the restricted weak one | `Auto.restrictedWeak_of_restrictedStrong`
proved | **`lem:finite-marcinkiewicz`, combining two vertices with equal output exponent** | `Auto.restrictedStrong_combine`, `Auto.restrictedWeak_combine`, `Auto.restrictedBdd_combine`
proved | **`lem:finite-marcinkiewicz`, restricted strong estimates at interior points of the convex hull, by iterated two-vertex steps** | `Auto.restrictedStrong_of_chain`
proved | `lem:finite-marcinkiewicz`, the dyadic floor and its two-sided comparison with the value | `Auto.dyadicFloor`, `Auto.dyadicFloor_nonneg`, `Auto.dyadicFloor_le`, `Auto.le_two_mul_dyadicFloor`
proved | `lem:finite-marcinkiewicz`, the dyadic floor is constant on each dyadic level set | `Auto.dyadicFloor_eq_of_mem`
proved | `lem:finite-marcinkiewicz`, bounded nonnegative measurable data, the class the dyadic expansion stays inside | `Auto.BddMeas`
proved | **`lem:finite-marcinkiewicz`, monotonicity of the operator on nonnegative inputs, which the proof needs and the statement omits, see the ErrorReport entry of 2026-09-13** | `Auto.Mono3`
proved | `lem:finite-marcinkiewicz`, the real integrand of the averages and its integrability | `Auto.prodShiftR`, `Auto.prodShift_ofReal`, `Auto.measurable_prodShiftR`, `Auto.prodShiftR_nonneg`, `Auto.prodShiftR_mono`, `Auto.exists_bound_prodShiftR`, `Auto.intervalIntegrable_prodShiftR`
proved | **`lem:finite-marcinkiewicz`, the averages of `def:averages` are monotone on nonnegative inputs** | `Auto.A_ofReal`, `Auto.mono3_A`
proved | `lem:finite-marcinkiewicz`, the level index is determined by the value, and the comparison holds at zero too | `Auto.dyadicLevel_eq_log`, `Auto.le_two_mul_dyadicFloor'`
proved | **`lem:finite-marcinkiewicz`, the finite dyadic expansion of a nonnegative simple input** | `Auto.exists_finset_dyadicFloor`, `Auto.ofReal_indicator`, `Auto.exists_finset_dyadicFloor_complex`
proved | `lem:finite-marcinkiewicz`, the dyadic floor stays inside the class the expansion needs | `Auto.measurable_dyadicFloor`, `Auto.bddMeas_dyadicFloor`, `Auto.bddMeas_two_mul`
proved | **`lem:finite-marcinkiewicz`, expansion of the operator over the three finite dyadic sums** | `Auto.update3_eq_matrix`, `Auto.indicators_matrix`, `Auto.Trilin.expand3`
proved | `lem:finite-marcinkiewicz`, the triangle inequality in `L^q` for a finite sum of scaled terms | `Auto.eLpNorm_const_mul'`, `Auto.aestronglyMeasurable_sum_mul`, `Auto.eLpNorm_sum_mul_le`
proved | **`lem:finite-marcinkiewicz`, the triple dyadic sum estimated term by term in `L^q`** | `Auto.eLpNorm_triple_sum_mul_le`
proved | `lem:finite-marcinkiewicz`, the two-sided geometric series along a ray of the lattice | `Auto.tsum_pow_natAbs_le`
proved | **`lem:finite-marcinkiewicz`, one term of the extremal ray: the normalization bounds the measure and the perturbed exponent decays** | `Auto.term_le_pow_natAbs`
proved | **`lem:finite-marcinkiewicz`, the geometric summation along an extremal ray** | `Auto.tsum_extremal_ray`, `Auto.tsum_extremal_ray_ne_top`
proved | `lem:finite-marcinkiewicz`, the exponent of a coordinate and the exponent vector on the cone of a lattice point | `Auto.coneExp`, `Auto.coneVec`, `Auto.tsum_extremal_ray_coneExp`
proved | **`lem:finite-marcinkiewicz`, the nested triple sum of a product factorizes into three rays** | `Auto.nested_sum_le`
proved | **`lem:finite-marcinkiewicz`, the cone split and the geometric summation combined** | `Auto.nested_sum_cone_le`
proved | `lem:finite-marcinkiewicz`, eta for a triple and scaling one slot | `Auto.matrix_eta3`, `Auto.Trilin.smul_slot`
proved | **`lem:finite-marcinkiewicz`, scaling all three slots: the factor eight the dyadic comparison costs** | `Auto.Trilin.smul3`
proved | `lem:finite-marcinkiewicz`, the extended norms of the dyadic coefficients | `Auto.enorm_two_zpow`
proved | **`lem:finite-marcinkiewicz`, a null slot kills the output, the second hypothesis the statement omits, see the ErrorReport entry of 2026-09-13** | `Auto.Null3`, `Auto.eLpNorm_eq_zero_of_null3`
proved | **`lem:finite-marcinkiewicz`, the estimate for the dyadic floors** | `Auto.eLpNorm_dyadicFloor_le`
proved | **`lem:finite-marcinkiewicz`, the statement for normalized nonnegative simple inputs** | `Auto.finite_marcinkiewicz_simple`
proved | `lem:finite-marcinkiewicz`, a single dyadic term is below the `L^p` integral | `Auto.two_zpow_rpow`, `Auto.meas_dyadicLevel_le`, `Auto.lintegral_rpow_eq_eLpNorm_rpow`
proved | **`lem:finite-marcinkiewicz`, the normalization from the `L^p` norms of the inputs** | `Auto.normalization_of_eLpNorm_le_one`
proved | `lem:finite-marcinkiewicz`, continuity along monotone limits, the third hypothesis the statement omits, and the collected hypotheses | `Auto.Lim3`, `Auto.Admissible`
proved | `lem:finite-marcinkiewicz`, the monotone simple approximation in real form | `Auto.exists_simple_approx_real`
proved | **`lem:finite-marcinkiewicz`, the passage from nonnegative simple inputs to nonnegative measurable ones** | `Auto.finite_marcinkiewicz_bddMeas`
proved | **`lem:finite-marcinkiewicz`, the passage from bounded to arbitrary nonnegative measurable inputs, by truncation** | `Auto.finite_marcinkiewicz_meas`
proved | `lem:finite-marcinkiewicz`, the four unimodular coefficients recombining a complex input | `Auto.cpartSign`, `Auto.enorm_cpartSign`, `Auto.cpart_sum`
proved | **`lem:finite-marcinkiewicz`, the statement at interior points of the convex hull** | `Auto.finite_marcinkiewicz`
proved | **`thm:strong-real-improving`, the exponent vector of the improving vertex** | `Auto.improvingVertex`, `Auto.improvingVertex_inv`
proved | `thm:strong-real-improving`, the exponent vectors of the four trivial vertices and of the target | `Auto.trivialVertex`, `Auto.trivialVertexInf`, `Auto.targetVertex`, `Auto.targetVertex_inv`
proved | **`thm:strong-real-improving`, the trivial vertex `L^infinity x L^infinity x L^infinity -> L^infinity`** | `Auto.bddMeas_indicator`, `Auto.indicators_eq_ofReal`, `Auto.indicator_le_one`, `Auto.restrictedBdd_A`
proved | **`thm:strong-real-improving`, the three trivial vertices `L^1 x L^infinity x L^infinity -> L^1`, by Fubini** | `Auto.prodShiftR_le_single`, `Auto.lintegral_indicator_shift`, `Auto.ofReal_indicator_enn`, `Auto.restrictedStrong_A_one`
proved | **`thm:strong-real-improving`, merging the three `L^1` vertices with weights `3/5, 1/5, 1/5`** | `Auto.RestrictedStrong.congr`, `Auto.mergedTrivialVertex`, `Auto.restrictedStrong_A_merged`
proved | **`thm:strong-real-improving`, the convex combination with weights `1/2, 1/4, 1/12, 1/12, 1/12`** | `Auto.strong_real_improving_weights`, `Auto.targetVertex_eq_combination`, `Auto.target_output_eq_combination`, `Auto.target_output_exponent`
proved | `thm:strong-real-improving`, the scale gain `1/2 * (-1/10) = -1/20` | `Auto.strong_real_improving_gain`proved | `thm:strong-real-improving`, monotonicity of a restricted estimate in its constant, and the restricted strong `L^1` estimate at every point of the simplex | `Auto.RestrictedStrong.mono_const`, `Auto.RestrictedWeak.mono_const`, `Auto.restrictedStrong_A_simplex`
proved | `thm:strong-real-improving`, `Auto.Trilin` restricted to bounded measurable slots, `Auto.Lim3` weakened to Fatou with a degenerate alternative, `Auto.Admissible.measInd` restricted to measurable sets, and the complex input reduced by modulus domination instead of the four-term splitting | `Auto.BddMeasC`, `Auto.bddMeasC_zero`, `Auto.BddMeasC.const_mul`, `Auto.BddMeasC.add`, `Auto.bddMeasC_finset_sum`, `Auto.bddMeasC_ofReal`, `Auto.bddMeasC_indicator`, `Auto.bddMeasC_update`, `Auto.Trilin`, `Auto.Trilin.update_zero`, `Auto.Trilin.finset_sum`, `Auto.Trilin.expand3`, `Auto.Trilin.smul_slot`, `Auto.Trilin.smul3`, `Auto.eLpNorm_le_of_tendsto_or_zero`, `Auto.Lim3`, `Auto.Admissible`, `Auto.finite_marcinkiewicz`
proved | **`thm:strong-real-improving`, discharging `Auto.Admissible (Auto.A N)`**: trilinearity on bounded measurable slots, monotonicity, the null slot, measurability, monotone limits, and modulus domination | `Auto.prodShift_update`, `Auto.intervalIntegrable_slot`, `Auto.trilin_A`, `Auto.modC_A`, `Auto.measurable_intervalIntegral_prodShiftR`, `Auto.measFun_A`, `Auto.measInd_A`, `Auto.null3_A`, `Auto.lim3_A`, **`Auto.admissible_A`**
proved | **`thm:strong-real-improving`, the eight cone vectors at `N = 1`** by `Auto.restrictedStrong_of_chain`, with half-width `1/400` | `Auto.improvingVertex_base_ne_top`, `Auto.improvingVertex_base_ne_zero`, `Auto.improvingConst_ne_top`, `Auto.improvingConst_ne_zero`, `Auto.improvingExp_zero_one`, `Auto.chainConst`, `Auto.chainConst_ne_top`, `Auto.restrictedStrong_A_chain`, **`Auto.exists_restrictedStrong_A_cone`**
proved | **`thm:strong-real-improving`, the scaling transfer from `N = 1`**, giving the factor `N^{-1/20} = N^{6/q - sum 6/p_i}` | `Auto.measurable_S`, `Auto.measurable_A`, `Auto.eLpNorm_A_of_scale_one`, `Auto.strong_real_improving_scale_factor`
proved | **`thm:strong-real-improving`, the resulting strong estimate with `N^{-1/20}`** | `Auto.A_smul_slots`, `Auto.A_ae_zero_of_slot_ae_zero`, `Auto.eLpNorm_A_one_le`, `Auto.one_sub_ofReal_rpow_inv_ne_top`, **`Auto.strong_real_improving`**
proved | **`thm:strong-real-improving` at every index triple**, which `Auto.main_smoothing` needs because it quantifies over all `j` | `Auto.fin3_third`, `Auto.targetV`, `Auto.targetV_zero_one`, `Auto.restrictedStrong_A_chain'`, `Auto.trivialVertexInf_apply`, `Auto.sum_of_perm`, `Auto.coneConst`, `Auto.coneConst_ne_top`, **`Auto.restrictedStrong_A_cone'`**, `Auto.targetV_pos`, `Auto.targetV_ge`, `Auto.targetV_sum`, `Auto.strong_real_improving_scale_factor'`, **`Auto.strong_real_improving'`**
proved | `cor:kosz-53-internal`, the a priori `L^2` finiteness of the adjoint for nice inputs, from the pointwise bound by the curve average of `|g_0|`, which is bounded and in `L^1` | `Auto.enorm_rpow_two`, `Auto.enorm_Astar_le`, `Auto.lintegral_enorm_Astar_ne_top`, **`Auto.eLpNorm_Astar_two_ne_top`**
proved | **`cor:kosz-53-internal`**, pairing with `g_0`, the adjoint identity, and the supremum over the unit ball of `L^2` in the slot `j`, giving `norm(A_N^{*j}(g), L^2) <= C N^{-1/20} norm(g_0, L^6) norm(g_{j'}, L^{40/7}) norm(g_k, L^6)` | `Auto.erase_fin3_eq`, `Auto.targetV_at_j`, `Auto.targetV_at_m`, `Auto.targetV_at_k`, `Auto.adjShift_update`, `Auto.Astar_update`, **`Auto.kosz53_internal`**
proved | **`cor:kosz-53-internal`, the exponent identities over the denominator `120`** | `Auto.kosz53_conjugate`, `Auto.kosz53_sum`, `Auto.kosz53_sum'`, `Auto.kosz53_range`, `Auto.kosz53_gain`, `Auto.kosz53_inputs`
proved | **`lem:adjoint-gain-to-subunit`, reduction to `N = 1` by anisotropic dilation** | `Auto.eLpNorm_Atilde_of_scale_one`, `Auto.kosz_subunit`
proved | `lem:adjoint-gain-to-subunit`, coordinate continuity on `R^3` | `Auto.continuous_E3_coord`
proved | **`lem:adjoint-gain-to-subunit`, the unit-cube partition and its finite enlargements** | `Auto.unitCube`, `Auto.bigCube`, `Auto.measurableSet_unitCube`, `Auto.measurableSet_bigCube`, `Auto.unitCube_disjoint`, `Auto.mem_unitCube_floor`, `Auto.iUnion_unitCube`
proved | **`lem:adjoint-gain-to-subunit`, the enlargement contains every translate that occurs, and has finite measure** | `Auto.unitCube_subset_bigCube`, `Auto.curve_mem_Icc`, `Auto.shift_mem_bigCube`, `Auto.volume_bigCube_lt_top`
not applicable | `lem:adjoint-gain-to-subunit`, principal and nonprincipal cubes of the finite dyadic tree -- superseded: patch 2 replaces the stopping-time proof, see the ErrorReport entry of 2026-09-14 | --
not applicable | `lem:adjoint-gain-to-subunit`, the cyclic stopping-time iteration -- superseded by patch 2 | --
proved | patch 2 `lem:three-set-restricted-upper-half`, the incidence integral as a fibre integral (D1) and one measurable refinement (D2) | `Auto.uhI`, `Auto.measurableSet_uhI`, `Auto.uhInc`, `Auto.uhFib`, `Auto.measurable_uhPair`, `Auto.measurable_uhFib`, **`Auto.uhInc_eq_setLIntegral`**, `Auto.uhFib_update`, `Auto.uhRefine`, `Auto.measurableSet_uhRefine`, `Auto.uhRefine_subset`, **`Auto.uhInc_refine_le`**
proved | patch 2 `lem:three-set-restricted-upper-half`, the three updates in the order `1, d, 1` with thresholds `1/2, 1/4, 1/8` (D3), and the choice of `z` | `Auto.enn_div_mul`, `Auto.uhAlpha`, `Auto.uhAlpha_mul`, `Auto.uhF1`, `Auto.uhF2`, `Auto.uhF3`, `Auto.measurableSet_uhF1`, `Auto.measurableSet_uhF2`, `Auto.measurableSet_uhF3`, `Auto.uhF1_ne`, `Auto.uhF2_ne`, `Auto.uhF3_ne`, `Auto.uhF1_zero`, `Auto.uhF2_self`, `Auto.uhF3_zero`, **`Auto.uhInc_uhF3_ge`**, **`Auto.uhF3_zero_nonempty`**
proved | patch 2 `lem:three-set-restricted-upper-half`, the three-step tower, fibre separation, and `|P| >= 2^{-10} alpha_1^2 alpha_d` (T1), (T2) | `Auto.enn_le_half_of_two_mul_le`, `Auto.uhFibSet`, `Auto.measurableSet_uhFibPre`, `Auto.measurableSet_uhFibSet`, `Auto.prod_indicator_eq_indicator`, `Auto.uhFib_eq_volume`, **`Auto.uhFibSet_zero_ge`**, **`Auto.uhFibSet_d_ge`**, **`Auto.uhFibSet_third_ge`**, `Auto.measurableSet_memFibSet`, `Auto.uhY1`, `Auto.uhY2`, `Auto.continuous_uhY1`, `Auto.uhParam`, `Auto.measurableSet_uhParam`, `Auto.volume_sep_interval`, **`Auto.volume_uhParam_ge`**
proved | patch 2 `lem:three-set-restricted-upper-half`, the transport of the parameter set to `R^3`, the change of variables for an injective `C^1` map, the flow and its routing into `E_ell` | `Auto.e3ToProd`, `Auto.measurePreserving_E3_prod`, `Auto.measurePreserving_e3ToProd`, `Auto.measure_e3ToProd_preimage`, `Auto.measurableSet_e3ToProd_preimage`, `Auto.lintegral_abs_det_le_of_injOn`, `Auto.uhFlow`, **`Auto.uhFlow_image_subset`**
proved | patch 2 `lem:three-set-restricted-upper-half`, the Jacobian (J1) in its two cases: `6 w^2 (v-u)` for `d = 1`, `l = 2` and `6 w (u^2-v^2)` for `d = 2`, `l = 1` | `Auto.det_toEuclideanLin3`, `Auto.uhPiA`, `Auto.uhPiB`, `Auto.uhMatA`, `Auto.uhMatB`, `Auto.det_uhMatA`, `Auto.det_uhMatB`, `Auto.uhMapA`, `Auto.uhMapB`, `Auto.uhDerivA`, `Auto.uhDerivB`, **`Auto.det_uhDerivA`**, **`Auto.det_uhDerivB`**, `Auto.hasFDerivAt_uhPiA`, `Auto.hasFDerivAt_uhPiB`, **`Auto.hasFDerivAt_uhMapA`**, **`Auto.hasFDerivAt_uhMapB`**
proved | patch 2 `lem:three-set-restricted-upper-half`, injectivity of the flow off `u = v`, and the change of variables (J2) | `Auto.sq_lt_sq_of_lt_nonneg`, `Auto.cube_lt_cube_of_lt_nonneg`, `Auto.injOn_const_add3`, `Auto.uhMapA_zero`, `Auto.uhMapA_one`, `Auto.uhMapA_two`, `Auto.uhMapB_zero`, `Auto.uhMapB_one`, `Auto.uhMapB_two`, `Auto.uhFlow_eq_uhMapA`, `Auto.uhFlow_eq_uhMapB`, `Auto.uhOmega`, **`Auto.injOn_uhMapA`**, **`Auto.injOn_uhMapB`**, `Auto.uhParam_preimage_subset_uhOmega`, `Auto.det_uhDerivA'`, `Auto.det_uhDerivB'`, **`Auto.uhArea_A`**, **`Auto.uhArea_B`**
proved | **patch 2 `lem:three-set-restricted-upper-half`**, the restricted estimate `K <= 16 |E_1|^{1/2} |E_d|^{1/2} |E_ell|^{1/4}` (R) | `Auto.volume_uhI`, `Auto.uhFib_le_one`, `Auto.uhInc_le_volume`, `Auto.uh_const_arith`, **`Auto.uhInc_pow_four_le`**, **`Auto.uhInc_le_restricted`**
proved | patch 2, the monomial average over an arbitrary parameter interval is admissible, so `Auto.Atilde 1` is | `Auto.Aint`, `Auto.A_eq_Aint`, `Auto.Atilde_eq_Aint`, `Auto.Aint_ofReal`, `Auto.trilin_Aint`, `Auto.mono3_Aint`, `Auto.measurable_intervalIntegral_prodShiftR'`, `Auto.measFun_Aint`, `Auto.measInd_Aint`, `Auto.null3_Aint`, `Auto.lim3_Aint`, `Auto.modC_Aint`, `Auto.admissible_Aint`, **`Auto.admissible_Atilde_one`**
proved | patch 2, the incidence integral is the `L^1` norm of the upper-half average on indicators, so (R) is a restricted strong estimate at `q = 1` | `Auto.enorm_Atilde_indicators`, **`Auto.eLpNorm_Atilde_indicators`**, `Auto.uhV`, **`Auto.restrictedStrong_Atilde_uhV`**, `Auto.restrictedStrong_Atilde_trivial`
proved | patch 2 `lem:three-set-strong-upper-half`, the barycentric coefficients and the restricted bound (S1) | `Auto.restrictedStrong_simplex`, **`Auto.restrictedStrong_Atilde_combo`**
proved | patch 2, the eight cone vectors of (S1): the barycentric coefficients are positive at each perturbation by `1/64` | `Auto.uhB`, `Auto.uhD`, `Auto.uhL`, `Auto.uhDL`, `Auto.restrictedStrong_Atilde_of_coeffs`, **`Auto.restrictedStrong_Atilde_cone`**
proved | **patch 2 `lem:three-set-strong-upper-half`**, the finite value-level summation giving the strong `L^1` bound (S) | `Auto.Aint_smul_slots`, `Auto.Aint_ae_zero_of_slot_ae_zero`, `Auto.eLpNorm_normalize`, `Auto.uhC1`, `Auto.uhB_pos`, `Auto.uhC1_ne_zero`, `Auto.uhC1_ne_top`, `Auto.eLpNorm_Atilde_normalized`, **`Auto.eLpNorm_Atilde_le`**
proved | patch 2 `lem:adjoint-gain-to-subunit`, localization to the unit cubes, their measure, and the bounded overlap of the enlargements | `Auto.Atilde_localize`, `Auto.unitCube_eq_preimage`, `Auto.volume_unitCube`, `Auto.isProbabilityMeasure_unitCube`, `Auto.tsum_indicator_bigCube_le`, **`Auto.tsum_setLIntegral_bigCube_le`**
proved | patch 2, Hoelder in three factors, for integrals and for sums | `Auto.holderConjugate_of_mem_Ioo`, `Auto.lintegral_rpow_mul_rpow_le`, `Auto.lintegral_rpow_mul3_le`, `Auto.eLpNorm_indicator_rpow`, **`Auto.tsum_rpow_mul3_le`**
proved | patch 2, the Hoelder step on a cube and the partition of the space into unit cubes | `Auto.lintegral_enorm_rpow_le_of_probability`, `Auto.lintegral_eq_tsum_unitCube`, `Auto.measurable_Aint`, `Auto.measurable_Atilde_one`, `Auto.uhM`, `Auto.uhTh`, `Auto.uhTh_pos`, `Auto.uhTh_sum`, **`Auto.lintegral_unitCube_le`**
proved | **patch 2 `lem:adjoint-gain-to-subunit`**, the subunit bound (Q) | `Auto.lintegral_enorm_rpow_eq_eLpNorm`, **`Auto.eLpNorm_Atilde_subunit`**
proved | **`lem:adjoint-gain-to-subunit`, the exponents `d_m`, `q_m`, `q_{i,m}` and the limit** | `Auto.dExp`, `Auto.dExp_pos`, `Auto.dExp_lt_half`, `Auto.dExp_reciprocal_sum`, `Auto.dExp_qj`, `Auto.dExp_qi_recip_lt_half`, `Auto.dExp_qi_recip_lt_one`, `Auto.dExp_one_sub`, `Auto.dExp_qm_range`
proved | **`lem:adjoint-gain-to-subunit`, absorbing the `2^{-m}` tail** | `Auto.absorb_le`, `Auto.two_inv_pow_lt_one`
proved | **`cor:kosz-subunit-internal`**, discharging `Auto.KoszSubunitScaleOne` from patch 2 (Q), with `B = 9/8` and `(b_i) = (1/p_i)` | **`Auto.koszSubunitScaleOne`**

### Part V -- row 4: `thm:real-inverse`

status | source item | Lean name
--- | --- | ---
proved | **`def:local-uniformity`, the Fejer kernel, its nonnegativity, support and integral one** | `Auto.fejer`, `Auto.fejer_nonneg`, `Auto.fejer_eq_zero_of_le`, `Auto.continuous_fejer`, `Auto.fejer_eq_of_mem`, `Auto.integral_affine`, `Auto.integral_fejer`
proved | **`def:local-uniformity`, the Fejer difference and its iterates** | `Auto.fdiff`, `Auto.fdiff_zero_shift`, `Auto.norm_fdiff_le`, `Auto.fdiffIter`, `Auto.fdiffIter_zero`, `Auto.fdiffIter_succ`, `Auto.norm_fdiffIter_le`
proved | **`def:local-uniformity`, the cube expansion of the iterated Fejer difference** | `Auto.conjPar`, `Auto.conjPar_succ`, `Auto.numFalse`, `Auto.cubeShift`, `Auto.numFalse_cons`, `Auto.cubeShift_cons`, `Auto.consBoolEquiv`, `Auto.fdiffIter_eq_cubeProd`
proved | **`def:local-uniformity`, the local uniformity norms** | `Auto.locUnifPow`, `Auto.prod_fejer_nonneg`, `Auto.norm_prod_fejer`, `Auto.norm_locUnif_integrand_le`, `Auto.locUnif_integrand_eq`
proved | **`def:local-uniformity`, the Fejer kernel is a convolution square: the overlap of an interval with its translate** | `Auto.integral_indicator_shift_Ioc`, `Auto.fejer_eq_overlap`
proved | `def:local-uniformity`, an interval integral times its conjugate is a double integral | `Auto.integral_mul_conj_integral`
proved | `def:local-uniformity`, the `x`-integral of a shifted pair depends only on the difference of the shifts | `Auto.integral_shift_pair`
proved | `lem:fejer-vdc`, the change of variables in the shift variables | `Auto.integral_comp_sub_interval`, `Auto.integral_comp_sub_full`, `Auto.integral_shift_pair_interval`
proved | `def:local-uniformity`, exchanging an integral over `R^3` with an integral over an interval | `Auto.integral_swap_interval`
proved | `def:local-uniformity`, an integral of `z * conj z` is real and nonnegative | `Auto.re_integral_mul_conj_nonneg`
proved | **`def:local-uniformity`, the positivity at one difference, given the exchange** | `Auto.re_integral_shift_pair_nonneg`
proved | **`def:local-uniformity`, the integrability the exchange needs, for inputs of class `Auto.Nice`** | `Auto.integrable_shift_pair_prod`, `Auto.integral_swap_shift_nice`
proved | `def:local-uniformity`, joint integrability of a shifted input in the point and the shift | `Auto.integrable_shift_prod`
proved | `def:local-uniformity`, the exchange in the second shift | `Auto.integrable_shift_pair_prod'`, `Auto.integral_swap_shift_nice'`
proved | `def:local-uniformity`, conjugation through an interval integral, and the inner shift integral carried out | `Auto.intervalIntegral_conj`, `Auto.integral_inner_shift`
proved | `def:local-uniformity`, the shifted average is strongly measurable and bounded | `Auto.stronglyMeasurable_shiftAvg`, `Auto.norm_shiftAvg_le`
proved | **`def:local-uniformity`, the double exchange** | `Auto.integral_swap_outer`, `Auto.integral_swap_double`
proved | **`def:local-uniformity`, the integral is real and nonnegative at one difference** | `Auto.re_integral_shift_pair_nonneg_nice`
proved | `lem:fejer-vdc`, the indicator of the shift interval and the inner substitution `b = a - h` | `Auto.shiftInd`, `Auto.measurable_shiftInd`, `Auto.shiftInd_nonneg`, `Auto.shiftInd_le_one`, `Auto.integral_shiftInd_shift`, `Auto.integral_inner_sub`
proved | **`lem:fejer-vdc`, the change of variables from the two shift variables to their difference, for measurable bounded data** | `Auto.integrable_shiftInd_prod`, `Auto.integral_double_sub_eq_fejer`
proved | `def:local-uniformity`, the paired average is continuous and bounded | `Auto.pairAvg`, `Auto.norm_pairAvg_le`, `Auto.continuous_pairAvg`
proved | **`def:local-uniformity`, the Fejer-weighted integral at one difference is real and nonnegative** | `Auto.re_fejer_pairAvg_nonneg`
proved | `def:local-uniformity`, the difference operator preserves the class `Auto.Nice` | `Auto.nice_fdiff`, `Auto.nice_fdiffIter`
proved | **`def:local-uniformity`, the positivity at every order** | `Auto.re_fejer_fdiffIter_nonneg`
proved | `lem:fejer-vdc`, the boundary estimate: shifting the interval changes the integral by at most `2h` | `Auto.norm_integral_shift_sub_le`
proved | `lem:fejer-vdc`, the shifted integral is measurable in the shift and bounded | `Auto.stronglyMeasurable_shiftIntegral`, `Auto.norm_shiftIntegral_le`, `Auto.intervalIntegrable_shiftIntegral`
proved | **`lem:fejer-vdc`, the averaged boundary estimate** | `Auto.norm_integral_avg_sub_le`
proved | **`lem:fejer-vdc`, the Cauchy-Schwarz step** | `Auto.sq_integral_le`, `Auto.sq_norm_integral_le`
proved | `lem:fejer-vdc`, expanding the square of the shifted average | `Auto.sq_norm_shiftAvg_eq`
proved | `lem:fejer-vdc`, exchanging the interval integral with the shift integral | `Auto.integrable_pair_prod_bdd`, `Auto.integral_swap_interval_pair`
proved | `lem:fejer-vdc`, changing the interval of integration costs the endpoint displacement | `Auto.norm_integral_sub_integral_le`
proved | `lem:fejer-vdc`, the endpoints of `I` intersected with its translate, and their displacement | `Auto.capLeft`, `Auto.capRight`, `Auto.endpoint_displacement_le`
proved | `lem:fejer-vdc`, a bounded measurable function is interval integrable everywhere | `Auto.intervalIntegrable_of_bdd`
proved | `lem:fejer-vdc`, the shift integral moved inside the interval integral | `Auto.integrable_shift_prod_bdd`, `Auto.integral_swap_shift_interval`
proved | `lem:fejer-vdc`, the inner shifted average is measurable and bounded | `Auto.stronglyMeasurable_shiftAvg'`, `Auto.norm_shiftAvg'_le`
proved | `lem:fejer-vdc`, interval integrability from a bound, in the real and complex cases | `Auto.intervalIntegrable_of_bdd_real`, `Auto.intervalIntegrable_of_bdd'`
proved | **`lem:fejer-vdc`, Cauchy-Schwarz applied to the average of the shifted averages** | `Auto.sq_norm_avg_le`
proved | `lem:fejer-vdc`, the paired integrand is measurable and bounded | `Auto.measurable_pairShift`, `Auto.norm_pairShift_le`
proved | **`lem:fejer-vdc`, replacing the two shifts by their difference, at a cost of `2H`** | `Auto.norm_pairIntegral_sub_le`
proved | `lem:fejer-vdc`, the outer exchange with a bounded factor of the interval variable | `Auto.integral_swap_interval_prod`
proved | **`lem:fejer-vdc`, the triple exchange: the interval integral moves past both shift integrals** | `Auto.integral_swap_triple_interval`
proved | **`lem:fejer-vdc`, the integral of the squared modulus as a triple integral** | `Auto.ofReal_integral_sq_norm_eq`
proved | `lem:fejer-vdc`, the paired integral is measurable in the difference and bounded by the interval length | `Auto.stronglyMeasurable_pairIntegral`, `Auto.norm_pairIntegral_le`
proved | `lem:fejer-vdc`, the paired integral with two shifts: joint measurability and the interval-length bound | `Auto.stronglyMeasurable_pairIntegral₂`, `Auto.stronglyMeasurable_pairDouble`, `Auto.stronglyMeasurable_diffDouble`, `Auto.norm_pairIntegral₂_le`
proved | `lem:fejer-vdc`, the cost of replacing the two shifts by their difference, over the square of shifts and the full interval | `Auto.norm_double_pair_sub_le`
proved | `lem:fejer-vdc`, a parametric integral over an `Ioc` with measurable endpoints is measurable in the parameter | `Auto.measurable_varSetIntegral`
proved | `lem:fejer-vdc`, the intersection of the interval with its translate is an `Ioc` of length at most `N` | `Auto.capSet`, `Auto.capSet_eq_Ioc`, `Auto.capLeft_le_capRight`, `Auto.volume_capSet_le`
proved | `lem:fejer-vdc`, the paired integral over `I` intersected with its translate: measurable in the shift, bounded by the interval length | `Auto.capPair`, `Auto.measurable_capPair`, `Auto.norm_capPair_le`, `Auto.capPair_eq_intervalIntegral`
proved | **`lem:fejer-vdc`, the change of variables from the two shifts to their difference over the intersected interval, at a total cost of `2H^3`** | `Auto.stronglyMeasurable_capDouble`, `Auto.norm_pairIntegral_sub_capPair_le`, `Auto.norm_double_pair_sub_cap_le`
proved | **`lem:fejer-vdc`, the assembly of the inequality -- the display is missing an operator, see the ErrorReport entry of 2026-09-13** | `Auto.norm_le_of_norm_sub_le`, `Auto.fejer_vdc`
proved | `lem:fejer-vdc`, the Fejér kernel is bounded, vanishes off its support, and times a bounded measurable function is integrable | `Auto.max_zero_add_max_zero_neg`, `Auto.fejer_le_inv`, `Auto.fejer_eq_zero_off`, `Auto.integrable_fejer_mul`
proved | **`lem:fejer-vdc` on a fixed interval: replacing `I ∩ (I - h)` by `I` costs `|h|`, giving the form the induction iterates** | `Auto.norm_pairIntegral_sub_capPair_le'`, `Auto.fejer_vdc'`
proved | `lem:fejer-vdc`, the nested Fejér average of the iterated Fejér differences: measurable in any parameter, nonnegative, at most one | `Auto.rdiff`, `Auto.measurable_rdiff`, `Auto.norm_rdiff_le`, `Auto.vdcAvg`, `Auto.measurable_vdcAvg`, `Auto.vdcAvg_nonneg`, `Auto.vdcAvg_le_one`
proved | `lem:fejer-vdc`, Cauchy-Schwarz against the kernel, and iterating it to move a power of two inside | `Auto.integrable_fejer`, `Auto.add_pow_le_two_pow_mul`, `Auto.sq_integral_fejer_le`, `Auto.pow_integral_fejer_le`
proved | **`lem:fejer-vdc`, the Gowers-Cauchy-Schwarz step**: iterating `Auto.fejer_vdc'` `s` times, with the powers moved inside the successive kernel averages, bounds the `2^s`-th power of the normalized average by `A_s` times the nested Fejer average of depth `s` plus `B_s sum_i H_i / N` | `Auto.pow_two_pow_le_mul`, **`Auto.exists_vdc_iterate`**
proved | **`lem:real-polynomial-oscillation`**, the oscillation bound for real polynomials, via the reusable prerequisite van der Corput's lemma in DFR/Auto/VanDerCorput.lean | `Auto.oscPoly`, `Auto.oscPoly_coeff`, `Auto.oscPoly_natDegree_le`, `Auto.oscPoly_eval`, **`Auto.real_polynomial_oscillation`**
superseded | **`lem:pet-reduction`** (new statement: every-input local uniformity for the monomial average) | `Auto.locUnif`, `Auto.petBox`, `Auto.petStep`, `Auto.petWeight`, `Auto.petWeight_step_lt`, `Auto.petStep_terminates`, `Auto.cfgProd`, `Auto.cfgAvg`, `Auto.cfgInt`, `Auto.cfgInt_translSub`, `Auto.cfgInt_cons`, `Auto.sq_norm_cfgHeadInt_le`, `Auto.cfgHeadInt_merge`, **`Auto.cfgHeadInt_cube`** (retained by the patch), `Auto.Lambda_eq_cfgHeadInt`, `Auto.cfgPair`, `Auto.cfgL2_le_innerSq`, `Auto.ofReal_integral_sq_norm_innerAvg`, `Auto.norm_cfgPairIntegral_sub_cfgCapPair_le`
removed | `lem:degree-lowering-zero` | (off path) `Auto.locUnifPow_succ_split`, `Auto.exists_shift_locUnifPow_ge`, `Auto.fejerHat`, `Auto.fourier_fejer`, `Auto.integrable_fejerHat`, `Auto.fourier_fejerHat`, `Auto.autocorr`, `Auto.fourier_autocorr`, `Auto.integral_fourier_mul_comm`, `Auto.integral_fejer_autocorr` -- all proved and all still valid; the Plancherel group is reusable at the patch's stage 4
open | **`thm:real-inverse`**, the specialized real inverse theorem | (off path) `Auto.phaseCutoff`, `Auto.integral_phaseCutoff_mul`, `Auto.norm_integral_phaseCutoff_mul`, `Auto.exists_phase_witness`, `Auto.exists_real_inverse_witness` -- proved and still valid, but the new proof does not need them.  `Auto.P_self_adjoint`, weakened to measurable second argument for them, stays useful

#### Part V (bis) -- the replacement proof path of `blueprints/task_2_patch_3_updated.tex`

status | stage | source item | Lean name
--- | --- | --- | ---
proved | 1 | `patch:budgets`, budget arithmetic and popularity | `Auto.budLo`, `Auto.budHi`, `Auto.budLo_pos`, `Auto.budHi_pos`, `Auto.budLo_antitone`, `Auto.budHi_monotone`, **`Auto.budLo_mul`**, **`Auto.budLo_pow`**, `Auto.setIntegral_const_real`, **`Auto.le_setIntegral_compl_add`**, **`Auto.measure_popular_ge`**, **`Auto.exists_cell_ge`**
proved | 1 | **`patch:fejer-squares`**, the Fejer square identity `int int u(x) conj(u(x + h e_j)) kappa_H(h) = ||T_{H,j} u||_2^2`, positivity of every order-`s` cube power, and `(Q_s)^2 <= (1 + H/S) Q_{s+1}` | `Auto.winAvg`, `Auto.norm_winAvg_sq`, **`Auto.integral_fejer_pairAvg_eq_sq`**, `Auto.locUnifPow_zero`, **`Auto.locUnifPow_one_eq`**, **`Auto.locUnifPow_two_eq`**, `Auto.sq_re_locUnifPow_zero_le`, **`Auto.sq_re_locUnifPow_le`**, `Auto.integral_norm_le_volume_petBox`, **`Auto.norm_locUnifPow_le_box`**, **`Auto.re_locUnifPow_mem_range`**, `Auto.norm_locUnifPow_le_L1`, `Auto.integral_norm_le_of_petBox`, **`Auto.re_locUnifPow_nonneg_le`**, `Auto.innerFejer_eq_ofReal`, **`Auto.im_locUnifPow_succ`**
proved | 2 | **`patch:signed-vdc`**, signed integrated removal (not obtained by deleting an absolute value from `Auto.fejer_vdc'`) | **`Auto.sq_norm_normalized_pairing_le`**, `Auto.integrable_shift_prod_line`, **`Auto.integral_windowAvg`**, `Auto.integral_swap_interval_line`, `Auto.integrable_shift_pair_prod_line`, `Auto.integrable_shift_pair_prod_line'`, **`Auto.integral_shift_pair_line`**, `Auto.autocorr_eq_shift_pair`, **`Auto.integral_swap_double_line`**, `Auto.stronglyMeasurable_autocorr`, `Auto.norm_autocorr_le`, **`Auto.integral_fejer_autocorr_eq_sq`**, `Auto.integrable_norm_pow_windowAvg`, **`Auto.sq_norm_integral_le_fejer_autocorr`**, **`Auto.autocorr_indicator_eq_capPair`**, **`Auto.norm_pairIntegral_sub_autocorr_le`**, **`Auto.integral_sq_norm_le_fejer_autocorr`**, **`Auto.normalized_sq_norm_le_fejer_autocorr`**, **`Auto.integral_mul_norm_le_of_sq_le`**, **`Auto.norm_integral_mul_conj_le_of_sq_le`**, `Auto.integrable_fejer_abs`, **`Auto.integral_fejer_abs_le`**, **`Auto.corrLine`**, `Auto.measurable_corrLine`, **`Auto.norm_corrLine_le`**, **`Auto.norm_corrIntegral_sub_capCorr_le`**, `Auto.integral_re_of_integrable`, `Auto.measurable_corrLine_pair`, `Auto.measurable_barCorrInt`, `Auto.measurable_capCorrInt`, **`Auto.integral_capPair_eq_setIntegral_corrLine`**, **`Auto.integral_fejer_autocorr_swap`**, **`Auto.sq_norm_signed_vdc_mid`**, **`Auto.norm_integral_fejer_capCorr_sub_le`**, **`Auto.sq_norm_signed_vdc`**
proved | 2 | **`patch:cylinder`**, cylinder Cauchy-Schwarz with its explicit state -- the reusable Gowers-Cauchy-Schwarz induction | **`Auto.cubeSel`**, `Auto.cubeSel_apply`, `Auto.cubeSel_self`, **`Auto.cubeSel_snoc`**, `Auto.measurable_cubeSel`, `Auto.measurePreserving_fst_self`, `Auto.measurePreserving_snd_self`, **`Auto.measurePreserving_cubeSel`**, `Auto.integrable_of_bdd_finite`, **`Auto.integral_mul_conj_integral_measure`**, **`Auto.sq_norm_integral_mul_le_sq`**, **`Auto.cubeProdSel`**, **`Auto.cubeProdSel_zero`**, `Auto.norm_cubeProdSel_le`, `Auto.measurable_cubeProdSel`, **`Auto.cubeProdSel_succ`**, **`Auto.sq_norm_integral_mul_inner_le`**, **`Auto.pow_two_pow_le_of_sq_chain`**, **`Auto.cubeProdSel_one`**, `Auto.measurePreserving_piFinLast`, **`Auto.integral_pi_fin_last`**, **`Auto.sq_norm_integral_eq_re_doubled`**, **`Auto.integral_re_doubled_nonneg`**, **`Auto.measurable_snoc`**, **`Auto.cylStep`**, `Auto.norm_cylStep_le`, `Auto.measurable_cylStep`, `Auto.integrable_of_bdd_finite'`, **`Auto.integral_pi_snoc`**, `Auto.norm_integral_le_one`, **`Auto.integral_mul_pi_snoc`**, `Auto.conjPar_mul`, `Auto.conjPar_conj`, **`Auto.cubeProdSel_mul_conj`**, **`Auto.cubeProdSel_cylStep`**, `Auto.integral_swap_of_bdd`, `Auto.integral_prod_of_bdd`, `Auto.integral_re_of_bdd`, **`Auto.integral_regroup_prod`**, **`Auto.integral_re_doubled_eq_cylStep`**, `Auto.measurable_cubeProdSel_right`, `Auto.measurable_cubeProdSel_snocPair`, `Auto.measurable_cubeProdSel_snocPair_fixFst`, `Auto.measurable_cubeProdSel_snocPair_fixBoth`, `Auto.integral_cubeProdSel_snoc_aux1`, `Auto.integral_cubeProdSel_snoc_aux2`, `Auto.integral_cubeProdSel_snoc_aux3`, **`Auto.integral_cubeProdSel_snoc`**, `Auto.measurable_cubeProdSel_param`, **`Auto.pow_two_pow_step`**, **`Auto.integral_cube_cylStep`**, **`Auto.sq_norm_pow_le_integral_cubeProdSel`**, **`Auto.cylStep_mul`**, **`Auto.cylStep_indep`**, **`Auto.eq_integral_of_indep_last`**, **`Auto.cylStep_prod`**, **`Auto.integral_mul_indep_pi_snoc`**, **`Auto.sq_norm_pow_le_integral_cubeProdSel_prod`**, **`Auto.integral_cubeProdSel_re_nonneg`**
proved | 2 | `patch:triangular`, distinct degrees give a triangular frequency bound | **`Auto.sum_Ico_le_of_triangular`**, **`Auto.sum_range_le_of_triangular`**, **`Auto.coeff_bound_of_oscillation_ge`**, `Auto.budLo_inv`, **`Auto.coeff_sum_smul_eq`**, **`Auto.triangular_step`**, `Auto.eval_eq_const_add_sum_Icc`, **`Auto.norm_integral_expPhase_const_add`**, **`Auto.sum_triangular_le`**, **`Auto.sum_le_of_oscillation_ge`**
proved | 3 | **`patch:pet-update`**, a labelled update preserves the protected head | **`Auto.natDegree_taylor_sub_self_le`**, **`Auto.coeff_taylor_sub_self`**, **`Auto.taylor_sub_pivot_sub`**, **`Auto.linear_in_fresh_ne_zero`**, **`Auto.isHomogeneous_add_X_mul`**, **`Auto.add_X_mul_ne_zero`**, **`Auto.petLead_add_fresh`**, **`Auto.natDegree_petChild_unshifted_le`**, **`Auto.coeff_petChild_unshifted`**, **`Auto.petChild_shifted`**, **`Auto.leadingCoeff_taylor`**, **`Auto.petSubConst`**, `Auto.petSubConst_coeff_zero`, **`Auto.petSubConst_coeff`**, `Auto.natDegree_petSubConst_le`, **`Auto.natDegree_petSubConst`**, **`Auto.leadingCoeff_petSubConst`**, **`Auto.petSubConst_sub_coeff`**, `Auto.pi_const_mul_single`, `Auto.pi_single_add'`, **`Auto.leadVec_ne_zero`**, `Auto.ne_of_sub_coeff_ne_zero`, **`Auto.coeff_petChild_unshifted_vec`**, **`Auto.petHead_ne_child`**, **`Auto.PetFactor`**, `Auto.PetFactor.starFac`, `Auto.PetFactor.shiftFac`, `Auto.PetFactor.origin_shiftFac`, `Auto.PetFactor.origin_starFac`, **`Auto.NormalPETState`**, **`Auto.ProtectedLeadingInvariant`**, **`Auto.ProtectedLeadingInvariant.subConst`**, **`Auto.petChildren`**, **`Auto.petNormalizeItem`**, `Auto.map_origin_starFac`, `Auto.length_petNormalizeItem`, `Auto.origin_petNormalizeItem`, `Auto.petNormalizeItem_coeff_zero`, **`Auto.petNewHead_ne_child`**, **`Auto.petAllItems`**, **`Auto.petRawChildren`**, **`Auto.petNormalized`**, **`Auto.petNewSpatial`**, **`Auto.petNewHead`**, `Auto.petNewHead_block_length`, `Auto.petNewHead_block_origin`, `Auto.petNewHead_coeff_zero`, `Auto.petNormalized_coeff_zero`, **`Auto.petGroup`**, `Auto.petGroup_keys`, **`Auto.petGroup_nodup`**, **`Auto.petSubConst_ne_of_natDegree_pos`**, **`Auto.petNewHead_ne_shiftedChild`**, `Auto.petGroup_fst_mem`, **`Auto.petGroup_property`**, **`Auto.petAssemble`**, **`Auto.petNewHeadFactor`**, `Auto.petNewHeadFactor_origin`, **`Auto.petNonConstChildren`**, `Auto.petNonConstChildren_ne_zero`, `Auto.petNonConstChildren_coeff_zero`, **`Auto.petUpdate_protected`**, **`Auto.petNormalized_tail_eq`**, **`Auto.mem_petNonConstChildren`**, **`Auto.PetLeadData`**, `Auto.petLeadData_zero`, **`Auto.petNewHead_ne_child_highDeg`**, **`Auto.petNewHead_ne_child_full`**, `Auto.petSubConst_zero`, **`Auto.petNewHead_ne_zero`**, **`Auto.petNewHead_ne_all`**, **`Auto.petUpdate_protected_of_invariant`**, `Auto.natDegree_petSubConst_sub_le`, **`Auto.petUpdate_invariant_diff`**, **`Auto.petUpdate_invariant_head`**, **`Auto.petUpdate_invariant_diff_highDeg`**
proved | 3 | `patch:cs-loss`, explicit accumulation of the removal losses | **`Auto.csPhi`**, `Auto.csPhi_nonneg`, `Auto.csPhi_le_one`, `Auto.csPhi_mono`, **`Auto.csPhi_lipschitz`**, `Auto.csPhi_iter_nonneg`, `Auto.csPhi_iter_le_one`, **`Auto.csPhi_iter_eq`**, **`Auto.csLoss`**
proved | 3 | `patch:multiaffine-sublevel`, the sublevel estimate actually needed | **`Auto.volume_abs_affine`**, **`Auto.integral_fejer_indicator_abs_affine_le`**, `Auto.measurableSet_abs_affine`, **`Auto.fejerMeasure`**, `Auto.fejerMeasure_apply`, `Auto.isProbabilityMeasure_fejerMeasure`, **`Auto.fejerMeasure_le_volume`**, **`Auto.fejerMeasure_abs_affine_le`**, `Auto.two_mul_div_sqrt`, **`Auto.measure_pi_fin_last`**, **`Auto.fejerPi_snoc_sublevel_le`**, **`Auto.fejerPi_linear_sublevel_le`**, **`Auto.measure_pi_fin_succAbove`**, **`Auto.fejerPi_succAbove_sublevel_le`**, **`Auto.multiAff`**, **`Auto.multiAffLead`**, **`Auto.multiAff_split`**, **`Auto.fejerPi_linear_sublevel_le'`**, `Auto.measurable_multiAff`, `Auto.measurable_multiAffLead`, `Auto.one_le_abs_intCast`, **`Auto.multiAff_eq_const`**, **`Auto.multiAff_sublevel_le_of_b_zero`**, **`Auto.multiAff_sublevel_le_of_quad`**, **`Auto.multiAff_sublevel_le`**, **`Auto.multilinear_support_cases`**, **`Auto.monTerm`**, `Auto.monTerm_zero`, `Auto.monTerm_single`, `Auto.monTerm_add`, **`Auto.monTerm_pair`**, **`Auto.aeval_eq_sum_monTerm`**, `Auto.support_single_add_single`, **`Auto.pair_exponent_inj`**, `Auto.affSupp`, `Auto.card_support_single`, `Auto.card_support_pair`, `Auto.singles_ne_pairs`, `Auto.zero_ne_single`, `Auto.zero_ne_pair`, **`Auto.sum_affSupp`**, `Auto.support_subset_affSupp`, **`Auto.aeval_eq_multiAff`** (the bridge, discharging the debt recorded 2026-09-17T15:25)
proved | 3 | `patch:uniformize`, mixed radii to one radius, positivity before comparison | **`Auto.fejer_le_scaled`**, **`Auto.fejerCube_le_scaled`**, **`Auto.fejerCubeMixed`**, `Auto.fejerCubeMixed_const`, `Auto.fejerCubeMixed_nonneg`, **`Auto.fejerCubeMixed_le_scaled`**, `Auto.continuous_fejerCubeMixed`, `Auto.integrable_fejerCubeMixed`, `Auto.integral_fejerCubeMixed`, **`Auto.fejerCubeMixed_cons`**, **`Auto.locUnifPowMixed`**, `Auto.locUnifPowMixed_const`, `Auto.pos_fin_cons`, `Auto.integrable_locUnifMixed_integrand`, **`Auto.locUnifPowMixed_swap`**, `Auto.integrable_split_integrand_mixed`, **`Auto.locUnifPowMixed_succ_eq`**, `Auto.integrable_fejerCubeMixed_innerFejer`, **`Auto.locUnifPowMixed_re_nonneg`**, **`Auto.integral_fejerCubeMixed_le_scaled`**, **`Auto.sq_norm_avg_le_enlarged`**, `Auto.re_locUnifPowMixed_eq`, `Auto.re_locUnifPow_succ_eq`, **`Auto.locUnifPowMixed_re_le_scaled`**, **`Auto.innerFejer_eq_sq`**, **`Auto.re_innerFejer_eq_sq`**, `Auto.norm_locUnifPowMixed_fdiff_le`, `Auto.measurable_locUnifPowMixed_fdiff_c`, `Auto.measurable_locUnifPowMixed_fdiff`, `Auto.integrable_fejer_locUnifPowMixed_fdiff`, **`Auto.re_locUnifPowMixed_succ_split`**, `Auto.eq_cons_cons`, `Auto.swap_comp_eq_cons_cons`, `Auto.cons_cons_swap_apply`, **`Auto.locUnifPowMixed_swap_cons`**, **`Auto.sq_re_locUnifPowMixed_le`**, **`Auto.sq_re_locUnifPowMixed_le_scaled`**
open | 3 | **`patch:highest-control`** (Proposition, line 739), highest-active-input control with measurable polynomial phases | --
open | 4 | `patch:u2-fourier-selection` (Lemma, line 785), one-dimensional `U^2` inverse estimate and measurable frequencies | --
open | 4 | `patch:dual-difference`, dual-difference interchange, explicit cylinder proof | --
open | 4 | `patch:missing-phase`, removal of missing-coordinate phases | --
open | 4 | `patch:dummy-phase`, a measurable dummy phase with a small exceptional set | --
open | 5 | **`patch:conditional-degree`**, conditional structured degree lowering | --
open | 6 | **`patch:major-arc`**, the real major-arc property | --
open | 6 | `patch:structured-degree` (Corollary, line 1182), unconditional degree lowering for structured adjoints | --
open | 7 | `patch:remove-high-inputs`, backward elimination of higher inputs | --
open | 7 | **`patch:lowest-energy`**, lowest-input positive Fourier energy | --
open | 8 | **`patch:energy-core`** (Theorem, line 1364), every-input positive energy, independently proved | --
open | 9 | `patch:monomial-energy`, independent monomial projected energy | --
partial | 9 | **`patch:energy-to-u2`**, low-frequency energy constructs the order-two cube | `Auto.integral_winAvg`, `Auto.winAvg_eq_zero_of_forall`, `Auto.winWidth`, `Auto.petBoxWin`, `Auto.measurableSet_petBoxWin`, **`Auto.volume_petBoxWin_le`**, **`Auto.winAvg_eq_zero_of_notMem_petBoxWin`**, `Auto.norm_winAvg_le`, `Auto.stronglyMeasurable_winAvg`, `Auto.integrable_norm_pow_winAvg`, **`Auto.sq_norm_pairAvg_le`**, `Auto.re_locUnifPow_zero_fdiff`, **`Auto.sq_re_locUnifPow_one_le`**, `Auto.winMult`, `Auto.norm_winMult_sub_one_le`, `Auto.half_le_norm_winMult`
open | 9 | **`lem:pet-reduction`** (new), every-input local uniformity for the monomial average, `s_* = 2` | --
open | 9 | **`thm:real-inverse`** (new), the specialized real inverse theorem, witness `h_j = f_j` | --

### Part VI -- row 5: `thm:kosz-613-internal`

status | source item | Lean name
--- | --- | ---
open | `lem:hb-decomposition`, Hahn-Banach separation | --
open | `lem:hb-decomposition`, the structured plus uniform decomposition | --
open | `prop:real-structural-decomposition`, the structural decomposition | --
partial | `lem:projection-off-diagonal`, the off-diagonal decay of the projection kernel | **`Auto.etaKer_decay`**, **`Auto.projKernel_decay`**, `Auto.etaKerMom`, `Auto.integrable_etaKer_mom`, `Auto.integral_projKernel_mom`, **`Auto.integral_projKernel_tail_le`**
open | `prop:compact-high-pass`, the compactly supported high-pass estimate | --
open | `prop:l2-decaying-point`, a decaying point on the `L^2` hyperplane | --
open | `lem:support-removal`, support removal | --
open | `lem:convex-exponent-completion`, convex completion of the exponent range | --
open | **`thm:kosz-613-internal`**, discharging `Auto.KoszAdjoint` | --

### Part VII -- row 6: normalized smoothing and the main theorem

status | source item | Lean name
--- | --- | ---
proved | `thm:kosz-adjoint` as an imported hypothesis | `Auto.KoszAdjoint`
proved | `thm:kosz-subunit` scale-one input as an imported hypothesis | `Auto.KoszSubunitScaleOne`
proved | `thm:kosz-subunit`, the blueprint's derivation from its scale-one input | `Auto.kosz_subunit`
proved | `lem:endpoint-geometry`, the interpolation geometry at the endpoint | `Auto.endpointTau`, `Auto.endpointTheta`, `Auto.endpointC`, `Auto.endpoint_geometry`
proved | the operator `Tproj` interpolated at the endpoint | `Auto.Tproj`, `Auto.Tproj_trilinear`
proved | the interpolation step packaged with the endpoint exponents | `Auto.endpoint_interpolate`
proved | `prop:normalized-endpoint`, normalized smoothing at `p = 1` | `Auto.normalized_endpoint`
proved | `prop:normalized-banach`, normalized smoothing for `p > 1` | `Auto.normalized_banach`
proved | `def:normalized-constants` and `cor:normalized-smoothing` | `Auto.normalized_smoothing`
proved | `prop:primitive-smoothing`, uniform smoothing for the primitives | `Auto.primitive_smoothing`
proved | `def:main-constants`, the final constants | inside `Auto.main_smoothing`
proved | **`thm:main`**, the requested smoothing theorem | `Auto.main_smoothing`

### Not formalized by design

status | source item | reason
--- | --- | ---
n/a | `prop:removed-material`, `prop:simplifications`, `prop:no-imported-analytic-declarations` | metatheoretic commentary on the blueprint, not mathematical content
n/a | `prop:acyclic-implementation-order` | the implementation order itself, realized by this ledger

## Task 2: `Auto.KoszAdjoint` from `blueprints/task_2_koszAdjoint_blueprint.tex`, in forward reasoning order

### Overview

status | source item | Lean name | timestamp
--- | --- | --- | ---
complete | `new:exact-lean-target`, `theorem koszAdjoint (j : Fin 3) : KoszAdjoint j` | `Auto.koszAdjoint` | 2026-09-25T20:31:04-04:00

### Reusable prerequisite: Plancherel for the integral Fourier transform on `L^1 ∩ L^2`

Justification: needed by `new:multiplier-facts`, `new:average-multiplier`, `patch:u2-fourier-selection`, `patch:lowest-energy` and `new:compact-highpass`; Mathlib has only the Schwartz and the abstract `L^2` versions, not the identification for integrable square-integrable functions; a named textbook theorem, stated on finite-dimensional real inner product spaces; file `DFR/Auto/IntegralPlancherel.lean`.

status | source item | Lean name | timestamp
--- | --- | --- | ---
complete | `new:integral-plancherel`, the multiplication formula `∫ (𝓕 g) f = ∫ g (𝓕 f)` for Schwartz `g` and integrable `f` | `Auto.integral_fourier_smul_eq_of_integrable` | 2026-09-25T07:00:11-04:00
complete | `new:integral-plancherel`, `𝓕 f` agrees a.e. with the `L^2` Fourier transform of `f ∈ L^1 ∩ L^2` | `Auto.fourierLp_ae_eq_fourier` | 2026-09-25T07:00:11-04:00
complete | `new:integral-plancherel`, `f̂ ∈ L^2` and `∫ |f̂|^2 = ∫ |f|^2` | `Auto.memLp_two_fourier`, `Auto.eLpNorm_two_fourier`, `Auto.integral_norm_sq_fourier` | 2026-09-25T07:00:11-04:00
complete | `new:integral-plancherel`, the pairing identity `∫ f conj g = ∫ f̂ conj ĝ` | `Auto.integral_conj_mul_fourier`, `Auto.integral_mul_conj_fourier` | 2026-09-25T07:00:11-04:00

### Section 1: conventions and budgets

status | source item | Lean name | timestamp
--- | --- | --- | ---
complete | `patch:budgets`, budget arithmetic, popularity, a heavy cell of a finite partition | `Auto.budLo`, `Auto.budHi`, `Auto.budLo_mul`, `Auto.budLo_pow`, `Auto.le_setIntegral_compl_add`, `Auto.measure_popular_ge`, `Auto.exists_cell_ge` | 2026-09-25T06:51:43-04:00

### Section 2: analytic facts

status | source item | Lean name | timestamp
--- | --- | --- | ---
complete | `new:integral-inequalities`, translation invariance of `‖·‖_p` | `Auto.eLpNorm_comp_add_right_of_aestronglyMeasurable` | 2026-09-25T07:11:15-04:00
complete | `new:integral-inequalities`, finite Hoelder `‖∏ f_i‖_p ≤ ∏ ‖f_i‖_{p_i}` | `Auto.eLpNorm_prod_le` | 2026-09-25T07:11:15-04:00
complete | `new:integral-inequalities`, Minkowski's integral inequality `‖∫ F(u,·) dν‖_p ≤ ∫ ‖F(u,·)‖_p dν` | `Auto.eLpNorm_lintegral_le`, `Auto.eLpNorm_integral_le_lintegral` | 2026-09-25T07:11:15-04:00
complete | `new:integral-inequalities`, the one-coordinate convolution bound `‖∫ a(u) f(· - u e_j) du‖_p ≤ ‖a‖_1 ‖f‖_p` | `Auto.eLpNorm_integral_smul_translate_le` | 2026-09-25T07:11:15-04:00
complete | `new:translation-continuity`, approximation of `f ∈ L^p` by bounded finite-valued box-supported functions | `Auto.exists_simpleFunc_isBounded_support_eLpNorm_sub_le` | 2026-09-25T07:15:15-04:00
complete | `new:translation-continuity`, `‖f(· - h) - f‖_p → 0` as `h → 0` | `Auto.tendsto_eLpNorm_comp_add_sub` | 2026-09-25T07:15:15-04:00
complete | `new:duality`, `|∫ F h| ≤ B ‖h‖_{p'}` for bounded compactly supported `h` implies `‖F‖_p ≤ B` | `Auto.eLpNorm_le_of_pairing_bound_of_measurable` | 2026-09-25T07:22:15-04:00
complete | `new:duality`, the same with finite-valued tests for locally integrable `F` | `Auto.eLpNorm_le_of_pairing_bound_simpleFunc` | 2026-09-25T07:22:15-04:00
complete | `new:measurability`, the unit phase `conj b / |b|` is measurable and `b · phase = |b|` | `Auto.unitPhase`, `Auto.norm_unitPhase_le`, `Auto.unitPhase_mul`, `Auto.measurable_unitPhase` | 2026-09-25T07:25:02-04:00
complete | `new:measurability`, a.e.-equal inputs give a.e.-equal averages | `Auto.ae_prod_comp_add_eq`, `Auto.ae_ae_comp_add_eq` | 2026-09-25T07:25:02-04:00
complete | `new:kernel-facts`, `k` real, even, Schwartz, `k̂ = η`, `∫ k = 1` | `Auto.etaKerS`, `Auto.fourier_etaKer`, `Auto.etaKer_even`, `Auto.etaKer_conj`, `Auto.integral_etaKer` | 2026-09-25T07:32:47-04:00
complete | `new:kernel-facts`, finiteness of `B_0 = ‖k‖_1`, `B_1 = ‖k'‖_1`, `B_M^tail` | `Auto.etaKerL1`, `Auto.etaKer_integrable`, `Auto.etaKerDerivL1`, `Auto.etaKerDeriv_integrable`, `Auto.etaKerMom`, `Auto.integrable_etaKer_mom` | 2026-09-25T07:32:47-04:00
complete | `new:kernel-facts`, `‖K_R‖_1 = B_0`, `‖K_R'‖_1 = R B_1`, the tail bound `B_M^tail (Ra)^{-M}` | `Auto.projKernel_L1`, `Auto.hasDerivAt_projKernel`, `Auto.integral_norm_deriv_projKernel`, `Auto.integral_projKernel_tail_le'` | 2026-09-25T07:32:47-04:00
complete | `new:kernel-facts`, `‖P_R f‖_∞ ≤ B_0` and the Lipschitz bound `R B_1 |v|` for `|f| ≤ 1` | `Auto.norm_P_le_of_norm_le_one`, `Auto.lintegral_projKernel_sub_le`, `Auto.norm_P_add_sub_le` | 2026-09-25T07:32:47-04:00
complete | `new:multiplier-facts`, the multiplier of `P_R^{(j)}` on `L^1 ∩ L^2` and the `L^2` contraction | `Auto.fourier_P_of_measurable`, `Auto.integrable_P_of_measurable`, `Auto.memLp_two_P`, `Auto.eLpNorm_two_P_le` | 2026-09-25T07:50:41-04:00
complete | `new:multiplier-facts`, self-adjointness and `⟨f, P_R f⟩ = ∫ η(ξ_j/R) |f̂|^2 ≥ 0` | `Auto.integral_P_mul_conj_eq`, `Auto.integral_mul_conj_P_eq`, `Auto.integral_eta_mul_norm_sq_nonneg` | 2026-09-25T07:54:03-04:00
complete | `new:multiplier-facts`, `P_L (I - P_R) f = 0` for `L ≤ R/2` | `Auto.eta_div_eq_one_of_eta_ne_zero`, `Auto.P_sub_P_ae_eq_zero` | 2026-09-25T07:54:03-04:00
complete | `new:multiplier-facts`, `⟨f, P_{L'} f⟩ ≥ ⟨f, P_L f⟩` for `L' ≥ 2L` | `Auto.eta_div_le_eta_div`, `Auto.integral_eta_mul_norm_sq_mono` | 2026-09-25T07:54:03-04:00
complete | `new:multiplier-facts`, slicing `⟨f, P_R f⟩ = ∫ ⟨f_v, P_R f_v⟩ dv` and sectional nonnegativity | `Auto.secSwap`, `Auto.measurePreserving_secSwap`, `Auto.integral_integral_sec`, `Auto.padSec`, `Auto.P_padSec`, `Auto.integral_mul_conj_P_slice`, `Auto.integral_padSec_energy_eq` | 2026-09-25T07:59:48-04:00
complete | `new:average-multiplier`, the multiplier of `T f = E_t b(t) f(· - v(t))` and its `L^2` identity | `Auto.avgTranslate`, `Auto.avgMultiplier`, `Auto.eLpNorm_avgTranslate_le`, `Auto.memLp_avgTranslate`, `Auto.fourier_avgTranslate`, `Auto.integral_norm_sq_avgTranslate` | 2026-09-25T08:03:39-04:00
complete | `new:three-lines`, `|F(θ)| ≤ M_0^{1-θ} M_1^θ` | `Auto.norm_le_three_lines` | 2026-09-25T08:05:27-04:00
complete | `new:interpolation`, the analytic family on simple functions and its boundary norms | `Auto.eIn`, `Auto.anFam_at'`, `Auto.eLpNorm_anFam_edge_le`, `Auto.anFamCoef`, `Auto.anFam_eq_sum`, `Auto.simpleOn_anFam` | 2026-09-25T08:14:07-04:00
complete | `new:interpolation`, the multilinear interpolation bound on a fixed support domain | `Auto.interpolate_of_analyticFamily_ext`, `Auto.trilin_anFam_expand`, `Auto.interpolate_trilin_simple` | 2026-09-25T08:14:07-04:00

### Section 3: the real improving estimate

status | source item | Lean name | timestamp
--- | --- | --- | ---
complete | `new:refinements`, nested refinements and pointwise incidence bounds | `Auto.refinement_stage`, `Auto.refinement_tower` | 2026-09-25T06:51:43-04:00
complete | `new:flows`, parameter towers, flow maps, `|det DΦ|`, two injective pieces | `Auto.measure_tower6_ge`, `Auto.det_flowDeriv`, `Auto.abs_det_flowDeriv`, `Auto.flowBlock3_pair` | 2026-09-25T06:51:43-04:00
complete | `new:incidence-consequence`, `|E_b| ≥ c_* (α_0 α_1 α_2 α_3)^10` and the incidence bound | `Auto.lintegral_abs_det_fderiv_le_card_mul_image`, `Auto.exists_separated_lintegral_ge` | 2026-09-25T06:51:43-04:00
complete | `new:restricted-neighborhood`, restricted bounds at `v` and at the corners `β + ε σ` | `Auto.incid_lifted`, `Auto.restrictedStrong_of_chain` | 2026-09-25T06:51:43-04:00
complete | `new:restricted-strong`, the strong form bound | `Auto.strong_real_improving` | 2026-09-25T06:51:43-04:00
complete | `new:improving`, `‖A_N f‖_{6/5} ≤ C N^{-1/20} ‖f_j‖_2 ‖f_b‖_{40/7} ‖f_c‖_6` for measurable inputs | `Auto.strong_real_improving'` | 2026-09-25T06:51:43-04:00
complete | `new:improving`, the adjoint identity | `Auto.adjoint_identity` | 2026-09-25T06:51:43-04:00
complete | `new:improving`, `‖A_N^{*j} g‖_2 ≤ C N^{-1/20} ‖g_0‖_6 ‖g_b‖_{40/7} ‖g_c‖_6` for `Nice` inputs | `Auto.kosz53_internal` | 2026-09-25T06:51:43-04:00
complete | `new:improving`, the adjoint estimate for all finite-norm inputs, the concrete integral a.e. | `Auto.adjoint_identity_of_integrable`, `Auto.lintegral_prodShift_mul_le`, `Auto.measurable_Astar`, `Auto.kosz53_of_memLp` | 2026-09-25T08:23:20-04:00

### Section 4: the real inverse theorem

status | source item | Lean name | timestamp
--- | --- | --- | ---
complete | `def:local-uniformity`, Fejer densities `κ_H` | `Auto.fejer`, `Auto.fejer_nonneg`, `Auto.fejerMeasure` | 2026-09-25T06:51:43-04:00
complete | `patch:cube-succ`, `C_{s+1} = C_s · conj(C_s(· + h e_j))` | `Auto.cubeSel_snoc`, `Auto.locUnifPow_succ_split` | 2026-09-25T06:51:43-04:00
complete | `patch:fejer-squares`, Fejer square identity, positivity, `0 ≤ Q ≤ 1` | `Auto.integral_fejer_pairAvg_eq_sq`, `Auto.locUnifPow_re_nonneg` | 2026-09-25T06:51:43-04:00
complete | `patch:raise-order`, `Q_s^2 ≤ (1 + H/S) Q_{s+1}` | `Auto.locUnifPow_one_eq`, `Auto.locUnifPow_two_eq` | 2026-09-25T06:51:43-04:00
complete | `lem:fejer-vdc` | `Auto.fejer_vdc'` | 2026-09-25T06:51:43-04:00
complete | `patch:signed-vdc-eq`, signed integrated removal | `Auto.sq_norm_normalized_pairing_le`, `Auto.sq_norm_signed_vdc` | 2026-09-25T06:51:43-04:00
complete | `patch:cylinder`, cylinder Cauchy-Schwarz with its state | `Auto.cubeSel`, `Auto.sq_norm_pow_le_integral_cubeProdSel_prod`, `Auto.integral_cubeProdSel_re_nonneg` | 2026-09-25T06:51:43-04:00
complete | `lem:real-polynomial-oscillation` | `Auto.real_polynomial_oscillation` | 2026-09-25T06:51:43-04:00
complete | `patch:triangular` | `Auto.sum_le_of_oscillation_ge` | 2026-09-25T06:51:43-04:00
complete | `patch:lead-invariant`, `patch:initial-shift-family` | `Auto.petUpdate_invariant_head`, `Auto.petUpdate_invariant_diff` | 2026-09-25T06:51:43-04:00
complete | `patch:pet-update` | `Auto.petUpdate_protected_of_invariant`, `Auto.petNewHeadFactor_origin` | 2026-09-25T06:51:43-04:00
complete | `patch:pet-producer`, the pivot rule, `w' < w`, length at most `2L` | `Auto.petType_lt_of_pivot`, `Auto.petStateClasses_update_at_pivot`, `Auto.exists_petPivot`, `Auto.PetRunInv`, `Auto.petRunStep` | 2026-09-25T09:06:16-04:00
complete | `patch:pet-producer`, the uniform iteration bound `B(w, L)` | `Auto.petRun_bounded` | 2026-09-25T06:51:43-04:00
complete | `patch:pet-analytic-step` | `Auto.sq_norm_signed_vdc_bdd`, `Auto.vecProd`, `Auto.vecChildren`, `Auto.corrLine_vecProd`, `Auto.vecStep` | 2026-09-25T08:44:22-04:00
complete | `patch:pet-producer`, full coefficient and translation bounds along the run | `Auto.EvalBd`, `Auto.PetRunBd`, `Auto.petRunBd_step`, `Auto.petRunSeq`, `Auto.petRun_terminates` | 2026-09-25T09:19:09-04:00
complete | `patch:affine-block`, `patch:affine-cube-invariant`, `patch:affine-terminal` | `Auto.cs_remove_slope_block`, `Auto.headBlock_eq_fdiffIter` | 2026-09-25T06:51:43-04:00
complete | `patch:cs-loss` | `Auto.csPhi_iter_eq`, `Auto.csLoss` | 2026-09-25T06:51:43-04:00
complete | `patch:multiaffine-sublevel`, `Pr{|p(u)| ≤ ε} ≤ 4 √ε` | `Auto.fejerMeasure_abs_affine_le` | 2026-09-25T06:51:43-04:00
complete | sublevel exclusion after `patch:multiaffine-sublevel`: old shifts off the bad union with raw cube `≥ κ/2` | `Auto.exists_notMem_ge_of_mean` | 2026-09-25T08:25:13-04:00
complete | `patch:pet-physical-radii`, the change of variables `z_i = a p_i(h) u_i` and the radii bounds | `Auto.aeval_smul_of_isHomogeneous`, `Auto.petPhysicalRadius_bounds` | 2026-09-25T08:31:26-04:00
complete | `patch:uniformize` | `Auto.fejerCubeMixed_le_scaled`, `Auto.sq_re_gapScaled_le_locUnifPow` | 2026-09-25T06:51:43-04:00
complete | the four phase steps: four differences annihilate a cubic phase | `Auto.pdiffIter_four_eq_zero` | 2026-09-25T06:51:43-04:00
complete | `patch:cs-loss` along a chain of levels: Jensen, averaging over the fresh shift, and the power bound | `Auto.fejerMean`, `Auto.fejerMean_sq_le`, `Auto.fejerChain`, `Auto.fejerChain_box`, `Auto.vecAmp`, `Auto.integral_children_eq_vecAmp`, `Auto.vecAmp_step`, `Auto.norm_vecAmp_le_one`, `Auto.measurable_vecAmp_param` | 2026-09-25T09:43:50-04:00
complete | the four phase steps before `patch:highest-control` as levels `0` to `4` of the chain | `Auto.phaseHead`, `Auto.phaseLevel`, `Auto.vecProd_phaseHead_mul`, `Auto.measurable_phaseLevel`, `Auto.phaseLevel_step`, `Auto.phaseLevel_zero`, `Auto.phaseProdIter_four_eq` | 2026-09-25T09:43:50-04:00
complete | the degree-one branch before `patch:highest-control` | `Auto.phaseLevel_step_re`, `Auto.phaseProdIter_four_linear`, `Auto.phaseLevel_four_linear`, `Auto.fejer_mean_cube_eq`, `Auto.sq_fejer_mean_cube_le`, `Auto.d1_chain`, `Auto.highestControl_one` | 2026-09-25T12:39:30-04:00
complete | `patch:pet-analytic-step` along the run: evaluation of a symbolic state at numeric shifts and the children identity | `Auto.petEvalPoly`, `Auto.petFacFun`, `Auto.petBlockFun`, `Auto.petEvalFam`, `Auto.prod_group_eq`, `Auto.vecProd_petGroup`, `Auto.vecProd_vecChildren_petEvalFam`, `Auto.vecProd_vecChildren_update` | 2026-09-25T09:52:08-04:00
complete | `patch:pet-producer`, Lean state: translation records use only the shift variables already introduced, along the run | `Auto.PetFacBelow`, `Auto.PetFacsBelow`, `Auto.petNormalized_facBelow`, `Auto.petFacsBelow_update`, `Auto.PetRunInv.itemsBelow`, `Auto.petRunSeq_facsBelow` | 2026-09-25T09:54:42-04:00
complete | "Full coefficient and translation bounds": the support envelope of the evaluated shifts along the run | `Auto.PetEnv`, `Auto.PetEnv.normalize`, `Auto.PetStateEnv`, `Auto.petStateEnv_update`, `Auto.petRunSeq_env` | 2026-09-25T09:59:45-04:00
complete | `patch:pet-analytic-step` along the run: the step between consecutive PET levels with the translated enlarged box | `Auto.translBox_facts`, `Auto.petSpatialFun`, `Auto.petLevel`, `Auto.measurable_petLevel`, `Auto.petLevel_norm_le_one`, `Auto.petLevel_step`, `Auto.petEvalFam_eq_of_below`, `Auto.measurable_vecProd_petEvalFam`, `Auto.mem_petBox_of_add_mem` | 2026-09-25T10:07:42-04:00
complete | `patch:initial-shift-family`, the family after the four phase steps as a normal state with the run invariant | `Auto.vecLift`, `Auto.initPoly`, `Auto.sub_initPoly_same`, `Auto.vShiftZ`, `Auto.petShiftVec`, `Auto.petShiftVec_cons`, `Auto.initItem_lead`, `Auto.initState`, `Auto.initState_inv`, `Auto.initState_bd`, `Auto.initState_facsBelow`, `Auto.initState_env`, `Auto.vecProd_initState`, `Auto.phaseLevel_four_eq_petLevel` | 2026-09-25T10:24:40-04:00
complete | `patch:cs-loss` along the run: the PET levels from `4` to the linear state | `Auto.petRun_level_step` | 2026-09-25T10:27:27-04:00
complete | `patch:pet-producer`, Lean state: every block of the run is nonempty, so every nuisance block has bounded support | `Auto.PetBlocksNonempty`, `Auto.petGroup_nonempty`, `Auto.petBlocksNonempty_update`, `Auto.petRunSeq_nonempty`, `Auto.initState_nonempty`, `Auto.petBlockFun_eq_zero_of_notMem` | 2026-09-25T10:29:30-04:00
complete | `patch:affine-block`, `patch:affine-cube-invariant`: the affine removal steps as levels of the chain | `Auto.vecAmp_step_re`, `Auto.affG`, `Auto.affFam`, `Auto.affAmp`, `Auto.affG_succ`, `Auto.affChildren_eq`, `Auto.AffData`, `Auto.affAmp_step`, `Auto.affAmp_step_re`, `Auto.measurable_affAmp` | 2026-09-25T10:40:26-04:00
complete | `patch:affine-terminal`: the last affine level is the raw cube of the protected input | `Auto.affAmp_terminal` | 2026-09-25T10:40:26-04:00
complete | `patch:affine-terminal` at the linear state: slopes along `e_m`, gaps `a p_i(h)` | `Auto.petEvalPoly_linear`, `Auto.linState_facts`, `Auto.linState_gap`, `Auto.linState_headSlope`, `Auto.linBlocks`, `Auto.linSlopes`, `Auto.linBlocks_affData`, `Auto.petLevel_eq_affAmp_zero` | 2026-09-25T10:44:54-04:00
complete | `patch:pet-producer`, "take the finite maximum of `B(w, L_0)`": a run bound uniform over all initial types of bounded length | `Auto.petRun_terminates_uniform` | 2026-09-25T10:50:03-04:00
complete | `patch:highest-control`, proof: the whole chain of levels (four phase steps, the PET run, the affine removal) and `patch:cs-loss` along it | `Auto.hcLevel`, `Auto.measurable_hcLevel`, `Auto.hcLevel_bounds`, `Auto.hcSeq`, `Auto.hcLevel_step`, `Auto.hc_chain`, `Auto.measurable_affAmp_param`, `Auto.affAmp_congr`, `Auto.hcW`, `Auto.hcOld` | 2026-09-25T11:06:19-04:00
complete | `patch:highest-control`, proof: the terminal mean as the averaged raw cube of the protected input at the gaps `a p_i(h)` | `Auto.fdiffIter_translate`, `Auto.fdiffIter_conj`, `Auto.re_integral_fdiffIter_condConj`, `Auto.hcGap`, `Auto.hcLevel_terminal`, `Auto.fejer_inner_eq`, `Auto.integral_split_fejer`, `Auto.hcTerm`, `Auto.hc_terminal_mean` | 2026-09-25T11:13:47-04:00
complete | `patch:highest-control`, proof: the sublevel exclusion at the old shifts and `patch:pet-physical-radii` | `Auto.pi_fejerMeasure_eq`, `Auto.mvPoly_sublevel_le`, `Auto.integral_prod_fejer_indicator_scale`, `Auto.integral_bad_le`, `Auto.exists_good_old`, `Auto.exists_reverse_poly`, `Auto.linState_gap_witness`, `Auto.hc_good_old` | 2026-09-25T11:27:45-04:00
complete | `patch:highest-control`, proof: sign symmetry of the Fejer density, the change of variables to the radii `|a p_i(h)| H`, `patch:uniformize` and padding | `Auto.signFlip`, `Auto.integral_fejer_signFlip`, `Auto.fejer_mean_hcTerm_eq`, `Auto.sq_fejer_mean_hcTerm_le`, `Auto.locUnifPow_pad` | 2026-09-25T11:44:15-04:00
complete | `patch:highest-control`, proof: the choice of `H/N`, the lower bound `κ` from the loss lemma, and the output budgets | `Auto.hc_core`, `Auto.chain_mean_lower`, `Auto.MonoLow`, `Auto.MonoHigh`, `Auto.hcPhi`, `Auto.monoLow_hcPhi`, `Auto.locUnifPow_pad`, `Auto.exists_budLo_le`, `Auto.hcSeq_length` | 2026-09-25T12:21:04-04:00
complete | `patch:highest-control` for continuous compactly supported inputs | `Auto.highestControl_ge2`, `Auto.highestControl_one`, `Auto.highestControl_nice` | 2026-09-25T12:39:30-04:00
complete | `patch:conventions` (Borel representatives), `patch:highest-control` for Borel inputs | `Auto.measurable_phaseProd`, `Auto.AdmissiblePoly.mono`, `Auto.norm_phaseCorr_update_sub_le`, `Auto.abs_re_locUnifPow_sub_le`, `Auto.diskClamp`, `Auto.exists_boxCutoff`, `Auto.exists_nice_approx`, `Auto.highestControl` | 2026-09-25T12:58:11-04:00
complete | `patch:u2-fourier-selection`, `Q_{2,H,S}(f) ≤ H^{-2} ‖f̂‖_∞^2` | `Auto.unifMeas`, `Auto.avgH`, `Auto.fourier_avgH`, `Auto.lintegral_enorm_avgMult_sq`, `Auto.corrFT`, `Auto.fourier_corrFT`, `Auto.lintegral_corrFT_sq_le`, `Auto.lintegral_pair_avgH_le`, `Auto.unifPow1`, `Auto.integral_cube_two_eq`, `Auto.unifPow1_two_le` | 2026-09-25T13:25:46-04:00
complete | `patch:u2-fourier-selection`, measurable least-rational frequency selection | `Auto.exists_measurable_freq`, `Auto.measurable_fourier_param`, `Auto.exists_measurable_freq_unifPow1` | 2026-09-25T13:25:46-04:00
complete | `patch:dual-diff-bound` | `Auto.unifIcc`, `Auto.ephase`, `Auto.vkey`, `Auto.prod_vertices_split`, `Auto.ddVert`, `Auto.ddHead`, `Auto.ddNuis`, `Auto.cubeBoxSet`, `Auto.altPhase`, `Auto.cubeProdSel_ddHead`, `Auto.integral_prod_ddVert`, `Auto.integral_ddHead_nuis`, `Auto.integral_cube_ddHead`, `Auto.dual_diff_bound` | 2026-09-25T13:41:22-04:00
complete | `patch:missing-phase-bound` | `Auto.integral_avgH`, `Auto.sq_norm_integral_le_avgH`, `Auto.altPhase_eq_zero_of_indep`, `Auto.cubeProdSel_snoc_shift`, `Auto.unifPow1_succ_eq`, `Auto.missing_phase_bound` | 2026-09-25T13:54:33-04:00
complete | `patch:dummy-phase` | `Auto.sum_neg_one_pow_prod_cubeSel`, `Auto.unif_prod_abs_sub_le`, `Auto.measurePreserving_coord_pair`, `Auto.exists_dummy_phase` | 2026-09-25T13:58:36-04:00
complete | `patch:ma-correlation`, `patch:ma-set`, the property `MA(m, l)` | `Auto.maPhase`, `Auto.maSize`, `Auto.maSet`, `Auto.MajorArcProperty`, `Auto.maPhase_natDegree_le`, `Auto.measurable_maPhase_coeff` | 2026-09-25T14:01:37-04:00
complete | `patch:conditional-degree`, step 1, Fourier coefficients on popular sections | `Auto.unifPow1_add_two`, `Auto.unifPow1_mem_Icc`, `Auto.measurable_unifPow1_param`, `Auto.exists_measurable_freq_unifPow1'`, `Auto.cdl_step1` | 2026-09-25T14:40:48-04:00
complete | `patch:conditional-degree`, step 2, dual-difference interchange | `Auto.cdlCoef`, `Auto.cdlBox`, `Auto.cdlPsi`, `Auto.cdlG`, `Auto.cdlL`, `Auto.cdl_step2`, `Auto.measure_prod_popular_ge` | 2026-09-25T14:40:48-04:00
complete | `patch:conditional-degree`, step 3, interchange of section and cube parameters | `Auto.measure_popular_sections_right`, `Auto.measure_popular_sections_left`, `Auto.cdl_abstract` | 2026-09-25T14:40:48-04:00
complete | `patch:conditional-degree`, step 4, extension by a dummy phase | `Auto.exists_dummy_phase`, `Auto.cdl_abstract` | 2026-09-25T14:40:48-04:00
complete | `patch:conditional-degree`, step 5, application of `MA(m, l)` | `Auto.cube_cdlPhi`, `Auto.cdl_step5_identity`, `Auto.integral_embT`, `Auto.lintegral_embT`, `Auto.transMeas`, `Auto.MAAt`, `Auto.cdl_step5` | 2026-09-25T15:28:10-04:00
complete | `patch:conditional-degree`, step 6, recovery of the original cube phase | `Auto.measure_prod_ge_of_sections`, `Auto.ae_pi3_unifMeas_mem`, `Auto.cdl_abstract` | 2026-09-25T14:40:48-04:00
complete | `patch:conditional-degree`, step 7, quantization and partition of the nonzero vertices | `Auto.exists_heavy_cell`, `Auto.exists_section_last`, `Auto.cdlAlpha`, `Auto.cdlAlpha_sum`, `Auto.sum_vertices_split` | 2026-09-25T14:40:48-04:00
complete | `patch:conditional-degree`, step 8, phase removal and integration | `Auto.norm_ephase_sub_le`, `Auto.norm_cdlCoef_sub_le`, `Auto.cdl_step8`, `Auto.cdlOut`, `Auto.cdl_abstract`, `Auto.cdlOut_ge`, `Auto.monoLow_cdlOutLow`, `Auto.conditionalDegreeLowering` | 2026-09-25T15:39:57-04:00
complete | `patch:major-arc`, base case `m = 1` | `Auto.MonoHigh.exists_budHi`, `Auto.maCoef`, `Auto.maPhase_one_eq`, `Auto.maSize_one_eq`, `Auto.majorArc_base` | 2026-09-25T15:47:52-04:00
complete | `patch:ma-adjoint`, the exact adjoint of the last active input | `Auto.maAdj`, `Auto.conj_maAdj`, `Auto.phaseCorr_eq_inner_maAdj`, `Auto.measurable_cdlF`, `Auto.cdlF_eq_zero_of_box`, `Auto.ma_adjoint` | 2026-09-25T15:55:32-04:00
complete | `patch:major-arc`, uniformity and degree lowering using `MA(m, l)` | `Auto.conditionalDegreeLowering'`, `Auto.unifPow1_zero_eq`, `Auto.sq_unifPow1_zero_le`, `Auto.sq_integral_raise`, `Auto.cdl_iterate`, `Auto.sq_integral_sections_raise`, `Auto.ma_uniformity` | 2026-09-25T16:34:29-04:00
complete | `patch:ma-smaller-pattern`, Fourier selection and the smaller pattern | `Auto.projT_add_smul`, `Auto.projT_sub_smul`, `Auto.maAdj_update`, `Auto.spIn`, `Auto.spFreq`, `Auto.maPhase_spFreq_eval`, `Auto.phaseCorr_update_eq_sp`, `Auto.norm_sections_eq_sp`, `Auto.mem_of_embT_ne_zero`, `Auto.unitScalar`, `Auto.ma_smaller_pattern` | 2026-09-25T16:46:47-04:00
complete | `patch:major-arc`, the induction step and the theorem | `Auto.maSize_succ_le_spFreq`, `Auto.maSet_sp_subset`, `Auto.majorArc_step`, `Auto.majorArc` | 2026-09-25T16:49:32-04:00
complete | `patch:structured-degree` | `Auto.structuredDegree`, `Auto.structured_uniformity` | 2026-09-25T16:52:14-04:00
complete | `patch:high-section-coeff`, measurable section frequencies | `Auto.exists_section_freq` | 2026-09-25T17:00:13-04:00
complete | `patch:remove-high-inputs`, small frequencies via `MA(l, l)` and the dummy value | `Auto.volume_cyl`, `Auto.maSize_self_eq`, `Auto.removeHigh_small` | 2026-09-25T17:00:13-04:00
complete | `patch:remove-high-inputs`, the constant frequency and the backward step | `Auto.maPhase_spFreq_const`, `Auto.spIn_eq_update`, `Auto.removeHigh_step`, `Auto.removeHighInputs` | 2026-09-25T17:06:10-04:00
complete | `patch:lowest-energy` | `Auto.phaseCorr_one_eq_avg`, `Auto.avgMultiplier_one_eq`, `Auto.maPhase_two_one_eval`, `Auto.maPhase_one_one_eval`, `Auto.lowestEnergy` | 2026-09-25T17:15:38-04:00
complete | `patch:energy-core`, step 1, replacing the first input and smoothing its adjoint | `Auto.phaseCorr_comp_perm`, `Auto.rot`, `Auto.phaseCorr_rot`, `Auto.update_comp_rot`, `Auto.maPhase_empty`, `Auto.integrable_memLp_of_box`, `Auto.energyCore_step1` | 2026-09-25T17:24:06-04:00
complete | `patch:energy-core`, step 2, freezing on one of `K` intervals | `Auto.abs_eval_sub_le_of_admissible`, `Auto.sub_eval_smul_mem_petBox`, `Auto.measurable_intervalIntegral_param`, `Auto.intervalIntegrable_of_norm_le_one`, `Auto.energyCore_freeze` | 2026-09-25T17:35:14-04:00
complete | `patch:frozen-correlation`, step 3, the lower-dimensional polynomial family | `Auto.frozenPoly`, `Auto.frozenPoly_eval`, `Auto.frozenIn`, `Auto.phaseCorr_frozen`, `Auto.abs_coeff_le_of_admissible`, `Auto.abs_coeff_taylor_le`, `Auto.add_eval_smul_mem_petBox`, `Auto.petBox_subset_scale`, `Auto.phaseCorr_congr_inputs`, `Auto.frozenCut`, `Auto.phaseCorr_frozenCut`, `Auto.energyCore_frozen` | 2026-09-25T17:40:03-04:00
complete | `patch:energy-core`, step 4, a measurable set of large sections | `Auto.energyCore` | 2026-09-25T17:45:51-04:00
complete | `patch:all-energy`, step 5, induction hypothesis and integration of energies | `Auto.norm_fourier_comp_sub`, `Auto.energy_raise`, `Auto.frozenCut_pred`, `Auto.energyCore` | 2026-09-25T17:45:51-04:00

### Sections 5-6: the adjoint estimate and the exact proposition

status | source item | Lean name | timestamp
--- | --- | --- | ---
complete | `new:monomial-inverse`, witness `h_j = f_j` | `Auto.monoDir`, `Auto.monoPoly`, `Auto.monoIn`, `Auto.Lambda_eq_phaseCorr`, `Auto.admissible_monoPoly`, `Auto.monomialInverse` | 2026-09-25T17:49:47-04:00
complete | `new:adjoint-basic`, support and `|G| ≤ 1` | `Auto.measurable_adjShift`, `Auto.Astar_basic` | 2026-09-25T17:55:25-04:00
complete | `new:adjoint-basic`, the crude `L^r` bounds for `G` and `(I - P_R) G` | `Auto.adjShift_eq_prod`, `Auto.eLpNorm_Astar_le`, `Auto.eLpNorm_projKernel`, `Auto.eLpNorm_P_le_of_measurable`, `Auto.eLpNorm_sub_P_le`, `Auto.eLpNorm_Astar_sub_P_le` | 2026-09-25T17:55:25-04:00
complete | `new:compact-highpass`, `⟨h, G⟩ ≥ M^{-1} ‖H‖_2^2` | `Auto.norm_sub_sq_eq`, `Auto.highpass_energy` | 2026-09-25T18:02:45-04:00
complete | `new:compact-highpass`, the tail bound for `1_{(B')^c} H` | `Auto.highpass_tail` | 2026-09-25T18:02:45-04:00
complete | `new:compact-highpass`, the contradiction and the bound `C_1 μ^a N^3` | `Auto.integrable_fourier_integrand`, `Auto.fourier_sub_of_integrable`, `Auto.fourier_const_mul`, `Auto.integral_sq_le_of_eLpNorm_le`, `Auto.rpow_inv_two_mul_pow`, `Auto.integral_sq_le_box`, `Auto.compactHighpass` | 2026-09-25T18:15:23-04:00
complete | `new:compact-decaying-point`, interpolation with weight `60/61` on bounded finite-valued inputs | `Auto.adjVec`, `Auto.adjT`, `Auto.adjIn`, `Auto.Astar_adjIn`, `Auto.trilin_adjT`, `Auto.P_linear`, `Auto.hpAdj`, `Auto.trilin_hpAdj`, `Auto.hpAdj_ae_congr`, `Auto.integral_sq_sub_P_le`, `Auto.hpAdj_improving`, `Auto.hpAdj_bounded`, `Auto.cdpExp`, `Auto.compactDecaying` | 2026-09-25T18:43:04-04:00
complete | `new:compact-decaying-point`, extension to all finite-norm inputs | `Auto.qz`, `Auto.norm_hpAdj_sub_le`, `Auto.allExponentsBdd`, `Auto.truncIn`, `Auto.allExponentsCont` | 2026-09-25T20:20:43-04:00
complete | `new:global-decaying-point`, the exact input-cube decomposition | `Auto.boxIdx`, `Auto.boxRes`, `Auto.boxIdx_add_smul`, `Auto.offV`, `Auto.piece`, `Auto.prod_decomp`, `Auto.adjT_decomp`, `Auto.P_finset_sum`, `Auto.hpAdj_decomp`, `Auto.cornerVec`, `Auto.hpAdj_translate`, `Auto.simpleOn_piece_translate`, `Auto.piece_bound` | 2026-09-25T19:05:16-04:00
complete | `new:global-decaying-point`, the off-diagonal tail `B_2^tail μ^4 (|l| - 2)^{-2}` | `Auto.tailKer`, `Auto.integral_tailKer_le`, `Auto.cubeDist`, `Auto.far_u_bound`, `Auto.weighted_tail` | 2026-09-25T19:17:42-04:00
complete | `new:global-decaying-point`, discrete Young and Hoelder, the global bound | `Auto.sum_inv_one_add_sq_int_le`, `Auto.sq_norm_sum_le_weighted`, `Auto.sum_mul3_le_holder`, `Auto.sum_integral_boxRes_le`, `Auto.adjT_piece_support`, `Auto.hpAdj_piece_passive`, `Auto.offset_bound`, `Auto.eLpNorm_adjT_le`, `Auto.holder_cubes`, `Auto.coverSet`, `Auto.globalDecaying` | 2026-09-25T19:54:32-04:00
complete | `new:adjoint-all-exponents`, the convex completion exponents `τ`, `v_i` | `Auto.slotExp`, `Auto.eLpNorm_hpAdj_crude`, `Auto.allExponentsSimple` | 2026-09-25T20:01:20-04:00
complete | `new:adjoint-all-exponents`, interpolation and extension to full `L^p` | `Auto.allExponentsBdd`, `Auto.eLpNorm_adjT_crude`, `Auto.norm_adjT_le_adjT_norm`, `Auto.ae_lt_top_of_eLpNorm`, `Auto.adjT_truncIn_eventually`, `Auto.allExponentsCont` | 2026-09-25T20:20:43-04:00
complete | `new:exact-lean-target`, zero, infinite and finite-norm cases, `KoszAdjoint j` | `Auto.Astar_congr`, `Auto.koszSlots`, `Auto.Astar_eq_adjT`, `Auto.sum_three_eq`, `Auto.prod_erase_eq`, `Auto.eq_zero_of_eLpNorm_eq_zero`, `Auto.koszAdjoint` | 2026-09-25T20:31:04-04:00
complete | `thm:main` in the original formulation, with `KoszAdjoint` and `KoszSubunitScaleOne` discharged | `Auto.mainTheorem` | 2026-09-25T20:31:04-04:00
