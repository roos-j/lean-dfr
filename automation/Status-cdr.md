# CDR status: Theorems 1-4 of arXiv:2008.10140v2 (`cdr.tex`)

## Main theorem overview

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | Theorem 1 `thm:singint`, lines 216-224 | `Auto.CDR.thm_singint`: `‖pvT f₁ f₂‖_r ≤ C ‖f₁‖_p ‖f₂‖_q` for test functions, `p,q ∈ (1,∞)`, `r ∈ [1,2)`, `1/p+1/q = 1/r`; `DFR/Auto/CDR/Sec2PreliminaryReductions1Decomposition.lean`; axioms propext, Classical.choice, Quot.sound | 2026-10-01T16:40:00-04:00
complete | Theorem 2 `thm:anisotp`, lines 266-283 | `Auto.CDR.thm_anisotp`: `T_m` (Fourier form, `IsAnisoSymbol α β N₁ C₀ m`) `L^p × L^q → L^r`, `p,q ∈ (1,∞)`, `r ∈ (1/2,2)`, constant depending on `m` only through `C₀`; `DFR/Auto/CDR/Sec4SmoothCase.lean`; axioms propext, Classical.choice, Quot.sound | 2026-10-01T15:30:00-04:00
complete | Theorem 3 `thm:maxfct`, lines 297-306 | `M(f_1,f_2) = sup_{r>0} (2r)^{-1} ∫_{-r}^r |f_1(x+t,y) f_2(x,y+t^2)| dt`: `L^p × L^q → L^r`, `p,q ∈ (1,∞)`, `r ∈ [1,∞)` (`Auto.CDR.thm_maxfct`) | 2026-10-01T10:29:38-04:00
complete | Theorem 4 `thm:patterns`, lines 311-318 | `E ⊆ [0,1]^2` measurable, `|E| ≥ ε ∈ (0,1/2)`: `(x,y),(x+t,y),(x,y+t^2) ∈ E` with `t > exp(-exp(ε^{-C}))` | 2026-10-01T08:39:35-04:00

## Reusable prerequisite: `DFR/Auto/ShiftedMaximalFunction.lean`

2026-10-01T08:55:00-04:00 - Need: the bound `‖𝓜_σ g‖_p ≲ log(2+|σ|)^{1/p} ‖g‖_p` (`eqn:shiftedmaxfct-basic`, cited from Stein 1993, p. 78) for the polylogarithmic loss in Theorems 1 and 3. Missing: Mathlib and lean-spherical have the centered Hardy-Littlewood maximal theorem but no shifted maximal function. Substance: a named textbook theorem (Stein, Harmonic Analysis, Ch. II §5.10; Muscalu-Schlag Vol. I), proved by a Vitali covering argument and Marcinkiewicz interpolation. Generality: arbitrary real shift `σ`, bounded measurable `g : ℝ → ℂ`, all `p > 1`, stated with Mathlib notions only. File: `DFR/Auto/ShiftedMaximalFunction.lean`, namespace `Auto`.

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | `eqn:shiftedmaxfct-basic` (Stein 1993, p. 78) | weak type `(1,1)` of `𝓜_σ` with constant `≲ log(2+|σ|)` (Vitali covering) | 2026-10-01T09:02:45-04:00
complete | `eqn:shiftedmaxfct-basic` (Stein 1993, p. 78) | `‖𝓜_σ g‖_p^p ≲ log(2+|σ|) ‖g‖_p^p`, `1 < p < ∞` (Marcinkiewicz) | 2026-10-01T09:02:45-04:00

## Generalized prerequisite: `DFR/Auto/BilinearInterpolation.lean`

2026-10-01T10:06:34-04:00 - Need: interpolation of the bounds `L^2 × L^2 → L^1` (decay `2^{-δ|k|}`) and
`L^{p_1} × L^{q_1} → L^{r_1}` (polynomial loss) for the pieces `M^{(k)}` (§2.6, lines 689-692) and
later `T^{(k)}` (§2.3, line 549). Missing: Mathlib has no bilinear Riesz-Thorin theorem; the existing
file proved only the special case used by `Smoothing2D` (fixed second exponent). Substance: the
bilinear Riesz-Thorin interpolation theorem (complex interpolation of bilinear operators, a standard
textbook theorem proved by Stein's three-lines argument). Generality: complex simple functions on arbitrary measure spaces, all six
exponents `≥ 1`, `θ ∈ (0,1)`, `q ≠ ∞`. File: `DFR/Auto/BilinearInterpolation.lean`, extended by
appending `Auto.bilinear_interpolation` (existing declarations unchanged; `Smoothing2D` rebuilt).

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | bilinear Riesz-Thorin theorem | Stein's three-lines argument with the deformed second input and the normalization `‖g‖_q ≤ 1` (`bilinear_interpolation`) | 2026-10-01T10:06:34-04:00

## Reusable prerequisite: `DFR/Auto/BilinearMarcinkiewicz.lean`

2026-10-01T10:55:00-04:00 - Need: strong `L^p × L^q → L^r` bounds, `1/2 < r < 2`, from weak-type bounds
on an open set of exponents (§4.5, "Multilinear interpolation (see for instance [MS13])", the step
to `fwrange-1`). Missing: Mathlib has no real (Marcinkiewicz) interpolation for bilinear operators;
`Auto.Twisted.FourVertexMarcinkiewicz` is trilinear with Banach target `R > 1` and does not reach
`r < 1`. Substance: the multilinear Marcinkiewicz interpolation theorem (a standard textbook theorem).
Generality: bilinear maps on simple functions of finite measure support on arbitrary measure spaces,
weak bounds at the four corners `(1/p ± δ, 1/q ± δ)`, any target `r > 0`. File:
`DFR/Auto/BilinearMarcinkiewicz.lean`.

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | multilinear Marcinkiewicz interpolation | double splitting at heights `λ^{r/p}`, `λ^{r/q}`, layer cake, `P^u Q^v ≤ P + Q`, finite-sum Tonelli (`Auto.bilinear_marcinkiewicz`) | 2026-10-01T11:20:00-04:00

## Section 5.1: proof of Theorem 4

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | `lem:lowerbd` proof, lines 2112-2116 | martingale averages `E_k` on `[0,1]` and `E_k g ≤ C g * ϑ_k` for `g ≥ 0` | 2026-10-01T07:41:48-04:00
complete | `lem:lowerbd` proof, lines 2117-2136 | `∫ f (E^{(1)}_k f)(E^{(2)}_l f) ≥ (∫ f)^4` by Cauchy-Schwarz | 2026-10-01T07:41:48-04:00
complete | `lem:lowerbd`, lines 2034-2039 | `∫ f (f *_1 ϑ_k)(f *_2 ϑ_l) ≥ c_0 (∫ f)^4` | 2026-10-01T07:41:48-04:00
complete | proof of Theorem 4, lines 2042-2057 | `τ`, `τ_k`; `2^{k'} I ≥ I_1 + I_2 + I_3` | 2026-10-01T08:39:35-04:00
complete | proof of Theorem 4, lines 2058-2059 | `|I_3| ≲ 2^{2σk' - σk''}` from the smoothing inequality | 2026-10-01T08:39:35-04:00
complete | proof of Theorem 4, lines 2060-2061 | `|I_2| ≤ ‖f *_2 ϑ_{k''} - f *_2 ϑ_k‖_2` | 2026-10-01T08:39:35-04:00
complete | proof of Theorem 4, lines 2062-2071 | `I_1 = I_4 + I_5 + I_6`, `|I_4| ≲ 2^{k-k'}` | 2026-10-01T08:39:35-04:00
complete | proof of Theorem 4, lines 2072-2081 | `|I_5| ≤ ‖f *_1 ϑ_{k''} - f *_1 ϑ_k‖_2 + O(2^{k'-k''} + 2^{k-k'})` | 2026-10-01T08:39:35-04:00
complete | proof of Theorem 4, lines 2082-2083 | `I_6 ≥ c_0 ε^4` | 2026-10-01T08:39:35-04:00
complete | proof of Theorem 4, lines 2086-2090 | the dichotomy for `1 < k < k' < k''` | 2026-10-01T08:39:35-04:00
complete | proof of Theorem 4, lines 2093-2101 | the sequence `k_{l+1} = M k_l`, `k_0 ≳ log ε^{-1}`, `M` independent of `ε` | 2026-10-01T08:39:35-04:00
complete | proof of Theorem 4, lines 2103-2106 | Plancherel: `∑_l ‖f *_i ϑ_{k_{l+1}} - f *_i ϑ_{k_l}‖_2^2 ≲ 1`, so `(dychotomy1)` holds for some `l ≲ ε^{-C}` | 2026-10-01T08:39:35-04:00
complete | `eqn:patternpenult`, lines 2027-2031, 2106-2108 | `∫_{[0,1]^3} f(x,y) f(x+t,y) f(x,y+t^2) > exp(-exp(ε^{-C}))` | 2026-10-01T08:39:35-04:00
complete | Theorem 4, line 2031 | `f = 1_E` and the lower bound on `t` | 2026-10-01T08:39:35-04:00

## Section 2: preliminary reductions (shared part)

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | `eqn:thtc`, lines 215-219 | `pvT`, `tendsto_pvT` (the principal value exists for test functions), `DFR/Auto/CDR/Sec2PreliminaryReductions1Decomposition.lean` | 2026-10-01T16:40:00-04:00
complete | §2.1, lines 441-445 | `φ`, `ψ`, `ψ_j`, `φ_j`, `∑_j ψ_j = 1` off `0`; partial operators `Δ^{(ℓ)}_j`, `S^{(ℓ)}_j` on `ℝ^2` | 2026-10-01T10:29:38-04:00
complete | §2.1, line 445 | `ψ̃ = ψ(2·)+ψ+ψ(·/2)` (`lpDfat`), `Δ_m Δ̃_m = Δ_m` (`lpD_lpDfat`), square-function bounds `eLpNorm_lpD_square_le`, `eLpNorm_lpDfat_square_le` (1D theorem from lean_spherical), `DFR/Auto/CDR/Sec2PreliminaryReductions1LittlewoodPaley.lean` | 2026-10-01T13:20:00-04:00
complete | §2.1, lines 446-448 | `hasSum_Tj_pvT`: `T = ∑_j T_j` pointwise, `DFR/Auto/CDR/Sec2PreliminaryReductions1Decomposition.lean` | 2026-10-01T16:40:00-04:00
complete | `eqn:basicfreqdecomp`, `eqn:basic-freq-dec`, lines 449-458 | `partition_unity`, `sum_Tj_decomp` (Fourier form: `T_m` with `symSum lowNu`, `mixNuI`, `mixNuII`, plus the `𝔉_H` sum), `DFR/Auto/CDR/Sec2PreliminaryReductions1Decomposition.lean` | 2026-10-01T16:40:00-04:00
complete | §2.2, lines 462-463 | the shifted dyadic maximal function `𝓜_σ` | 2026-10-01T10:29:38-04:00
complete | `eqn:shiftedmaxfct-basic`, lines 464-467 | `‖𝓜_σ g‖_p ≲ log(2+|σ|)^{1/p} ‖g‖_p`, `1 < p < ∞` (`shiftedMaximal_lintegral_rpow_le`, `eLpNorm_cShift_le`; `p = ∞` is not used) | 2026-10-01T10:29:38-04:00
complete | `lem:shiftedmaxfct` proof, lines 494-502 | the splitting into `I_l` and the rapid decay of `ψ̌`, for `T_j` (`enorm_avg_lpD_le`, general bump), `DFR/Auto/CDR/Sec2PreliminaryReductions3HighFrequencies.lean` | 2026-10-01T12:55:00-04:00
complete | `lem:shiftedmaxfct` proof, lines 503-519 | the intervals `J_l`, shifts `σ_{l,n}`, both signs of `l`; also `κ ≤ 0` (`enorm_avg_lpD_le_nonpos`), `DFR/Auto/CDR/Sec2PreliminaryReductions3HighFrequencies.lean` | 2026-10-01T12:55:00-04:00
complete | `lem:shiftedmaxfct`, `eqn:shiftedmaxfct-main`, lines 474-481 | domination of `T_j(F, Δ^{(2)}_{2j+κ} G)` by fixed-scale shifted averages `cAvg` (route change, see ErrorReport), `enorm_Tj_lpD_le`, `DFR/Auto/CDR/Sec2PreliminaryReductions3HighFrequencies.lean` | 2026-10-01T12:55:00-04:00
complete | `eqn:shiftedmaxfct-j`, lines 482-491 | stated directly at scale `2^{-j}` (no separate dilation step), `enorm_Tj_lpD_le` | 2026-10-01T12:55:00-04:00
complete | `eqn:HHT0` proof, lines 551-556 | scaling built into `scaled_smoothing_gen` / `Bj_gain` (general bump `ψ(u)/u`), `DFR/Auto/CDR/Sec2PreliminaryReductions3HighFrequencies.lean` | 2026-10-01T12:55:00-04:00
complete | `eqn:HHT0`, `eqn:local-gain-L2`, lines 526-528, 576-597 | the `L^2` decay `TkF_L2` via `Tj_gain` (global form of Theorem 5, no spatial localization needed), `DFR/Auto/CDR/Sec2PreliminaryReductions3HighFrequencies.lean` | 2026-10-01T14:40:00-04:00

## Section 2.6: maximal operator (Theorem 3)

Route change (see `automation/ErrorReport-cdr.md`, 2026-10-01T10:06:34-04:00): the mixed terms `M^M_j` are not put in
kernel form by non-stationary phase. Since `M_j` is a positive operator, every term in which one
input is `S_j a` or `S_{2j} b` is dominated pointwise by `𝓜^{(1)} a 𝓜^{(2)} b`; all remaining
pieces `(k_1, k_2)` with `k_1, k_2 ≥ 1` are treated as the paper treats `F_H`.

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | §2.6, lines 649-651 | `M(f_1,f_2) ≤ 2 sup_j M_j(|f_1|,|f_2|)` (`maxOp_le_iSup_MjE`) | 2026-10-01T10:06:34-04:00
complete | §2.6, lines 652-670 (route change) | `|M_j(a,b) - M_j(a - S_j a, b - S_{2j} b)| ≲ 𝓜^{(1)} a 𝓜^{(2)} b`, incl. the parabolic average `∫ ψ_j(t) |g(y+t^2)| dt ≲ 𝓜 g(y)` (`lowPart_bound`) | 2026-10-01T10:06:34-04:00
complete | `eqn:shiftedmaxfct-main`, `lem:shiftedmaxfct` proof, lines 474-519, at scale `2^{-j}` | `|M_j(F, Δ^{(2)}_{2j+κ} G)| ≤ ∑_{|l| ≤ 2^{κ+1}} ∑_n C 2^{-κ} (1+|n|)^{-4} 𝓜^{(1)}_l F 𝓜^{(2)}_{σ_{l,n}} G` (`enorm_Mj_lpD_le`) | 2026-10-01T10:06:34-04:00
complete | `eqn:shiftedmaxfct-coeff`, `eqn:shiftedmax-max`, lines 681-688 | a majorant of `sup_j |M_j(Δ_{j+k_1} a, Δ_{2j+k_2} b)|` with `L^r` norm `≲ (k_2+5)^2 ‖a‖_p ‖b‖_q` (`coeffSum_le`, `highPiece_Lp`) | 2026-10-01T10:06:34-04:00
complete | `eqn:max-l2-decay`, `eqn:Mk-l2-decay`, lines 671-680 | `∑_{j ∈ F} ‖M_j(Δ_{j+k_1+1} f, Δ_{2j+k_2+1} g)‖_1 ≲ 2^{-δ max(k_1,k_2)} ‖f‖_2 ‖g‖_2` for bounded integrable `f, g` (`Mj_piece_L1`, `sum_Mj_piece_L1`) | 2026-10-01T10:29:38-04:00
complete | §2.6, lines 689-692 | interpolation: `sup_{j ∈ F}` linearized by a measurable selector and phase (`iSup_finset_eq_Bfun`), `bilinear_interpolation` on simple functions (`Bsel_interp`), approximation by simple functions (`Bfun_bound`), `F ↑ ℤ` (`MkH_bound`) | 2026-10-01T10:29:38-04:00
complete | §2.6, lines 652-656 | `a - S_j a = ∑_{k ≥ 1} Δ_{j+k} a` (`lpS_tendsto_self`, `sum_lpD_telescope`) and `|M_j(a - S_j a, b - S_{2j} b)| ≤ ∑_k |M_j(Δ, Δ)|` (`enorm_Mj_high_le`) | 2026-10-01T10:29:38-04:00
complete | Theorem 3, lines 297-306 | assembly: summation over `k ∈ ℕ^2` (`summable_highCoeff`), Hölder for the low part (`thm_maxfct`) | 2026-10-01T10:29:38-04:00

## Section 4: the smooth case (Theorem 2)

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | §4.1, lines 1515-1540 | `g`, `h = g'`, `ψ`, `φ`; `mdecompose`, `mdecompose2` (via the fundamental theorem of calculus in `t`), `DFR/Auto/CDR/Sec4SmoothCaseConeDecomposition.lean` | 2026-10-01T14:05:00-04:00
complete | §4.1, lines 1541-1563 | `m^{(t)}`, Fourier series, coefficient decay; the model operators `modelOpFull` (`Cone.hasSum_TOp_cone1`), `DFR/Auto/CDR/Sec4SmoothCaseConeDecomposition.lean` | 2026-10-01T14:05:00-04:00
complete | §4.1, lines 1574-1580 | Theorem 2 from the model bounds by summation over `(u,v)` and symmetry: `thm_anisotp_of_modelBound`, `DFR/Auto/CDR/Sec4SmoothCaseConeDecomposition.lean` | 2026-10-01T14:05:00-04:00
complete | §4.1, lines 1584-1607 | dyadic rectangles, `Ω_𝒬`, trees, convex trees, leaves, `θ`, `𝓜_𝒬`, `Λ^{(u,v)}_𝒬` (`DyRect`, `DyTree`, `cellInt`, `collInt`, `locForm`, `theta1`, `theta2`, `xiForm`, `Msize`, `modelOp`; `Sec4SmoothCase1ConeDecomposition.lean`) | 2026-10-01T11:54:35-04:00
complete | `lem:bdbymax`, lines 1655-1688 | the bound by `∏ (f_j^2 * (θ ⊗ θ))^{1/2}` (`Telescoping.bdbymax`) | 2026-10-01T11:54:35-04:00
complete | §4.3, lines 1758-1800 | single-rectangle telescoping: `eqn:telescoping-pre`, `eqn:gh-idts` (`Sec4SmoothCase3Telescoping.lean`; reuses `Auto.Twisted.scalar_oneDim_telescoping_of_ne_zero`) | 2026-10-01T11:54:35-04:00
complete | §4.3, lines 1800-1867 | `lemma:telescoping` for convex trees, `eqn:barkest-final`, `eqn:treecountingest` (`telescoping_identity`, `telescoping_bound`; counting by a different argument, see ErrorReport) | 2026-10-01T11:54:35-04:00
complete | `domfct`, lines 1645-1653 | bounds for `Ξ` (Twisted's bracket dominations) | 2026-10-01T11:54:35-04:00
complete | `prop:tree` proof, lines 1693-1754 | Cauchy-Schwarz, `eqn:dominatebygaussians`, positivity of `Θ^{(2)}` (`gauss_dom`, `enorm_quadForm_le_split`, `cells_lambda_bound`, `theta2_abba_le`) | 2026-10-01T11:54:35-04:00
complete | `prop:tree`, lines 1609-1615 | `|Λ^{(u,v)}_𝒯| ≤ C_{u,v} |Q_𝒯| ∏ 𝓜_𝒯(f_j)` (`tree_estimate`, `Sec4SmoothCase2TreeEstimate.lean`) | 2026-10-01T11:54:35-04:00
complete | §4.4, lines 1869-1900 | stopping time and planting: `combining_trees` (localized form over a convex collection, `f_4 = 1`, `2 < p_j`, `∑ 1/p_j = 1`), `DFR/Auto/CDR/Sec4SmoothCase4CombiningTrees.lean`; pointwise disjointness of maximal rectangles replaces the level-set sums | 2026-10-01T12:40:00-04:00
complete | §4.4, lines 1900-1910 | limiting argument (`locForm_boxColl_tendsto`, `Sec4SmoothCase4CombiningTreesLimit.lean`) and `pt2` (`modelForm_initial`; complex form `FullRange.strong_initial` in `DFR/Auto/CDR/Sec4SmoothCase.lean`) | 2026-10-01T15:30:00-04:00
complete | §4.5, lines 1912-1960 | fibrewise Calderón-Zygmund decomposition: good part (`modelOp_weak_fiber1`, `Sec4SmoothCase5FiberwiseCZ.lean`) | 2026-10-01T11:54:35-04:00
complete | §4.5, lines 1961-2021 | bad part: `h`, `‖h‖_p ≲ (∑ |I|)^{1/p}` (Grafakos Exercise 4.6.6), weak `L^p × L^q → L^{r,∞}` for `1 ≤ p ≤ p_0` (`modelOp_weak_fiber1`, `modelOp_weak_fiber2`) | 2026-10-01T11:54:35-04:00
complete | `fwrange-1`, lines 1932-1937 | interpolation to the full range and the second fibre (`FullRange.ustrong_phase1`, `ustrong_phase2`, `modelOp_full_range`), `DFR/Auto/CDR/Sec4SmoothCase.lean` | 2026-10-01T15:30:00-04:00
complete | `prop:twisted`, lines 1565-1572 | `ModelBound` with constant `C (AB+1)^D` (`Glue.modelBound_of_truncFull`; kernels and untruncation in `Sec4SmoothCaseModelKernels.lean`), `DFR/Auto/CDR/Sec4SmoothCase.lean` | 2026-10-01T15:30:00-04:00
complete | Theorem 2, lines 277-283 | assembly `thm_anisotp` from `thm_anisotp_of_modelBound`, `DFR/Auto/CDR/Sec4SmoothCase.lean` | 2026-10-01T15:30:00-04:00

## Section 2: reduction of Theorem 1

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | `eqn:shiftedfs`, lines 468-472 | replaced (route change) by the fixed-scale form `exists_eLpNorm_sqrt_sum_sq_shiftedAverage_le` (`‖(∑_i A_{σ,k_i} g_i^2)^{1/2}‖_p ≲ log(2+|σ|) ‖(∑|g_i|^2)^{1/2}‖_p`), `DFR/Auto/ShiftedMaximalFunction.lean` | 2026-10-01T13:20:00-04:00
complete | `eqn:Tk-l2-decay`, lines 529-538 | `TkF_L2`: `‖T^{(k)}‖_{L^2×L^2→L^1} ≲ 2^{-δ max k}` uniformly in finite `j`-ranges, `DFR/Auto/CDR/Sec2PreliminaryReductions3HighFrequencies.lean` | 2026-10-01T14:40:00-04:00
complete | §2.3, lines 539-548 | `TkF_poly`: `‖T^{(k)}‖ ≲ (|k_2|+5)^2` (fixed-scale shifted averages, route change), `DFR/Auto/CDR/Sec2PreliminaryReductions3HighFrequencies.lean` | 2026-10-01T14:40:00-04:00
complete | §2.3, lines 549-550 | interpolation: `TkF_decay` (`≲ 2^{-δ max k}` on `𝔉_H` for all `1<p,q<∞`, `r ≥ 1`); the summation over `k` is in the Theorem 1 assembly, `DFR/Auto/CDR/Sec2PreliminaryReductions3HighFrequencies.lean` | 2026-10-01T14:40:00-04:00
complete | §2.4, lines 600-611 | `T^L` in Fourier form: symbol `symSum lowNu F` (`lowNu = φ⊗φ·ϑ`, `ϑ(0)=0` replaces the mean-zero kernel `κ`), `DFR/Auto/CDR/Sec2PreliminaryReductions4LowFrequencies.lean` | 2026-10-01T15:50:00-04:00
complete | `sym-est`, lines 612-619 | `lowNu_isAnisoSymbol` (general `isAnisoSymbol_symSum` for sums of anisotropic dilates), uniform in finite `j`-ranges, `DFR/Auto/CDR/Sec2PreliminaryReductions4LowFrequencies.lean` | 2026-10-01T15:50:00-04:00
complete | §2.5, lines 622-639 | `T^M = I + II` in Fourier form: symbols `mixNuI`, `mixNuII`, `DFR/Auto/CDR/Sec2PreliminaryReductions5MixedFrequencies.lean` | 2026-10-01T15:50:00-04:00
complete | `est-statph`, lines 640-647 | non-stationary phase `AmpI.deriv_decay`, `AmpII.deriv_decay`; `mixNuI_isAnisoSymbol`, `mixNuII_isAnisoSymbol`, `DFR/Auto/CDR/Sec2PreliminaryReductions5MixedFrequencies.lean` | 2026-10-01T15:50:00-04:00
complete | Theorem 1, lines 221-224 | assembly `thm_singint`: Theorem 2 for `T^L`, `T^M`, `high_bound` for `T^H`, Fatou over `j ∈ [-J, J]`, `DFR/Auto/CDR/Sec2PreliminaryReductions1Decomposition.lean` | 2026-10-01T16:40:00-04:00
