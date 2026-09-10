# Formalization status

## Main theorem overview

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
in progress | arXiv:2008.10140v2, Theorem 5 | Task 1: trilinear smoothing inequality | 2026-09-10T11:06:10.5169482-04:00
not started | Task 2 blueprint pending | Task 2: 3d smoothing inequality | 2026-09-10T09:42:06.7141336-04:00
not started | Task 3 blueprint pending | Task 3: Twisted | 2026-09-10T09:42:06.7141336-04:00
not started | Task 4 blueprint pending | Task 4: main theorem via Reduction | 2026-09-10T09:42:06.7141336-04:00

## Task 1 source proof ledger

Source: [arXiv:2008.10140v2](https://arxiv.org/html/2008.10140v2), Theorem 5 and Section 3. Rows identify source equations or unnumbered passages; their order places prerequisites before uses. Unnumbered display numbering is local to the named proof. Dependency order: Lemma 3.1 precedes Lemma 3.2; the proof of Lemma 3.3 precedes its use in Section 3.4; (3.24) and Lemma 3.2 precede (3.30); (3.30), (3.31), and (3.40) precede (3.2); the averaging estimate and (3.2) precede interpolation and (1.10). No row below is complete merely because a supporting Lean lemma exists.

Ledger refinement recorded 2026-09-10T12:44:37.8315626-04:00. Existing Lemma 3.1 work remains in progress. New rows describe uncompleted source obligations; their timestamp records this audit, not when proof work began.

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | §3.2, Lemma 3.1 proof, first unnumbered display | Fourier formula for the multiplicative difference | 2026-09-10T13:00:27.2212653-04:00
complete | §3.2, Lemma 3.1 proof, second unnumbered display | Expand the squared Fourier modulus | 2026-09-10T13:02:25.7932849-04:00
complete | §3.2, Lemma 3.1 proof, third unnumbered display | Integrate the squared modulus in the translation parameter | 2026-09-10T13:05:48.3116235-04:00
complete | §3.2, Lemma 3.1 proof, final display, equality | Identify the frequency-pair integral over distance at most R | 2026-09-10T13:12:23.7254769-04:00
complete | §3.2, Lemma 3.1 proof, final display, inequality | Bound energy by total mass times maximal ball mass | 2026-09-10T13:12:55.3269446-04:00
complete | §3.2, Lemma 3.1 proof, final paragraph | Choose a ball and obtain the orthogonal decomposition with the stated norm bound | 2026-09-10T13:14:22.6762663-04:00
complete | §3.2, Lemma 3.2 proof, first sentence | Choose the smooth integer partition of unity | 2026-09-10T13:18:17.5671364-04:00
complete | §3.2, Lemma 3.2 proof, definition of the index set and cardinality assertion | Select high-mass intervals and bound their number | 2026-09-10T13:23:20.4632247-04:00
complete | §3.2, Lemma 3.2 proof, displayed definitions of sharp and flat parts | Construct the frequency decomposition | 2026-09-10T13:27:14.7693672-04:00
complete | §3.2, Lemma 3.2(1) | Bound the two L² norms | 2026-09-10T13:29:13.9107524-04:00
complete | §3.2, Lemma 3.2(2), smoothness clause for h_n | Construct the smooth demodulated pieces | 2026-09-10T13:32:53.6931026-04:00
complete | §3.2, Lemma 3.2(2), Fourier support clause for h_n | Prove Fourier support in [-R,R] | 2026-09-10T13:36:19.4485594-04:00
complete | §3.2, Lemma 3.2(2), L² bound for h_n | Bound each piece's L² norm | 2026-09-10T13:37:31.3491380-04:00
complete | §3.2, Lemma 3.2(2), displayed modulated sum | Recover the sharp part as the finite modulated sum | 2026-09-10T13:43:53.9084129-04:00
complete | §3.2, Lemma 3.2(2), derivative inequality | Prove uniform derivative bounds with the stated R powers | 2026-09-10T13:55:07.4728456-04:00
complete | §3.2, Lemma 3.2(2), final support inclusion | Keep the sharp Fourier support inside the input Fourier support | 2026-09-10T13:57:24.0541170-04:00
complete | §3.2, Lemma 3.2(3), (3.25), final contradiction argument | Bound the flat part's multiplicative-difference energy | 2026-09-10T14:05:58.0712823-04:00
complete | §3.5 opening, change of variables and (3.41) | Transform the sublevel set by the spatial shear | 2026-09-10T14:17:05.4228044-04:00
complete | §3.5 opening, normalization sentence after (3.41) | Reduce the compact domain to the unit spatial square and a positive unit interval | 2026-09-10T14:23:16.1150578-04:00
complete | §3.5 opening, final sentence before the claim | Dispose of the zero-measure sublevel-set case | 2026-09-10T14:24:56.0595170-04:00
complete | §3.5 claim proof, (3.43) | First fiber refinement | 2026-09-10T14:28:50.0606990-04:00
complete | §3.5 claim proof, (3.44) | Lower bound for the first refined set | 2026-09-10T14:33:25.2566943-04:00
complete | §3.5 claim proof, unnumbered definitions between (3.44) and (3.45) | Second and third fiber refinements | 2026-09-10T15:06:59.5427297-04:00
complete | §3.5 claim proof, (3.45)-(3.47) | Construct the three nested parameter fibers | 2026-09-10T15:08:40.4043946-04:00
complete | §3.5 claim proof, final unnumbered display | Obtain parameter-set measure at least a constant times the seventh power | 2026-09-10T15:13:34.2979099-04:00
complete | §3.5 claim, (3.42), and following definition of F | Combine the three inequalities into the scalar sublevel condition | 2026-09-10T15:15:23.5267261-04:00
complete | §3.5, definitions of theta_1, theta_2, and V preceding (3.48) | Construct the vector field tangent to both level sets | 2026-09-10T15:19:09.1761651-04:00
complete | §3.5, (3.48) | Compute the nonzero derivative of vartheta along V | 2026-09-10T15:22:04.9554609-04:00
complete | §3.5, coordinates u = Jt following (3.48) | Diagonalize the vector field and compute the Jacobian | 2026-09-10T15:29:59.8780903-04:00
in progress | §3.5, unnumbered Omega_(k,d) decomposition | Decompose away from the degenerate line | 2026-09-10T15:29:59.8780903-04:00
not started | §3.5, normalized v-coordinates and phi maps | Construct flow charts and their Jacobians | 2026-09-10T12:44:37.8315626-04:00
not started | §3.5, definition of G and (3.49) | Differentiate along a flow chart | 2026-09-10T12:44:37.8315626-04:00
not started | §3.5, (3.50)-(3.51) | Factor the derivative and control its scale | 2026-09-10T12:44:37.8315626-04:00
not started | §3.5, (3.52) | Bound the polynomial-composition sublevel measure | 2026-09-10T12:44:37.8315626-04:00
not started | §3.5, proof of (3.53), (3.54) | Apply the Łojasiewicz inequality on the compact chart | 2026-09-10T12:44:37.8315626-04:00
not started | §3.5, proof of (3.53), near-cube estimate | Bound the contribution near the zero set | 2026-09-10T12:44:37.8315626-04:00
not started | §3.5, proof of (3.53), far-cube estimates | Use the derivative lower bound and Fubini | 2026-09-10T12:44:37.8315626-04:00
not started | §3.5, proof of (3.53), boundary-cube estimate | Bound the boundary contribution | 2026-09-10T12:44:37.8315626-04:00
not started | §3.5, proof of (3.53), last display | Choose the cube scale and combine the three contributions | 2026-09-10T12:44:37.8315626-04:00
not started | §3.5, dyadic sum following (3.53) | Sum the scales and conclude Lemma 3.3, (3.40) | 2026-09-10T12:44:37.8315626-04:00
not started | §3 opening, (3.1), and following sentence | Define the localized operator and reduce to positive t | 2026-09-10T12:44:37.8315626-04:00
not started | §3 opening, (3.3)-(3.4), and following normalization | Perform the frequency and amplitude reductions | 2026-09-10T12:44:37.8315626-04:00
not started | §3 opening, (3.5) | Localize the inputs in space | 2026-09-10T12:44:37.8315626-04:00
not started | §3 opening, (3.6) | Bound the number of interacting localization pairs | 2026-09-10T12:44:37.8315626-04:00
not started | §3.1, (3.7)-(3.8) | Apply Cauchy-Schwarz and choose reference points | 2026-09-10T12:44:37.8315626-04:00
not started | §3.1, unnumbered mean-value estimates before (3.9) | Linearize the quadratic shift | 2026-09-10T12:44:37.8315626-04:00
not started | §3.1, (3.9)-(3.10) | Separate the main term and bound the linearization error | 2026-09-10T12:44:37.8315626-04:00
not started | §3.1, (3.11)-(3.12) | Apply Cauchy-Schwarz to the localization sum | 2026-09-10T12:44:37.8315626-04:00
not started | §3.1, (3.13)-(3.14) | Expand in local Fourier series and apply Parseval | 2026-09-10T12:44:37.8315626-04:00
not started | §3.1, (3.15) | Bound the high-frequency coefficient tail | 2026-09-10T12:44:37.8315626-04:00
not started | §3.1, (3.16)-(3.17) | Control the phase gradient and discard nonstationary frequencies | 2026-09-10T12:44:37.8315626-04:00
not started | §3.1, (3.18)-(3.20) | Bound the resonant coefficient sum | 2026-09-10T12:44:37.8315626-04:00
not started | §3.1, (3.21)-(3.23) | Count admissible localization indices | 2026-09-10T12:44:37.8315626-04:00
not started | §3.1, remainder estimate immediately before (3.24) | Separate low coordinate frequencies and bound the remainder | 2026-09-10T12:44:37.8315626-04:00
not started | §3.1, (3.24) | Conclude the basic estimate for each input | 2026-09-10T12:44:37.8315626-04:00
not started | §3.3, opening convolution decomposition and mean-value bound | Control the localization commutator | 2026-09-10T12:44:37.8315626-04:00
not started | §3.3, fiberwise applications of Lemma 3.2 preceding (3.26) | Construct measurable sharp and flat fiber decompositions | 2026-09-10T12:44:37.8315626-04:00
not started | §3.3, (3.26)-(3.29) | Localize and assemble the sharp, flat, and error terms | 2026-09-10T12:44:37.8315626-04:00
not started | §3.3, (3.30) | Bound the flat contribution using (3.24) | 2026-09-10T12:44:37.8315626-04:00
not started | §3.3, (3.31) | Bound the error contribution | 2026-09-10T12:44:37.8315626-04:00
not started | §3.4, (3.32)-(3.34) | Expand the structured term and separate disjoint cube families | 2026-09-10T12:44:37.8315626-04:00
not started | §3.4, (3.35)-(3.37) | Bound the nonstationary structured contribution | 2026-09-10T12:44:37.8315626-04:00
not started | §3.4, (3.38)-(3.39) | Reduce the remaining contribution to a sublevel measure | 2026-09-10T12:44:37.8315626-04:00
not started | §3.4, last two paragraphs after Lemma 3.3 | Apply (3.40), choose decay parameters, and conclude (3.2) | 2026-09-10T12:44:37.8315626-04:00
not started | §3 opening, unnumbered averaging estimates following (3.2) | Prove the L^(3/2) product estimate using parabolic averaging | 2026-09-10T12:44:37.8315626-04:00
not started | §1.3 after (1.10), §3 opening reduction after (3.2) | Interpolate, sum frequency pieces, and dualize to Theorem 5 | 2026-09-10T12:44:37.8315626-04:00

Baseline lake build passed (3343 jobs) at this recording time; dependency linter warnings remain. Auto requires separate direct compilation. No Task 1 theorem is complete. Searches of Mathlib, lean-spherical and local source found no matching structural decomposition or analytic sublevel estimate. Existing LittlewoodPaley homogeneousDyadicResolution and integerLittlewoodPaleyL2 are reuse candidates, pending exact hypothesis and axiom audits. Mathlib Analysis.Fourier.LpSpace provides the L2 Fourier isometry. The anisotropic norms must preserve the printed half-exponents in their squared norm; decay exponents may require renaming during the dyadic bridge.

### Task 1 current verified declarations

2026-09-10T11:10:48.7425148-04:00 - Direct lake env lean Auto/SmoothingIneq2D/Smoothing2D.lean passed. Axiom checks for Auto.integrable_smoothingMultiplicativeDifference, Auto.smoothing_frequencyRestriction_orthogonal, Auto.smoothing_frequencyProjection, Auto.smoothing_exists_large_window, and Auto.smoothing_frequencyRestriction_norm_sq each report only propext, Classical.choice, Quot.sound. These are supporting results for Lemma 3.1, not completion of that lemma or Theorem 5.

Next obligation: prove the Fourier energy identity for multiplicative differences of arbitrary L2 inputs, including almost-everywhere and integrability justifications; specialize the averaging lemma to frequency balls and combine it with the projection and norm identities. Remaining source obligations are listed in the proof order above.


### Latest Task 1 verification and continuation

2026-09-10T11:19:28.2785658-04:00 - Direct compilation passed for Auto/SmoothingIneq2D/Smoothing2D.lean. All eleven theorem declarations were checked with #print axioms and use only propext, Classical.choice, Quot.sound. In addition to the five declarations above, verified Auto.smoothing_frequencyProjection_of_mass, Auto.smoothing_integrable_ball_energy, Auto.smoothing_exists_ball_mass, Auto.smoothing_concentration_of_fourier_energy, Auto.smoothing_fourier_toLp_ae_eq, and Auto.smoothing_integral_norm_sq_fourier.

The frequency concentration/projection argument is proved, including the zero-input case. The source Lemma 3.1 is still in progress: its multiplicative-difference Fourier energy has not yet been equated to the frequency-pair energy. The conditional frequency-energy theorem is an intermediate result, not a replacement for Lemma 3.1. L1/L2 Fourier compatibility and raw-integral Plancherel are now available to support the remaining identity. Next: prove the identity first for suitable integrable inputs, justify the iterated integrals, and extend to arbitrary L2 inputs before closing Lemma 3.1. Do not advance to Lemma 3.2 while this remains open.

Reuse confirmed: Mathlib Lp.fourier_toTemperedDistribution_eq, ae_eq_of_integral_contDiff_smul_eq, VectorFourier.integral_fourierIntegral_smul_eq_flip, Lp.inner_fourier_eq, and Lp.norm_fourier_eq. Their use is covered by the transitive axiom checks above. The lean-spherical planeWaveModulatedCompactSchwartz construction requires compact support and does not directly cover arbitrary L2 modulation; do not silently impose that restriction. Theorem 5 and all later proof-order rows remain incomplete. No commit or push performed.

## Proof ledger

Setup introduced no mathematical proofs. Task 1 now has verified supporting lemmas; see its resumed proof order and current verification below.
After reading each available source, expand that task into substantial steps in
forward dependency order before implementing it. Task 4 follows all of Tasks 1-3.
Place any justified reusable-prerequisite sections before the consuming proof rows.

## Historical setup verification

Setup build: lake build passed (3345 jobs), 2026-09-10T09:46:43.7252496-04:00. Both DFR and the new
Auto.SmoothingIneq2D.Smoothing2D module were covered. Existing dependency linter warnings remain.
Axiom audits: not applicable yet; there are no completed Auto targets.
Reduction gate: closed.

## Continuation

Task 1 starter: Auto/SmoothingIneq2D/Smoothing2D.lean.
Task 1 is active. Continue the first unfinished source row below. Theorem 5 has no completed exported interface.

Skill copies: SHA-256 verified against installed editions (Codex: 6 files; Claude: 5).
Git diff --check passed; automation/raw.md is ignored.
The initial broad Mathlib import build was stopped during starter compilation;
the final starter uses Mathlib.Analysis.Normed.Module.Basic and the full build passed.

## Verification policy and earlier history

2026-09-10T09:58:01.5996155-04:00 - Auto is excluded from lakefile.toml by explicit user instruction. The setup build above is historical evidence only. Current lake build passed (3343 jobs) for configured targets; it does not check Auto. Owned Auto sources require separate direct lake env lean checks. Both vendored skill editions and their bootstrap references now follow this policy.
Task 1 source study is underway; no mathematical declarations have been added or proved. Theorem 5 and portions of Section 3 have been read; the full proof/dependency audit remains unfinished.

2026-09-10T09:58:47.5716059-04:00 - Task 1 paused by explicit user request after the Auto build-inclusion instruction cleanup. No Lean source edits or proofs were made. Source study remains incomplete; resume with the full Section 3 dependency audit only when directed. Documentation diff check passed.


Verification 2026-09-10T13:00:27.2212653-04:00: smoothing_fourier_multiplicativeDifference proves the first display for arbitrary L² inputs. Direct Lean verification passed; its transitive axioms are propext, Classical.choice, Quot.sound. lake build passed (3343 jobs). Next: the second display, squared-modulus expansion.

Verification 2026-09-10T13:02:25.7932849-04:00: smoothing_fourier_multiplicativeDifference_norm_sq proves the second display. Direct Lean and allowed-axiom audit passed; lake build passed (3343 jobs). The third display is next.

Verification 2026-09-10T13:05:48.3116235-04:00: smoothing_integral_fourier_multiplicativeDifference_norm_sq proves the third display almost everywhere in frequency for arbitrary L² inputs, with the correlation's integrability justified by Fubini. Direct Lean and allowed-axiom audit passed; lake build passed (3343 jobs). Next: integrate over the frequency ball and interchange integrals.

Verification 2026-09-10T13:12:23.7254769-04:00: smoothing_fourierDifference_ball_energy proves the final display's equality. Joint integrability and restricted Fubini are proved without additional input assumptions. Direct Lean and allowed-axiom audit passed; lake build passed (3343 jobs). Next: the maximal-ball-mass inequality.

Verification 2026-09-10T13:12:55.3269446-04:00: smoothing_fourierDifference_energy_le_ball_mass proves the source supremum inequality. Direct Lean and allowed-axiom audit passed; lake build passed (3343 jobs). Next: connect the original energy hypothesis to the orthogonal decomposition.

Verification 2026-09-10T13:14:22.6762663-04:00: Auto.smoothing_lemma3_1 proves the full source Lemma 3.1 from its original hypothesis, with the stated one-half square-root norm bound and Fourier support understood almost everywhere for L² classes. Every Lemma 3.1 source row is complete. Direct Lean verification, transitive allowed-axiom audit, lake build (3343 jobs), and git diff --check passed. Next: Lemma 3.2's smooth integer partition of unity; matching constructions found in pinned lean-spherical CalderonVaillancourt and Spherical.MSS, under inspection.

Verification 2026-09-10T13:18:17.5671364-04:00: smoothing_lemma3_2_partition proves the smooth compactly supported integer partition in (-1,1), with positivity and unit bounds. Reused Auto.CalderonVaillancourt.sum_Icc_telescope from the pinned lean-spherical dependency; its transitive axioms are allowed. Direct Lean, axiom audit, and lake build (3343 jobs) passed. Next: high-mass interval selection and cardinality bound; the zero input must be handled separately because the source's positive-mass counting argument presumes nonzero total mass.

Verification 2026-09-10T13:23:20.4632247-04:00: smoothingHighMassIndices defines the source index set using length-R intervals meeting the scaled cutoff support. smoothingHighMassIndices_finite proves finiteness and the explicit bound 6/ρ for a nonnegative integrable density of positive total mass. Its source application is the nonzero-input case; zero input uses the empty decomposition. Direct Lean, allowed-axiom audit, and lake build (3343 jobs) passed. Next: construct sharp and flat parts by the source Fourier multipliers.

Verification 2026-09-10T13:27:14.7693672-04:00: smoothing_lemma3_2_frequency_decomposition connects the selected index set (including zero input) to the exact L² sharp/flat decomposition and the displayed Fourier multipliers. Direct Lean, allowed-axiom audit, and lake build (3343 jobs) passed. Next: Lemma 3.2(1), the L² norm bounds.

Verification 2026-09-10T13:29:13.9107524-04:00: smoothing_lemma3_2_L2_bounds proves part (1) with uniform constant 2. Direct Lean, allowed-axiom audit, and lake build (3343 jobs) passed. Part (2) is split into its actual clauses so smoothness, spectral support, individual norms, modulated reconstruction, derivative bounds, and final support inclusion are tracked separately. Next: smoothness of the demodulated pieces, via Mathlib Real.contDiff_fourier and compact spectral moments.

Verification 2026-09-10T13:32:53.6931026-04:00: smoothingPiece_contDiff proves smoothness of the source's demodulated pieces for every L² input and positive R, using the proved integrability of every spectral moment and Mathlib Real.contDiff_fourier. Direct Lean, allowed-axiom audit, and lake build (3343 jobs) passed. Next: identify their L² Fourier representatives and prove support in [-R,R].

Verification 2026-09-10T13:36:19.4485594-04:00: smoothingPieceL2_coe identifies each smooth piece with its L² class; smoothingPieceL2_fourier_support proves spectral vanishing outside [-R,R]. Direct Lean, allowed-axiom audit, and lake build (3343 jobs) passed. Next: the individual L² norm bound.

Verification 2026-09-10T13:37:31.3491380-04:00: smoothingPieceL2_norm_le proves the individual piece norm bound with constant one. Direct Lean, allowed-axiom audit, and lake build (3343 jobs) passed. Next: the displayed modulated sum for the sharp part.

Verification 2026-09-10T13:43:53.9084129-04:00: smoothingSharpPart_eq_sum_exp proves the source modulated reconstruction with real frequencies -2πnR and the already verified smooth pieces. Direct Lean, allowed-axiom audit, and lake build (3343 jobs) passed. Next: uniform derivative estimates. Pinned lean-spherical norm_fourierInv_scaled_schwartz_multiplier_le assumes Schwartz input; the current L² input requires a proved extension. Use Schwartz test-function Fourier duality to retain arbitrary L² inputs and an almost-everywhere L∞ bound.

Verification 2026-09-10T13:55:07.4728456-04:00: smoothingPiece_derivative_bound proves the pointwise derivative bound C_N R^N M for every almost-everywhere input bound M. C_N is the L¹ norm of the Fourier transform of the fixed derivative cutoff and depends only on N. Smoothness was proved independently for all L² inputs. The arbitrary-L² scaled multiplier extension and all spectral moment assumptions are proved. Direct Lean, allowed-axiom audit, and lake build (3343 jobs) passed. Next: sharp Fourier support inclusion.

Verification 2026-09-10T13:57:24.0541170-04:00: smoothingSharpPart_fourier_support proves the source's final support inclusion in the L² almost-everywhere sense. Direct Lean, allowed-axiom audit, and lake build (3343 jobs) passed. Next: (3.25), starting with the source argument that all cutoff indices meeting a high-mass length-R interval have been selected.

Verification 2026-09-10T14:05:58.0712823-04:00: Auto.smoothing_lemma3_2 combines all source clauses for one selected finite decomposition; smoothingFlatPart_energy_bound proves (3.25) with constant 2. Source constants are explicit and uniform, and all L² representative bridges are proved. Direct Lean, transitive allowed-axiom audit, lake build (3343 jobs), and git diff --check passed. Lemmas 3.1 and 3.2 are complete; Task 1 remains incomplete. Next: §3.5 opening shear leading to (3.41), followed by the source normalization and fiber refinements. Do not skip to later algebraic computations.

2026-09-10T14:17:05.4228044-04:00 - Section 3.5 opening shear verified by smoothing_sublevel_shear_preimage, smoothing_sublevel_shear_measure, and smoothing_sublevel_shear_domain. Direct Lean verification passed; both audited conclusions use only propext, Classical.choice, Quot.sound; lake build passed (3343 jobs); git diff --check passed. Next source item: compact-domain normalization after (3.41).

2026-09-10T14:23:16.1150578-04:00 - The normalization after (3.41) is verified by smoothing_sublevel_normalization, with smoothing_compact_parabolic_box, smoothing_sublevel_parabolic_preimage and smoothing_parabolic_map_volume supplying the compact enclosure, exact coefficient transformation and Jacobian. Direct Lean and allowed-axiom audit passed; lake build passed (3343 jobs). Parameters depend only on K. Next: the source zero-measure case, then (3.43).

2026-09-10T14:24:56.0595170-04:00 - The source zero-measure case is verified by smoothing_sublevel_zero_measure; direct Lean and allowed-axiom audit passed, and lake build passed (3343 jobs). Continuing with (3.43).

2026-09-10T14:28:50.0606990-04:00 - Equation (3.43) verified by smoothing_eq3_43_upper and smoothing_eq3_43, including measurable fibers and the exact one-half lower bound. Direct Lean, allowed-axiom audit and lake build (3343 jobs) passed. Next source item is (3.44).

2026-09-10T14:33:25.2566943-04:00 - Equation (3.44) verified with its exact quarter-square bound by smoothing_eq3_44_identity, smoothing_eq3_44_threshold and smoothing_eq3_44. Direct Lean, allowed-axiom audit and lake build (3343 jobs) passed. The next refinement has a false printed definition/bound; a correction question is pending. See ErrorReport.md. No corrected source claims have been adopted.

2026-09-10T14:35:03.7084674-04:00 - Final verification of the current source state: lake env lean Auto/SmoothingIneq2D/Smoothing2D.lean passed, including smoothing_printed_second_refinement_empty; all printed axiom sets are subsets of propext, Classical.choice, Quot.sound. The configured lake build passed (3343 jobs), git diff --check passed, and the owned Lean source contains no sorry, admit, or new axiom declarations. Task 1 and the second-refinement source row remain incomplete. A correction question is pending; the proposed revised fibers and explicit m^7/(2048 M^2) bound are in the source audit comment. No downstream proof item was started. No commits, staging or pushes were performed.

2026-09-10T15:06:59.5427297-04:00 - Corrected second and third refinements verified: smoothing_second_refinement_lower and smoothing_third_refinement_nonempty, using the beta-projection box of area M=4(a+1) and threshold |E1|/(2M). The retained E2 has measure at least (|E1|/(2M))(|E1|/2). Direct Lean, allowed-axiom audit and lake build (3343 jobs) passed. The correction is authorized by the user's renewed completion instruction; no further question is pending. Next: nested source fibers (3.45)-(3.47).

2026-09-10T15:08:40.4043946-04:00 - The corrected fibers (3.45)-(3.47) are verified by smoothing_time_fibers_measurable, smoothing_time_fibers_lower and smoothing_time_fibers_subset. They share alternating alpha and beta coordinates as required by (3.42). Direct Lean, allowed-axiom audit and lake build (3343 jobs) passed. Next: the parameter-set measure bound with seventh power.

2026-09-10T15:13:34.2979099-04:00 - The seventh-power parameter-set bound is verified in smoothingParameterSet_seventh_power and smoothing_exists_parameterSet, with coefficient 2^(-11) M^(-2), M=4(a+1). The same measurable set lies in I^3. Direct Lean, allowed-axiom audit and lake build (3343 jobs) passed. Next: (3.42) and the scalar sublevel expression F.

2026-09-10T15:15:23.5267261-04:00 - smoothing_eq3_42 proves the source three inequalities on the parameter set; smoothing_scalar_sublevel_bound gives the uniform scalar bound with c=alpha(z)/2 and constant (((a+1)/a+2)/(2a)). Direct Lean, allowed-axiom audit and lake build (3343 jobs) passed. Next: tangent vector field preceding (3.48).

2026-09-10T15:19:09.1761651-04:00 - The tangent field is verified in smoothingVectorField_thetaOne, smoothingVectorField_thetaTwo and smoothingVectorField_eq_zero. Both actual Frechet derivatives annihilate V, whose zero set is exactly the source diagonal. Direct Lean, allowed-axiom audit and lake build (3343 jobs) passed. Next: (3.48).

2026-09-10T15:22:04.9554609-04:00 - Equation (3.48) is verified in smoothing_eq3_48, smoothing_eq3_48_ne_zero and smoothing_eq3_48_prefactor. The cubic factors into the three coordinate differences, and the positive rational factor has the source uniform bounds on I^3. Direct Lean, allowed-axiom audit and lake build (3343 jobs) passed. Next: the J-coordinate change and Jacobian.

2026-09-10T15:29:59.8780903-04:00 - The J-coordinate change is verified: smoothingJ includes its continuous linear inverse, smoothingJ_vectorField diagonalizes V, smoothingJ_det proves determinant -1 for the actual linear map, and smoothingJ_measurePreserving/smoothingJ_image_volume give the volume identities. smoothingJ_timeCube_bounds verifies the stated coordinate enclosure. Direct Lean, allowed-axiom audit and lake build (3343 jobs) passed. Next: the dyadic Omega_(k,d) decomposition away from the degenerate line.
