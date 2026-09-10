# Source discrepancies

No mathematical source audit has been performed during setup.
No discrepancies recorded. Add timestamped source locations, differences, and
resolutions here as required by the autoformalize skill.

2026-09-10T11:06:10.5169482-04:00 - arXiv:2008.10140v2, Lemma 3.2 proof: the displayed multipliers use the undefined scale lambda^(-tau). The preceding definition fixes scale R, so read this as R^(-1); Section 3.3 later specializes R = lambda^tau. This is an unambiguous local notation correction; the theorem statement is unchanged.

2026-09-10T13:18:17.5671364-04:00 - Lemma 3.1, third display: the L² identity is formalized almost everywhere in frequency, where the spectral correlation is square-integrable. Fubini proves this qualification, and smoothing_fourierDifference_ball_energy proves the subsequent unrestricted iterated energy identity. This is the standard L² representative interpretation; the lemma's objects, hypothesis and conclusion are unchanged.

2026-09-10T14:05:58.0712823-04:00 - Lemma 3.2 proof, final paragraph: the source switches from radius-R balls to length-R intervals and suppresses the zero-input case. The formalization covers a radius-R ball by two length-R intervals, yielding explicit constant 2 in (3.25), and uses the empty index set for zero input. It applies Lemma 3.1's proved maximal-ball energy inequality directly to the source high-interval vanishing argument, rather than extracting another orthogonal summand. The source estimate and all parameter ranges are preserved; smoothing_lemma3_2 is verified.

2026-09-10T14:33:25.2566943-04:00 - Section 3.5, unnumbered second refinement after (3.44): unresolved false printed E2 definition and lower bound. Take alpha=1, beta=0, epsilon=1, K=[0,1]^2 x [2,3]. Then E=E1=K and |E|=1. For w in [0,1]^2 and t in [2,3], w1-t<0, so the fiber defining E1' is empty. Thus E2 is empty, contradicting |E2| >= 2^(-6)|E|^4. The subsequent fiber coordinates also do not give (3.42). User direction requested before replacing these source steps and their numerical constants. A concrete proposed repair is recorded in the task's Lean documentation; it preserves the claim's seventh power and the main statements, but is not yet formally adopted or proved.

2026-09-10T14:35:03.7084674-04:00 - The second-refinement obstruction is now checked in Lean by smoothing_printed_second_refinement_empty, with only allowed axioms. Proposed correction remains pending user direction; the source discrepancy is unresolved.

2026-09-10T15:02:01.6771576-04:00 - User directs continued completion in response to the correction question. Proceed with the documented coordinate and constant corrections; the main theorem is unchanged. Formal verification of the corrected refinement remains in progress.

2026-09-10T15:06:59.5427297-04:00 - The corrected second and third refinement definitions and bounds are verified in smoothing_second_refinement_lower and smoothing_third_refinement_nonempty. The spatial-area factor M is explicit. Corrected subsequent fibers and the seventh-power conclusion remain to be proved in logical forward reasoning order.

2026-09-10T15:13:34.2979099-04:00 - The corrected fiber construction now has its source seventh-power bound, proved in smoothing_exists_parameterSet. In the following displayed F, (3.42) requires alpha0=alpha(zbar)/2 rather than alpha(zbar): the printed three relations contain 2t, so elimination leaves alpha(zbar)t2/(2t1t3)-beta. Use this forced factor-of-two correction; it preserves the nondegeneracy and the main result.

2026-09-10T15:44:44.7832059-04:00 - Section 3.5 dyadic Omega decomposition: the printed pointwise cover omits the degenerate line, which is null; smoothingOmega_ae_cover proves the needed almost-everywhere cover. The printed two-sided volume comparison cannot hold for empty or boundary-clipped pieces; smoothingOmegaPiece_volume_le proves the uniform upper bound actually used in the dyadic estimate. Main statements are unchanged.

2026-09-10T16:10:55.9655978-04:00 - Section 3.5, change-of-variables display before G: the four signed boxes overlap, so the printed equality with their summed measures must be an upper bound. smoothingFlowBox_volume_le and smoothingOmegaPiece_flow_volume_le verify subadditivity with the stated coefficient. The subsequent estimate and main results are unchanged.

2026-09-10T16:25:48.4350490-04:00 - Equation (3.52) invokes a generic van der Corput type estimate. For this exact cubic the formalization instead proves the needed special case by its explicit two-factor formula, two interval covers, and Fubini, yielding exponent 1/2 and constant 4 log(2) uniformly in all four charts. The claimed source bound is preserved.

2026-09-10T16:29:27.7598925-04:00 - Equation (3.54): no general Lojasiewicz theorem is available in the pinned libraries. The required instance is proved directly from the explicit zero branches, with exponent 2 and constant 1/1024, retaining the prescribed local zero set. This replaces the external theorem invocation while preserving the exact needed inequality.

2026-09-10T17:08:39.6246632-04:00 - Boundary-cube estimate in the proof of (3.53): the source suppresses uniform geometric justification. Six explicit smooth interval constraints with dyadic dependence only in their endpoints give uniform strip-volume bounds. The formalization first proves the O(rho) union-volume bound and then deduces O(rho^(-2)) cardinality from disjoint interiors. Both source claims are verified.

2026-09-10T17:15:25.0474266-04:00 - Grid covering in the proof of (3.53): equal-side closed grid cubes need not fit exactly inside the compact chart rectangle at its boundary. The verified grid permits boundary cubes in the fixed radius-two ambient box. Near and far cubes remain inside the actual chart domain; the proved boundary estimate already covers the larger box. Covering includes endpoints and all source measure estimates remain unchanged.

2026-09-10T17:40:23.1761669-04:00 - Lemma 3.3 comparability convention and beta branch: smoothing_lemma3_3 makes the fixed positive lower comparability constant m explicit; C depends on K and m and is uniform over the measurable functions. No upper bound is used. The source says it first proves the alpha case but omits a separate beta argument at the end of Section 3.5. smoothing_lemma3_3_beta supplies it: the small sublevel condition forces alpha above the compact time lower bound; a measurable truncation allows the alpha result, and the remaining epsilon range uses volume(K). Dyadic summation uses a quarter-power balance of the verified analytic and trivial bounds, giving exponent 1/64 before the refinement and 1/448 afterwards. All these proofs are verified; Theorem 5 is unchanged.

2026-09-10T18:23:34.428125-04:00 - Repository layout error: setup created a root Auto directory despite existing DFR/Auto task directories. Corrected task locations, verification commands, agent entry point, and both vendored skills/bootstrap guides. Files are relocated without replacing their contents. Main and Tasks 2-4 receive only their original starter and instruction corrections, never Task 1 formalization work.
