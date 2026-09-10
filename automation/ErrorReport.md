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

2026-09-10T15:06:59.5427297-04:00 - The corrected second and third refinement definitions and bounds are verified in smoothing_second_refinement_lower and smoothing_third_refinement_nonempty. The spatial-area factor M is explicit. Corrected subsequent fibers and the seventh-power conclusion remain to be proved in source order.

2026-09-10T15:13:34.2979099-04:00 - The corrected fiber construction now has its source seventh-power bound, proved in smoothing_exists_parameterSet. In the following displayed F, (3.42) requires alpha0=alpha(zbar)/2 rather than alpha(zbar): the printed three relations contain 2t, so elimination leaves alpha(zbar)t2/(2t1t3)-beta. Use this forced factor-of-two correction; it preserves the nondegeneracy and the main result.
