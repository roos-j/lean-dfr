# Source discrepancies

No mathematical source audit has been performed during setup.
No discrepancies recorded. Add timestamped source locations, differences, and
resolutions here as required by the autoformalize skill.

2026-09-10T18:23:34.428125-04:00 - Repository layout error: setup created a root Auto directory despite existing DFR/Auto task directories. Corrected task locations, verification commands, agent entry point, and both vendored skills/bootstrap guides. Files are relocated without replacing their contents. Main and Tasks 2-4 receive only their original starter and instruction corrections, never Task 1 formalization work.

2026-09-11T12:14:59-04:00 - Task 2, blueprints/task_2_smoothingineq3d_blueprint.tex. Three results are asserted with literature citations instead of proofs: `thm:kosz-adjoint` (Kosz-Mirek-Peluse-Wan-Wright, arXiv:2411.09478, Thm 6.13, specialized), the scale-one upper-half estimate used inside the proof of `thm:kosz-subunit` (same paper, Cor. 5.3 and eq. (6.24)), and `thm:quasi-interpolation` (Grafakos-Mastylo, Nonlinear Analysis 107 (2014), Thm 3.2). Remark `rem:formalization-boundary` explicitly sanctions importing them. This conflicts with the Task 2 completion gate in automation/tasks.md, which forbids unproved bridges, and with the prohibition on sorry/axioms in automation/instructions.md. Unresolved: referred to the user. No main statement is changed; `thm:main` keeps its blueprint content. Meanwhile all blueprint steps independent of the resolution are being formalized, and the imported statements will be carried as explicit, clearly named hypotheses rather than axioms, so that nothing is hidden and they can later be discharged.

2026-09-11T12:48:04-04:00 - Task 2, change of proof route (not a source discrepancy). The blueprint proves `lem:trivial-holder` and the final display of `thm:main` with Minkowski's integral inequality, which Mathlib does not provide in its continuous form. Both uses are instead derived from Hölder's inequality in the parameter variable together with Tonelli's theorem, via the Lean lemma `Auto.eLpNorm_integral_le`: for a finite parameter measure `nu` and `1 <= p < infinity`, if `eLpNorm (G t) p <= C` for every `t`, then `eLpNorm (fun x => integral of G t x d nu) p <= nu(univ) * C`. This yields exactly the blueprint's constants (`prod of norms` for A_N and `r * prod of norms` for B_r), so no estimate is weakened and no statement changes. Recorded because the skill requires documenting substantive departures from the source argument.

2026-09-11T15:01:39-04:00 - Task 2, blueprint `lem:projection-properties`, first two displays. The blueprint states the L^s bounds for `P_R^{(j)}` and `Q_R^{(j)}` for every s in [1, infinity]. The Lean lemmas `Auto.eLpNorm_P_le` and `Auto.eLpNorm_Q_le` currently require s < infinity, because they are derived from `Auto.eLpNorm_integral_kernel_le`, whose Holder-in-the-parameter proof uses a finite exponent. Every downstream use in this blueprint applies these bounds with finite exponents only (`prop:normalized-endpoint` uses q_i = 1/b_i and s_i, all in (1, infinity); `prop:normalized-banach` uses only the vanishing statement), so no target is weakened. Unresolved as a fidelity gap in the prerequisite lemma itself; the s = infinity case is an easy separate pointwise argument and will be added if a later step needs it.

2026-09-11T15:42:49-04:00 - Task 2, blueprint `thm:quasi-interpolation`. automation/instructions.md (user direction of 2026-09-10T09:48:18) asks agents to try deriving the required multilinear interpolation from the pinned lean-spherical machinery, and records the expectation that this should be relatively easy. That route does not reach the statement the blueprint needs. The results in .lake/packages/lean_spherical/LeanSpherical/Auto/SteinInterpolation.lean, namely `stein_interpolation` and `riesz_thorin`, are stated for a single linear operator `T : SimpleFunc X C -> Y -> C` and require `1 <= q0` and `1 <= q1`; they are Banach-range results. Blueprint `thm:quasi-interpolation` is trilinear and is applied in `prop:normalized-endpoint` with output exponent `q = 1 / (b_1 + b_2 + b_3)`, which `thm:kosz-subunit` places strictly inside `(1/2, 1)`. A subunit output exponent is exactly the quasi-Banach case that Riesz-Thorin and Stein interpolation do not cover, and is the reason the blueprint cites Grafakos-Mastylo rather than a classical interpolation theorem. Marcinkiewicz interpolation in LeanSpherical.Auto.Spherical.Auxiliary is likewise linear and does not apply. Unresolved: proving `thm:quasi-interpolation` therefore requires developing quasi-Banach multilinear interpolation, not adapting an existing result.

2026-09-11T17:07:03-04:00 - Task 2, blueprint `thm:kosz-subunit`, constant. The blueprint defines the constant as `64 * Dyad(Ctilde)`, obtained by bounding `(2^q - 1)^(-1/q)` by 64 for q in (1/2, 1). The Lean proof `Auto.kosz_subunit` instead carries the exact factor the geometric series produces, `Auto.subunitLoss q * Ct` where `subunitLoss q = ((1/2)^q / (1 - (1/2)^q))^(1/q)`. Both are explicit finite constants and the blueprint's own statement only asserts that some constant exists, so no estimate is weakened; the numeric rounding to a power of two is simply not carried out. Related: the blueprint's remark that every numerical factor in its constants is an integer power of 2 is a presentational normalization that this formalization does not track anywhere. The mathematical content of every estimate, including `thm:main`, is unaffected, since each statement asserts existence of constants rather than their dyadic form.

2026-09-11T17:07:03-04:00 - Task 2, blueprint `thm:kosz-adjoint`, hypothesis class. The blueprint states the imported estimate for "every Schwartz family (g_i)". `Auto.KoszAdjoint` instead quantifies over continuous families. Since Schwartz functions are continuous, this is a STRENGTHENING of the imported hypothesis, not a weakening of the conclusion, and it is recorded here as a departure. The reason is that the blueprint's own proof of `prop:normalized-banach` applies the estimate to a test function produced by L^p duality, which is not Schwartz; the blueprint bridges that gap silently by density of the Schwartz class in L^{p'}. Stating the import for continuous test functions makes that step explicit and avoids a separate density development. The corresponding estimate in Kosz-Mirek-Peluse-Wan-Wright is an L^p operator bound and does hold in this class, so the strengthened hypothesis is faithful to the cited result, but a reader should be aware that `thm:main` as formalized assumes slightly more than the blueprint's literal wording of `thm:kosz-adjoint`.

2026-09-11T17:07:03-04:00 - Task 2, blueprint `prop:normalized-banach`, missing library result. The proof concludes with "Duality between L^p and L^{p'} gives ...". Mathlib provides no L^p duality: there is no statement of the form `eLpNorm f p <= M` from a bound on the pairing against L^{p'} functions, and no `eLpNorm` supremum formula. It must therefore be developed inside DFR/Auto/SmoothingIneq3D/. The planned route avoids the general theorem and its truncation argument: in the application `eLpNorm (A N f) p` is already known to be finite by `Auto.eLpNorm_A_le`, so it suffices to prove the duality bound under an explicit finiteness hypothesis, using the explicit dual function `x -> (norm (F x)) ^ (p - 2) . F x`, which is continuous for every p > 1 and pairs with F to give `norm (F x) ^ p`. Unresolved until that development is complete.

2026-09-11T18:33:56-04:00 - Task 2, user instruction versus blueprint contents. The user directed the agent to rely on an "updated blueprint" in which the three imported results are said to be proved rather than assumed. The file blueprints/task_2_smoothingineq3d_blueprint.tex on disk is UNCHANGED: 1637 lines, 49645 bytes, mtime 2026-09-11 09:37 (earlier than the start of this session's work), MD5 ccd112efd5c27774665abd555a904076. The text selected in the editor is the same document the formalization has been using. It still proves `thm:kosz-adjoint` by the single sentence "This is Theorem 6.13 of Kosz-Mirek-Peluse-Wan-Wright, specialized as follows" (line 657), still proves `thm:quasi-interpolation` by "This is Theorem 3.2 of Grafakos-Mastylo" (line 869), still takes the scale-one estimate behind `thm:kosz-subunit` from Corollary 5.3 and equation (6.24) of the same paper, and still contains Remark `rem:formalization-boundary` (line 1614) stating that a formalization may treat all three as imported analytic modules. No proof of any of the three appears anywhere in the document. The instruction therefore cannot be carried out from this file, and the agent has not changed the status of the three imports. Unresolved: the actual updated document is needed, or a decision to develop the two source papers' arguments from scratch, which is far beyond this blueprint.

2026-09-11T18:44:08-04:00 - Task 2, resolution of the 2026-09-11T18:33:56-04:00 entry. The updated blueprint was supplied under a new filename, blueprints/task_2_smoothingineq3d_blueprint_updated.tex (2626 lines, 101237 bytes, MD5 6795374a15cd47616798ebb82058f25d), not as an overwrite of the original path the agent had been checking. The earlier entry is therefore correct as written about the original file but no longer describes the operative source. The updated document does prove all three formerly imported results internally, in new sections `sec:internal-gm`, `sec:internal-kosz-improving` and `sec:internal-kosz-adjoint`, and its `prop:no-imported-analytic-declarations` forbids axioms, sorries and foreign declarations at those nodes. Resolved: the three Lean statements `Auto.KoszAdjoint`, `Auto.KoszSubunitScaleOne` and `Auto.QuasiInterpolation` stop being permanent hypotheses and become proof obligations. They stay as named Props; the work is to prove them, after which every downstream theorem becomes unconditional without restructuring.

## 2026-09-11T19:17:47-04:00 - Minkowski's integral inequality, weighted form

Blueprint `thm:main` invokes Minkowski's integral inequality to pass from the
fundamental-theorem-of-calculus identity of `lem:weighted-primitive-identity` to

    ||A_psi(f)||_p <= int_a^b |psi'(u)| ( ||B_u f||_p + ||B_a f||_p ) du .

Mathlib has no Minkowski integral inequality, and the earlier replacement
`Auto.eLpNorm_integral_le` only handles a bound that is uniform in the parameter, which would
have produced the constant `(b-a) sup|psi'|` instead of the blueprint's `M = ||psi'||_{L^1}`.

Resolution: the parameter integral is taken against the weighted measure
`nu = (volume.restrict (Ioc a b)).withDensity (fun u => ||psi' u||_e)`, whose total mass is at
most `M`.  The Hoelder-in-the-parameter plus Tonelli argument was factored out as

    Auto.eLpNorm_le_of_enorm_le_lintegral

which takes any `F` with `||F x||_e <= int^- ||G t x||_e d nu` and any `nu`-a.e. uniform bound on
`||G t||_p`, and concludes `||F||_p <= nu(univ) * C`.  `Auto.eLpNorm_integral_le` is now the
two-line corollary for `F x = int G t x d nu` with a bound holding for every `t`; all earlier
call sites are unchanged.  Applying the general form with `G u x = B u f x - B a f x` yields the
constant `M * 2 * C_j`, matching `def:main-constants` exactly.

No change to any statement was needed.  The blueprint's separate `M = 0` case analysis is not
required in Lean: when the density has total mass zero the bound is `0`, which is below the
stated right-hand side.

Supporting fact proved for this step: `Auto.continuous_uncurry_B`, joint continuity of
`(x, r) |-> B_r f x`, obtained from
`intervalIntegral.continuous_parametric_primitive_of_continuous`.  It supplies the joint
measurability required by the weighted Minkowski lemma.

## 2026-09-11T19:36:35-04:00 - Defect found and fixed: `QuasiInterpolation` was false as stated

While preparing to prove `thm:gm-internal` (the internal proof of the imported
`thm:quasi-interpolation`), the Lean statement `Auto.QuasiInterpolation` was re-read against
the blueprint and found to be **false**, not merely unproved.

The blueprint requires "`T` a trilinear operator defined on a dense common subspace" of the six
input spaces.  The earlier Lean rendering quantified over an arbitrary operator
`T : (Fin 3 -> E3 -> C) -> E3 -> C` and an arbitrary domain predicate, with no trilinearity and
no structure on the domain.  With no structure, the two endpoint hypotheses concern a single
output function `g = T f`, and Lyapunov interpolation gives only

    ||g||_q <= M_0^{1-t} M_1^t (prod ||f_i||_{p_{i,0}})^{1-t} (prod ||f_i||_{p_{i,1}})^t ,

whereas the asserted conclusion has `prod ||f_i||_{p_i}` on the right.  Lyapunov for the inputs
runs the other way, `prod ||f_i||_{p_i} <= (prod ||f_i||_{p_{i,0}})^{1-t} (prod ||f_i||_{p_{i,1}})^t`,
so the asserted bound is strictly stronger and fails for a suitable single triple.  A false
hypothesis makes every conditional theorem downstream vacuous, so this had to be repaired before
any further work.

Fix, entirely inside the authorized file:

* `Auto.QuasiInterpolation` now takes the blueprint's dense common subspace as a predicate
  `S : (E3 -> C) -> Prop` on single functions (the shape actually used: the domain is the same
  subspace in every slot) together with the three structural hypotheses of the blueprint theorem:
  `S` is a linear subspace; every element of `S` lies in all six input spaces; `S` is dense in
  each of them; and `T` is trilinear on triples drawn from `S`.
* The call site `Auto.endpoint_interpolate` discharges all of them for `S = Auto.Nice`:
  `Auto.nice_smul_add` (subspace), `Auto.Nice.memLp` (membership), `Auto.nice_dense` (density,
  from `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le` plus
  `Auto.nice_of_hasCompactSupport`), and a new trilinearity hypothesis now carried by
  `endpoint_interpolate` itself.
* Trilinearity of the operator actually interpolated, `Auto.Tproj N R j`, is proved in
  `Auto.Tproj_trilinear`, via `Auto.P_smul_add`, `Auto.Q_smul_add`,
  `Auto.prodShift_update_smul_add` and `Auto.A_smul_add`.

No statement of a main result changed.  `Auto.main_smoothing` and `Auto.primitive_smoothing`
are unchanged and still audit to [propext, Classical.choice, Quot.sound]; they are now
conditional on a hypothesis that is no longer refutable.

Lesson recorded for the remaining imports: `Auto.KoszAdjoint` and `Auto.KoszSubunitScaleOne`
must be re-audited the same way against the blueprint before their internal proofs are attempted.

## 2026-09-11T20:09:19-04:00 - Library coverage found for the maximum-principle step

The blueprint proof of `lem:scalar-strip` derives the harmonic majorization from "the Poisson
formula for a rectangle, the maximum principle, and monotone convergence", letting the rectangle
grow and using `c < pi` to kill the horizontal sides.

That last part does not have to be redone: Mathlib's
`PhragmenLindelof.vertical_strip` already proves the maximum principle on
`{z | a < re z < b}` under the hypothesis
`exists c < pi / (b - a), exists B, f =O[...] fun z => exp (B * exp (c * |z.im|))`.
For `a = 0`, `b = 1` this threshold is exactly the blueprint's `c < pi`, and the growth form is
exactly the blueprint's `|H(z)| <= exp (C exp (c |Im z|))`.
`Auto.norm_le_of_strip_growth` converts the blueprint's pointwise bound into the `IsBigO` form
and exposes the conclusion on the closed strip.

Consequence for the plan: the growing-rectangle argument of the blueprint proof is replaced by a
library citation, with no change to the statement and no change to the constants.  The remaining
new development for `lem:scalar-strip` is the Poisson representation of the strip and its
boundary behaviour, not the maximum principle.

No discrepancy with the blueprint; this is a proof-route simplification of the same lemma.

## 2026-09-11T20:30:19-04:00 - Decay estimate obtained in a stronger form than planned

The previous entry planned the estimate
`abs (im (stripKernelNorm sigma t z)) <= C(z) exp(-pi abs t)`, to be proved by splitting on the
signs of `t` and of `t - im z`.  The split is genuinely needed for that statement, because
`im (stripKernelNorm sigma t z)` is a difference of two terms neither of which decays: each one
tends to `-sigma/2` at one end and to `sigma/2` at the other, and only the difference decays.

Writing the difference over a common denominator and applying
`sinh (a - b) = sinh a cosh b - cosh a sinh b` collapses it to

    sigma (sigma cos(pi x) sinh(pi t) - sinh(pi y))
      / (2 (cosh(pi (t - y)) - sigma cos(pi x)) cosh(pi t)) ,   x = re z, y = im z.

Bounding `abs (sinh(pi t)) <= cosh(pi t)` and `1 <= cosh(pi t)` then cancels `cosh(pi t)`
entirely and gives

    abs (im (stripKernelNorm sigma t z))
      <= (abs (cos(pi x)) + abs (sinh(pi y))) / sin(pi x) * re (stripKernelNorm sigma t z) ,

with no case analysis.  This is both shorter to formalize and stronger: it says the imaginary
part is dominated pointwise by the real part, which is the Poisson kernel itself.  Downstream
this removes the need for any integrability hypothesis on the boundary data beyond the one
already required for the real part.

No change to any statement; this is a better proof of a stronger intermediate lemma.

## 2026-09-12T10:44:18-04:00 - Boundary limit proved without the peak-function theorem

The plan recorded on 2026-09-11 was to obtain the boundary limit from Mathlib's
`tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto`, splitting at a radius `delta` because
that theorem needs globally integrable data while the boundary data here is integrable only
against the kernel.

The split was kept but the Mathlib theorem was not used.  Once the tail estimate
(`Auto.integral_tail_le`) and the kernel mass (`Auto.integral_poissonStrip_translate`) were
available, the whole limit followed from one explicit inequality,

    abs (Poisson average - g y)
      <= eps + abs (g y) * x
         + sin(pi x) * (cosh(pi delta)/(cosh(pi delta) - 1)) * cosh(pi y)
           * (weighted L1 norm of g + abs (g y) * weighted L1 norm of 1),

valid whenever `g` oscillates by at most `eps` on the `delta`-neighbourhood of `y`
(`Auto.abs_poissonAverage_sub_le`).  Deriving `Auto.tendsto_poissonAverage` from it is then an
ordinary epsilon-delta argument using `sin(pi x) <= pi x`.

Two reasons this is the better route here.  The peak-function theorem produces a limit statement
only, whereas the explicit inequality is quantitative: its constants depend on the height `y`
solely through `cosh (pi y)`, which is what makes the pending upgrade to the two-variable
boundary limit (uniform for `y` in a compact set) possible at all.  And it avoids having to
match the theorem's hypothesis pattern -- a peak family indexed by a filter, uniform convergence
off every open neighbourhood, and a mass converging to one on a finite-measure set -- against a
kernel that is naturally parameterized by two real variables.

No change to any statement; this is a proof-route change for an intermediate lemma, recorded so
the earlier plan entry is not followed by mistake.

## 2026-09-12T11:06:28-04:00 - Structural gap found: Mathlib has no boundary-limsup maximum principle

Preparing the assembly of `lem:scalar-strip` exposed a gap that changes the remaining plan, so it
is recorded in full.

The blueprint proof majorizes `log (abs H + eps)` by the harmonic extension of its boundary
values and concludes by the maximum principle.  In Lean the natural route is to form the analytic
function `G = H exp (-Phi)`, where `Phi` is the analytic completion of the Poisson integral
(`Auto.stripPoissonIntegral`, proved holomorphic on the strip), and to apply
`PhragmenLindelof.vertical_strip` -- whose growth threshold for the strip `0 < re z < 1` is
exactly the blueprint's `c < pi` (`Auto.norm_le_of_strip_growth`).

The obstruction: `PhragmenLindelof.vertical_strip` requires `DiffContOnCl`, i.e. `G` continuous
up to the boundary.  That fails in general.  What is continuous up to the boundary is `norm G`,
because its boundary values involve only `re Phi`, and that is exactly what was proved in the
previous cycles (`Auto.tendsto_poissonAverage`, `Auto.tendsto_poissonAverage_far`).  The function
`G` itself need not be, because `im Phi` is a conjugate function -- a Hilbert transform -- which
has no reason to converge at the boundary for merely continuous data.

Searched for the two standard ways out and found neither in Mathlib:

* a maximum principle with boundary *limit superior* conditions.  Mathlib's
  `Complex.norm_le_of_forall_mem_frontier_norm_le` and every variant in
  Mathlib/Analysis/Complex/AbsMax.lean require `DiffContOnCl`; `grep` for `limsup` in both
  AbsMax.lean and PhragmenLindelof.lean returns nothing.
* subharmonicity.  Mathlib has no `Subharmonic` predicate at all -- `grep -rl` for
  "subharmonic" over all of Mathlib returns no file.  So the textbook route, "`u - P[u]` is
  subharmonic and has nonpositive boundary limsup", is not available either.

Resolution adopted: prove the missing maximum principle.  `Auto.norm_le_of_eventually_lt_boundary`
states it for a bounded connected open set in the plane: if `f` is differentiable on `U` and
`norm f` is eventually `< C` on approach to every boundary point, then `norm f <= C` on `U`, with
no continuity of `f` up to the boundary assumed.  The proof is the classical one: the set where
`norm f` is at least the value at an alleged counterexample is closed in the plane -- closed
inside `U` by continuity, and with no limit point on the frontier by hypothesis -- hence compact,
so `norm f` attains a maximum there which is a maximum over all of `U`; then
`Complex.norm_eqOn_of_isPreconnected_of_isMaxOn` forces `norm f` constant on `U`, contradicting
the boundary hypothesis at any frontier point.

No statement of the blueprint changes.  This is a Lean-library gap, not a discrepancy in the
mathematics, and it is being closed inside the prerequisite file as a supporting lemma, as the
skill directs for lemmas developed specifically for a reusable prerequisite.

Consequence for the plan: the remaining route to `lem:scalar-strip` now needs the strip
Phragmen-Lindelof argument rebuilt on top of `Auto.norm_le_of_eventually_lt_boundary` instead of
being a direct call to `PhragmenLindelof.vertical_strip`, since the latter's `DiffContOnCl`
hypothesis cannot be met.  `Auto.norm_le_of_strip_growth` remains correct but is not usable for
this application; it is kept because it is the right statement whenever `G` does extend
continuously.

## 2026-09-12T11:26:31-04:00 - Both Mathlib gaps closed

The two gaps recorded in the previous entry are now closed inside the prerequisite file:

* `Auto.norm_le_of_eventually_lt_boundary` -- maximum modulus with boundary limit superior
  conditions on a bounded connected open set;
* `Auto.norm_le_of_boundary_lt_strip` -- Phragmen-Lindelöf for the strip with the same kind of
  boundary hypothesis and the blueprint's growth condition `c < pi`.

Together these replace `PhragmenLindelof.vertical_strip`, whose `DiffContOnCl` hypothesis cannot
be met by the majorant `G = H exp (-Phi)`.  `Auto.norm_le_of_strip_growth`, the thin wrapper over
the Mathlib lemma proved earlier, is retained but is not on the path to `lem:scalar-strip`; it
remains correct and usable whenever the function does extend continuously to the boundary.

No statement of the blueprint changed at any point in this detour.

## 2026-09-12T12:12:44-04:00 - `lem:scalar-strip` proved with the regularization parameter still explicit

`Auto.norm_le_geom_mean_strip` is the blueprint's `lem:scalar-strip` with one difference: the
power means on the two edges are formed from `norm (H ...) + eps` rather than `norm (H ...)`, for
an arbitrary `eps > 0`.  Recording this precisely, because it is a real difference and not a
rephrasing.

The `eps` is the blueprint's own: its proof of `lem:scalar-strip` sets
`u_eps(z) = log (abs (H z) + eps)`, runs the subharmonic majorization for that, and removes the
`eps` at the end "using monotone convergence as `eps` decreases to 0".  The Lean development
follows the same route, and everything up to and including the majorization and the Jensen step
is done; what is not yet done is that last passage.

Why it is not a one-liner in Lean.  The natural argument is dominated convergence for
`A(eps) = int (norm H + eps)^s * w / m` as `eps -> 0`, with dominating function the `eps = 1`
integrand.  Two points need care:

* the hypotheses themselves depend on `eps` -- the log-integrability
  `Integrable (abs (log (norm H + eps)) / cosh)` is assumed for the given `eps`, so the limiting
  statement has to assume it for a range of `eps`, or assume the `eps`-free integrability of
  `log (norm H)` directly;
* Lean's `Real.log 0 = 0` convention means the monotone convergence
  `int log (norm H + eps) w` decreasing to `int log (norm H) w` is not available in the naive
  form when `H` has zeros on an edge.

The limit route avoids the second point entirely: from the proved inequality for every `eps > 0`,
letting `eps -> 0` gives the bound with `A(0)` by continuity of `rpow` in the base -- including
the degenerate case `A(0) = 0`, where the conclusion `norm (H theta) <= 0` comes out of the limit
rather than needing a reflection principle.  So the remaining work is the dominated-convergence
step plus continuity of `x |-> x ^ p` at `0` for `p > 0`
(`Real.continuousAt_rpow_const` with `Or.inr`).

Until that is done, the ledger should read `lem:scalar-strip` as proved in regularized form only.

## 2026-09-12T12:30:02-04:00 - The regularization caveat is closed

The previous entry recorded that `Auto.norm_le_geom_mean_strip` carried the blueprint's
regularization parameter `eps` explicitly, and that the ledger should read `lem:scalar-strip` as
proved in regularized form only.  That is no longer the case:
`Auto.norm_le_geom_mean_strip_zero` is the blueprint's statement, with `norm H` and not
`norm H + eps` in the two power means.

Both difficulties named in that entry were avoided as anticipated.  The `eps`-dependence of the
hypotheses was removed by reducing them to their `eps = 1` instances
(`Auto.integrable_abs_log_shift`, `Auto.integrable_rpow_shift`), using that `log (x + eps)` lies
between `log eps` and `log (x + 1)` and that `(x + eps) ^ s <= (x + 1) ^ s`.  And Lean's
`Real.log 0 = 0` convention never entered, because the limit was taken in the conclusion, where
only `rpow` appears, rather than in the intermediate logarithmic form.

No statement of the blueprint was weakened at any point, and no hypothesis beyond those of the
blueprint lemma is carried: continuity on the closed strip, analyticity inside, the growth bound
with `c < pi`, and integrability of the edge data against the reference weight.

## 2026-09-12T13:21:06-04:00 - Where the analyticity of the family comes from: a recorded deviation

`lem:lebesgue-strip` needs, for almost every output point `y`, that

  `H_y(z) = T (F_1(z), F_2(z), F_3(z)) (y)`

be analytic in the strip variable `z`.  The blueprint obtains this by taking each `f_i` to be a
finite-valued simple function, so that `F_i(z)` is a finite sum of fixed functions with entire
scalar coefficients and trilinearity expands `H_y` into a finite sum of entire functions.  That
route has a prerequisite the blueprint states but does not prove: `T` is given only on a dense
subspace `S`, simple functions need not lie in `S`, and so `T` must first be **extended** to the
endpoint products.  For output exponents `q < 1` that extension needs the completeness of the
quasi-Banach space `L^q`, which Mathlib does not have: `MeasureTheory.Lp` is a normed group, and
complete, only under `Fact (1 <= p)`.  Building it would mean redoing Chebyshev, Borel-Cantelli
and the a.e.-limit construction for subunit exponents, and then a theory of continuous extension
of *trilinear* maps between quasi-Banach spaces, neither of which exists.

**What was done instead.**  `DFR/Auto/SteinInterpolation.lean` proves the Lebesgue-space half of
the argument for an arbitrary analytic family, taking the analyticity, continuity and local
boundedness of `z |-> H z x` as hypotheses:

  `Auto.eLpNorm_le_of_analyticFamily`.

No operator, no dense subspace and no extension occurs in it.  The operator-dependent hypotheses
are then discharged in the application, where the family is explicit: the inputs are continuous
with compact support, `Auto.anFam` keeps them in that class on the whole closed strip, and the
analyticity of `H_y` is proved from the explicit kernel of the operator by differentiation under
the integral sign, not from a finite expansion.

**This is a deviation in the route, not in the estimate.**  The inequality proved is the one the
blueprint states.  What changes is which hypothesis carries the analyticity, and therefore that
`Auto.QuasiInterpolation` will be restated: the density hypotheses on `S` are replaced by the
requirement that `S` be closed under `Auto.anFam` on the closed strip together with the
analyticity of the composed family.  `thm:main` and every other blueprint statement are
unaffected.  The cost is moved, not removed: the analyticity of the concrete operator's family
must be proved, and that proof is the next ledger item.

## 2026-09-12T14:58:06-04:00 - The deviation of the previous entry is now discharged, not carried

The previous entry recorded that the analyticity of `z |-> T (F_1 z, F_2 z, F_3 z) (y)` would be
taken as a hypothesis of the reusable interpolation theorem rather than derived from a
simple-function expansion, and that the cost was moved rather than removed.  That cost has now
been paid in full.  For the operator actually interpolated, `Auto.Tproj`, the composed family is
proved to be

* holomorphic in the open strip (`Auto.differentiableAt_Tproj_anFam`), by differentiation under
  the two integrals that define the operator, the derivative bound coming from Cauchy's estimate
  rather than from an extra hypothesis (`Auto.differentiableAt_integral_of_bounded`);
* continuous on the closed strip (`Auto.continuousAt_Tproj_anFam`) and bounded there
  (`Auto.exists_bound_Tproj_anFam`);
* jointly measurable in the output point and the boundary parameter
  (`Auto.aestronglyMeasurable_Tproj_anFam`).

The dense class is `Auto.Ccs`, continuous with compact support, which is closed under the
analytic family; `Auto.Nice` is not, because `|u| ^ r` need not be integrable for `r < 1`.  The
return from `Auto.Ccs` to `Auto.Nice` is by truncation and Fatou
(`Auto.tendsto_Tproj_trunc`, `Auto.eLpNorm_le_of_tendsto`); it uses **pointwise** convergence
only, so it needs no convergence in any `L^p` norm and in particular no completeness of `L^q` for
`q < 1`.

`Auto.QuasiInterpolation` has been deleted.  Nothing about `thm:main` changed; what changed is
that one of its three imported hypotheses is now a theorem.

## 2026-09-12T15:20:47-04:00 - Two library findings that shape the plan for `prop:restricted-improving-vertex`

**Mathlib has no Lorentz spaces.**  Searching the pinned Mathlib for `Lorentz`, `wnorm`, weak
`L^p` quasi-norms, restricted weak type, or any real-interpolation file returns nothing; the
Lebesgue-space development stops at `eLpNorm`.  `prop:restricted-improving-vertex` is stated in
the blueprint as a map `L^{2,1} x L^{60/11,1} x L^{6,1} -> L^{6/5,infinity}`, but its proof
produces, and `lem:finite-marcinkiewicz` consumes, the equivalent **set form**

  `K^60 <= C N^{-10} abs(E_0)^{10} abs(E_j)^{30} abs(E_{j'})^{11} abs(E_k)^{10}`,

where `K` is the incidence integral of the four indicators.  The plan is therefore to formalize
the restricted weak-type statements in that set form throughout and to prove
`lem:finite-marcinkiewicz` directly from it, as the blueprint's own proof of that lemma does
(dyadic decomposition of simple functions, a finite cone split, and geometric summation).  This
avoids building a Lorentz-space theory that the blueprint never actually uses.  No statement is
weakened: the set form is what the Lorentz phrasing abbreviates.

**Mathlib's reverse area formula needs injectivity.**
`MeasureTheory.lintegral_abs_det_fderiv_le_addHaar_image` carries the hypothesis
`Set.InjOn f s`, while the flow of `lem:real-flow-jacobian` is only finite-to-one.  The forward
direction, `addHaar_image_le_lintegral_abs_det_fderiv`, needs no injectivity but is the wrong
direction here.  `Auto.lintegral_abs_det_fderiv_le_card_mul_image` bridges the gap: cover the
parameter set by finitely many measurable pieces on which the map is injective and sum, giving
`integral of abs det <= n * measure of the image`.  The blueprint's own multiplicity argument
supplies such a cover -- the degree-two block is injective off its diagonal
(`Auto.flowBlock2_injective`) and the degree-three block has at most the two orderings of its
outer pair (`Auto.flowBlock3_pair`).

## 2026-09-12T16:02:28-04:00 - Why the lift stays `EuclideanSpace R (Fin 6)`

The parameter tower is built one parameter at a time, so it is natural to write the lift as a
right-nested product `R x R x R x R x R x R`, on which Fubini is a five-fold application of one
two-variable lemma and on which Mathlib's area formula would apply directly.  That change was
made and then reverted, for a concrete reason: on the six-fold nested product **`volume` does not
resolve `IsAddHaarMeasure` or `IsAddRightInvariant`**.  Both instances are found for
`R x R`, and both are found for `EuclideanSpace R (Fin 6)`, but instance search does not carry
the product instance through six levels of nesting.  Haar-ness is not optional here: the adjoint
identity `Auto.incid_shift` is translation invariance, and the area formula is stated for an
additive Haar measure.

The lift therefore stays `EuclideanSpace R (Fin 6)`, and Fubini in the six tower parameters will
be obtained by transporting along `EuclideanSpace.volume_preserving_measurableEquiv` to
`Fin 6 -> R` and then along `MeasureTheory.measurePreserving_piFinSuccAbove`, peeling one
coordinate at a time.  The two moves of the tower,
`Auto.measure_prod_ge_of_fibres` and `Auto.lintegral_prod_ge_of_fibres`, are stated for an
arbitrary product of measure spaces and so are unaffected by the choice; only the transport is.

## 2026-09-12T17:55:40-04:00 - What the blueprint leaves undetermined in `lem:real-flow-jacobian`

Every analytic ingredient of `lem:real-flow-jacobian` is now proved: the fibre separation, the
deletion step in the form that returns the refined *configuration*
(`Auto.refinement_delete_fwd`, `Auto.refinement_delete_adj`), a full stage with all four
pointwise bounds referred to the configuration at the start of the stage
(`Auto.refinement_stage`), the tower moves (`Auto.measure_towerCons_ge`,
`Auto.lintegral_towerCons_ge`, `Auto.measure_piTower_ge`), the flow and its Frechet derivative
(`Auto.hasFDerivAt_flowMap`), the Jacobian (`Auto.det_flowDeriv`), the injective cover
(`Auto.flowMap_injective_cover`) and the area formula with multiplicity
(`Auto.lintegral_abs_det_fderiv_le_card_mul_image`).

What is **not** determined by the blueprint is how these are assembled into the tower.  The proof
of `lem:real-flow-jacobian` is four sentences: "Start at a point of a nonempty depth-60
refinement.  A pointwise lower bound furnished by `lem:lossless-refinements` says that the set of
parameters carrying that point to the next required refinement has measure at least a fixed
multiple of `alpha_i N`.  Apply Fubini after every move.  The parity pattern for degrees 1,2,3 is
precisely `(1) | (0,2) | (0,3,0,3)`."  Left open by that text, and needed before the Lean
statement can be written down:

1. which of the four densities is used at each of the six moves -- the seven set labels
   `(1,0,2,0,3,0,3)` name sets, not densities, and the correspondence is not given;
2. the signs `sigma_k` of the six translations, hence whether a move goes forward or along an
   adjoint;
3. how the six moves are distributed over the sixty refinement stages, that is which stage's
   bound is used at which move;
4. why the blueprint's flow is only block lower triangular rather than block diagonal: with the
   moves written as a sum of translations the cross terms vanish, so the "terms in a block
   depending only on earlier blocks" must come from a step of the construction that the text does
   not display.

None of this changes any statement of the blueprint, and `thm:main` is unaffected.  The
consequence for the formalization is that `lem:real-flow-jacobian`'s assembly, and therefore
`prop:restricted-improving-vertex`, cannot be completed from the blueprint as written without
inventing the missing choices.  The remaining rows of Part III are marked accordingly, and work
continues on the parts of the blueprint that are determined.

## 2026-09-12T19:35:05-04:00 - A step missing from the sketch of `lem:finite-marcinkiewicz`

The blueprint's proof of `lem:finite-marcinkiewicz` reads: expand the three nonnegative simple
inputs dyadically, expand by trilinearity, split the lattice of triples into finitely many cones
according to which endpoint functional is largest, "on each cone use that endpoint's distribution
estimate, and sum first along its extremal ray".

Taken literally this does not close.  The hypothesis at a vertex is a *restricted weak* estimate
(`prop:restricted-improving-vertex` produces `L^{2,1} x L^{60/11,1} x L^{6,1} -> L^{6/5,infinity}`),
and the conclusion is a *strong* estimate.  The dyadic expansion is a sum, and the weak
quasi-norm is not subadditive, so summing the per-cone weak bounds produces nothing.  The step the
sketch passes over is the upgrade

  restricted weak estimates at the vertices  ==>  restricted *strong* estimates at interior points,

after which the triangle inequality in `L^q` -- legitimate here because the target output exponent
is `q = 6/5 > 1` -- makes the per-cone summation work exactly as the sketch describes, over
triples and not over quadruples.  That upgrade is the classical Marcinkiewicz argument on the
distribution function: cut the layer-cake integral

  ||g||_q^q = q * int_0^infinity lam^(q-1) mu{|g| > lam} dlam

at a level chosen so that a weak bound below the cut and another above it both contribute the same
power of the two constants.  It is standard and determined, so unlike `lem:real-flow-jacobian`
nothing has to be invented; it is recorded here because the formalization contains a group of
lemmas with no counterpart in the blueprint text, and because the blueprint's own phrase
"distribution estimate" is the only trace of it.

The formalization therefore proves the lemma in two stages, and `automation/Status.md` lists them
as separate rows:

1. the distributional upgrade, `Auto.eLpNorm_le_of_wnorm_of_bdd` and its siblings: a weak `L^{q0}`
   bound together with a second endpoint bound gives a strong `L^q` bound for `q0 < q`, with the
   constant a product of powers of the two endpoint constants -- which is what lets the `N`-power
   of the improving vertex be tracked through the interpolation with weight `1/2`;
2. the dyadic/cone assembly, which consumes stage 1 at each vertex.

No blueprint statement changes and `thm:main` is unaffected.

## 2026-09-13T12:39:34-04:00 - `lem:finite-marcinkiewicz` needs positivity, which its statement does not assume

The lemma is stated for "a trilinear operator".  Its proof begins "for nonnegative finite simple
inputs, write `f_i = sum over n of 2^n * indicator(E_{i,n})`", and then expands by trilinearity.

That display is not an identity.  The sum has at most one nonzero term at each point -- the
largest power of two below the value, which is `Auto.dyadicFloor` -- and the value lies strictly
between that power and twice it (`Auto.dyadicFloor_le`, `Auto.le_two_mul_dyadicFloor`).  So what
the expansion actually controls is the operator applied to the dyadic minorant, and passing from
there to the operator applied to `f_i` needs the operator to be monotone in each slot on
nonnegative inputs.  An arbitrary trilinear operator is not.

There is no way around the comparison: an exact expansion of a nonnegative simple function into
scaled indicators exists (its own level sets, or the binary expansion of its values), but neither
carries the dyadic structure the cone summation needs -- the binary expansion in particular gives
sums `sum_n 2^(n p) |G_n|` that diverge at the low end, so it cannot replace the dyadic one.

The formalization therefore carries monotonicity on nonnegative inputs as an explicit hypothesis
of the assembly, and the hypothesis is discharged where the lemma is used: the operator there is
`Auto.A`, which is `N⁻¹` times an integral over `[0, N]` of a product of translates of the three
inputs, hence nonnegative and monotone in each slot on nonnegative inputs.  No blueprint statement
changes and `thm:main` is unaffected; the gap is in the lemma's hypotheses, not in its
application, and the added hypothesis is weaker than the positivity that
`lem:adjoint-gain-to-subunit` already assumes of the same operator.

## 2026-09-13T13:16:18-04:00 - How the cone split of `lem:finite-marcinkiewicz` is realized

The blueprint says: "split the lattice of triples `(n_1,n_2,n_3)` into finitely many cones
according to which endpoint linear functional is largest.  On each cone use that endpoint's
distribution estimate, and sum first along its extremal ray.  If the target vector is in the
relative interior, every resulting ratio is `2^(-eps |m|)` for some `eps > 0`, hence every sum is
geometric."

Formalizing this needs a decision the text does not make, namely which finite family of exponent
vectors the cones are indexed by.  The family that makes the sums work, and the one the argument
is really using, is not the vertices themselves but a family of interior points: with the target
vector `r` and a `delta > 0` small enough that all of them stay in the hull, the eight vectors
`r + delta * sigma`, `sigma` ranging over the sign patterns in `{-1,+1}^3`.  The cone containing
a lattice point `n` is then the one whose sign pattern is the sign pattern of `n`.

The reason is visible in `Auto.term_le_pow_natAbs`.  After normalization the dyadic data obeys
`2^(n p) * |E_n| <= 1` in each coordinate, so the coordinate's contribution `2^n * |E_n| ^ rho` is
at most `2^(n (1 - p rho))`.  That decays as `n -> +infinity` exactly when `rho > 1/p` and as
`n -> -infinity` exactly when `rho < 1/p`, so the exponent must be moved off the target value
`1/p` in the direction that depends on the sign of `n`, and the two moves are available precisely
because the target is an interior point.  Summing the resulting `2^(-p delta |n|)` over the whole
lattice is the two-sided geometric series `Auto.tsum_pow_natAbs_le`.

The vertices enter one step earlier: they are what produce the restricted strong estimates at the
eight perturbed vectors, through `Auto.restrictedStrong_of_chain`.  So the formalization carries
those eight estimates as hypotheses of the assembly and leaves it to the consumer --
`thm:strong-real-improving` -- to produce them, which is exactly the division of labour the
blueprint intends.  No statement changes; what is recorded here is that "which endpoint functional
is largest" is implemented as "which sign pattern the lattice point has", the two being the same
partition for this family.

## 2026-09-13T13:31:24-04:00 - A second hypothesis `lem:finite-marcinkiewicz` needs: null slots

Alongside the monotonicity recorded earlier on this date, the assembly needs to know that a slot
which vanishes almost everywhere kills the output.  The reason is narrow and concrete.  The
expansion runs over the dyadic level sets of the inputs, and a level set can be nonempty but of
measure zero.  A restricted estimate says nothing about such a set -- its hypotheses are about sets
of finite positive measure, and at measure zero the right-hand side is zero, so the estimate would
assert that the output vanishes, which for an arbitrary trilinear operator is false.  The terms of
the expansion indexed by null level sets therefore have to be discarded on other grounds.

`Auto.Null3` is that hypothesis, in the exact form the assembly uses: if one of the three sets is
null then the operator applied to the corresponding triple of indicators vanishes almost
everywhere, hence has zero `L^q` seminorm (`Auto.eLpNorm_eq_zero_of_null3`).  It holds for the
operator the lemma is applied to: `Auto.A` integrates a product of translates, Lebesgue measure is
translation invariant, so a factor vanishing almost everywhere makes the integrand vanish almost
everywhere and the average vanish almost everywhere.

As with the monotonicity, no blueprint statement changes and `thm:main` is unaffected; the gap is
in the lemma's hypotheses, and the hypothesis is discharged where the lemma is used.

## 2026-09-13T14:00:41-04:00 - The full list of hypotheses `lem:finite-marcinkiewicz` needs beyond trilinearity

The blueprint states the lemma for "a trilinear operator".  Its proof uses four further properties,
each recorded above or here, and all four hold for the operator it is applied to.  They are now
collected in the structure `Auto.Admissible`:

- `lin`, trilinearity, the only one the statement gives;
- `mono` (`Auto.Mono3`), monotonicity on nonnegative inputs, needed because the dyadic
  decomposition is a two-sided comparison and not an identity;
- `null` (`Auto.Null3`), vanishing when a slot is null, needed because a dyadic level set can be
  nonempty and still carry no restricted estimate;
- `measInd` and `measFun`, measurability of the output on the inputs that occur, needed by the
  triangle inequality in `L^q` and by Fatou;
- `limit` (`Auto.Lim3`), continuity along monotone limits, which is what the blueprint's
  "passing to monotone limits" asks of the operator.  Without it the estimate for inputs with
  finitely many values does not reach arbitrary inputs at all: Fatou needs the outputs to converge,
  and nothing in trilinearity makes them.

None of these changes a blueprint statement and `thm:main` is unaffected.  For the averages of
`def:averages` they are all consequences of the same fact -- that `Auto.A` is `N⁻¹` times an
integral over a bounded interval of a product of translates -- through positivity, translation
invariance of Lebesgue measure, and dominated convergence respectively.

## 2026-09-13T15:23:28-04:00 - What the blueprint leaves undetermined in `lem:adjoint-gain-to-subunit`

The lemma's proof is a finite stopping-time argument.  Its outer steps are determined and are being
formalized: the reduction to `N = 1` by anisotropic dilation (already available as
`Auto.eLpNorm_Atilde_of_scale_one`), the partition into unit cubes with finite enlargements
(`Auto.unitCube`, `Auto.bigCube`, `Auto.shift_mem_bigCube`), the arithmetic of the exponents
`d_m`, `q_m`, `q_{i,m}`, and the absorption of the `2^{-m}` tail.

The selection of cubes is not determined.  Five specific things are missing.

1. "Inside each enlargement take the finite dyadic tree resolving all level sets of the three
   nonnegative simple inputs."  No finite dyadic tree resolves the level sets of an arbitrary
   nonnegative simple function -- those level sets are arbitrary measurable sets of finite measure,
   not finite unions of dyadic cubes.  Either the inputs are first replaced by dyadic step
   functions, which the proof does not say and which would need its own approximation step, or
   "resolving" means something weaker that the text does not give.

2. "call `Q` principal for the `i`-th input if its local `L^{r_i}`-mass is more than twice the
   sum of the masses of its strict descendants."  Read with "descendants" ranging over all dyadic
   subcubes, the condition is unsatisfiable: the children of `Q` already partition `Q`, so the
   masses of the descendants at each single level sum to the mass of `Q`.  Read with
   "descendants" ranging over the members of the finite family `Q`, the condition is satisfiable,
   but then which family that is depends on item 1.

3. "local `L^{r_i}`-mass" is not defined.  The integral of `|f_i|^{r_i}` over the cube and its
   average over the cube give different selections, and the sentence in item 2 is false for the
   average under either reading of "descendants".

4. "The principal cubes are nested, and the nonprincipal children have total mass at most one half
   of the parent."  Under the satisfiable reading of item 2 the second clause is a statement about
   all strict descendants, not about the nonprincipal children, and the first clause does not
   follow at all: principal cubes of a dyadic family are pairwise nested or disjoint, not nested.

5. "Iterate this operation cyclically through the three inputs.  After `m` cycles, expansion by
   positivity gives ..."  The recursion is not given: which cube is assigned to which input at
   which cycle, what "the coordinate selected by that child" means, and how the per-cube estimates
   are combined into the displayed inequality.  The later sentence "Discrete Hoelder sums the
   principal cubes because the displayed reciprocal identity is exact" names neither the index set
   nor the form of the inequality.

The standard constructions in the literature -- principal cubes in the sense of
Nazarov-Treil-Volberg, where a cube is principal when its average exceeds twice the average over
the smallest principal ancestor -- do give a correct argument of this shape, but they are not what
the text says, and choosing one of them is a mathematical decision rather than a reading of the
blueprint.  As with `lem:real-flow-jacobian`, the choice is not made here.

Consequence for the formalization: the rows "principal and nonprincipal cubes of the finite dyadic
tree" and "the cyclic stopping-time iteration" are blocked.  The determined rows around them are
proved, so that if the selection is later specified only those two rows and the final assembly
remain.  No blueprint statement is affected and `thm:main` is unaffected; the consequence is that
`cor:kosz-subunit-internal`, and with it the discharge of `Auto.KoszSubunitScaleOne`, cannot be
completed from the blueprint as written.

## 2026-09-13T18:08:09-04:00 - A missing operator in the display of `lem:fejer-vdc`

The lemma's display reads, verbatim,

  |(1/N) int_I F|^2  <=  4 int_R kappa_H(h) |(1/N) int_{I cap (I-h)} F(t+h) conj(F(t)) dt| dh
  (8H)/N .

with no operator between the `dh` and the final fraction: in the TeX source the line
`\left|...\right|\dd h` is followed directly by `\frac{8H}{N}.`.  As written the right-hand
side is a product, which is false -- letting `F` be identically one makes the left side `1` and the
right side `4 * 1 * 8H/N`, which is smaller than `1` as soon as `H < N/32`, well inside the
lemma's own range `0 < H <= N/4`.

The proof says what the operator is.  It writes the average of `F` as the average of
`(1/H) int_0^H F(t+h) dh` "up to the two boundary intervals, whose total normalized contribution is
at most `2H/N`", and finishes "after `(a+b)^2 <= 2a^2 + 2b^2`".  That is an additive error term, so
the display should read

  |(1/N) int_I F|^2  <=  4 int_R kappa_H(h) |...| dh  +  (8H)/N .

The constants are then valid, if not sharp: the square of the boundary term contributes
`2 (2H/N)^2 = 8H^2/N^2`, which is at most `2H/N` in the lemma's range and so certainly at most
`8H/N`, and the Cauchy-Schwarz term needs only the factor `2`.

The formalization uses the additive reading.  No other statement is affected; this is a typographical
slip rather than a gap in the argument, and it is recorded only because the literal display is false.

Resolved at 2026-09-13T20:57:21-04:00.  `Auto.fejer_vdc` proves the additive reading verbatim, for
`I = (c, c + N]`, `0 < H <= N/4` and measurable `F` of modulus at most one:

  ‖N⁻¹ • ∫ t in c..(c + N), F t‖ ^ 2
    ≤ 4 * (∫ h : ℝ, fejer H h * ‖N⁻¹ • capPair F c N h‖) + 8 * H / N

where `Auto.capPair F c N h` is the integral of `F(t+h) conj(F t)` over `Auto.capSet c N h`, defined
as `Ioc c (c+N) ∩ Ioc (c-h) (c+N-h)` -- that is, over `I ∩ (I - h)` exactly as the display asks.
The constants come out as the entry predicted: the Cauchy-Schwarz term is produced with the factor
`2` and relaxed to `4`, and the boundary contributes `4H/N + 8H^2/N^2 <= 6H/N <= 8H/N` in the
lemma's range.  Nothing in the statement had to be weakened.

## 2026-09-13T21:28:34-04:00 - Patch 1 resolves the block in `lem:real-flow-jacobian`

The user supplied `blueprints/patch_1.tex`, a 744-line document that replaces the four-sentence
proof at lines 1889--1895 of the main blueprint and corrects the lemma's statement.  It answers
each of the four items of the entry of 2026-09-12T17:55:40-04:00, and it is authorized as a
blueprint source alongside `blueprints/task_2_smoothingineq3d_blueprint_updated.tex`.

1. *Which density at which move.*  Patch `lem:transition` and `rem:which-density`: the fibre of the
   move leaving label `a` has measure at least `c_{r,a} alpha_a N`.  The density is the one attached
   to the set being **left**; the label being entered plays no part in the size of the fibre and
   only decides whether a refinement level is consumed.

2. *The six signs.*  Patch `def:flow`: with the convention `Gamma_0 = 0`, the displacement of the
   move `(w_{l-1}, w_l)` is `Gamma_{w_{l-1}}(t_l) - Gamma_{w_l}(t_l)`, so the sign is `+` on the
   block being left and `-` on the block being entered.  This makes all four labels uniform and
   removes the three-case split.

3. *Six moves over sixty stages.*  Patch `lem:levels`: a level is consumed exactly at the moves
   `a -> b` with `a < b`, of which each of the three itineraries has three.  Levels run
   `60, ..., 57`, so the only quantitative role of the depth is the uniform bound
   `c_{lambda_l, i} >= 2^{-240}`.  Six moves do not distribute over sixty stages; they consume
   three.

4. *Block lower triangular versus block diagonal.*  Patch `lem:parity`: an itinerary all of whose
   moves touch `E_0` has `n_i(w) = #B_i`, and `(d_1,d_2,d_3) = (1,2,3)` then forces
   `{w_0, w_6} = {1,3}`.  So the blueprint's word `(1,0,2,0,3,0,3)` cannot terminate at `j' = 2`;
   for that terminal index one must use `w^{(2)} = (1,3,0,3,2,0,2)`, whose moves 1 and 4 have both
   endpoints nonzero, and the derivative is then block lower triangular but not block diagonal.

**Statement change.**  The patch's `rem:statement-correction` records that the main blueprint's
"harmless relabelling that sends `j` to the distinguished slot and `j'` to the terminal slot" is
not harmless: the degrees `(1,2,3)` are attached to the coordinates, not to the function slots, and
`L_N` has no symmetry exchanging two slots of different degree.  The corrected lemma
(`lem:real-flow-jacobian-fixed`) is stated with lower triangularity, with block diagonality
asserted only for `j' in {1,3}`.  The starting index stays free, and the downstream use in
`prop:restricted-improving-vertex` needs only that the terminal set is `E_{j'}`, so all six ordered
pairs `(j, j')` are still supplied.  This is a change to a blueprint statement, made on the user's
explicit instruction of 2026-09-13T21:28:34-04:00.

**Effect on the ledger.**  Every analytic ingredient named in the entry of 2026-09-12T17:55:40-04:00
is already proved, so what the patch unblocks is the assembly.  The row
"`lem:lossless-refinements`, iterating the stage to depth 60" is unblocked: patch
`def:refinements` gives the explicit tower with `c_{r,i} = 2^{-(4(r-1)+i+1)}` and patch
`lem:nonempty` its nonemptiness.  The three open rows of `prop:restricted-improving-vertex` are
likewise determined, through patch `lem:integrated`, which supplies the exponent `10 = 1+3+6` and
the constant `2^{-2455}`.

One caveat carried forward: the existing flow machinery in the Lean file
(`Auto.flowMap`, `Auto.det_flowDeriv`, `Auto.flowMap_injective_cover`) is built for the block
structure `B_1 = {0}`, `B_2 = {1,2}`, `B_3 = {3,4,5}`, which is the one of `w^{(3)}` and `w^{(1)}`.
The block lower triangular case `w^{(2)}` needs a second flow map; it is a separate row.

## 2026-09-13T22:19:25-04:00 - The pre-patch flow map does not match any admissible itinerary

While formalizing patch 1 `lem:jacobian` it became clear that the flow map already in the file,
`Auto.flowPi`, is not the flow of any admissible itinerary, under either sign convention.  Its
three blocks are

  block 1: `-(s 0)`
  block 2: `s 1 - s 2`, `s 1 ^ 2 - s 2 ^ 2`
  block 3: `-(s 3 - s 4 + s 5)`, `-(s 3 ^ 2 - s 4 ^ 2 + s 5 ^ 2)`, `-(s 3 ^ 3 - s 4 ^ 3 + s 5 ^ 3)`

so the signs of the three block-3 moves are `-, +, -`.  In the convention of `Auto.transSet`, where
the displacement of the move `(a, b)` is `Gamma_b - Gamma_a`, a move *leaving* a block contributes
`-Gamma` and a move *entering* it contributes `+Gamma`; so `-, +, -` reads leave, enter, leave, and a
word whose last block-3 move leaves block 3 does not end at the label 3.  Under the patch's own
convention the signs are reversed throughout and block 1 then fails instead.  The block-3 signs of
the patch's word `w^(3) = (1,0,2,0,3,0,3)` are `+, -, +`, the negatives of `Auto.flowPi`'s.

Nothing is wrong with `Auto.flowPi` as a piece of algebra: its determinant
(`Auto.det_flowMatrix`, `Auto.det_flowDeriv`) and its injective cover
(`Auto.flowMap_injective_cover`) are correct statements about it, and they were proved before the
patch determined the word.  What they are not is statements about the flow the patch prescribes.
Since the two maps differ by negating the last three coordinates -- an isometry of determinant
`-1` -- the Jacobian in absolute value and the multiplicity are the same; but the identity
`det = 12 (u-v)(a-b)(a-c)(b-c)` acquires a minus sign, and the flow that must be shown to land in
`E_{j'}` is the patch's, not this one.

The consequence for the formalization is that the Jacobian and multiplicity rows are rebuilt for
the patch's words rather than reused verbatim.  This changes no blueprint statement: patch
`lem:jacobian` asserts `|det D Phi| = 12 |u-v| |a-b| |a-c| |b-c|`, in absolute value, which is what
both maps satisfy.

## 2026-09-14T15:17:45-04:00 - `lem:adjoint-gain-to-subunit`: the three blocked rows are resolved by patch 2, and the blueprint's abstract implication is false

`blueprints/patch_2.tex` (user-supplied, authorized 2026-09-14T15:17:45-04:00) resolves the block recorded on
2026-09-13T15:23:28-04:00.  It confirms the two readings flagged there and adds a third, decisive
point that the entry did not reach.

**The lemma as stated in the blueprint is false.**  Patch 2 exhibits a counterexample to the
abstract implication "a positive scale gain for the `j`-adjoint gives a balanced subunit estimate
for the average".  Take the equal-linear corner averages
`B_N(f)(x) = N^{-1} int_0^N prod_i f_i (x + t e_i) dt`, which satisfy the degree restriction.  The
four-dimensional Loomis-Whitney inequality (via the unit-determinant substitution
`x = (-z_1,-z_2,-z_3)`, `t = z_0+z_1+z_2+z_3`) gives the adjoint bound
`|S_N(g)|_2 <= N^{-3/4} prod_i |g_i|_4`, so the reciprocal sum of the adjoint exponents is
`3/4` and the scale gain is strictly positive.  Yet no balanced subunit estimate holds for
`B_1`: with `E_delta = {x in [-2,2]^3 : 0 <= x_1+x_2+x_3 <= delta}` and `f_i = 1_{E_delta}`, the
average equals `delta` on the fixed cube `[-1/4,-1/8]^3`, while `|E_delta| <= 16 delta`, so an
estimate with `B = sum_i 1/q_i > 1` would force `delta |U|^{1/q} <= C (16 delta)^B` for all small
`delta`.

**What replaces it.**  Patch 2 keeps the historical label but specializes the statement to the
actual monomial system, and proves it directly rather than through the adjoint gain: the
upper-half monomial average at scale one satisfies
`|Atilde_1 (f_1,f_2,f_3)|_{8/9} <= C_j prod_i |f_i|_{p_i}` with `p_j = 2` and the other two
exponents `8/3` and `4`, so `sum_i 1/p_i = 9/8 = 1/q` for `q = 8/9`.  The route is: three
measurable refinements of the three sets with thresholds `1/2, 1/4, 1/8` in the order `1, d, 1`;
an explicit three-step parameter tower with fibre separation; an explicit polynomial flow whose
Jacobian is `6 w^2 |u-v|` or `6 w (u+v) |u-v|` and which is injective off the diagonal `u = v`;
the injective change of variables; finite value-level summation in place of a general
restricted-weak interpolation; and fixed-scale cube localization.  No stopping-time selection,
no principal cubes, and no spatial dyadic resolution occur.

Sections 1 and 2 of the patch give local repairs of the two readings flagged on
2026-09-13T15:23:28-04:00, and are not needed once Section 3 is used.  Patch 2 states explicitly
that the mass contraction the old proof assumed does not follow: the proved contraction is for
Lebesgue volume, not for the analytic remainder.

## 2026-09-14T22:03:08-04:00 - `lem:pet-reduction`: the PET step must difference against a polynomial of *smallest* degree, not largest

The proof of `lem:pet-reduction` says: "Choose a polynomial of largest degree and apply
`lem:fejer-vdc`; translate so that this polynomial becomes zero.  Every other polynomial `Q` is
replaced by `Q(t+h) - P(t)` and `Q(t) - P(t)`.  If `Q` has the same leading coefficient as `P`,
its degree drops; otherwise the number of top-degree leading classes drops after the selected
factor is removed by Cauchy-Schwarz."

**With `P` of largest degree the weight need not decrease.**  Take the system `{t, t^2}`, whose
weight is `(w_2, w_1) = (1, 1)`, and difference against `P = t^2`, the polynomial of largest
degree.  The new family is

  `Q(t+h) - P(t) = -t^2 + t + h`,   `Q(t) - P(t) = -t^2 + t`   (from `Q = t`),
  `P(t+h) - P(t) = 2 h t + h^2`   (from `P` itself; `P - P = 0` is dropped).

Its degrees are `2, 2, 1`, the two degree-two members share the leading coefficient `-1`, so
`w_2 = 1`, and `w_1 = 1`.  The new weight is `(1, 1)`, equal to the old one: no decrease, and the
induction does not terminate.

The failure is structural, not an artefact of the example.  When `P` has the largest degree `D`,
every member `Q` of degree strictly below `D` produces `Q(t) - P(t)` of degree exactly `D`, with
leading-coefficient class `-lead_D(P)`.  That class is new -- it is not the shift of any class of
the original family, because a member of degree exactly `D` never has leading vector zero -- so
the top-level class count can be replenished as fast as it is drained.

**The correct rule is to difference against a polynomial of smallest degree `m`**, which is the
rule of the standard PET induction.  Then for every `Q` of degree `d > m` both replacements have
degree exactly `d` and the leading coefficient of `Q` (shifting does not move a leading
coefficient), so `w_d` is unchanged for every `d > m`; at level `m` the classes become
`{lead_m(Q) - lead_m(P)}` over those `Q` of degree `m` with `lead_m(Q) != lead_m(P)`, which is
the old class set with the class of `P` removed and then translated, so `w_m` drops by exactly
one.  New members of degree below `m` may appear, but they are less significant in the
lexicographic order read from the top.  On the example above, differencing against `P = t` gives
`{t^2 + (2h-1) t + h^2, t^2 - t}` with weight `(1, 0) < (1, 1)`.

**Consequence for the formalization.**  No blueprint statement changes: `lem:pet-reduction` is
asserted for the fixed system `t, t^2, t^3` and its conclusion is untouched.  Only the choice of
the differencing polynomial inside its proof is corrected, from largest to smallest degree.  The
Lean development therefore selects a member of minimal degree, and the descent is proved in that
form.

## 2026-09-15T11:35:11-04:00 - `lem:pet-reduction`: the headed turn is a true inequality but still does not descend, and why

**What I claimed.**  The Status entries of 2026-09-15T10:27:58-04:00 and 2026-09-15T10:41:33-04:00
said that carrying a *head* repairs the defect of 2026-09-14T23:30:27-04:00, and in particular that
with `Auto.exists_head_descent` "the family shrinks at each step" and "the survivors are exactly
the members `Auto.petStep` keeps".  **That is wrong**, and the correction is recorded here.

**What is actually true.**  Every statement proved on 2026-09-15 is a correct inequality; none of
them is false and none needs to be removed.  But `Auto.exists_head_descent` maps a configuration
indexed by `iota` to one indexed by `iota x Bool`, with translations `Auto.dcfgTransl gamma h`,
namely `translShift (gamma a) h` and `gamma a`.  By `Auto.translDeg_translShift` and
`Auto.leadVec_translShift` those have exactly the degrees and the leading-coefficient classes of
the original `gamma a`.  So the translation set is unchanged up to duplication and

  `petWeight` is **invariant** under the turn.

The head that the turn sheds is `Auto.dHead`, a fresh `Auto.unitPhase` factor.  Shedding it removes
nothing from the polynomial family: it only undoes the modulus that the previous step introduced.
The index type therefore grows `|iota| -> 2|iota|` every turn and the combinatorial half
(`Auto.petWeight_step_lt`, `Auto.petStep_terminates`) never applies.  This is the same defect as
2026-09-14T23:30:27-04:00 relocated, not repaired; the hope recorded on 2026-09-14T23:52:39-04:00
that the unimodular bridge would let the family shrink is not borne out.

**The root cause, stated exactly.**  `Auto.sq_norm_cfgAvg_le'` applies van der Corput *pointwise in
the point* `x`, so the modulus it produces sits inside the integral in `x`.  Two operations of the
blueprint's step are unavailable on the far side of that modulus, and they are precisely the two
that make the weight drop:

* the translation `x -> x - Gamma_P(t)` depends on the parameter, so it cannot pass through a
  modulus taken pointwise in `x`.  Without it there is no normalization, and without normalization
  no member acquires the zero translation;
* consequently the factor the next Cauchy-Schwarz removes is never a *member* of the family, only
  the phase factor that the modulus itself created.

**The repair.**  Take the modulus only *after* the integral in the point.  Concretely, apply van
der Corput to the `L^2(E3)`-valued average `t -> cfgProd(., t)` rather than to the scalar
`t -> cfgProd(x, t)` for each fixed `x`.  The inner product of two such vectors is
`int_x cfgProd(x, t+h) conj(cfgProd(x, t)) dx`, so the parameter average of those inner products is
`Auto.cfgInt` of the differenced family -- the point integral running over all of `E3`, with no
modulus anywhere inside it.  In that form:

1. `Auto.cfgInt_translSub` normalizes by the selected translation `P` of smallest degree (it is
   valid exactly because the point integral is over all of `E3`);
2. after normalizing, the member whose translation was `P` carries the zero translation, so by
   `Auto.cfgInt_cons` it *is* the next head -- a genuine member of the family, one-bounded and,
   since every member function is a conjugate of one of the original `f_i`, supported in the box;
3. the members whose translation became constant merge into that head by `Auto.cfgHeadInt_merge`;
4. the surviving nonconstant translations are exactly `Auto.petStep h P`, so `petWeight` drops and
   `Auto.petStep_terminates` bounds the number of turns.

The missing ingredient is therefore one lemma: **the van der Corput inequality for a Hilbert-space
valued average**, with `H = L^2(E3)`.  The scalar `Auto.fejer_vdc` and `Auto.fejer_vdc'` are that
statement for `H = C`, and their proof uses nothing about `C` beyond its inner product, so the
generalization is a reproving rather than a new idea.

**Disposition of the 2026-09-15 work.**  Kept and needed on the corrected route:
`Auto.cfgHeadInt` with `Auto.norm_cfgHeadInt_le` and `Auto.sq_norm_cfgHeadInt_le` (the shedding
Cauchy-Schwarz is unchanged); `Auto.cfgCons`, `Auto.translCons`, `Auto.cfgProd_cons`,
`Auto.cfgInt_cons` (head as member, which is step 2 above); `Auto.constFactor` and
`Auto.cfgHeadInt_merge` (step 3); the cube family and `Auto.cfgProd_cube`, `Auto.cfgAvg_cube`,
`Auto.cfgHeadInt_cube` (the endpoint); `Auto.Lambda_eq_cfgHeadInt` and its companions (the entry
point).  True but on the superseded route, kept in the file as `Auto.cfgL2_step` and
`Auto.exists_iterated_descent` already are: `Auto.cfgL1` and its bookkeeping,
`Auto.cfgL2_le_fejer_cfgL1`, `Auto.exists_shift_cfgL1_ge`, `Auto.dHead` with
`Auto.cfgHeadInt_dHead`, `Auto.exists_shift_cfgHeadInt_ge`, `Auto.exists_head_descent`,
`Auto.headBound`, `Auto.exists_iterated_head_descent`, `Auto.exists_iterated_descent_of_Lambda`.

No blueprint statement changes, and no proved statement is retracted.  What changes is the route
and the ledger annotations for the three rows that asserted the shrinking.

### Addendum, 2026-09-15T11:46:00-04:00: the "normalize later" workaround also fails

Before building the Hilbert-valued van der Corput I checked the one cheap alternative: keep the
pointwise-modulus step, convert its output to a headless `Auto.cfgInt` with the unimodular bridge
and `Auto.cfgInt_cons`, and only then normalize.  It does not work, for a reason worth recording
because it is the same phenomenon as the largest-degree defect of 2026-09-14T22:03:08-04:00.

After the differencing the translations are `Auto.dcfgTransl gamma h`, and the phase member carries
the zero translation.  Choosing `P = gamma_{a_0}` of minimal degree `m` and normalizing sends the
family to `{gamma_a(t+h) - P(t), gamma_a(t) - P(t)}`, which is exactly `Auto.petStep h P`, *plus*
the phase member, whose translation becomes `0 - P = -P`, of degree exactly `m`.

At level `m` the petStep analysis removes the class of `P` and translates the rest, giving
`w_m - 1` classes.  The phase member contributes the class `-lead_m(P)`, which is the translate of
the class `0`; no member of degree exactly `m` has zero leading vector, so `0` was not among the
old classes and `-lead_m(P)` is genuinely new.  The count returns to `w_m`: **no descent**.  Nor
does deferring help -- shedding the phase at the next turn removes that class but the next step
creates a fresh phase in the same way.

So the phase member exactly replenishes the class the step removes, which is the structural
obstruction described for the largest-degree choice.  There is no ordering of normalization and
modulus that avoids it: the modulus must not be taken pointwise in the point at all.  This confirms
the conclusion above from a second, independent direction.

## 2026-09-15T13:16:11-04:00 - `Auto.CfgSupported` is not preserved by the normalization, and the invariant that is

Checking the support hypothesis against the iteration, before assembling the turn, shows that the
notion I introduced on 2026-09-15T11:43 does not survive one turn.  No blueprint statement is
affected and no proved statement is wrong; the definition is simply the wrong invariant to carry.

**The definition.**  `Auto.CfgSupported B g gamma` says `cfgProd g gamma x t = 0` for every `x`
outside `B` **and every real `t`**.

**Where it fails.**  By `Auto.cfgProd_translSub`,
`cfgProd g (gamma - P) x t = cfgProd g gamma (x - translAct P t) t`, so the normalized
configuration is supported where `x ∈ B + translAct P t`.  For nonconstant `P` the displacement
`translAct P t` is unbounded in `t`, so no fixed `B'` works.  The same failure affects shedding:
after Cauchy-Schwarz removes the head, the reduced family need not be supported in any fixed set,
since the head may have been the only compactly supported factor.

Both are preserved in the *intended* argument for a reason the definition does not record: the
parameter only ever ranges over a bounded interval.  Every integral in the chain runs over
`t ∈ [0, N]` with shifts in `[0, H]`, `H <= N`.  Over a bounded parameter range,
`translAct P t` is bounded and the support simply grows by a controlled amount -- which is the
blueprint's own bookkeeping, where the box `I_N(C)` is enlarged from step to step by increasing the
constant `C`.

**The invariant that is preserved.**  Not a property of the product but of the members: *every
member function is supported in a fixed bounded set*, together with a bounded parameter range.
From those two, for any nonempty family and any chosen member `a`, the product is supported in
`Bmem - translAct (gamma a) t`, which over a bounded range of `t` lies in a fixed bounded set.  That
invariant survives every operation of the turn: differencing keeps the same functions up to
conjugation, normalization changes only the translations, merging multiplies translates of members
into the head, and shedding only removes members.

**The fix.**  `Auto.CfgSupported` acquires a parameter set: `CfgSupported T B g gamma` says the
integrand vanishes off `B` for every `t ∈ T`.  Each lemma that consumes it -- there are about
twelve, from `Auto.cfgPair_eq_setIntegral` to `Auto.exists_shift_cfgInt_ge` -- gains the
hypothesis that the parameters it evaluates the pairing at lie in `T`; in every call site they do,
since they are `t`, `t + a`, `t + b` with `t ∈ [0, N]` and `a, b ∈ [0, H]`, so `T = [0, 2N]`
suffices.  A constructor then produces `CfgSupported` from the member-support invariant.

Nothing proved is retracted: every statement carrying the present `Auto.CfgSupported` remains true,
and the refactor only weakens its hypothesis, so the proofs transfer.  The work is mechanical.

## 2026-09-15T13:57:18-04:00 - The endpoint of the PET recursion is asserted, not proved, in the blueprint

Source study of the step that turns the terminated PET recursion into a local uniformity norm,
carried out before building the turn assembly on top of it.  This is not yet a blocker and nothing
is retracted, but it is the step most likely to become one, and the analysis is recorded now so the
decision is not taken under time pressure later.

**What the blueprint supplies.**  `lem:fejer-vdc` states the van der Corput inequality proper, which
is proved and formalized (`Auto.fejer_vdc'`).  Its *last assertion* is the whole reduction:

> Repeated use of this inequality followed by Cauchy-Schwarz in all variables except a selected
> function bounds every polynomial average obtained from the monomials `t, t^2, t^3` by a finite
> power of a local uniformity norm of that selected function, plus a boundary error.

and its proof is four sentences: expand one copy of the average and its conjugate after each
application; translations preserve Lebesgue measure; every unselected factor has modulus at most
one and Cauchy-Schwarz removes it; "an induction on the number of applications gives exactly the
cube product in `def:local-uniformity`".

**What is missing.**  That the endpoint is *exactly* the cube product is asserted, not shown.  The
cube product of `def:local-uniformity` differences a single function along a single axis `e_j`, with
shifts `omega . h`.  For the induction to land there, the concrete run of the recursion on
`{t, t^2, t^3}` must end with one surviving member whose translation is linear and directed along
`e_j`; only then does the Gowers step produce `cubeShift h omega . e_j`, which is what
`Auto.cubeTransl` encodes and `Auto.cfgHeadInt_cube` bridges.

The concrete run is not obviously so.  The monomial translations `Auto.curveTransl` each live in a
*single* coordinate -- `gamma_0 = (t,0,0)`, `gamma_1 = (0,t^2,0)`, `gamma_2 = (0,0,t^3)` -- but the
normalization subtracts the selected `P` from all of them, so after the first turn every member
carries a component in `P`'s coordinate and the members no longer live in one coordinate each.
Which member survives, and in which direction its final translation points, is exactly the
bookkeeping the blueprint compresses into "an induction on the number of applications".

**A related mismatch, noted so it is not mistaken for a defect.**  The blueprint says the recursion
"terminates at linear polynomials", whereas `Auto.petStep_terminates` runs to the empty family,
i.e. until every translation is constant.  These are consistent -- differencing a linear
translation makes it constant, so the empty family is reached by continuing through the Gowers
steps -- but they place the cube at different points.  Reaching the empty family makes the
configuration average parameter-free (`Auto.cfgAvg_of_constant`), which is a product of fixed
translates and *not* a local uniformity norm unless the surviving members are the cube family.  So
the identification cannot be read off from termination alone; it needs the concrete run either way.

**Assessment.**  The step is standard PET/Gowers and there is no reason to think it false; the gap
is that the concrete endpoint bookkeeping is not supplied.  This is the same shape as the two
earlier blocked items, which were resolved by user-supplied `blueprints/patch_1.tex` and
`blueprints/patch_2.tex`.  If the assembly reaches the endpoint and the identification cannot be
derived from the material present, the honest outcome is to report and request a patch for this
step rather than to invent the bookkeeping.

**Effect on the plan.**  None yet.  The turn assembly is required however the endpoint is
identified, so work continues there; the endpoint is the last piece and will be attempted with the
material available before any request is made.

## 2026-09-15T14:20:11-04:00 - Correction: the weight of `Auto.petStep` DOES depend on the shift

In the Status entry of 2026-09-15T14:16:31-04:00 I claimed that "the *weight* of `Auto.petStep h P S`
does not depend on `h` at all, because shifting a polynomial preserves its degree and its leading
coefficient", and proposed running the combinatorial recursion first, at `h = 0`, to obtain the
number of turns.  **The claim is false** and the proposal built on it is withdrawn.

**Counterexample.**  Take `S = {t^2}` and `P = t^2`.  Then

  `petStep h P S = {translSub (translShift q h) P, translSub q P : q ∈ S}` filtered to positive degree
                 = `{(t+h)^2 - t^2, t^2 - t^2}` filtered
                 = `{2ht + h^2}` when `h ≠ 0`, and `∅` when `h = 0`,

since `2ht + h^2` has degree one for `h ≠ 0` and degree zero for `h = 0`.  So
`petWeight (petStep h P S) = (0,0,1)` for `h ≠ 0` and `(0,0,0)` for `h = 0`.

**Where the reasoning went wrong.**  Shifting preserves the leading coefficient *at the top degree of
that polynomial*, which is what `Auto.leadVec_translShift` says, and it requires `translDeg q ≤ d`.
After subtracting `P` the top terms can cancel, and then lower coefficients -- which shifting does
move, since `Auto.translShift` is a Taylor expansion -- become the leading ones.  The hypothesis of
`Auto.leadVec_translShift` is exactly what fails in that case.  Nothing proved is affected; the
error was in an unproved remark.

**Why it does not matter, and what the blueprint actually prescribes.**  The remark was made to solve
a problem that does not exist.  I had assumed a single `H` fixed before the induction, which would
indeed need the number of turns in advance.  The blueprint does not do that.  Its proof of
`lem:pet-reduction` says:

> At each use of van der Corput take `H = c delta^C N` **in the current normalized parameter**.  The
> boundary error in `lem:fejer-vdc` is then at most half the current lower bound after enlarging `C`.

So `H` is chosen afresh at every step, from the current lower bound, and the smallness condition is
discharged step by step.  No uniform bound on the number of turns is needed, and the shift
dependence of the weight is irrelevant.  The same paragraph adds "in Lean they can be implemented by
primitive recursion on the weight triple", which is the structure to follow.

Operative effect: `Auto.exists_shift_cfgInt_of_cfgHeadInt` takes `H` as a parameter, so the induction
instantiates it per turn from the current `beta`.  The quantifier-ordering worry recorded on
2026-09-15T14:16:31-04:00 is withdrawn along with the false remark.

## 2026-09-15T15:07:51-04:00 - BLOCKED: the PET endpoint. The selection of the surviving function is not supplied

The recursion of `Auto.exists_constant_endpoint` now runs to completion, and with it the analytic
and combinatorial halves of `lem:pet-reduction` are joined.  The remaining step cannot be derived
from the material present, and this entry states precisely what is missing and why.

**What the recursion produces.**  Each turn sheds the head by Cauchy-Schwarz
(`Auto.sq_norm_cfgHeadInt_le`), differences the rest, normalizes by the selected translation, and
merges the members whose translation became constant into the new head
(`Auto.cfgHeadInt_of_cfgInt_normalized`).  At the end the family is empty and the conclusion is a
lower bound on `int_x u`, where `u` is the accumulated head: a product of conjugated, translated
copies of the *original* functions -- all four of them.

**What is needed.**  `lem:pet-reduction` concludes, for **every** `j`, a lower bound on
`U^{s_*}_{j,H_j}(f_j)`: the local uniformity norm of a *single, designated* `f_j`, differenced along
the single axis `e_j`, with the cube shifts `omega . h` of `def:local-uniformity`.  So the endpoint
must be a cube product of one designated function, not an unstructured product of all four.

**Why the gap is real.**  In the recursion the factor that is shed at each turn is the head, and the
factor that becomes the next head is the one whose translation has minimal degree -- a choice made by
the *combinatorics of the translations*, with nothing selecting a particular `f_j`.  The blueprint's
argument is different: the last assertion of `lem:fejer-vdc` says the bound follows from "repeated
use of this inequality **followed by Cauchy-Schwarz in all variables except a selected function**".
That selection -- keeping the copies of `f_j` and discarding the others at each application -- is the
mechanism that makes a single function survive, and it is exactly what is not spelled out.  Its
proof is four sentences ending "an induction on the number of applications gives exactly the cube
product", with no account of which factor is kept, why the surviving translations are
`cubeShift h omega . e_j`, or how the conjugation pattern `conjPar (numFalse omega)` arises.

A second, related point, already noted on 2026-09-15T13:57:18-04:00: the blueprint terminates the
recursion "at linear polynomials" and then applies a final Cauchy-Schwarz, whereas the weight
descent `Auto.petStep_terminates` runs to the empty family.  The two endpoints are different
objects, and only the blueprint's -- a single function with a linear translation, to which the
iterated van der Corput `Auto.exists_vdc_iterate` then applies -- yields the cube.

**What a patch would need to supply.**  A proof of the last assertion of `lem:fejer-vdc` for the
system `t, t^2, t^3`, concretely enough to formalize:

1. which factor is selected and kept at each application, so that only copies of the designated
   `f_j` survive, and why the discarded factors can be removed by Cauchy-Schwarz without destroying
   the lower bound;
2. that the recursion is to be stopped when the surviving translation is linear along `e_j`, and the
   form of that translation;
3. the identification of the resulting product with the cube of `def:local-uniformity` -- the shifts
   `cubeShift h omega` and the parity conjugations -- which in Lean is `Auto.cfgHeadInt_cube`,
   already proved and waiting for its input;
4. the accounting of the powers of `delta` and the resulting range for `H_j`.

Everything else for `lem:pet-reduction` is proved: the turn, its iteration, the endpoint bridge, the
`delta` iteration lemma `Auto.exists_pow_iterate`, and the passage to the norm
`Auto.le_locUnif_of_le_pow`.

**Effect on the plan.**  `lem:pet-reduction` is blocked at this step.  It is *not* a discrepancy
requiring a change to a main result -- no statement is wrong -- so work continues on the ledger rows
that do not depend on it.  The next such row is `lem:degree-lowering-zero`, whose statement is about
local uniformity norms under the hypotheses of `lem:pet-reduction` and whose proof is independent of
how `lem:pet-reduction` is established, followed by the Part VI rows.

## 2026-09-15T15:43:29-04:00 - Patch 3 arrives: the terminal step is supplied, the every-`j` input producer is not

`blueprints/patch_3.tex` replaces blueprint lines 2183 and 2193, the two spots recorded as blocked
on 2026-09-15T15:07:51-04:00.  It answers the request in full for the step that was asked about, and
it also narrows the claim that can be made, which is recorded here so the row's status is not
overstated later.

**What it supplies.**  A terminal-configuration theorem.  Given an affine configuration

  `A_0 = V^{-1} int_{R^3} E_{t in I} prod_{i=0}^m g_i(x + a_i t e_j) dx`,

with all `g_i` one-bounded, `int |g_i|^2 <= V`, the protected input `g_m = f` supported in a box of
volume `V = B S` with `j`-th side `S`, and **distinct slopes** `a_m != a_i` for `i < m`, it proves

  `|A_0|^{2^{m+1}} <= c_{m+1} ( R (N^6/V) locUnifPow(f; j, L, m+1) + m^2 H/N )`

with `L_i = |a_m - a_i| H`, `L = 2 max{S, L_0, ..., L_{m-1}}`, `R = (1 + L/S) prod_{i<m} 2L/L_i`,
`c_r = 2^(2^r - 1)`.  The proof is given in five explicit stages with the removal order fixed as
`0, 1, ..., m-1`, the removed block at stage `r` being the `2^r` descendants of the nuisance input
`g_r`, and no block carrying `g_m` ever removed.  That is precisely the selection mechanism whose
absence was the block.

**Three points where it corrects me.**  First, "being linear is not, on its own, the required
hypothesis" -- the hypothesis is *affine with the protected input alone in its slope class*, which
is sharper than the "terminates at linear polynomials" reading I had taken from the original.
Second, it confirms independently that "a new theorem about Hilbert-valued van der Corput is not
necessary", which matches the finding recorded on 2026-09-15T12:00:56-04:00.  Third, it warns
against two things I might have reached for: deleting the absolute value in `Auto.fejer_vdc'` to get
the one-step inequality, and dominating kernels pointwise against a complex cube integrand before
the positivity identity is in place.

**What it does not supply, in its own words.**  "The proof below supplies the missing *analytic
terminal step*; it does not assert that the current proof of `lem:pet-reduction` already constructs
its input for every `j`."  And in its closing Source boundary paragraph: the underlying paper's
PET-to-box results (Lemma 4.43, Theorem 4.45) concern the *highest-degree* input, general selected
inputs needing the further reduction of its Section 4.3.1, so "the supplied files therefore do not
justify declaring the every-`j` assertion proved merely by adding this terminal lemma".

**Consequence for the ledger.**  `lem:pet-reduction` becomes *partially* unblocked.  The terminal
step is now formalizable; the input producer -- affine terminal data for every `j`, with the
protected function identified, nonzero slope gaps and their quantitative bounds -- is not supplied
and remains open.  The row must not be marked proved on the strength of the terminal lemma alone.
The patch also prescribes the replacement wording for the affected sentence of `lem:pet-reduction`,
which makes the division of labour explicit.

**Plan.**  Formalize the terminal theorem along the patch's own node names: the block recursion
(`headBlock_succ`, `headBlock_cube`, `headBlock_norm_le`, `linearStage_norm_le_one`), the removal
step (`cs_remove_slope_block`), the error induction (`linearStages_le_mixedCube`), and the
single-scale comparison (`uniformTranslateAverage_normSq_eq_fejer`,
`cubeIntegral_sq_le_nextDifference`, `fejerKernel_le_larger`, `mixedCube_sq_le_locUnifPow`,
`linearHead_le_locUnifPow`), finishing at the existing `Auto.cfgHeadInt_cube`.  Work in progress on
`lem:degree-lowering-zero` is paused at a clean point and resumes after.

## 2026-09-15T18:41:00-04:00 -- a verification that did not verify (self-correction #5)

**What I reported.**  At 2026-09-15T17:39:56-04:00 I recorded the file as clean at 25450 lines,
"no errors, no warnings", and cited a passing `lake build`.

**What was true.**  Three genuine elaboration errors were standing in the file at that moment:

- `Auto.sq_integral_mul_le`: `pow_eq_zero_iff (two_ne_zero).mp h2` parses as
  `pow_eq_zero_iff ((two_ne_zero).mp) h2` -- the projection binds to `two_ne_zero`, not to the
  `Iff`.  Replaced by `sq_eq_zero_iff.mp h2`.
- `Auto.sq_norm_integral_le_measure_mul` and `Auto.integrable_of_bdd_support`:
  `(integrable_const c).integrable_indicator hs`.  Dot notation resolves on the head constant of
  the *stated* type; `integrable_const` states `Integrable`, while `integrable_indicator` lives in
  the `IntegrableOn` namespace, so Lean unfolded `Integrable` to its `And` and looked for
  `And.integrable_indicator`.  Replaced by `(integrable_indicator_iff hs).mpr (integrable_const c)`.
  (The file already contained the working idiom at two other places -- ascribe `IntegrableOn`
  first -- so this was an inconsistency, not a missing lemma.)

**Why the check missed them.**  The verification command was

    lake env lean <file> ... ; echo "sorry: $(grep -c sorry <file> || true)" ; wc -l <file>

It printed the `sorry` count and the line count but never inspected `lake env lean`'s own output,
and `lake env lean` exits 0 on elaboration errors.  The corroborating `lake build` proves nothing
about this file at all: `DFR/Auto` is deliberately excluded from `lakefile.toml`, so `lake build`
never compiles it.  Two signals, neither of which was measuring the thing I claimed.

**Rule.**  A verification claim must quote the compiler's own diagnostics.  From here the check is

    lake env lean <file> 2>&1 | grep -E '\.lean:[0-9]+:[0-9]+: (error|warning)'

with the *absence of output* as the evidence, and `lake build` is never cited as evidence about an
`Auto` file.

**Scope.**  The three errors were confined to their own declarations; nothing downstream consumed
them, so no other proof was resting on a false lemma.  Re-verified after the fixes: no error, no
warning, and `#print axioms` on the affected declarations gives exactly
`[propext, Classical.choice, Quot.sound]`.

## 2026-09-15T22:05:00-04:00 -- `blueprints/patch_3_updated.tex` supersedes `patch_3.tex`, and
## deletes `lem:degree-lowering-zero`

The user supplied `blueprints/patch_3_updated.tex` (1862 lines, MD5
8190ab6c754a2619b45f6cfcab5e2007) to replace `blueprints/patch_3.tex` and repair the original
blocked passages at blueprint lines 2183 and 2193.  Recorded in `automation/instructions.md` at the
same timestamp.  `patch_3.tex` is superseded and is not to be used.

**The two blockers, as the new patch names them.**  Line 2183 asserted, without proof, that repeated
van der Corput and Cauchy-Schwarz bound *every* polynomial average generated from `t, t^2, t^3` by a
power of the local uniformity norm of a selected input; it specified no polynomial state and did not
show the selected input survives.  Line 2193 asserted that "Cauchy-Schwarz removes" each unselected
factor and that an induction "gives exactly the cube product"; it identified neither the removed
block nor the induction invariant.  These are the same two gaps recorded here on 2026-09-15T15:07:51
and 2026-09-15T11:35:11.

**A discrepancy the patch itself records, affecting work already in the file.**  The patch deletes
`lem:degree-lowering-zero` outright: "its proposed argument applied degree lowering to a generic
selected input and identified a `U^2` expression with the wrong Fourier energy."  Ledger rows 372
and 373 are therefore not open items but removed ones.

Consequence for what is in `DFR/Auto/SmoothingIneq3D/Smoothing3D.lean`.  Nothing has to be retracted:
every declaration proved against the old `lem:degree-lowering-zero` is an unconditional theorem about
`Auto.fejer`, `Auto.locUnifPow` or the Fourier transform, and each is still true.  What changes is
that they are off the proof path:

- `Auto.locUnifPow_succ_split`, `Auto.exists_shift_locUnifPow_ge` -- the selection of the last
  difference.  Off path.
- `Auto.fejerHat`, `Auto.fourier_fejer`, `Auto.fejerHat_nonneg`, `Auto.fejerHat_le_one`,
  `Auto.integrable_fejerHat`, `Auto.fourier_fejerHat`, `Auto.autocorr`, `Auto.fourier_autocorr`,
  `Auto.integral_fourier_mul_comm`, `Auto.integral_fejer_autocorr` -- the Plancherel group.  Off the
  `s = 2` endpoint, which no longer exists, but the patch's stage 4 (`patch:u2-fourier-selection`,
  `patch:dual-difference`) does use Plancherel and one-dimensional `U^2` Fourier selection, so this
  group is expected to be reused there rather than deleted.
- `Auto.phaseCutoff`, `Auto.exists_phase_witness`, `Auto.exists_real_inverse_witness` -- the witness
  of the old `thm:real-inverse`.  The new `thm:real-inverse` takes `h_j = f_j` and needs no phase
  selection at all, so these are off path.  The weakening of `Auto.P_self_adjoint` to a measurable
  second argument, made for them, is a strict generalization and stays.

I have not deleted any of these.  They are marked "(off path)" in the ledger so that a later reader
does not mistake them for live dependencies, and so that the stage-4 reuse is visible.

**No main result changes.**  `thm:main` and the Part VII chain are untouched; the replacement is
confined to the inverse-theorem portion, exactly as the patch's own scoped replacement map directs.

## 2026-09-16T01:05:00-04:00 -- Plancherel is not a library prerequisite in this Lean environment

`blueprints/patch_3_updated.tex` lists, under "Background library", "Lebesgue integration,
Fubini-Tonelli, Cauchy-Schwarz and Hoelder, standard convergence theorems, translation and dilation
changes of variables, elementary polynomial algebra and calculus, and Plancherel", and says these
"are library prerequisites, not new analytic assumptions specific to this problem".

For every item on that list except the last, that is accurate.  For Plancherel it is not, in the
form the proof needs.

**What the proof needs.**  `patch:energy-to-u2` step two is `Q_1 >= E_L(f)/4`, i.e.

    ‖P_L^{(j)} f‖_2^2 <= 4 ‖T_{H,j} f‖_2^2,

argued from `|eta(v/L)|^2 <= 4 |m_H(v)|^2` on the Fourier side.  Both `P_L^{(j)}` and `T_{H,j}` are
convolutions in one coordinate, so this is Parseval applied to `f`: `∫ ‖g‖^2 = ∫ ‖𝓕 g‖^2` for
`g = P_L^{(j)} f` and `g = T_{H,j} f`, with `f` merely one-bounded and supported in a box.

**What Mathlib provides.**  `MeasureTheory.Lp.fourierTransformₗᵢ` is the Fourier transform on `L^2`
as a linear isometry equivalence, with `MeasureTheory.Lp.norm_fourier_eq` as Plancherel.  It is
*defined by extension from Schwartz space*, and the only bridge to the pointwise Fourier integral is
`SchwartzMap.toLp_fourier_eq`, for Schwartz functions.  There is no lemma identifying the `L^2`
transform of an `L^1 ∩ L^2` function with its Fourier integral, and our `f` is not Schwartz -- it is
an indicator-supported one-bounded function.

**Routes that do not work.**  Mathlib's `VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip`
plus `MeasureTheory.Integrable.fourierInv_fourier_eq` does give Parseval, but only under
`Integrable (𝓕 g)`; here `𝓕 (P_L^{(j)} f) (xi) = eta(xi_j/L) 𝓕 f (xi)` is supported in a slab and
bounded, not integrable, so that hypothesis fails.  A physical-space comparison also fails: writing
both `L^2` norms as `∫ K c` against the paired integral `c`, the required inequality is
`∫ (4 kappa_H - K_L) c >= 0` with `c` positive definite, which is a Bochner statement and not a
pointwise domination -- `4 kappa_H - K_L` is not pointwise nonnegative, `kappa_H` being supported in
`[-H, H]` with `H = 1/(8L)` while `K_L` has tails.

**Status.**  This is a missing-infrastructure obstacle, not a discrepancy in the patch's
mathematics, and not a reason to change a main result.  Closing it means building the
`L^1 ∩ L^2` Plancherel bridge (approximate by Schwartz functions in `L^1` and `L^2` simultaneously;
the `L^1` convergence gives uniform convergence of the Fourier integrals, the `L^2` convergence
gives convergence of the `L^2` transforms, and the two limits agree a.e.).  That is a sub-project of
its own and is recorded here so that the single remaining step of row 407 is not mistaken for a
small one.

No other step of the patch has been found to need Plancherel: `patch:fejer-squares` and
`patch:raise-order` are purely physical, as the patch itself emphasizes ("positivity before
comparison").  The patch's stage 4 (`patch:u2-fourier-selection`, `patch:dual-difference`) will need
it again, in one variable.

## 2026-09-16T03:05:00-04:00 -- correction: the Plancherel obstacle is avoidable

The entry of 2026-09-16T01:05 concluded that closing `Q_1 >= E_L(f)/4` means building an
`L^1 ∩ L^2` Plancherel bridge.  That conclusion was wrong: there is an elementary route, and it is
the one being taken.

**The route.**  What is wanted is `‖P_L^{(j)} f‖_2 <= c ‖T_{H,j} f‖_2`.  Both operators are
convolutions in the `j`-th coordinate, with multipliers `eta(v/L)` and
`m_H(v) = H^{-1} int_0^H e(vt) dt`.  Put `H = 1/(8L)` and substitute `v = L nu`: then
`m_H(L nu) = int_0^1 e(nu s / 8) ds =: mu(nu)` **does not depend on `L`**, and neither does

    Phi(nu) = eta(nu) / mu(nu),

which is smooth (on the support of `eta`, `|mu| >= 1 - pi/8 > 1/2`) and compactly supported, hence
Schwartz, hence `Phi = 𝓕 phi` for a Schwartz `phi`.  Undoing the substitution, the operator `S_L`
with multiplier `eta(v/L)/m_H(v)` is convolution with `w_L(u) = L phi(L u)`, and

    ‖w_L‖_{L^1} = ‖phi‖_{L^1} =: c_0

is an absolute constant, independent of `L`.  Since `P_L^{(j)} = S_L ∘ T_{H,j}`, Young's inequality
-- already in the file as `Auto.eLpNorm_integral_kernel_le`, i.e. Minkowski's integral inequality --
gives `‖P_L^{(j)} f‖_2 <= c_0 ‖T_{H,j} f‖_2` with no `L^2` Fourier theory at all.

The only Fourier input is the operator identity `P_L^{(j)} = S_L ∘ T_{H,j}`, which is an equality of
two `L^1` convolution kernels whose Fourier transforms agree.  Both kernels have integrable
transforms (`k_L` is Schwartz; `w_L ⋆ window` has transform `eta(./L)`, smooth and compactly
supported), so Mathlib's `MeasureTheory.Integrable.fourierInv_fourier_eq` applies to each and the
identity follows.  That is inversion for `L^1` functions with integrable transforms, which Mathlib
does provide -- unlike the `L^1 ∩ L^2` Plancherel bridge.

**What this costs.**  The patch's constant `4` in `|eta(v/L)|^2 <= 4 |m_H(v)|^2` is replaced by
`c_0^2` with `c_0 = ‖𝓕⁻(eta/mu)‖_{L^1}`, an absolute constant fixed by the cutoff `eta`.
`patch:energy-to-u2` then reads `Q_2 >= E_L(f)^2/(C beta)` with `C` depending on `eta` rather than
the literal `32`.  This is a constant change and it will be stated as such; the patch's budget
framework fixes constants by "rounding upward by the Archimedean property", and `lem:pet-reduction`
selects `c_*` from whatever constant the bridge returns, so nothing downstream is weakened.  It is
recorded here so that the discrepancy with the patch's displayed `32 beta` is not silent.

**Standing.**  Plancherel is still not available for `L^1 ∩ L^2` functions in this Mathlib, so the
2026-09-16T01:05 survey of Mathlib stands; what was wrong was the inference that the step therefore
requires it.  The patch's stage 4 may still need genuine Fourier inversion in one variable, but that
is inversion, not Plancherel, and Mathlib has it.

## 2026-09-16T04:20:00-04:00 -- an overstated ledger row (self-correction #6)

Row 387 of `automation/Status.md` (`patch:fejer-squares`) was standing at status `proved`.  It is
not proved: the lemma has three clauses -- the square identity, the order-raising inequality, and
`0 <= Q_s <= 1` for a one-bounded input supported in a box -- and the third has not been formalized.
The row has been set back to `partial` naming exactly what is missing.

I did not reconstruct how the status field came to read `proved`; the ledger is edited with anchored
textual substitutions and one of them evidently matched more of the row than intended.  The entries
of 2026-09-16T01:05 and 2026-09-16T03:40 both describe the row correctly in prose ("only
`0 <= Q_s <= 1` remains"), so the prose log and the table had drifted apart.

**Rule.**  A ledger substitution that rewrites a status field must assert the *old* status too, not
only the row's source item.  From here the anchor includes the leading status word, and after any
ledger edit the affected line is printed back and read.

Nothing in `DFR/Auto/SmoothingIneq3D/Smoothing3D.lean` is affected: no declaration was claimed that
does not exist, and no proof depended on the row's status.  The error was confined to the ledger.

## 2026-09-16T08:00:00-04:00 -- a silent no-op append, and a gap in the verification (self-correction #7)

**What happened.**  A one-liner meant to delete two unused binders from a scratchpad brick,

    perl -CSD -i -e 'my @l = <>; $l[5] = "..."; print @l;' brick.lean

emptied the file instead.  The append script then replaced the owned file's trailing
`\nend Auto\n` with nothing, so the file lost its `end Auto` **and gained no new declarations**.

**Why the check did not catch it.**  Two independent failures.

1. `lake env lean` on a file whose `namespace` is never closed reports *nothing at all* -- no error,
   no warning.  Lean tolerates an unclosed namespace at end of input.  So the diagnostics grep,
   which is otherwise the right check (see 2026-09-15T18:41), passed a structurally broken file.
2. The grep only asks "were there diagnostics".  It never asks "did the declarations I just wrote
   actually appear".  A no-op append is invisible to it.

The `#print axioms` step is what surfaced the problem: it reported both new constants as unknown.

**Rules, added to the append/verify procedure.**

- The append script now refuses to run unless the brick is non-empty, the brick ends with
  `end Auto`, and the *result* still ends with `end Auto`.  All three are `die` guards.
- After appending, the line count is printed and read, and `#print axioms` is run on the new
  declarations; an "unknown constant" there is treated as an append failure, not a naming slip.
- Never use `perl -i -e` with an explicit `<>` read on a file that matters.  Use the Write tool to
  rewrite a brick outright, or `perl -i -pe` for line-local edits.

**Scope.**  Nothing was lost: the owned file was restored from the backup taken before the append,
which is the state verified clean at 27400 lines, and the brick was rewritten and appended under the
new guards.  The file is now 27467 lines, `lake env lean` reports no error and no warning, and both
new declarations are on `[propext, Classical.choice, Quot.sound]`.  No earlier verification claim is
affected: this append was the only one that silently did nothing, and it was caught in the same tick.

## 2026-09-16T10:50:00-04:00 -- the same `perl -i` failure, twice more (self-correction #8)

The rule recorded at 2026-09-16T08:00 -- "never use `perl -i -e` with an explicit `<>` read on a file
that matters; use the Write tool to rewrite a brick outright" -- was correct and I did not follow it.
Two further scratchpad bricks were emptied the same way this session, once by `perl -CSD -i -e` with
an explicit `my @l = <>` and once by `perl -CSD -i -ne 'print unless ...'`.

**What worked.**  The append guards added at 08:00 did their job: the second failure hit
`die "EMPTY BRICK"`, the owned file had already been restored from its backup, and nothing was
written.  No compile time was spent on a broken file and no ledger claim was affected.

**What changes.**  The rule is promoted from "prefer" to "only": scratchpad bricks are written and
rewritten *only* with the Write tool.  `perl -i -pe` remains acceptable for a pure line-local
substitution on the owned file, where the content is not being restructured, but not for bricks.
When Write refuses because a file changed on disk, delete the file and write a fresh one under a new
name rather than reaching for a shell edit.

**Scope.**  Confined to scratchpad files.  `DFR/Auto/SmoothingIneq3D/Smoothing3D.lean` was never in a
damaged state during either incident, and its verified content is unchanged.

## 2026-09-16T18:05:00-04:00 - self-correction #9: the wrong route for the cut-off cost of `patch:signed-vdc`

**What I got wrong.**  When building the ingredients of `patch:signed-vdc` I proved the cut-off cost
as `Auto.norm_pairIntegral_sub_capPair_le'`: for a fixed spatial point, with `‖F x t‖ <= 1`, the
replacement of `I ∩ (I - h)` by `I` costs at most `|h|`.  I recorded it in the row-388 ingredient
list as the patch's `|h|/N`.  It is not.

**What the patch actually says.**  "Its replacement of `I ∩ (I-h)` by `I` costs at most `|h|/N`:
indeed `∫|F(x,t) conj(F(x,t+h))| dx <= V` by Cauchy-Schwarz."  The justification is an inequality
about the *spatially integrated* correlation, obtained from the hypothesis `∫|F(x,s)|^2 dx <= V`.
The pointwise version needs a sup bound on `F`, which the patch does not assume, and after
integrating it in `x` it produces `|h| mu(univ)` rather than `|h| V` -- a different constant, and
one that does not normalize to `|h|/N` without an extra unstated relation between `mu(univ)` and
`V`.

**Why it mattered and why it did not.**  It did not corrupt anything: the pointwise lemma is true
and stays in the file, and no ledger row claimed the composite.  It did matter for the interface,
which is precisely what row 388 was deferred over: I had been planning the composite around an
object (`capPair` of a fixed `F x`, with `x` outermost) that cannot carry the patch's constant.
The correct object has `x` innermost, and is now `Auto.corrLine`, with
`Auto.norm_corrLine_le` and `Auto.norm_corrIntegral_sub_capCorr_le` giving the patch's bound with
its own constant `V |h|`.

**What changes.**  When a blueprint justifies a bound with a named inequality, formalize the object
that inequality is *about*, not a pointwise analogue that happens to be easier.  Concretely: before
proving an ingredient, check that its hypotheses are a subset of the source lemma's hypotheses.
`norm_pairIntegral_sub_capPair_le'` assumes `‖F t‖ <= 1`, which `patch:signed-vdc` never assumes;
that mismatch was visible at the time and I did not check it.

## 2026-09-16T19:50:00-04:00 - self-correction #10: a row called blocked that was not blocked

**What I got wrong.**  In the 19:05 status entry I wrote that row 392 (`patch:triangular`) is
"blocked on `lem:real-polynomial-oscillation` -- a blueprint lemma of the main document, not of the
patch, and not yet formalized".  The last clause is false.  That lemma is row 370 of the ledger,
`proved`, and lives in the owned file as `Auto.real_polynomial_oscillation` at line 19699, together
with its `Auto.oscPoly` apparatus.

**How it happened.**  I inferred "not yet formalized" from the fact that the patch cites it as "the
preceding lemma" and that it is not one of the patch's own rows, without grepping the ledger.  One
grep would have settled it, and I did grep -- but only after writing the claim.

**Why it mattered.**  A wrong "blocked" is worse than a wrong "open": under the standing
instruction to work in strict forward dependency order, it would have made me skip the row
indefinitely.  The cost here was zero only because the very next step was to check.

**What changes.**  Never write "blocked" without naming the specific missing item *and* recording
the grep that establishes it is missing.  "Blocked" is a claim about the repository, not an
impression, and it is the one status value that stops work.

## 2026-09-17T02:15:00-04:00 - self-correction #11: a specification I had not read

**What I got wrong.**  At 01:05 I recorded that the remaining work on row 393 was "mostly design,
not proof", that "the design is uncomfortably underdetermined", and that no consumer existed to pin
it down.  I repeated that to the user.  It was wrong: `patch_3_updated.tex` contains a paragraph
headed "Lean state" (line 540) that specifies the representation directly -- factor fields, the
outer polynomial ring, the singleton head list, classical polynomial equality, and the instruction
to use a lexicographic well-founded relation for termination -- and a "Lean nodes" list (line 764)
that names `NormalPETState`, `ProtectedLeadingInvariant`, `petUpdate_protected`,
`petPivot_type_decreases` and `petIteration_bound`.

**How it happened.**  I read `patch:pet-update` and its proof, then the pivot subsubsection, and
stopped.  The specification sits between the termination discussion and the next subsection, under
a `\paragraph` heading rather than a `\label`, so it did not show up in the label greps I had been
navigating the patch with.

**Why it mattered.**  I deferred a design decision for a tick and told the user the blueprint did
not determine it, when it does.  That is the same failure as self-correction #10 -- asserting
something about the source material without checking -- and it is worse here because I had already
been warned by #10.

**What changes.**  Before saying a blueprint leaves something open, grep the source for the
construct's name *and* read the surrounding subsection end to end, including unlabelled
`\paragraph` blocks.  Label greps are not a substitute for reading.  Concretely: for every
remaining row, read the whole subsection before starting, not just the lemma and its proof.

## 2026-09-17T15:25:00-04:00 - `le_or_lt` does not exist in this Mathlib

`rcases le_or_lt a b with h | h` in `Auto.fejer_le_scaled` gave
`error(lean.unknownIdentifier): Unknown identifier 'le_or_lt'`, followed by a second, misleading
error from `rcases` complaining that the (now unelaborated) scrutinee "is not an inductive
datatype".  The second error is noise; only the first is real.

The name available here is `le_or_gt : a <= b \/ a > b`, which the owned file already uses in about
a dozen places (lines 2633, 3469, 6929, 9160, 9382, 10958, ...).  Its right branch is `a > b`, i.e.
`b < a`, so `h.le` still gives `b <= a` and downstream `le_trans` steps are unchanged.

Rule: reach for `le_or_gt` (and check an existing use in the file) rather than guessing at the
`le_or_lt` / `lt_or_le` family, whose membership differs between Mathlib versions.

## 2026-09-17T18:05:00-04:00 - self-correction #12: I broke the "bricks only with Write" rule

While fixing `Auto.locUnifPowMixed_re_le_scaled` I reached for `perl -0pi -e` to insert two `show`
lines into `brickGT.lean`.  Perl re-encoded the file's UTF-8 as Latin-1: every `ℝ`, `ℂ`, `→`, `∀`,
`∫`, `‖`, `≤` and `∏` in the brick was mangled into mojibake, and the brick was unusable.  I had to
rewrite it from scratch with the Write tool.

This is precisely the failure the existing rule was written to prevent -- scratchpad bricks are
written and rewritten **only** with the Write tool, never with `perl -i`.  The rule stands, and the
reason is now recorded: `perl -i` on this platform does not preserve UTF-8 without an explicit
encoding layer, and Lean source here is dense with non-ASCII notation.

The narrower rule that *is* safe and remains in force: `perl -i -pe` for pure line-local
substitution on the *owned* file, and only where the replacement text is ASCII.  The two ledger-row
rewrites in this session's `automation/Status.md` went through `perl -i -pe` with ASCII-only
replacement text and are intact.

**Rule, restated so it cannot be read narrowly:** any edit whose replacement text contains
non-ASCII characters goes through the Write tool, whatever the target file.

## 2026-09-17T18:05:00-04:00 - `rw` under `integral_congr_ae` sees an un-beta-reduced goal

Four rewrites failed in `Auto.re_locUnifPowMixed_eq` and `Auto.locUnifPowMixed_re_le_scaled` with
"Did not find an occurrence of the pattern `(↑?r * ?z).re`", although the target visibly contained
that pattern.  The reported target was

    (fun x => (↑(fejerCubeMixed Lv x) * innerFejer L (basisVec j) s f x).re) h
      = (fun h => (innerFejer L (basisVec j) s f h).re * fejerCubeMixed Lv h) h

-- a redex, not the beta-reduced form.  `refine integral_congr_ae (Filter.Eventually.of_forall
fun h => ?_)` and `Integrable.congr` both leave the pointwise goal in that shape, and `rw` matches
syntactically, so it sees no `Complex.re` application at the head.

Fix: interpose an explicit `show` of the beta-reduced equation before the `rw`.  `show` matches up
to definitional equality, so it both beta-reduces and, where the ambient lemma produced
`RCLike.re`, restates it as `Complex.re` -- which is what `Complex.re_ofReal_mul` needs.  A second
trick used for the same reason: giving an intermediate `have hre : Integrable fun h => (...).re :=
hcI.re` an explicit type annotation forces `Complex.re` rather than `RCLike.re` in the subsequent
goal.

## 2026-09-18T11:51:17-04:00 - three wording and convention points in `blueprints/patch_3_updated.tex`

Recorded here rather than only in `automation/Status.md`, correcting a gap in this session's
record-keeping: the skill directs *convention differences* and departures from the source's literal
text to this file, and these three had been noted only in the status log.

**None of them is a mathematical error in the blueprint.**  Each is a place where the source's
literal wording differs from the statement that is provable, and where a formalization following the
wording exactly would be either false or weaker than intended.

### 1. "At `r = 4` the phase is identically one" (subsubsection on polynomial phases)

Read literally this is false: the phase `e(p_x(t))` is not the constant `1`.  What is true, and what
the argument uses, is that it contributes nothing to the *fourfold parity cube* -- the alternating
sum of a cubic over the four-dimensional cube vanishes, so the product of the conjugation-signed
phases is one.  Formalized as `Auto.phase_cube_eq_one` and, in the form the steps consume,
`Auto.phaseProd_cube_eq`.  A formalization asserting the pointwise reading would be unprovable.

### 2. "Translating `x` by its affine `P_1(t)` removes `t`" (degenerate degree-one branch)

True of the *input factor* only.  After the translation the `t`-dependence survives in the phase,
whose argument is evaluated at the translated point.  `Auto.phaseProd_one_translate` states exactly
that.  The dependence is genuinely gone only once the four steps have run and the phase has been
removed, which is where the branch is taken; `Auto.phaseProd_zero_phase` records the shape it is in
by then.

### 3. Sign convention in the alternating cube sum

The blueprint writes the sum as `sum_omega (-1)^{|omega|} p(t + omega . h)`, i.e. with
`Auto.numTrue`.  The Lean statements use `Auto.numFalse`.  The two differ by the global factor
`(-1)^r`, so the vanishing is the same assertion; `numFalse` is chosen because the difference
operator `Delta_u Q = Q(. + u) - Q` puts the minus sign on the *unshifted* vertex, and because
`Auto.conjPar` conjugates on odd parity.  With `numTrue` the exponent would be `r - |omega|`, a
natural subtraction to guard through the whole induction, and a global `(-1)^r` to carry through the
exponential in `Auto.conjPar_expPhase`.  Deviation is notational only.

### Not a discrepancy, recorded for completeness

The modelling choices of the same period -- each input carrying its own coordinate direction
(`j : ℕ → Fin 3`), measurability rather than continuity of the phase, and the enlarged box being
taken in the `Auto.petBox` family -- are recorded in `automation/Status.md` at 19:54 and 10:06.
They follow the source rather than departing from it; the measurability one in particular is the
source's own hypothesis, and assuming continuity there would have weakened the proposition.

## 2026-09-21T14:56:26-05:00 - the two cube conventions, now formally bridged

Addendum to "3. Sign convention in the alternating cube sum" (line 1578), which recorded that the
blueprint's `(-1)^{|omega|}` labelling (`Auto.numTrue`) and the Lean statements' `Auto.numFalse`
differ by the global factor `(-1)^r`, and judged the deviation notational.

That judgement is now *proved* rather than asserted, in the form the proposition needs:
**`Auto.conjPar_numTrue_eq_numFalse`** shows the two conjugation conventions agree whenever the cube
dimension `r` is even, which is exactly the case `(-1)^r = 1` of the factor recorded there.  Since
`patch:highest-control` runs four steps, both conventions apply to the same object at the point
where the affine development meets the local uniformity norms, and
**`Auto.headBlock_eq_fdiffIter`** identifies the affine block with the iterated Fejer difference
outright, the increments being the slope gaps times the shifts.

The supporting facts are `Auto.numTrue_add_numFalse` (the counts sum to the dimension) and
`Auto.slopeShift_eq_cubeShift` (the affine shift is the ordinary cube shift of the gap-scaled
vector).  No change to any statement of the blueprint or to any Lean statement was required; this
addendum records that the notational deviation is now discharged by a theorem, so a later reader
need not re-derive it.

## 2026-09-25T07:00:11-04:00 - `new:integral-plancherel`: proof route replaced by verified Mathlib reuse

Source: `blueprints/koszAdjoint_blueprint.tex`, Theorem `new:integral-plancherel` (lines 386-417),
proved there from `new:approximate-identity` and `new:translation-continuity`.  The Lean proof in
`DFR/Auto/IntegralPlancherel.lean` instead identifies the integral transform with Mathlib's `L^2`
Fourier isometry `MeasureTheory.Lp.fourierTransformₗᵢ`, by testing both against smooth compactly
supported functions (tempered distributions, `ae_eq_of_integral_contDiff_smul_eq`).  Statement
unchanged; only the proof route differs.  `new:approximate-identity` is used nowhere else in the
blueprint and is therefore not on the formalized dependency path.  Resolved.

## 2026-09-25T08:14:07-04:00 - `new:interpolation`: Stein's analytic-family route instead of duality

Source: `blueprints/koszAdjoint_blueprint.tex`, Lemma `new:interpolation` (lines 497-539),
proved there by pairing with analytic families of simple tests and `new:three-lines`, then
`new:duality`.  The Lean proof (`Auto.interpolate_trilin_simple`) applies the existing Stein
interpolation theorem `Auto.eLpNorm_le_of_analyticFamily` directly to the output family, whose
analyticity comes from expanding the trilinear operator over level sets
(`Auto.trilin_anFam_expand`).  The `L^∞` input endpoints are encoded as exponent `0`
(`Auto.eIn`).  Statement unchanged (it even allows subunit output exponents); resolved.

## 2026-09-25T08:31:39-04:00 - `patch:pet-analytic-step` reopened; `patch:highest-control` split

`Auto.petStep_signed` (recorded complete in the retrospective ledger mapping) handles shifts along a
single coordinate only, while `patch:pet-analytic-step` (blueprint lines 1185-1209) acts on vector
polynomial shifts across all coordinates.  The row is reopened.  The existing affine endpoint and
`patch:uniformize` lemmas assume continuous inputs; `patch:highest-control` is therefore proved
first for continuous compactly supported inputs and then extended to Borel inputs by approximation,
the blueprint's own convention at `patch:conventions` ("changing representatives does not change
any correlation or cube integral").  No statement changes; unresolved until both rows close.

## 2026-09-25T09:19:09-04:00 - "Full coefficient and translation bounds" (blueprint lines 1167-1175)

The Lean route does not need translation or coefficient envelopes: every block and every spatial
block contains a translate of an input bounded by one and supported in the budget box, so all
`L^2` bounds are the budget-box volume whatever the translations (`Auto.vecStep_phase` takes a
bounded support set `K` with `|K| ≤ V`).  What is needed is the uniform bound on the integer
witnesses on the unit cube, used for the radii upper bound; it is carried as `Auto.PetRunBd`, with
factor `D + 2` per step (`Auto.petRunBd_step`).  Statement-level change: none; resolved.

## 2026-09-25T11:38:12-04:00 - "Full coefficient and translation bounds" revisited: the support envelope is needed

The entry of 2026-09-25T09:19:09-04:00 is corrected.  The PET steps put back a spatial block, and
that block must cover the support of the children for every parameter in the window; this needs
the envelope of the evaluated shifts in units `N^{expo k}` of the box sides, which the blueprint
supplies in the same paragraph.  It is carried as `Auto.PetStateEnv` (factor `4` and range loss
`H` per update, `Auto.petRunSeq_env`); the spatial block is the enlarged box translated with the
protected input (`Auto.petSpatialFun`).  The phase steps likewise bound the protected shift in
units of its box side (`Auto.phaseProdIter_eq_zero_of_notMem_scaled`), so that the chain volume
stays `u(δ) N^6`.  No statement changes; resolved.

## 2026-09-25T11:38:12-04:00 - `patch:highest-control`: one output budget for both the radius and the lower bound

Source: `blueprints/koszAdjoint_blueprint.tex`, Proposition `patch:highest-control` (lines
1406-1424): "There are integers `s_0 ≥ 2` and `C ≥ c` ... at the deterministic radius
`H = u_C(δ) N^{d_m}`, `Q ≥ ℓ_C(δ)`."  With the same `C` for the radius and the lower bound
the proof does not give the assertion: `patch:uniformize` loses `∏ 2L/L_i`, so at radius
`L = u_C(δ) N^{d_m}` the bound obtained is `δ^{O(1)} u_C(δ)^{-s}`, never `≥ ℓ_C(δ)` for
`s ≥ 2`.  The loss is genuine: for `f_m` the indicator of the budget box the order-`s` power at
radius `u_C(δ) N^{d_m}` is of size `u_c(δ)^3 (u_c(δ)/u_C(δ))^s`, below `ℓ_C(δ)` as `δ → 0`
once `C > (s + 3) c / (s - 1)`.  The Lean
statement therefore returns two budgets, `C₁` for the radius and `C₂` for the lower bound;
this is all that the later uses need ("at a radius `H` comparable to `N^{d_m}` up to powers",
line 1880).  Status: the formal statement deviates in this respect; recorded, awaiting review.

## 2026-09-25T13:00:01-04:00 - `patch:highest-control` proved; the split of 08:31 resolved; conventions of the Lean statement

The continuous case (`Auto.highestControl_nice`, both the degree-one branch and degree at least
two) and the Borel extension (`Auto.highestControl`, by `L^1` approximation of the protected
input, `Auto.exists_nice_approx`) are proved; the entry of 2026-09-25T08:31:39-04:00 is resolved.
Conventions of the Lean statement relative to lines 1406-1424: the ambient space is `E3` with the
inputs along coordinates `j i` of degree `expo (j i)` (a degree list contained in `{1,2,3}`,
other coordinates passive), so the normalizations are `N^6` in place of `N^{D_k}`; the scale is
`N ≥ 1` (the blueprint writes `N > 0`); the phase coefficients are Borel and the phase has
degree at most three, as stated.  Two output budgets as recorded above.  Status: statement
conventions recorded; the `N ≥ 1` restriction awaits review when the consumers are formalized.

## 2026-09-25T13:25:54-04:00 - `patch:u2-fourier-selection`: conventions of the Lean statements

`Auto.unifPow1 H S r f` defines the one-dimensional `Q_{r,H,S}(f)` by the paired-cube average
`S^{-1} Re E_{a,b ∈ [0,H]^r} ∫ D^r_{a,b} f` of lines 1440-1447 (uniform pairs), not by Fejer
densities; the blueprint states the two agree after translation, and the Fejer form is not needed
by the consumers `patch:dual-difference` and `patch:missing-phase`.  The support interval is
`[c, c + S]`.  The measurable selection enumerates a countable dense sequence of reals in place of
`ℚ` (the argument is the same), with the explicit threshold `H √η / 2` for `Q_2 ≥ η`.
Status: recorded; no change to the mathematics.

## 2026-09-25T13:58:36-04:00 - `patch:dummy-phase`: a different dummy phase

`Auto.exists_dummy_phase` proves the statement of `patch:dummy-phase` (lines 1573-1580) with
`Φ(a,b) = L ∏_i b_i`, whose alternating sum is `Ψ(a,b,c) = L ∏_i (b_i - c_i)`
(`Auto.sum_neg_one_pow_prod_cubeSel`), in place of the grid function `2M 2^{ι(b)}` of the
blueprint's proof: `|Ψ| ≤ M` forces `|b_i - c_i| ≤ η` for some `i`, and each such event has
probability at most `2η/H`.  The statement, including measurability and finite values, is
unchanged; the blueprint's argument is correct as well.  Status: recorded; no change to the
statement.

## 2026-09-25T14:01:37-04:00 - `MA(m, l)` is stated on `ℝ³` with passive coordinates

`Auto.MajorArcProperty k j m l` states `MA(m, l)` of lines 1600-1629 for functions on `ℝ³` rather
than on `ℝ^{m-1}`: the inputs `g_1, …, g_{m-1}` move in the directions `j 1, …, j (m-1)` of degrees
`expo (j i)`, every other coordinate is passive, the phases `ζ_i` may depend on all of `x`, and
both the correlation lower bound and the measure of the canonical set are in units `N^6` with the
envelope `petBox (u_C(δ)) N`.  This is the passive-section family form used in
`patch:structured-degree`; it matches `Auto.highestControl` (also on `ℝ³`), and it removes the
`z`-section selections of Step 5 of `patch:conditional-degree` and of the major-arc induction
step, since the full `ℝ³` correlations there are already of this form.  For `m = 1` the base case
becomes pointwise in the passive variables (`patch:triangular` plus popularity).  The scale is
`N ≥ 1` as for `Auto.highestControl`.  Status: convention recorded; awaiting review.

## 2026-09-25T15:40:11-04:00 - `patch:conditional-degree`: conventions of the Lean statement

`Auto.conditionalDegreeLowering` states the lemma of lines 1631-1646 for the adjoint-type function
`Auto.cdlF` on `ℝ³` (inputs along `j i`, passive coordinates as in `Auto.MajorArcProperty`).  The
order-`s` norm of `F` in the direction `e_m` is expressed through its sections
`z ↦ F(embT (j m) y z)` over the transverse coordinates `y ∈ ℝ²`: the hypothesis and the conclusion
are `∫ y, Q_{s,H,S}(F_y) dy ≥ ℓ(δ) N^{6 - d_m}` with the one-dimensional paired-cube powers
`Auto.unifPow1` and the section length `S = 10 u_c(δ) N^{d_m}` (the enlarged support of the
sections); `s = r + 2 ≥ 3`.  The blueprint's explicit thresholds are followed with minor
variations recorded in `Auto.cdlOut` (cell width `b₀/(2π Z)` and a `c` section of relative
measure `m₀/2`).  Step 5 is proved for every measurable phase `ψ` of the transverse variable,
after replacing `ψ` by `B + 1` off the envelope (`Auto.cdl_step5`).  Status: conventions recorded.

## 2026-09-25T17:16:40-04:00 - `patch:major-arc`, `patch:remove-high-inputs`, `patch:lowest-energy`: Lean conventions

With `MA(m, l)` on `ℝ³` (entry 2026-09-25T14:01:37-04:00), the smaller pattern of
`patch:ma-smaller-pattern` is itself an `MA(m, l)` correlation on all of `ℝ³` (`Auto.spIn`,
`Auto.spFreq`; the coordinate `x_m` is passive for it), so `Auto.majorArc_step` applies the
induction hypothesis once to it instead of to each `x_m` section with a popular set `Z_m`; the
canonical set of the smaller pattern lies in that of `MA(m+1, l)` after dropping
`N^{d_m} |λ|` (`Auto.maSet_sp_subset`).  The same applies to the `w`-section step of
`patch:remove-high-inputs` (`Auto.removeHigh_small`).  The pairing scalar `c(y)` is chosen by
`Auto.unitScalar`.  The order raising of the major-arc step always raises twice from the order
`s₀` of `patch:highest-control` and then lowers `s₀` times (`Auto.ma_uniformity`), which covers
`s₀ ∈ {0, 1, 2}` uniformly.  `Auto.lowestEnergy` holds for all `N ≥ 1` (no `N ≥ u_C(δ)` is
needed) and for any phase data of `Γ_k`; its energy is `∫ η(ξ_{j 1} / L) |ĝ_1|²` with
`L = u_C(δ) (N^{d_1})⁻¹`.  Status: conventions recorded.

## 2026-09-25T17:46:30-04:00 - `patch:energy-core`: Lean conventions

`Auto.energyCore` is stated on `ℝ³` for unmodulated `Γ_k` (phase `fun _ => 0`), all
increasing degree lists of length `k`, and `N ≥ u_C(δ)`.  Step 1 obtains the adjoint of the
first input as `Auto.maAdj` after rotating the inputs so that the first comes last
(`Auto.phaseCorr_rot`), and normalizes the smoothed adjoint by `max 1 ‖k‖₁` so that it is
one-bounded; its cut-off to the enlarged box enters the correlation (it agrees with the smoothed
adjoint wherever the output factor is nonzero).  Step 2 uses the explicit increment bound
`|P_1(t) - P_1(a)| ≤ 12 u N^{d_1 - 1} |t - a|` (`Auto.abs_eval_sub_le_of_admissible`) and
`K = ⌈192 u^4 u_{C_1}/ℓ_{C_1}⌉ + 1`.  Step 3's frozen inputs are cut off above `k - 1`
(`Auto.frozenCut`), since the hypotheses of the induction theorem quantify over all input indices.
Step 4 is not needed: with passive coordinates the frozen correlation is itself a `Γ_{k-1}` on
`ℝ³`, so the induction hypothesis applies to it directly and gives the full-space energy of the
translate `g_i(· - P_i(a) e_i)`, whose Fourier modulus is that of `g_i`
(`Auto.norm_fourier_comp_sub`).  Status: conventions recorded.
