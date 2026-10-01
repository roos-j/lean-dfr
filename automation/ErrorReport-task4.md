# Task 4 source discrepancies (`blueprints/main.tex`)

2026-09-25T21:31:10-04:00 - Reading audit of `blueprints/main.tex` before formalization. Typographical slips, resolved
by the evident intended meaning; none changes `thm:main`:
- line 466: `‖T^{(k)}(f)‖_1` should be `‖T^{(k)}(f)‖_p`; line 470: `‖f_n‖_3` should be `‖f_n‖_{p_n}`.
- line 576: the label `eq:final_gain` is used a second time (for `T^{MH,1}`).
- line 588: the second set is `F_{MH,1,-}` (printed `F_{MH,1,+}` twice).
- line 617: `|k|^5` in `lem:loss_2` is `|k|^5` for `k = (max(k_2,k_3) - 100, k_2, k_3)`.
- line 647: `\widecheck{\phi}` is `φ̌`.
- line 415: derivatives `∂^α θ` range over all multi-indices, not only positive ones.
- line 487: `\mathcal{I}^{(3)}` is the index set `\mathcal{I}` of line 489.

2026-09-25T21:31:10-04:00 - `thm:smoothing_2` (lines 205-221) is proved only by reference ("analogous to that of
Theorem 5 in CDR21, keeping track of the dependence on the cutoff function", line 705). Task 1
formalized Theorem 5 of CDR21 for the curve `(t, t^2)` with a fixed cutoff and an implicit
constant (`Auto.smoothing_theorem5`); `lem:gain_2-` needs the curve `(t^2, t^3)` with the explicit
constant `(‖ψ‖_∞ + ‖ψ'‖_1) λ^{-δ}`. Unresolved: this is a proof obligation of Task 4, to be met by
adapting the Task 1 argument.

2026-09-25T21:41:30-04:00 - lines 295-303: `ψ̃` is required to satisfy
`1_{1/2 ≤ |ζ| ≤ 1} ≤ ψ̃ ≤ 1_{1/2 - 1/100 ≤ |ζ| ≤ 1 + 1/100}`, but then `ψ̃_j ψ_j = ψ_j` fails, since
`ψ = φ - φ(2·)` is nonzero on `1 < |ζ| < 2`. Resolved: `Auto.lpPsiTilde` satisfies
`1_{1/2 ≤ |ζ| ≤ 2} ≤ ψ̃ ≤ 1_{1/2 - 1/100 ≤ |ζ| ≤ 2 + 1/100}`, which gives `ψ̃_j ψ_j = ψ_j`
(`Auto.lpPsiTildeJ_mul_lpPsiJ`) and `Δ_j Δ̃_j = Δ̃_j Δ_j = Δ_j`; `ψ̃` is only used through these
identities and its boundedness, so nothing downstream changes.

2026-09-25T21:44:43-04:00 - lines 305-345 (proof route, not an error of the statement): the source
rearranges `T = ∑_j T_j = ∑_j ∑_k T_j(Δ f_1, Δ f_2, Δ f_3)` into the four components `T^ω` without
discussing convergence; the double series is not absolutely convergent in `j` in general. The
formalization works with the scale truncations `T_J = ∑_{|j| ≤ J} T_j` (`Auto.simplexTrunc'`),
for which the `k`-series converges absolutely so that the regrouping is legitimate, proves every
component bound uniformly in `J` (the source's estimates only ever sum norms over sets of scales),
and passes to `T` by the pointwise convergence `T_J f → T f` (`Auto.tendsto_simplexTrunc'_simplexT`)
and Fatou's lemma.

2026-09-25T22:05:59-04:00 - line 232: `Γ(f)(x) = ∫_{ℝ^3} K(t) ∏ f_n(x + t^n e_n) dt` writes `t^n` for the `n`-th
coordinate `t_n` of `t ∈ ℝ^3` (as in the Task 3 blueprint); formalized as `Auto.gammaOp`. Line 224:
`\widehat{K}(\xi,\eta)` has a stray `η`. `thm:main_twist` is formalized (`Auto.mainTwist`) for Schwartz
kernels `K` whose multiplier `K̂` satisfies the symbol condition with a constant `M` (the source
takes `M = 1`), which is the form in which it is applied to the truncated kernels `K_L`, `K_{ML}`.

2026-09-25T23:23:18-04:00 - `lem:gain` (lines 440-447, proof 458-473): the lemma is stated for
`p ∈ [1, ∞)`, `p_n ≥ 2`, but the proof sums the single-scale bounds over `j` with Hölder's
inequality in `j` for the exponents `(p_1, p_2, p_3)`, which requires `∑ 1/p_n = 1`, i.e. `p = 1`
(the proof indeed writes `‖T^{(k)}(f)‖_1` and ends with `‖f_n‖_3`). Resolved: `lem:gain` is
formalized for `p = 1` (all `p_n ≥ 2` with `∑ 1/p_n = 1`), which is all the interpolation step
(line 456) uses: interpolating the gain at the single vertex `(1/3, 1/3, 1/3; 1)` against the
loss `eq:loss` at three surrounding vertices gives exponential gain at every admissible exponent.
The same applies to `lem:gain_2+` (proved "the same" way). The interpolation itself is carried out
with Task 3's multilinear Marcinkiewicz theorem (`ext:interpolation`), which needs the operators on
simple functions; the source does not discuss this extension, which is supplied (ledger rows at
line 456). Nothing in `thm:main` changes.

2026-09-26T00:06:06-04:00 - `lem:loss` (lines 448-455, proof 474-568), proof route for `eq:final_gain` in the range of
`thm:main`: the source proves the polynomial loss `‖T^{(k)}(f)‖_p ≲ |k|^5 ∏‖f_n‖_{p_n}` for all
`p_n ∈ (1, ∞)` via shifted maximal functions and the vector-valued shifted maximal inequality of
GHLR17 (Thm 3.1), in order to obtain `eq:final_gain` for all `p ∈ [1, ∞)`, `p_n ∈ (1, ∞)`. `thm:main`
only needs `eq:final_gain` for `p ∈ (1, 4/3)`, `p_n ∈ (1, 4)`, and there `1/p_n < 1 - 1/4 - 1/4 = 1/2`,
i.e. every `p_n > 2`. In that range a weaker loss suffices, with a much shorter proof that avoids
GHLR17: Hölder `(∞, 2, 2)` in `t`, with the `∞` slot controlled by the reproducing formula
`Δ_m = Δ̃_m Δ_m`, the decay of `ψ̃̌`, and the coordinate maximal function, and the two `L^2` slots by
duality with the coordinate maximal function and the partial Littlewood-Paley inequality, gives
`‖T^{(k)}_J(f)‖_{q/3} ≤ C_q 2^{40 (k^{(1)} + 2)/q} ∏ ‖f_n‖_q` for every `q ≥ 6`, a loss whose rate
tends to `0` as `q → ∞`. Interpolating `lem:gain` at a fixed triangle of vertices on
`∑ 1/p_n = 1` against this bound at `(1/q, 1/q, 1/q)`, with `q` large (depending on the target and
the gain exponents), gives exponential gain at every exponent of `thm:main`, which is all that the
summation `eq:final_gain` uses. `lem:shifted_max`, `eq:single_scale` and `lem:loss` are therefore
not formalized; the ledger rows for them are marked superseded, and replaced by rows for the
alternative route. `thm:main` is unchanged. The same device will be used for `lem:loss_2` (MH) if
it applies there.

2026-09-26T00:57:13-04:00 - line 456 (interpolation, proof route): instead of Task 3's four-vertex multilinear
Marcinkiewicz theorem (which needs real trilinear operators on simple functions in all slots), the
interpolation is done in the single slot `0`, with `f_1, f_2` fixed Schwartz functions, by the
linear Riesz-Thorin theorem of lean-spherical (`Auto.SteinInterpolation.riesz_thorin`, complex
simple functions, constant `M_0^{1-θ} M_1^θ`), along the segment from the `lem:gain` point
`(1 - 1/p_1 - 1/p_2, 1/p_1, 1/p_2; 1)` to the small-loss point `(ε, 1/p_1, 1/p_2)`; both carry the
same exponents in slots `1, 2`, and the target exponent of `thm:main` lies on the segment. Only slot
`0` needs the extension to simple functions. The small-loss bound is used in the form
`Auto.smallLoss_bound'` (general exponents `(q, p_1, p_2)`).

2026-09-26T01:23:04-04:00 - `thm:smoothing_2` (lines 205-221, proof line 705 "analogous to that of Theorem 5 in
[CDR21], keeping track of the dependence on the cutoff function"): this is the only ingredient of
`thm:main` whose proof the source does not give. It is needed for `lem:gain_2-` (the grouped
operators `T^{(k_2,k_3)}` on `F_{MH,n,-}`), for the three curve pairs `(t^2, t^3)` (MH,1),
`(t, t^3)` (MH,2) and `(t, t^2)` (MH,3), with an explicit constant `‖ψ‖_∞ + ‖ψ'‖_1`. Task 1
(`Auto.smoothing_theorem5`) proves CDR21 Theorem 5 only for `(t, t^2)`, with a constant depending on
the cutoff in an unspecified way, and its proof (CDR21 §3, in particular the sublevel-set Lemma 3.3 in
§3.5 with explicit flows for the quadratic curve) is specific to that curve. Other routes were checked
and fail: every gain estimate derived from `thm:smoothing` (finite exponents) and summed over `j` lands
at `p < 1`, and the grouped kernel does not satisfy the symbol condition of `thm:main_twist`. The
remaining parts of `F_MH` (`F_{MH,n,+}`, and `F_{MH,n,-}` with `k^{(1)} ≤ 100`) are handled without
it. Status: `thm:smoothing_2` is to be formalized as a separate reusable prerequisite (a
generalization of Task 1 to monomial curves); until then `thm:main` is assembled with
`thm:smoothing_2` as an explicit hypothesis (a named `Prop`), not a `sorry`.

2026-09-26T06:39:06-04:00 - `thm:smoothing_2` scope: per the user's answer, formalized for monomial curves `(t^a, t^b)`, `a ≠ b`, with `a, b ≥ 1` (the answer's "integers > 1" would exclude `(t, t^3)`, needed for MH,2, and `(t, t^2)`, needed for MH,3; the source states `α_1, α_2` positive distinct integers, which is what is formalized).

2026-09-26T06:53:26-04:00 - `lem:loss_2` (lines 612-619, proof 654-656, "analogous to lem:loss"): superseded like
`lem:loss`. For the grouped operators with the low-pass `S` in the smallest-frequency slot, the `∞`
slot needs no shift loss at all (`|S_m g(x + t e)| ≤ C M g(x)` for `|t| ≲ 2^{-m}`), so the
Cauchy-Schwarz-in-`t` route gives loss-free bounds at `(1/q_0, 1/q_1, 1/q_2)`; interpolation with
`lem:gain_2-` (in three successive single-slot Riesz-Thorin steps, slots 1, 2, 0) gives the
exponential gain needed at the exponents of `thm:main`. `thm:smoothing_2` enters only through
`lem:gain_2-` and is stated as `Auto.SmoothingTwo` (user instruction of this date), the single
hypothesis of `thm:main`.

