# Task 1 status: bilinear smoothing along distinct monomials (`blueprints/task_1_smoothing_inequality_2.tex`)

Earlier Task 1 (CDR21 Theorem 5 for `(t, t^2)`, `Auto.smoothing_theorem5`, complete) is superseded as the Task 1 target by the user instruction of 2026-09-26T08:23:42-04:00; its ledger is in the git history (commit 57660a2, `automation/Status-task1.md`). Its general lemmas (autocorrelation, Lemma 3.2 decomposition, interpolation, van der Corput) are reused where they apply.

## Main theorem overview

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | Target theorem, lines 30-61 | (T): distinct positive `α_1, α_2`, `0 < a < b`, `ψ ∈ C^1` with `supp ψ ⊆ [a,b]`, `λ ≥ 1`, `supp ĝ_j ⊆ {|ξ_j| ≥ λ}` for one `j`: `‖A_ψ(g_1,g_2)‖_1 ≤ C (‖ψ‖_∞ + ‖ψ'‖_1) λ^{-δ} ‖g_1‖_2 ‖g_2‖_2`, `δ` independent of `ψ` (`Auto.monomial_smoothing`, DFR/Auto/MonomialSmoothing.lean) | 2026-09-26T10:39:43-04:00
complete | Target theorem, application | `Auto.SmoothingTwo` from `Auto.monomial_smoothing` (DFR/Auto/Reduction/Reduction.lean) | 2026-09-26T10:41:25-04:00

## Reusable prerequisite: `DFR/Auto/MonomialSmoothing.lean`

2026-09-26T08:41:29-04:00 - Need: `thm:smoothing_2` of blueprints/main.tex (the Task 4 hypothesis `Auto.SmoothingTwo`) for the curve pairs `(t^2,t^3)`, `(t,t^3)`, `(t,t^2)`. Missing: Mathlib has no smoothing inequality; the repository's `Auto.smoothing_theorem5` covers only `(t,t^2)` with an unspecified cutoff dependence. Substance: a named research theorem (Christ-Durcik-Roos bilinear smoothing), proved in a 1400-line blueprint. Generality: arbitrary distinct positive integer exponents and `C^1` cutoffs on `[a,b] ⊂ (0,∞)`, stated with Mathlib notions only (Schwartz functions on `EuclideanSpace ℝ (Fin 2)`, `𝓕`, `eLpNorm`). File: DFR/Auto/MonomialSmoothing.lean, one file, namespace `Auto`.

## Section 1: framework and elementary Fourier facts

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | lines 72-93, (1.1) | `Q(t) = t^r`, `q = Q'`, `Γ(t) = (-t, Q(t))`, `T_ψ(f_1,f_2)(x,y) = ∫_I ψ(t) f_1(x+t,y) f_2(x,y+Q(t)) dt` | 2026-09-26T10:39:43-04:00
complete | lines 106-118, (1.2) | `‖T_ψ(f_1,f_2)‖_1 ≤ ‖ψ‖_1 ‖f_1‖_2 ‖f_2‖_2` | 2026-09-26T10:39:43-04:00
complete | lines 120-139, (1.3)-(1.4) | kernels `K_L(s) = L ϑ̌(Ls)`: decay and `L^1`, derivative and moment bounds, one-coordinate convolution | 2026-09-26T10:39:43-04:00
complete | lines 141-148, (1.5) | `‖K * f‖_p ≤ ‖K‖_1 ‖f‖_p` | 2026-09-26T10:39:43-04:00
complete | lines 150-193, (1.6)-(1.7) | autocorrelation identity for `U_R(f)` and its bound, `f ∈ L^2` | 2026-09-26T10:39:43-04:00
complete | lines 195-199, (1.8) | `∫ ‖D_s f‖_2^2 ds = ‖f‖_2^4` | 2026-09-26T10:39:43-04:00

## Section 2: the frequency decomposition

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | Lemma 2.1 proof, lines 244-257 | partition of unity `ϑ`; selected integers, at most `9ρ^{-1}` | 2026-09-26T10:39:43-04:00
complete | Lemma 2.1, (2.1)-(2.2), lines 259-275 | `f_♯`, `f_♭`: domination and the flat interval bound | 2026-09-26T10:39:43-04:00
complete | Lemma 2.1, (2.3)-(2.5), lines 277-284 | `f_♯ = ∑ h_ν e^{2πiω_ν x}`, Fourier support, derivative bounds `C_k R^k ‖f‖_∞`, centers | 2026-09-26T10:39:43-04:00
complete | lines 287-307, (2.6)-(2.7) | `U_R(f_♭) ≤ ρ ‖f‖^4`, localized version `U_R(χ f_♭) ≤ C ρ ‖f‖^4` | 2026-09-26T10:39:43-04:00
complete | lines 309-313 | the decomposition measurably on fibers, fixed enumeration, zero padding | 2026-09-26T10:39:43-04:00

## Section 3: the modified flow and the sublevel estimate

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | lines 342-369, (3.2)-(3.4) | `θ_1, θ_2, ν`, `V = ∇θ_1 × ∇θ_2`, `Vθ_1 = Vθ_2 = 0` | 2026-09-26T10:39:43-04:00
complete | lines 370-377, (3.5) | the formula for `Vν` | 2026-09-26T10:39:43-04:00
complete | lines 378-413, (3.6) | `|Vν| ≥ c ∏ |t_i - t_j|` (determinant, Rolle) | 2026-09-26T10:39:43-04:00
complete | lines 415-437, (3.7)-(3.8) | `H = (θ_1, θ_2, ν)`, `|det DH| = |Vν|` | 2026-09-26T10:39:43-04:00
complete | lines 452-460, (3.10) | exceptional set measure `≤ Cη`, `|det DH| ≥ cη^3` off it, cube cover `C η^{-9}` | 2026-09-26T10:39:43-04:00
complete | lines 462-476 | local injectivity of `H` on cubes of side `c_1 η^3` | 2026-09-26T10:39:43-04:00
complete | lines 477-501, (3.9) | change of variables, Fubini in the image, `η = ε^{1/13}`, measurability | 2026-09-26T10:39:43-04:00
complete | lines 505-534, (3.11)-(3.12) | the incidence set `E`, `d_A`, `d_B`, `∫_E d_A d_B ≥ c μ^3` | 2026-09-26T10:39:43-04:00
complete | lines 535-557, (3.13) | `∫ |A(z_0)| = ∫_E d_A d_B`, a large fiber | 2026-09-26T10:39:43-04:00
complete | lines 558-576, (3.14) | the three relations and `μ^3 ≤ C ε^{1/13}` (case `|α| ≥ c_0`) | 2026-09-26T10:39:43-04:00
complete | lines 578-587, Lemma 3.1 | the case `|β| ≥ c_0`, (3.1) with `κ = 1/39` | 2026-09-26T10:39:43-04:00

## Section 4: a positive `L^p`-improving bound

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | lines 598-619, (4.2) | density `k` of `μ * μ̃`, `∫ k^{3/2} < ∞` | 2026-09-26T10:39:43-04:00
complete | lines 620-637, (4.3) | `‖u * v‖_3 ≤ ‖u‖_{3/2} ‖v‖_{3/2}` | 2026-09-26T10:39:43-04:00
complete | lines 639-646, (4.4) | `‖μ * f‖_2 ≤ C ‖f‖_{3/2}` | 2026-09-26T10:39:43-04:00
complete | lines 648-668, (4.1) | `B(F,G) ≤ C ‖F‖_{12/7} ‖G‖_{12/7}` and (4.1) | 2026-09-26T10:39:43-04:00

## Section 5: the local correlation estimate

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | lines 714-733, (5.6) | compatible pairs, `O(h^{-3})` count, reference parameters | 2026-09-26T10:39:43-04:00
complete | lines 735-788, (5.7) | squaring, tangent replacement, error `C B_1 B_2 L^{1/2} h` | 2026-09-26T10:39:43-04:00
complete | lines 790-831, (5.8)-(5.10) | continuous Fourier expansion, kernel bound (5.9), weighted correlation (5.10) | 2026-09-26T10:39:43-04:00
complete | lines 833-848, (5.11) | Cauchy-Schwarz in `s`, Hölder `(4,4,2)` over pairs | 2026-09-26T10:39:43-04:00
complete | lines 850-891, (5.12)-(5.14) | total Fourier energy, slope counting | 2026-09-26T10:39:43-04:00
complete | lines 893-912, (5.15), Lemma 5.1 | low Fourier energy and (5.5) | 2026-09-26T10:39:43-04:00

## Section 6: local smoothing for bounded, frequency-localized inputs

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | lines 939-982, (6.2)-(6.5) | spatial localization preserving frequency restriction, commutator error | 2026-09-26T10:39:43-04:00
complete | lines 983-1026, (6.6)-(6.8) | fiberwise decomposition, energy, uniformity, component bounds | 2026-09-26T10:39:43-04:00
complete | lines 1029-1051, (6.9)-(6.10) | the terms containing a flat part | 2026-09-26T10:39:43-04:00
complete | lines 1053-1077, (6.11) | the elementary nonstationary estimate | 2026-09-26T10:39:43-04:00
complete | lines 1080-1112, (6.12)-(6.14) | sharp-sharp term, nonstationary contributions | 2026-09-26T10:39:43-04:00
complete | lines 1113-1151, (6.15)-(6.16) | stationary contributions via Lemma 3.1 | 2026-09-26T10:39:43-04:00
complete | lines 1154-1187, (6.17)-(6.18), Proposition 6.1 | parameter choice and (6.1) | 2026-09-26T10:39:43-04:00

## Section 7: global `L^2` smoothing

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | lines 1194-1210, (7.1)-(7.2) | the two endpoint bounds for `S_L` | 2026-09-26T10:39:43-04:00
complete | lines 1211-1249, (7.3) | three-lines interpolation and density | 2026-09-26T10:39:43-04:00
complete | lines 1253-1272, (7.4) | spatial tails | 2026-09-26T10:39:43-04:00
complete | lines 1274-1305, (7.5)-(7.7) | globalization | 2026-09-26T10:39:43-04:00

## Section 8: high-frequency tail, `C^1` cutoff, monomials

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | lines 1311-1340, (8.1)-(8.2) | telescoping and the high-frequency tail | 2026-09-26T10:39:43-04:00
complete | lines 1344-1386, (8.3)-(8.6) | mollification of the cutoff, (8.5) | 2026-09-26T10:39:43-04:00
complete | lines 1389-1419, (8.7)-(8.8) | substitution `u = t^m`, (T) | 2026-09-26T10:39:43-04:00
