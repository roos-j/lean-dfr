# Task 4 status: `thm:main` of `blueprints/main.tex` by reduction to Tasks 1-3
## Main theorem overview

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | `thm:main`, lines 139-148 | `‖T(f)‖_p ≤ C ∏ ‖f_n‖_{p_n}` for `p ∈ (1, 4/3)`, `p_n ∈ (1, 4)`, `∑ 1/p_n = 1/p`, Schwartz `f_n` | 2026-09-26T10:41:25-04:00

## Section 1: the operator

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | line 134-137 | the principal value `T(f)(x) = p.v. ∫ ∏ f_n(x + t^n e_n) dt/t` exists for Schwartz `f_n` | 2026-09-25T21:37:17-04:00

## Section 2.1: Littlewood-Paley decompositions

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | lines 273-288 | `φ`, `ψ = φ - φ(2·)`, `ψ_j`, `φ_j`; `supp ψ_j ⊆ {2^{j-1} ≤ |ζ| ≤ 2^{j+1}}`, `∑_j ψ_j(ζ) = 1` for `ζ ≠ 0` | 2026-09-25T21:39:19-04:00
complete | lines 289-293 | partial operators `Δ^{(ℓ)}_j`, `S^{(ℓ)}_j` on `ℝ^3` | 2026-09-25T21:41:30-04:00
complete | lines 295-303 | `ψ̃`, `ψ̃_j ψ_j = ψ_j`, `Δ_j Δ̃_j = Δ̃_j Δ_j = Δ_j` | 2026-09-25T21:41:30-04:00
complete | lines 305-308 | scale decomposition `T = ∑_j T_j` | 2026-09-25T21:44:43-04:00
complete | lines 315-325 | the partition `ℤ^3 = F_L ∪ F_ML ∪ F_MH ∪ F_H` | 2026-09-25T21:47:32-04:00
complete | lines 326-340 | `T^ω = ∑_j T^ω_j`, the splits `F_{ML,n}`, `F_{MH,n}` | 2026-09-25T21:58:03-04:00
complete | `eqn:basicfreqdecomp`, `eq:decomposition_k`, lines 311-345 | `T = T^L + T^ML + T^MH + T^H`, `T = ∑_k T^{(k)}` for Schwartz inputs | 2026-09-25T21:58:03-04:00

## Section 4 (imported): `thm:main_twist` from Task 3

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | `thm:main_twist`, lines 223-245 | Task 3 `Auto.Twisted.thm_main` for `α = (1,2,3)`: from the four-linear form bound to the operator bound by `L^p`-duality, `p' ∈ (4, ∞)` | 2026-09-25T22:05:58-04:00
complete | `thm:main_twist`, line 225, `eq:symbol_condition` | the kernel side: `Γ(f)` paired with `f₀` is Task 3's `multiplierForm` with `m = K̂` | 2026-09-25T22:05:58-04:00

## Section 2.2: low frequencies

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | line 356 | `T^L(f) = ∑_j T_j(f_1 *_1 φ̌_j, f_2 *_2 φ̌_{2j}, f_3 *_3 φ̌_{3j})` | 2026-09-25T22:10:28-04:00
complete | lines 370-374 | `κ_L` is Schwartz and `κ̂_L(0) = 0` | 2026-09-25T22:25:25-04:00
complete | line 374 | `K̂_L` satisfies `eq:symbol_condition` (anisotropy `(1,2,3)`): the truncated dyadic sums `∑_{|j| ≤ J} κ̂_L(D_{2^{-j}} ξ)` uniformly | 2026-09-25T22:26:05-04:00
complete | lines 358-369 | the kernel form with `K_L = ∑_j 2^{6j} κ_L(2^j u, 2^{2j} v, 2^{3j} w)` | 2026-09-25T22:36:34-04:00
complete | lines 376-379 | `‖T^L(f)‖_p ≤ C ∏ ‖f_n‖_{p_n}` by `thm:main_twist` | 2026-09-25T22:38:25-04:00

## Section 2.3: mixed frequencies ML

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | lines 411-418 | non-stationary phase: `|∂^α θ(ξ)| ≤ C(α,N)(1+|ξ|)^{-N}` on the support | 2026-09-25T23:01:15-04:00
complete | lines 402-409 | `κ̂_{ML,1}` and its vanishing near the origin | 2026-09-25T23:07:52-04:00
complete | lines 420-421 | `κ_{ML,1}` is Schwartz; `K̂_{ML,1}` satisfies `eq:symbol_condition` | 2026-09-25T23:07:52-04:00
complete | line 387 | `T^{ML,1}(f) = ∑_j ∑_{k>0} T_j(f_1 *_1 ψ̌_{j+k}, f_2 *_2 φ̌_{2j+k-101}, f_3 *_3 φ̌_{3j+k-101})` | 2026-09-25T23:17:40-04:00
complete | lines 389-400 | the kernel form with `K_{ML,1}` and `κ_{ML,1}` | 2026-09-25T23:17:40-04:00
complete | lines 423-426 | `‖T^{ML,1}(f)‖_p ≤ C ∏ ‖f_n‖_{p_n}` by `thm:main_twist` | 2026-09-25T23:19:57-04:00
complete | line 383 | the cases `T^{ML,2}`, `T^{ML,3}` | 2026-09-25T23:19:57-04:00

## Section 3 (imported): `thm:smoothing` from Task 2

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | `thm:smoothing`, lines 190-203 | Task 2 `Auto.mainTheorem` restated for Schwartz inputs | 2026-09-25T23:22:59-04:00

## Section 2.4: high frequencies H

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | `lem:gain` proof, lines 460-463 | single-scale gain from `thm:smoothing` after anisotropic rescaling | 2026-09-25T23:36:43-04:00
complete | `lem:gain` proof, lines 464-467 | Hölder in `j` with exponents `(p_1, p_2, p_3)` | 2026-09-25T23:57:04-04:00
complete | `lem:gain` proof, lines 468-471 | `ℓ^{p_n} ⊆ ℓ^2` and the partial Littlewood-Paley square function in `L^{p_n}` | 2026-09-25T23:53:37-04:00
complete | `lem:gain`, `eq:gain`, lines 440-447 | `‖T^{(k)}(f)‖_1 ≤ C 2^{-δ k^{(1)}} ∏ ‖f_n‖_{p_n}`, `p_n ≥ 2`, `∑ 1/p_n = 1` (the case `p = 1` proved in the source; see ErrorReport), `Auto.gain_one` | 2026-09-25T23:57:10-04:00
superseded (ErrorReport 2026-09-26T00:06) | line 477-480 | the shifted dyadic maximal function `M_σ` | 2026-09-25T21:31:10-04:00
superseded (ErrorReport 2026-09-26T00:06) | `lem:shifted_max` proof, lines 499-515 | the splitting into `I_l`, `I_m`, `I_n` with the rapid decay of `ψ̌` | 2026-09-25T21:31:10-04:00
superseded (ErrorReport 2026-09-26T00:06) | `lem:shifted_max` proof, lines 517-536 | the intervals `J_{l,m}`, `K_{l,n}`, shifts `σ_1, σ_2, σ_3`, both signs of `l` | 2026-09-25T21:31:10-04:00
superseded (ErrorReport 2026-09-26T00:06) | `lem:shifted_max`, `eq:est_shifted_max`, `eq:summability`, lines 484-497 | the pointwise bound and the summability condition, and the two analogous operators | 2026-09-25T21:31:10-04:00
superseded (ErrorReport 2026-09-26T00:06) | `eq:single_scale`, lines 539-548 | dilation invariance, `D_a M D_{1/a} = M` | 2026-09-25T21:31:10-04:00
superseded (ErrorReport 2026-09-26T00:06) | `lem:loss` proof, lines 550-557 | Hölder `(2,2,∞)` in `j` and `(p_1,p_2,p_3)` in `x` | 2026-09-25T21:31:10-04:00
superseded (ErrorReport 2026-09-26T00:06) | `lem:loss` proof, line 558 | `|Δ_j g| ≤ C M g` | 2026-09-25T21:31:10-04:00
superseded (ErrorReport 2026-09-26T00:06) | `lem:loss` proof, lines 559-562 | `‖M_σ g‖_p ≲ log(2+|σ|)^{1/p} ‖g‖_p` and the vector-valued bound (GHLR17 Thm 3.1) | 2026-09-25T21:31:10-04:00
superseded (ErrorReport 2026-09-26T00:06) | `lem:loss`, `eq:loss`, lines 448-455, 564-568 | `‖T^{(k)}(f)‖_p ≤ C |k|^5 ∏ ‖f_n‖_{p_n}` | 2026-09-25T21:31:10-04:00
complete | line 456 (alternative route) | Cauchy-Schwarz in `t`: `|T_j(g)(x)| ≤ sup_{|t| ≤ 2^{1-j}} |g_1(x+te_1)| (∫|g_2(x+t^2e_2)|^2 w_j)^{1/2} (∫|g_3(x+t^3e_3)|^2 w_j)^{1/2}` | 2026-09-26T00:08:38-04:00
complete | line 456 (alternative route) | the `∞` slot: `|Δ_m g(x+te_1)| ≤ C (1+R)^{10/s} (M^{(1)}|Δ_m g|^s)^{1/s}(x)` for `|t| ≤ R 2^{-m}`, from `Δ_m = Δ̃_m Δ_m` | 2026-09-26T00:16:26-04:00
complete | line 456 (alternative route) | the `L^2` slots: `‖∑_j ∫|G_j(·+t^n e_n)|^2 w_j‖_{ρ} ≲ ‖∑_j |G_j|^2‖_{ρ}`, `ρ ≥ 1`, by duality with `M^{(n)}` | 2026-09-26T00:32:27-04:00
complete | line 456 (alternative route) | the small-loss bound `‖T^{(k)}_J(f)‖_{q/3} ≤ C_q 2^{40(k^{(1)}+2)/q} ∏ ‖f_n‖_q`, `q ≥ 6` | 2026-09-26T00:39:52-04:00
complete | line 456 | extension of `T^{(k)}_J` in slot `0` to bounded measurable inputs (`Auto.kComp0`, line convolution `Auto.lineDelta`), linearity, measurability, the crude bound via Minkowski/Young/Hölder (`Auto.kComp0_crude`) | 2026-09-26T00:57:13-04:00
complete | line 456 | transfer of the vertex bounds from Schwartz to bounded inputs and back by density (`Auto.eLpNorm_bound_transfer`, `Auto.kComp0_bound_of_schwartz`, `Auto.kComp0_bound_of_simple`) | 2026-09-26T00:57:13-04:00
complete | line 456 | interpolation in slot `0` (Riesz-Thorin, lean-spherical `Auto.SteinInterpolation.riesz_thorin`) between `lem:gain` at `(1 - 1/p_1 - 1/p_2, 1/p_1, 1/p_2; 1)` and the small-loss bound at `(ε, 1/p_1, 1/p_2)`: exponential gain for all `p_n > 2`, `1/p_1 + 1/p_2 ≥ 1/2`, `p > 1` | 2026-09-26T01:04:32-04:00
complete | `eq:final_gain`, lines 430-437, 456 | summation over `k ∈ F_H`: `‖T^H(f)‖_p ≲ ∏ ‖f_n‖_{p_n}` | 2026-09-26T01:11:11-04:00

## Section 3: `thm:smoothing_2`

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | `thm:smoothing_2`, lines 205-221, statement | the statement for distinct positive integers `α_1, α_2`, `ψ ∈ C^1`, `supp ψ ⊆ [a,b]`, constant `C (‖ψ‖_∞ + ‖ψ'‖_1) λ^{-δ(a,b,‖ψ'‖_1)}` (`Auto.SmoothingTwo`) | 2026-09-26T06:53:26-04:00
complete | `thm:smoothing_2`, line 705, proof | "analogous to Theorem 5 of CDR21" (hypothesis of `thm:main` per user instruction) | 2026-09-26T10:41:25-04:00

## Section 2.5: mixed frequencies MH

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | lines 579-593 | `T^{(k_2,k_3)}`, `F_{MH,1,±}`, `T^{(k_2,k_3)} = ∑_{k_1} T^{(k)}` | 2026-09-26T07:08:17-04:00
complete | `lem:gain_2+`, lines 595-602, 622-624 | exponential gain on `F_{MH,1,+}`, `2^{-δ|k|} ≃ 2^{-δ k^{(1)}}` | 2026-09-26T01:22:02-04:00
complete | `lem:gain_2-` proof, lines 637-647 | Fubini reduction to the fibre forms with `ρ_s(t) = ψ(t) t^{-1} φ̌(t-s)` | 2026-09-26T07:17:25-04:00
complete | `lem:gain_2-` proof, lines 648-651 | `thm:smoothing_2` on each fibre, Cauchy-Schwarz in `x`, decay of `φ̌`: `eq:mixedfreqpenult` | 2026-09-26T07:49:02-04:00
complete | `lem:gain_2-` proof, lines 631-635 | Hölder `(∞,2,2)` in `j`, `|S_j g| ≤ C M g`, Plancherel | 2026-09-26T07:57:21-04:00
complete | `lem:gain_2-`, `eq:gain_2-`, lines 603-608 | `‖T^{(k_2,k_3)}(f)‖_1 ≤ C 2^{-δ max(k_2,k_3)} ‖f_1‖_∞ ‖f_2‖_2 ‖f_3‖_2` | 2026-09-26T07:57:21-04:00
superseded (ErrorReport 2026-09-26T06:53) | `lem:loss_2`, lines 612-619, 654-656 | polynomial loss for `T^{(max(k_2,k_3)-100, k_2, k_3)}` | 2026-09-25T21:31:10-04:00
complete | line 620 (alternative route) | loss-free bound for the grouped operators at `(1/q_0, 1/q_1, 1/q_2)`, `q_0 ∈ (1, ∞]`, `q_1, q_2 ∈ [2, ∞)`: `|S g(x+te)| ≤ C M g(x)`, Cauchy-Schwarz in `t`, duality for the `L^2` slots | 2026-09-26T08:14:40-04:00
complete | line 620 | interpolation and summation over `F_{MH,1}`: `‖T^{MH,1}(f)‖_p ≲ ∏ ‖f_n‖_{p_n}` | 2026-09-26T08:33:02-04:00
complete | line 573 | the cases `T^{MH,2}`, `T^{MH,3}` | 2026-09-26T08:33:02-04:00

## Section 2: assembly

status | exact source location | brief mathematical step | ISO 8601 timestamp with offset
--- | --- | --- | ---
complete | `thm:main`, lines 139-148 | `‖T(f)‖_p ≤ ‖T^L‖ + ∑‖T^{ML,n}‖ + ∑‖T^{MH,n}‖ + ‖T^H‖` | 2026-09-26T08:36:08-04:00
