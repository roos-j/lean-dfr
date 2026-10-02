# CDR source discrepancies (arXiv:2008.10140v2, `cdr.tex`)

2026-10-01T07:11:11-04:00 - Reading audit of Sections 2 and 5.1; typographical slips resolved by the evident
intended meaning, none affecting Theorems 1-4:
- line 445: `ℓ = 1,2,3` should be `ℓ = 1,2` (functions on `ℝ^2`).
- line 517: `-2^{k+1} ≤ ℓ ≤ 0` should be `-2^{κ+1} ≤ l ≤ 0`.
- lines 2066-2068 (`I_4`, `I_5`): with the convention `(f *_1 φ)(x,y) = ∫ f(x-u,y) φ(u) du` the factor
  `f(x+t,y)` averaged against `τ_{k'}(t)` is `f *_1 τ̃_{k'}` with `τ̃(u) = τ(-u)`, not `f *_1 τ_{k'}`. The
  estimates for `I_4`, `I_5` are unchanged with `τ̃`.
- line 2105: `(dychotomy2)` bounds a sum of two norms below by `2^{-10} c_0 ε^4`, so the squared sum is at
  least `2^{-21} c_0^2 ε^8`; the count is `L ≲ ε^{-8}`, not `ε^{-4}`. The conclusion `I > exp(-exp(ε^{-C}))`
  is unaffected (a larger `C`).

2026-10-01T08:39:35-04:00 - Section 5.1, route and formulation choices (Theorem 4 proved as stated):
- `lem:lowerbd` (lines 2034-2039) is proved without the hypothesis that `f` is supported in
  `[0,1]^2` (the bound holds for every measurable `0 ≤ f ≤ 1`); "monotone on `[1,2]`" is formalized as
  `MonotoneOn ∨ AntitoneOn`. The proof of Theorem 4 uses the core bound `Auto.CDR.lowerbd_core`
  (constant `ϑ(0)^2`, hypotheses: continuous, compactly supported, `ϑ ≥ 0`, constant on `[-1,1]`,
  `ϑ(0) > 0`) for the concrete bump `ϑ = ` normalized `ContDiffBump` with radii `1, 2`, which avoids
  verifying monotonicity of that bump. `lem:lowerbd` itself is the case `ϑ(0) > 0` derived from its
  hypotheses (`Auto.CDR.theta_zero_pos`).
- lines 2058-2059 (`I_3`): instead of a dyadic decomposition of `f - f *_2 ϑ_{k''}` into frequency
  blocks, a two-piece split at frequency `Λ = 2^{5k}` is used: the low part has `L^2` norm
  `≲ Λ 2^{-k''}` (since `|1 - ϑ̂(η)| ≲ |η|`), the high part is estimated by the global smoothing
  inequality `Auto.ms8_plane` rescaled to the scale `2^{-k'}`. Same bound `≲ 2^{-c(k''-2k')}`.
- lines 2072-2081 (`I_5`) and 2103-2106 (Plancherel): the convolution identities are replaced by
  pointwise bounds of the fiberwise Fourier multipliers (`τ̂ - ϑ̂_k = τ̂(ϑ̂_{k''} - ϑ̂_k) +
  τ̂(1 - ϑ̂_{k''}) - ϑ̂_k(1 - τ̂)`), giving the stated bounds; the almost orthogonality of the
  increments uses the telescoping weight `s^2/(1+s^2)`.
- lines 2086-2101: the parameters are fixed as `k' = 2k`, `k'' = 6k`, `k_{l+1} = 6 k_l` (the source's
  "sufficiently large `M`" is `6`), with `k_0 ≈ ε^{-4}` and `L ≈ ε^{-8}` (see the entry above on
  `ε^{-8}`); the error terms are `O(2^{-δ k})` with `δ = min(δ_smoothing, 1)`.
- Theorem 4 (line 2031): from `I > δ` one gets a pattern with `t > δ/2`; the factor `1/2` is
  absorbed by passing from `C` to `C + 1` (`Auto.CDR.exp_neg_exp_half`). The statement is formalized
  on `ℝ × ℝ` with `E ⊆ [0,1]^2` measurable and `ε ≤ |E|`.

## 2026-10-01T10:06:34-04:00 - Section 2.6 (Theorem 3): route choices

- lines 652-670 (`M^L_j`, `M^M_j`): the source puts the mixed terms `M_j(Δ_{j+k} f_1, S_{2j+k-101} f_2)`
  in the kernel form `eqn:max-red-1` by the non-stationary phase argument of §2.5. Because `M_j` has a
  nonnegative kernel and the inputs may be taken to be `a = |f_1|`, `b = |f_2|` (line 649), this is
  replaced by the identity `M_j(a,b) = M_j(a, S_{2j} b) + M_j(S_j a, b) - M_j(S_j a, S_{2j} b) +
  M_j(a - S_j a, b - S_{2j} b)`: the first three terms are dominated pointwise by
  `𝓜^{(1)} a · 𝓜^{(2)} b` (`Auto.CDR.lowPart_bound`; the parabolic average is controlled through the
  substitution `u = t^2`). The last term is `∑_{k_1, k_2 ≥ 1} M_j(Δ_{j+k_1} a, Δ_{2j+k_2} b)`, i.e. all of
  `{max(k_1,k_2) > 0} ∖ {min ≤ 0}` is treated by the high-frequency argument (`F_H` in the source).
  This is legitimate since `eqn:max-l2-decay` (Theorem 5 / `Auto.CDR.Mj_gain`) holds with decay
  `2^{-δ max(k_1,k_2)}` for every `k_1, k_2 ≥ 1`, and `eqn:shiftedmax-max` has loss polynomial in
  `k_2` only. No error in the source.
- `lem:shiftedmaxfct` (lines 474-519) is proved directly at scale `2^{-j}` (no dilation step,
  lines 482-491), for the bump `ψ(2^j t) 2^j` of `M_j`, with explicit shifts
  `σ_{l,n} = (l^2 2^{-κ} - n - 5)/16` and coefficients `C 2^{-κ} (1+|n|)^{-4}`,
  `|l| ≤ 2^{κ+1}`; then `∑_{l,n} a_{l,n} log(2+|l|)^{1/p} log(2+|σ_{l,n}|)^{1/q} ≲ (κ+5)^2`, which is
  the case `a = 1/p`, `b = 1/q` of `eqn:shiftedmaxfct-coeff` with exponent `2` instead of `a+b`
  (sufficient for the interpolation, which only needs subexponential growth).
- line 681: the pointwise bound `|Δ^{(1)}_m a| ≤ C 𝓜^{(1)} a` is used to pass from
  `𝓜_σ Δ_{j+k_1} a` to `𝓜_σ (C 𝓜^{(1)} a)`, uniformly in `j`, as in the source.

## 2026-10-01T10:29:38-04:00 - Theorem 3: interpolation and limits

- lines 689-692 ("Interpolation with `eqn:Mk-l2-decay`"): `M^{(k)}` is sublinear; the bilinear
  interpolation theorem is applied to the linearization `u(z) M_{σ(z)}(Δ f, Δ g)(z)` with a measurable
  maximizing selector `σ` over a finite set of scales and a phase `|u| ≤ 1`, on simple functions, with
  endpoints `(2,2,1)` and `(p_1,q_1,r_1)` on the ray from `(1/2,1/2)` through `(1/p,1/q)`
  (`Auto.CDR.interp_endpoint`, `ε = min(1/p, 1/q, 1 - 1/p, 1 - 1/q)`). The passage from simple
  functions to bounded integrable functions uses `approxOn` (`|s_n| ≤ 2|f|`, constant loss `4`), and
  the passage to `sup_{j ∈ ℤ}` monotone convergence.
- `eqn:max-l2-decay` needs every fibre of the inputs integrable (Theorem 5 is applied fibrewise); for
  general integrable inputs this holds off a null set of fibres, and the inputs are modified on that
  null set (`Auto.CDR.exists_fib_integrable_modification`), which changes `M_j` only on a null set.
- Theorem 3 is stated for test functions `f_1, f_2 ∈ C_c^∞(ℝ^2)` (as in the source); the proof uses only
  that `|f_1|, |f_2|` are continuous, bounded and integrable.

## 2026-10-01T11:45:58-04:00 - Section 4 (Theorem 2): route choices so far

- `lemma:telescoping` (§4.3, `DFR/Auto/CDR/Sec4SmoothCase3Telescoping.lean`): with the conventions of the
  formalization (`∫_{ℓ/2}^{ℓ} -t ∂_t F dt/t = F(ℓ/2) - F(ℓ)`) the identity reads
  `α Θ^{(1)} + β Θ^{(2)} = Ξ_{𝓛(𝒯)} - Ξ_{\{Q_𝒯\}} - π 𝓑`, i.e. the endpoint terms appear as leaves minus
  root (the source writes root minus leaves); only the absolute bound `eqn:barkest-final` is used later,
  so the sign is immaterial. The power is `(λ(1+|r|))^{21}` instead of `^{11}`.
- `eqn:treecountingest` (lines 1850-1866) is proved by a different counting argument: if `Q ∈ 𝒯` and its
  neighbour `Q + e_1 ∉ 𝒯`, then `Q + e_1` is a leaf, or `Q` is the root, or `Q` lies on the right edge of
  its parent, which has the same property; this gives `∑_{Q ∈ 𝒯, Q ± e_i ∉ 𝒯} |Q| ≤ 4|Q_𝒯|`. The source's
  disjoint-rectangles argument is not used.
- `lem:bdbymax` is proved with the pointwise inequality `|abcd| ≤ (ε a^2 b^2 + ε^{-1} c^2 d^2)/2` and
  factorization instead of two Cauchy-Schwarz inequalities (same bound).
- §4.2 (tree estimate): the Cauchy-Schwarz inequalities are used in the AM-GM form
  `|∫ U V w| ≤ (ε ∫ U^2 w + ε^{-1} ∫ V^2 w)/2` followed by optimization in `ε`; the index `r = 1` in
  "`Θ^{(2)}_{𝒯,λ,1}(f_1,f_3,f_3,f_1)`" (line 1734) is read as `r = 0`, which is what the computation gives
  (the factor `h_{t^β,q}(y)` there is unshifted). In the definition of `Λ^{(u,v)}_𝒬` (lines 1602-1606) the
  roles of `x, x'` and `y, y'` in the kernels are those of the rewritten form used in §4.2 (lines
  1700-1705): `g_{t^α,p}(x) (φ̌_{1,u})_{t^α,p}(x') h_{t^β,q}(y) (h * ψ̌_{1,v})_{t^β,q}(y')`; the source's
  displayed definition places `φ̌` on `x` and the convolution on `y`, which is inconsistent with its own
  rewriting (typo).
- §4.5 (`DFR/Auto/CDR/Sec4SmoothCase5FiberwiseCZ.lean`): on a selected interval the good part is the
  ordinary average of `f_1` (the source's `|I|^{-1/p} ‖f_{1,y}‖_{L^p(I)}` does not make the bad atoms mean
  zero; this is a typo in the source); the selection still uses `|f|^p` averages. The final Hölder step
  is replaced by `{|U(b,f_2)| > Kλ} ⊆ {h ≥ 1/4} ∪ {𝓜^{(2)} f_2 > λ^{r/q_0}}`, which needs only `‖h‖_1 ≲ λ^{-r}`
  (so the `L^p` bound for `h`, Grafakos Exercise 4.6.6, is not needed). The second fiber is obtained from
  the first by swapping the coordinates.

## 2026-10-01T12:12:29-04:00, Theorem 1 route choices (§2.3)

- `eqn:shiftedfs` (vector-valued shifted Fefferman-Stein inequality, cited from [GHLR17, Thm 3.1]) is not
  formalized. In the proof of `lem:shiftedmaxfct` every average is taken at a single scale tied to `j`
  (`|I_l| = 2^{-j-κ}`, `|J_l| ≍ 2^{-2j-κ}`), so the domination is kept with these fixed-scale shifted averages
  instead of `𝓜_σ`. For linear fixed-scale averages the vector-valued bound
  `‖(∑_j |A_{σ,s_j} g_j|^2)^{1/2}‖_p ≲ log(2+|σ|) ‖(∑_j |g_j|^2)^{1/2}‖_p` follows for `p ≥ 2` from Jensen and
  duality against `L^{(p/2)'}` weights with the scalar bound `eqn:shiftedmaxfct-basic`, and for `p < 2` by
  duality (the adjoint is again a fixed-scale shifted average). This gives the same polynomial bound in
  `|k|` for `T^{(k)}`.
- `ψ̃` is chosen as `ψ(2·) + ψ + ψ(·/2) = φ(·/2) - φ(4·)`, which is smooth and equals one on the support of
  `ψ` (the source's "say, supported in a 1/100-neighborhood" is only an example), so `Δ̃_m = Δ_{m-1} + Δ_m +
  Δ_{m+1}` and its square function is controlled by the Littlewood-Paley inequality for `Δ`.

## 2026-10-01T14:05:00-04:00, §4.1 and §4.4 route choices

- §4.1: the decomposition `mdecompose2` is obtained from the fundamental theorem of calculus for
  `t ↦ φ(t^α ξ) φ(t^β η)` (equivalent to the source's splitting of the double integral at `t = s`).
  `T_m` is formalized on the Fourier side with `m(-ξ,-η)` (the source's kernel form with `K̂ = m`,
  Mathlib's normalization of `𝓕`). The constant of Theorem 2 depends on the symbol only through the
  constant in `symest`.
- §4.4: the limiting argument from the localized forms to the trilinear form of the model operator is
  done with aligned boxes of dyadic rectangles (`boxColl`), dominated convergence, and Fubini;
  the kernels of the model operator are the correlations `corrK` (`gconv`, `hhconv` up to reflection).
- `DFR/Auto/BilinearMarcinkiewicz.lean`: the auxiliary declarations were moved into the
  subnamespace `Auto.BilMarc` (generic names such as `piece` clashed with
  `DFR/Auto/SmoothingIneq3D/Smoothing3D.lean`); `bilinear_marcinkiewicz` is exported to `Auto`.

## 2026-10-01T16:40:00-04:00, Theorem 1 route choices (§2.1, §2.3-2.5)

- `eqn:HHT0`: the `L^2` decay is obtained from the global form of Theorem 5 (`scaled_smoothing_gen`, as in
  Theorem 3), so the spatial localization with `η_m`, `η̃_m` and the error terms II, III is not needed.
- §2.4-2.5: the low and mixed parts are identified with `T_m` on the Fourier side (symbols `symSum lowNu`,
  `symSum mixNuI`, `symSum mixNuII`) instead of through the kernel forms `K = ∑_j 2^{3j} κ(2^j·, 2^{2j}·)`; the
  mean-zero property of `κ` becomes `ϑ(0) = ∫ ψ(t)/t dt = 0`. The `k > 0` sums of the source are indexed by
  `k + 1`, `k ≥ 0`.
- The bound for `T` is proved for the truncated sums `∑_{|j| ≤ J} T_j` (all constants uniform in `J`) and
  passed to the principal value by Fatou's lemma; Theorem 2 is applied with a constant depending only on the
  symbol-estimate constant, which is uniform in `J`.
- Theorem 1 is stated as the a priori inequality for test functions (the extension to `L^p × L^q` follows by
  density, as for Theorems 2 and 3).
