

## Measurability of a real power, and how to get it

Deriving measurability of a real power from continuity works only when the
exponent is nonnegative; for a negative exponent the function blows up at the
origin and is not continuous there, though it remains perfectly measurable.
The route taken elsewhere in this file — derive global continuity from the
pointwise statement, then compose — therefore fails for the test function used
in the duality argument, whose exponent is two less than the output exponent
and so may be negative.

The automation knows the fact directly. Where a measurability goal involves a
real power with a possibly negative exponent, discharge it with the
function-property tactic rather than routing through continuity.

## Duplicated an existing estimate-transfer lemma

I proved a Fatou transfer for the `R`-th power lower integral under
almost-everywhere convergence, only to find `lintegral_rpow_le_of_ae_tendsto`
already in the file — and strictly more general: an arbitrary measure space, an
arbitrary bound in `ℝ≥0∞`, and `AEMeasurable` rather than
`AEStronglyMeasurable` hypotheses.  The duplicate was removed.

The near miss is instructive.  I searched for the blueprint label and for the
phrase "Fatou", and neither hit, because the existing lemma is filed under the
approximation step of `lem:one_fiber` and never names Fatou.  Worse, the
operator-level consequence
`lintegral_rpow_ModelTruncatedOperator_le_of_ae_tendsto` was also already
present, so the step I had just identified as "the next target" was finished.

The search that would have found both is a search for the *shape of the
conclusion* — here `∫⁻ .* ofReal .* ≤` together with `ae_tendsto` — rather than
for the name of the technique or the label of the source.  Technique names are
the least reliable index into this file, since the prose describes what the
source does, not which theorem is being invoked.

## Missing prerequisite: Young's inequality for convolution

Neither Mathlib nor the pinned `lean_spherical` provides any `L^p` bound for a
convolution.  Searches for `eLpNorm_convolution`, convolution Young
inequalities, and Minkowski's integral inequality all come back empty;
Mathlib's `MeanInequalities` has Minkowski only for sums of two functions, not
the integral form.

This matters because the approximation step of `lem:one_fiber` needs the
Schwartz approximants' `L^q` norms controlled uniformly, and the approximants
are built by mollification.  The needed statement is the contraction case
only — convolution against a nonnegative kernel of unit mass does not increase
an `L^q` norm, `q ≥ 1` — which follows from Hoelder applied to the splitting
`φ = φ^{1/q'} · φ^{1/q}` followed by Tonelli and translation invariance.  It is
being formalized under these instructions as an unexpectedly needed
prerequisite rather than treated as missing source material, since the
manuscript legitimately treats it as background.

## Duplicated the interpolation toolkit, and the lesson that was already here

Asked to prove `ext:interpolation`, I built a dyadic level decomposition
(`dyadicLevelSet`, `dyadicLevelPiece`, `dyadicLevelIndices`,
`sum_dyadicLevelPiece`, `measure_dyadicLevelSet_le`,
`eLpNorm_dyadicLevelPiece_le`) and a three-slot trilinear expansion, only to
find that the file already contained all of it: `dyadicLayer`, `dyadicLayerSet`,
`dyadicLayerIndices`, `sum_dyadicLayerIndices`, the two-sided layer norm bounds,
and `trilinear_expand_three_finsets` — the last in a cleaner form than mine,
stated for a curried trilinear map on arbitrary functions rather than through
`Function.update`.  The file also already had the two-point weak-to-strong
passage `lintegral_rpow_le_of_two_weakNorm`, which I was about to build from
scratch, the level splitting `meas_lt_of_triple_expansion_bounds`, the
four-vertex geometric mean `norm_triple_finset_sum_le_geometric_mean`, and the
exponent bookkeeping.

The entry above — "Duplicated an existing estimate-transfer lemma" — records
exactly the right lesson and I did not apply it: search for the *shape of the
conclusion*, not for a technique name or a blueprint label.  Searching for
`ext:interpolation` and for "Marcinkiewicz" found only the hypothesis
definition, because the toolkit is filed under section headings that name what
the source does (`Dyadic level layers`, `Trilinear expansion over finite
decompositions`, `The weak-to-strong passage`).  A search for `Finset.sum` with
`weakNorm`, or for `∑ k1 ∈ S1, ∑ k2 ∈ S2`, would have found it immediately.

The practical rule, now twice learned: before building anything for a named
external theorem, list the section headings and declaration names in the file
region that theorem lives in, and grep for the shape of the intended
conclusion.

## An inaccurate cross-reference in the interpolation docstring

The section docstring for `ext:interpolation` states that two dependency audits
are "recorded in ErrorReport.md".  They are not in this file.  The claims
themselves — that the pinned `lean_spherical` does not supply multilinear
Marcinkiewicz, and that iterating unary Marcinkiewicz slot by slot cannot reach
a point interior to the three-dimensional tetrahedron — are both correct, and
the second was re-derived independently: two-point interpolation yields bounds
only at points of the segment joining two vertices, so no iteration of it
reaches the interior of a three-dimensional simplex.  The docstring has been
amended to state the conclusions rather than cite a location that does not hold
them.

## Missing prerequisite: the real interpolation method

`ext:interpolation` cannot be closed with the tools available.  The gap is not a
missing step in the argument but a missing piece of background theory, and it is
worth naming precisely so it is not searched for again.

Everything up to the last step is now in the file.  The four endpoint weak bounds
combine at any interior exponent (`weakNorm_le_of_four_weakNorm`); that combines
losslessly into a strong `L^R` bound at any weight vector whose exponent is `R`
(`lintegral_rpow_le_of_symmetric_weight_pair`); affine independence forces `R` to
be strictly straddled (`exists_straddling_output_exponents`); the trilinear
expansion over any finite decomposition is available
(`trilinearOnSimple_expand_three_general`); the level split with a tent share is
available and costs nothing (`exists_normalized_lattice_tent`,
`sum_tent_levels_le`); the multi-index sum of a two-sided geometric minimum is
bounded by the geometric mean of its two constants
(`exists_sum_min_two_geometric_bound`); and the bands aggregate in `ℓ^q`
(`lintegral_rpow_enorm_sum_dyadicLevelPiece`).  Together these give weak type at
the interior exponent.

They do not give strong type, and the computation in StatusLog.md shows the
ceiling is real: writing the level-set bound off balance as
`D₁(k₀) τ^{-r₁} + D₂(k₀) τ^{-r₂}`, the first term is integrable against
`τ^{R-1}` only for `k₀` growing faster than `(1/3) log₂ τ` and the second only for
slower, so the two constraints meet exactly at the balance, where the bound is
`τ^{-R}` and the integral diverges logarithmically at both ends.  Weak type at
`R` is the sharp output of this route.

What closes the gap classically is real interpolation: the pieces of the layer
decomposition are aggregated not by the triangle inequality but in the norm of an
interpolation space, through the inequality

  ‖∑_ν v_ν‖_{(X₀,X₁)_{θ,s}} ≲ ( ∑_ν (2^{-νθ} J(2^ν, v_ν))^s )^{1/s},

with `J(t,v) = max(‖v‖_{X₀}, t ‖v‖_{X₁})`, applied to the couple
`(L^{r₁,∞}, L^{r₂,∞})` and followed by the identification
`(L^{r₁,∞}, L^{r₂,∞})_{θ,R} = L^R`.  The `ℓ^s` aggregation is what converts the
divergent `ℓ¹` sum of the layer bounds into a convergent `ℓ^R` one; in the
witness example of StatusLog.md it turns `M^{1-1/R}` into `1`.  Note the naive
form of that aggregation — an `ℓ^R` sum of free geometric means `a_ν^θ b_ν^{1-θ}`
— is false, as taking all `v_ν` equal shows; the scale parameter inside the
`J`-functional is essential.

Neither Mathlib nor the pinned `lean_spherical` has any of this.  There are no
Lorentz spaces, no `K`- or `J`-functionals, and no real interpolation functor;
searches for `Lorentz`, `KFunctional` and `realInterpolation` return nothing in
Mathlib, and `lean_spherical` mentions Lorentz only in prose.  Mathlib's
interpolation content is the complex method only, which `lean_spherical` extends
with Stein interpolation and Riesz--Thorin — both requiring strong endpoints, and
so unable to start from weak ones.

Building real interpolation is a substantial project in its own right and well
outside the scope of this blueprint, which quotes `ext:interpolation` as external
precisely because it is background.  It is recorded here as an unexpectedly
needed prerequisite rather than as a defect in the blueprint.

### The prerequisite chain is longer than it first appeared

Working on the real interpolation route turned up a further link that should be
recorded with the entry above, because it changes the size of the job.

The `J`-method estimate is applied to a decomposition with infinitely many
pieces, and it needs the `K`-functional to be genuinely subadditive,
`K(t, ∑_ν v_ν) ≤ ∑_ν K(t, v_ν)`.  What the weak spaces give is only the
quasi-triangle inequality `weakNorm_add_le`, with a factor two, and a factor two
per addition compounds to `2^n` over `n` pieces — useless for a sum over `ν ∈ ℤ`.
The classical repair is that for `r > 1` the space `L^{r,∞}` is normable: the
quantity `sup_E μ(E)^{1/r - 1} ∫_E |f|` over sets of finite positive measure is a
genuine norm, equivalent to the weak quasi-norm with constants `1` and the
conjugate exponent `r'`.  With that equivalent norm the couple is a Banach couple
and `K` is subadditive.

So the chain is: normability of weak `L^r` for `r > 1`, then subadditivity of the
`K`-functional, then the `J`-method estimate, then the identification
`(L^{r₁,∞}, L^{r₂,∞})_{θ,R} = L^R`.  Each link is a known theorem and none is in
Mathlib.  `weakK_add_le`, added alongside this note, is the honest two-term form
that the quasi-norm supports: it estimates the `K`-functional of a sum against
any two chosen decompositions, carrying the factor two in each slot.

### Correction to my own earlier work: the `K`-functional must be taken over measurable decompositions

Not a blueprint error — a defect in a definition introduced earlier in this
task and caught while trying to chain the two halves of the real interpolation
argument together.

The candidate norm `weakNormPrime μ r v` is a supremum over measurable sets `E`
of `(μ E)^(1/r - 1) · ∫⁻ x in E, ‖v x‖ₑ`.  For a non-measurable `v` the inner
integral is Mathlib's lower Lebesgue integral, that is, the supremum of the
integrals of measurable simple functions below `‖v‖ₑ`.  That quantity can be
zero even when `v` is large everywhere.

Take `X = ℝ` with Lebesgue measure and let `N` be a set such that neither `N`
nor its complement contains a measurable set of positive measure (a Bernstein
set).  For any measurable `v` put `w = 1_N · v`.  Then `v - w = 1_{Nᶜ} · v`, and
every measurable simple function below `‖1_{Nᶜ} v‖ₑ` vanishes almost
everywhere, so `weakNormPrime μ r₁ (v - w) = 0`; symmetrically
`weakNormPrime μ r₂ w = 0`.  The infimum

    primeK μ r₁ r₂ t v = ⨅ w : X → ℝ, ‖v - w‖' + t ‖w‖'

is therefore identically zero on that space, for every `v`.

The consequence is that `primeK_le_left`, `primeK_le_right`, `primeK_add_le`,
`primeK_sum_le`, `primeK_sum_le_primeJ` and `primeJ_method` are all true but
say nothing: they are upper bounds on a quantity that can be zero.  Nothing in
the corpus is wrong, and no proof needs repair, but the chain that was being
built — `‖v‖_R ≲ dyadic K-profile` on one side and `K-profile ≲ J-profile` on
the other — cannot be closed through `primeK`, because the first half produces
`weakK`, and `weakK ≤ primeK` is false exactly because of the above.

The fix is to restrict the infimum to measurable decompositions.  `primeKm` is
defined with `w` ranging over `{w : X → ℝ // Measurable w}`, and
`primeK ≤ primeKm` always.  The bridge `weakK ≤ primeKm` then holds for
measurable `v` on a σ-finite measure, by `weakNorm_le_weakNormPrime` applied to
each of the two measurable pieces.  `weakK` itself needs no such restriction:
it is built from `μ {τ < |f|}`, which for a non-measurable set is the outer
measure and so is large, not small.

Every upper bound on `primeK` proved so far exhibits an explicit measurable
decomposition (`0`, `v`, `w₁ + w₂`, `∑ w i`, and the truncations in
`primeK_sum_le_primeJ`), so each one carries over to `primeKm` unchanged apart
from packaging the witness with its measurability proof.

### `ext:interpolation`: the per-operator statement is proved; two hypotheses were needed, and uniformity in the endpoint constants is still open

`fourVertexMarcinkiewicz_of_measurable` proves the recorded per-operator
statement `FourVertexMarcinkiewicz μ T` under two hypotheses the recorded
statement does not carry:

1. `[SigmaFinite μ]`.  Needed by `weakNorm_le_weakNormPrime`, the comparison
   between the weak quasi-norm and the genuine norm on which the real
   interpolation argument rests.  Lebesgue measure on `E3`, the only measure
   the downstream theorems use, is σ-finite.

2. Measurability of the outputs: `∀ g : Fin 3 → SimpleFunc X ℝ,
   Measurable (T (fun j ↦ ⇑(g j)))`.  The argument decomposes `T f` into
   layer terms `T(layer k)` and needs their weak norms to add, which requires
   them to be measurable.  The source states the bound for an operator on
   simple functions and does not say its values are measurable; for a
   non-measurable output `lpNorm` is zero by convention and the conclusion is
   empty, so the hypothesis is the natural reading rather than a restriction.

The uniform reading `FourVertexMarcinkiewiczUniform μ` — one constant for all
operators and all endpoint constants `A`, and membership of `T f` in `L^R` —
is what `thm:main` consumes, and it is not yet discharged.  Uniformity in the
operator is a reordering of quantifiers (the constants produced along the
proof depend only on the exponent data), and membership in `L^R` follows from
the bound once the output is measurable.  Uniformity in `A` is the genuine
remaining content: the present proof moves the interpolation weights within a
face of the simplex to gain geometric decay, and pays for that move with the
factor `∏_a max(A_a, A_a⁻¹)`.  The remedy, recorded in StatusLog, is to fold
`log A_a` into the deviation vector — the vector `(log A_a - ∑ ϑ_b log A_b)_a`
lies in the image of `ℓ ↦ (⟨v_a - x, ℓ⟩)_a`, so it is a shift `ℓ_A` of the
log-measures — and to run the blocks and fibres on the shifted measures
`m_j e^{(ℓ_A)_j}`; the constants this introduces are reciprocal at the two
interpolation points and cancel in the geometric mean.
