# Task 3 narrative work log

Running commentary on the formalization of Task 3.  The per-label status table
lives in `Status.md`.


The duality slot is now closed end to end.  Three steps did it.  A pairing bound
survives a norm-convergent approximation, because the pairing difference is
Hölder-controlled and the norms converge; density of the Schwartz class in the
predual supplies such an approximation, once the statement about the map into
the quotient is turned into an honest sequence of functions; and composing the
two with the dual-norm identification gives the output bound from a form bound
that was only ever proved for Schwartz inputs.  No mollification is needed in
this slot at all — the approximants built earlier are for the *other* slot,
where the operator itself has to be evaluated on the approximant.

The good budget is now reachable from both sides.  On one side the budget's
canonical form — a bound on the lower integral of the `R_0`-th power — is the
`L^{R_0}` norm bound in disguise, and composing that with the Schwartz-only
duality just proved turns a form bound into the budget directly.  On the other
side the budget transfers across the approximation step by Fatou alone: the
Schwartz approximants converge only almost everywhere, and that is enough,
which is why relaxing the approximation template to almost-everywhere
convergence was the right move rather than a concession.

A survey of the chain corrected the plan.  The operator-level estimate transfer
I had named as the next target was already present, and so was the Fatou lemma
underneath it; the duplicate I had just written was removed.  What the good
budget actually still needs is narrower than it looked: the strict-range output
estimate exists, but on the complexified operator and for Schwartz inputs in
all three slots, while the budget is about the real operator with only the
replaced slot approximated.  The complexification half is now closed —
complexifying is an `L^p` isometry, so the estimate transfers verbatim.  The
remaining half is that the two passive slots also carry non-Schwartz inputs in
the Calderon-Zygmund argument, so the approximation has to run in all three
slots, one at a time through the single-slot lemma that already exists.

The label-to-Lean audit is finished.  All sixty labelled definitions and
theorems of the manuscript now have a confirmed Lean name in `Status.md`, each
checked by elaborating it against the corpus rather than matched by eye.  The
twelve correspondences that were open at the start of this pass resolved to
declarations already present, which is the expected outcome: the material was
formalized under names derived from the mathematics rather than from the
manuscript labels, and only the index was missing.

Two facts the audit makes precise.  Thirty-seven of the forty-two labelled
theorems are proof-complete.  The five that are not are exactly the chain
through the extended range: `thm:main`, `lem:one_fiber` and
`thm:extended_model` carry hypotheses the manuscript does not, and the two
`exttheorem` environments are external by the manuscript's own design.  So the
whole of the remaining mathematical work is the discharge of
`UniformConeModeFormBound`, and nothing else in the manuscript is outstanding.

The good budget is now proved for Schwartz fields, in exactly the
lower-integral normalization `lem:one_fiber` quotes
(`lintegral_rpow_ModelTruncatedOperator_le_of_realSchwartz`).  Getting there
needed the real-valued `MemLp` premise, which the file had only in complexified
form; complexification is a `MemLp` isomorphism in both directions, so the
bridge is cheap and the existing complex lemma is reused rather than reproved.

That leaves one gap, and this pass identified it precisely.  The approximation
transfer needs the bound to hold uniformly along the approximants, so it needs
their `L^q` norms controlled.  Mollification does not increase an `L^q` norm,
but that fact is Young's inequality for convolution against a unit-mass kernel,
and neither Mathlib nor the pinned `lean_spherical` has it in any form — a
search for convolution `eLpNorm` bounds returns nothing.  So the single
remaining prerequisite for the whole task is a self-contained proof that
convolution with a nonnegative kernel of unit mass is an `L^q` contraction.

Young's inequality is proved, in the contraction case the development needs:
convolution against a nonnegative kernel of unit mass does not increase an
`L^q` norm for `q >= 1`.  The route avoids Jensen for vector-valued integrals
entirely.  Against a probability measure, Hoelder applied to the constant
function one already gives the Jensen step in the `ENNReal` world, and from
there the argument is Tonelli plus translation invariance of Lebesgue measure.
Both lemmas carry the `aux_` prefix, since neither is a labelled manuscript
result: they are the background the manuscript is entitled to assume and the
libraries happen not to supply.

Cleanup: the eleven scratch files this session used for candidate proofs have
been deleted now that their contents are promoted.  The 429 that remain predate
this session and are left untouched, since removing another agent's working
files is not this task's call to make.

Mollification is now known not to increase an `L^q` norm
(`eLpNorm_mollifiedApprox_le`), stated with `eLpNorm` as the instructions ask
rather than the `lpNorm` the surrounding corpus happens to use.  The cutoff
factor is handled by pointwise domination, so only the convolution needs the
contraction proved in the previous pass.  This supplies the uniform-in-`n`
hypothesis that the three-slot estimate transfer requires, which was the last
prerequisite for the good budget.

Operational note: a full `Twisted.lean` rebuild was killed by the OOM killer
while chained with the axiom audit, leaving the promotion appended but the
`olean` stale.  Rebuilds of this file are now run detached rather than chained,
so that a failure cannot leave the promoted source and its compiled artifact
out of step.

The rebuild after the OOM kill came back clean, so the mollifier contraction is
confirmed in the file and its scratch source is deleted.  Section 8 now has its
own module, restating `lem:permutation`, `lem:calderon`,
`lem:symbol_derivatives`, `lem:fourier_series` and `thm:cone` in the
manuscript's wording over the corpus proofs; all five were already
proof-complete, so the module is restatement rather than new mathematics, and
it is imported by the top-level module.

One defect noticed while reading signatures: the public statement of
`exists_uniform_mFourierCoeff_sourceWeight_110_decay_of_anisotropy` mentions
`scratch_standardModeOfInt`.  A scratch-prefixed name in a public API is a
naming defect under these instructions and should be renamed, but the rename
touches a heavily used declaration, so it is deferred until the good budget is
closed rather than risking a large rebuild mid-proof.

The good budget for bounded measurable fields is proved
(`lintegral_rpow_ModelTruncatedOperator_le_of_boundedMeasurable`).  This is the
theorem the last several passes were aimed at, and it assembles exactly the
four pieces built for it: mollified approximants that converge almost
everywhere while keeping the sup bound, the `lpNorm` contraction that keeps
their norms from growing, the Schwartz-field budget, and the three-slot
estimate transfer.  The constant is the one the Schwartz estimate already
supplies, with the original fields' norms in place of the approximants'.

The mathematical content went through on the first attempt; the three
corrections were all plumbing.  Two `simp only [mollifiedApproxSchwartz_apply]`
calls failed as no-ops because the Schwartz wrapper coerces to `mollifiedApprox`
definitionally, so there was nothing to rewrite, and the scale endpoints of the
integrability lemma had to be passed explicitly since nothing in the goal
determines them.

Verified: the good budget for bounded measurable fields audits clean, so the
hypothesis `lem:one_fiber` quotes is now available in the shape it quotes it.

Instantiating it exposes the next obligation, and it is a specific one.  The
budget needs each replaced slot to lie in its `L^q` space, and for the good
field that is not immediate: `fiberCZGoodField` is defined as `F` minus the
bad field, so membership reduces to membership of the Calderon-Zygmund bad
part.  Boundedness alone will not do it, since the selected set has infinite
measure in the transverse directions; what is needed is the standard `L^q`
bound for the bad part, `|bad|` being dominated by `|F|` plus the interval
averages of `|F|`.  The file has the pointwise bound
`abs_fiberCZBadField_le_of_bound` and the good part's lower-integral bound
`lintegral_rpow_fiberDyadicCountableGoodField_le`, but no `L^q` membership for
the bad part.

The `L^q` membership of the Calderon--Zygmund pieces is proved, in four steps:
a bounded function supported on a set of finite measure lies in every `L^p`;
each bad atom is such a function, since it is supported on an interval times a
selected fiber set and the file already knows both factors are finite; the bad
field is a finite sum of atoms; and the good field is the input minus the bad
field.

Worth recording that the sharp route was not needed.  The textbook argument
bounds the bad part in `L^q` by Jensen on each interval against the averages,
and I had expected to need it.  But the good budget quotes the fields' norms
rather than a particular constant, so mere membership suffices, and membership
follows from boundedness together with the finite measure of the support --
which `measure_fiberDyadicSelectionSet_ne_top_of_integrable` already supplied.
Checking what the consumer actually needs saved proving Jensen a second time.

The good field's `L^q` membership is now available on `E3` itself
(`memLp_coordinateFiberGoodField`), transported along the coordinate split.
Both directions of the transport were needed: the input is pulled back to the
fiber product along the join, and the conclusion is pushed forward along the
split, each being measure preserving.

With that, every hypothesis of the good budget is discharged for the fields the
Calderon--Zygmund argument actually carries: measurability, the sup bound, and
now `L^q` membership in all three slots.

The good budget is now available at the replaced slot
(`lintegral_rpow_ModelTruncatedOperator_goodField_le`), which is the exact
shape the canonical assembly of `lem:one_fiber` quotes: the truncated operator
applied to the input with the Calderon--Zygmund good field substituted in one
coordinate.  It went through on the first attempt, because the three
obligations had already been cut to fit -- measurability, the sup bound with
its enlarged constant `B + |T|(2B)`, and `L^q` membership -- and the only work
left was the case split on whether a slot is the replaced one.

The truncated operator's measurability is now a lemma in its own right
(`stronglyMeasurable_ModelTruncatedOperator_of_measurable` and its `Measurable`
corollary).  The file had this only buried inside the Schwartz-input
integrability proof; extracting it showed the scale hypothesis `0 < a` was not
needed at all, since measurability of a parametrised integral asks only for
joint measurability of the integrand, so the lemma is stated without it.

Reading the manuscript's own proof of `lem:one_fiber` confirms the route taken
over the last several passes is the intended one: it says to choose Schwartz
approximants converging in `L^{P_m}` and use the preliminary truncated-operator
bound to identify their output limit with the integral defining `U`, which is
exactly the estimate transfer built here.

Surveying what the canonical assembly of `lem:one_fiber` still wants, now that
the good side is closed.  Four of its hypotheses are in hand: the good/bad
split, the weighted bad tail, the good part's measurability and the good
budget.  What remains is not another large estimate but a set of side
conditions attached to the bad tail: measurability of the bad part's
convolution as a function of the scale, and, for each selected interval,
integrability of the bad atom against the dilated kernel in the fiber variable
and of the resulting scale integrand on the positive axis.

These look tractable rather than deep.  The atom is bounded and supported on a
bounded interval in the fiber variable, and the kernel is integrable, so each
product is integrable for elementary reasons; the file already has
`integrable_fiberCZBadAtom_of_fiberIntegrable` for the atom alone.  The outer
structure -- normalising the input norms, choosing the stopping height from the
level, and taking the supremum over levels -- is then what turns the level-set
bound into `eq:one_fiber`.

One of the three bad-tail side conditions is discharged.
`integrable_fiberCZBadAtom_mul_kernelDilate` matches the `hkernel` hypothesis
of `integral_scaleTail_coordinateFiberBadField_le_selectedFiberScaleTail`
exactly, once the fiber variable and the dilation are read off the coordinate
split.  The proof is the elementary one: the atom is bounded, so it multiplies
an integrable kernel into an integrable function, with the reflected translate
of the kernel handled by translation invariance rather than by a dedicated
composition lemma, since Mathlib has none for this shape on the whole line.

Of the remaining two, measurability of the bad part's convolution in the scale
is routine, while the integrability of the scale integrand on the positive axis
is the one with real content: it is where the atom's cancellation on its
interval has to be used, and it is the same mechanism the interval-tail
estimate rests on.

The second bad-tail side condition is discharged
(`measurable_ModelCoordinateConvolution_scale`).  The file had measurability of
the coordinate convolution in the spatial variable at a fixed scale; this is
the other variable, the scale at a fixed point, and the proof is the same
parametrised-integral argument with the roles exchanged.

The third side condition is now isolated, and it is the substantial one.
`selectedFiberScaleTail` is *defined* as the sum of the very integrals whose
convergence is being assumed, so the hypothesis is not bookkeeping: it asserts
that each atom's scale integral against `dt/t` actually converges.  That is the
interval-tail analysis proper -- cancellation of the mean-zero atom controls
the small scales, and the kernel's decay controls the large ones -- and it is
the largest single piece left in `lem:one_fiber`.

A structural point about the third side condition, worth recording before
attempting it.  The scale integral cannot converge for every point.  At a point
inside the atom's own interval the dilated kernel acts as an approximate
identity as the scale shrinks, so the integrand tends to the atom's value there
and the integral against `dt/t` diverges logarithmically.  Convergence needs the
point to sit away from the interval, where the mean-zero cancellation turns the
kernel's derivative bound into genuine decay.  That is precisely why the
canonical assembly conditions its bad-tail hypothesis on `x` lying outside the
exceptional set, and any proof of the side condition has to carry the same
restriction rather than being stated for all points.

The pieces the estimate will rest on are already in the file: the atom's mean
vanishes on a selected fiber, its support is centred on the interval, and its
`L^1` mass is controlled by the bound times the radius.  What is missing is
their combination against the kernel's decay and derivative bounds from
`lem:fiber_kernel`.

The third and last bad-tail side condition is done
(`integrableOn_scaleTail_fiberCZBadAtom`): away from its own interval, a
selected atom's scale integral against `dt/t` converges.  The analysis I had
expected to have to build was already present in the file under `scratch_`
names -- the pointwise cancellation bound
`abs_integral_activeModelKernel_badFiber_of_interval_radius_mass_bound` and the
majorant's integrability
`ScaleTailInternal.scratch_integrableOn_Ioi_scale_bracketKernelAt` -- so what
remained was to dominate one by the other and supply measurability.  Searching
for the shape of the majorant rather than for a name found them.

This confirms the structural reading from the previous pass: both of those
lemmas carry the far-field hypothesis `2 r_I <= |q - c_I|` explicitly, which is
the same restriction the canonical assembly's bad-tail hypothesis imposes by
conditioning on the exceptional set.

The scale tail's measurability hypothesis is discharged
(`stronglyMeasurable_fiberCZBadAtom_kernelDilate_joint`).  The file states that
measurability against a joint hypothesis in all four variables -- transverse
point, spatial point, scale and fiber variable -- and nothing had supplied it;
the proof is the same projection bookkeeping as the two-variable cases, with
the kernel's `if` split on its two branches as before.

With that, the canonical assembly of `lem:one_fiber` has every hypothesis
available except the two maximal-function measurability conditions, which are
about the majorants `M1` and `M2` supplied by the caller rather than about the
Calderon-Zygmund construction.

The weighted scale tail's measurability on `E3` is now available
(`aestronglyMeasurable_weighted_selectedFiberScaleTail`), assembled from the
joint measurability of the previous pass, the fiberwise statement already in
the file, and transport along the coordinate split.  It went through on the
first attempt.

That is the last hypothesis of the canonical assembly that belongs to the
Calderon--Zygmund construction itself.  What the assembly still takes from its
caller is the good/bad decomposition and the bad-tail bound -- both available
as separate theorems with their own hypotheses -- and the measurability of the
two maximal-function majorants, which are whatever the caller chooses to
supply.

The canonical assembly is now stated from structural data
(`ModelTruncatedOperator_weakOne_finite_of_structural_data`): the two
measurability side conditions that belong to the Calderon--Zygmund
construction are discharged inside it, from the measurability of the inputs
and of the stopping data alone.  What the caller supplies is now only the
good/bad decomposition, the bad-tail bound, the good budget, and the two
majorants' measurability.

The one friction was typeclass resolution: the assembly's Hoelder triples are
instance arguments whose exponents appear nowhere in the conclusion in a form
Lean can read off, so they have to be passed explicitly rather than left to
unification.

Surveying the outer argument of `lem:one_fiber` now that the assembly is
consolidated.  All three budgets already exist as separate theorems, each
stated at the stopping height the blueprint chooses: the exceptional budget
`weakOne_exception_budget_coordinate`, which even carries the hypothesis
`H = (lam / A) / 2` explicitly; the Chebyshev good budget
`weakOne_good_budget_of_lintegral_le` with its normalisation; and the weighted
tail budget `weakOne_weighted_tail_budget`.  Their combination into a single
normalised bound is `weakOne_combine_normalized_budgets`, and the passage from
a uniform-in-level bound to the weak norm is
`weakNorm_one_le_of_forall_level`.

So the outer argument is not missing mathematics either.  What it needs is the
instantiation: choosing the height from the level, matching each budget's
hypotheses to the Calderon--Zygmund data, and threading the three through the
combination.  The remaining inputs to those hypotheses are the fiber mass
estimate feeding the exceptional budget and the norm bounds feeding the tail.

The two halves of `lem:one_fiber` are now joined.
`exists_canonical_budget_witnesses_of_structural_data` produces, at a single
level, the three witnesses that `ModelTruncatedOperator_weakNorm_one_le_of_budgets`
consumes -- the latter was already in the file and is exactly the lemma's
conclusion, a weak-`L^1` bound from per-level budgets.  The witnesses are the
three terms of the structural assembly's conclusion, so the connector is the
assembly plus the three normalised estimates, with no further analysis.

What remains is the quantifier step: supplying that package for every level at
once, which is where the stopping height is chosen as a function of the level
and `lem:fiber_cz` is applied at that height.  Every ingredient of the package
is now a theorem; none of them is an estimate still to be proved.

An asymmetry to resolve before the level-quantifier step.  The
Calderon--Zygmund good-part estimate on `E3`,
`lintegral_rpow_coordinateFiberDyadicCountableGoodField_le`, is stated for the
*countable* good field -- it is the source's `‖g_m‖_P^P ≤ (2H)^{P/p-1}‖f_m‖_p^p`
-- while the canonical budget assembly, and hence the good budget proved here,
is about the *finite* good field at a finite family `T`.  The file has the
finite field's measurability, its sup bound and its agreement with the input
off the selection, but no `L^P` estimate for it.

The finite-to-countable passage that does exist,
`ModelTruncatedOperator_weakOne_countable_of_finite`, is about the bad field.
So either the good part should be carried through in its countable form and
only the bad part passed to the limit, or the finite good field needs its own
`L^P` bound.  Deciding which is the next thing to settle, and it should be
settled by reading how the source orders the two passages rather than by
picking whichever is easier to prove.

The finite-versus-countable question is settled from the manuscript, and the
answer is the countable form.  Its proof of `lem:one_fiber` applies the fiber
decomposition at the height once, bounds the good part by
`‖g_m‖_{P_m} <= C H^{1/p-1/P_m}` in that countable form, bounds the exceptional
set over the countable family, and only at the very end says to "pass from
finite sums" for the *bad* intervals.  So the finite-to-countable passage
belongs to the bad part alone, exactly as the file's
`ModelTruncatedOperator_weakOne_countable_of_finite` has it, and no `L^P` bound
for the finite good field is wanted.  Reading the source rather than guessing
avoided building a lemma the argument would never call.

Accordingly the countable good field is now known to lie in `L^P`
(`memLp_coordinateFiberDyadicCountableGoodField`), which is the membership the
good budget needs, obtained from the Calderon--Zygmund estimate itself rather
than from boundedness.

The good budget now exists in the countable form the source uses
(`lintegral_rpow_ModelTruncatedOperator_countableGoodField_le`), with the
enlarged sup bound `3B` that the countable good field carries.

Writing it exposed a hypothesis that had to be stated rather than derived.  The
countable good field's `L^P` membership rests on the input lying in `L^p` at the
*lower* stopping exponent, and on a space of infinite measure that does not
follow from membership at the higher exponent; the two are incomparable.  So
`f_m` in `L^p` is an independent hypothesis, which is faithful: the source
normalises `‖f_m‖_p = 1` and the exponent appears in the conclusion of
`eq:one_fiber`.  A first draft tried to derive it and would have been wrong.

A useful discovery while looking for a countable analogue of the assembly:
`ModelTruncatedOperator_fiberCZ_weakOne_of_good_bad_data` is already the
generic form.  It takes an arbitrary good part, bad part, tail majorant and
exceptional set, together with the three budget witnesses, and produces the
three-term level bound; the finite canonical assembly is a specialisation of
it.  So the countable case needs no new assembly, only its own instances of the
hypotheses.

Of those, the split is available
(`ModelTruncatedOperator_coordinateFiberDyadicCountableGoodBad_split_of_bounded_measurable`),
and the good budget witness is the composition of
`weakOne_good_budget_of_lintegral_le` with the countable budget proved this
pass.  The one that still has to be produced in countable form is the bad-part
bound outside the exceptional set, and by the source's own ordering that is
precisely where the finite-to-countable passage belongs.

The good budget witness at the countable good field is available
(`weakOne_good_budget_countableGoodField`): Chebyshev turns the countable good
part's `L^{R_0}` bound into the level-set budget the generic assembly consumes.
It went through on the first attempt, the operator's measurability coming from
the lemma extracted earlier rather than being rebuilt inline.

Two of the generic assembly's three witnesses are therefore in hand for the
countable case, the exceptional one being
`weakOne_exception_budget_coordinate`.  The third, the bad part's level bound
outside the exceptional set, is what the finite-to-countable passage exists to
supply.

All three witnesses of the generic assembly are now available in countable
form.  The bad one
(`weakOne_bad_budget_countableBadField_of_finite`) came out much cheaper than
expected.  I had assumed a countable analogue of the finite scale tail would be
needed, since none exists in the file; but the generic assembly lets the tail
majorant be chosen freely, and taking it to be the bad part itself makes its
domination hypothesis trivially true.  The level bound then transports from the
finite families by the passage already in the file, and intersecting with the
complement of the exceptional set only shrinks the set being measured.

So the absence of a countable scale tail was not a gap.  It reflects that the
tail majorant is a device for estimating the bad part, and once the bad part's
own level bound is available the device is unnecessary.

The level bound for the countable decomposition is proved
(`ModelTruncatedOperator_weakOne_countable_of_budgets`).  It is the generic
assembly instantiated at the countable good and bad fields, with the bad part
as its own tail majorant, so its domination hypothesis closes by reflexivity
and the split comes from the countable splitting theorem already in the file.
It went through on the first attempt.

This is the shape `ModelTruncatedOperator_weakNorm_one_le_of_budgets` consumes,
one level at a time.  What separates the present state from `eq:one_fiber` is
the choice of the stopping height from the level and the verification of the
three budgets at that height, which is the arithmetic the source carries out
after applying the fiber decomposition.

The structure of `lem:one_fiber` is now complete in Lean
(`ModelTruncatedOperator_weakNorm_one_le_of_countable_stopping_data`): given,
at every level, stopping data whose exceptional, good and bad budgets hold at
that level, the truncated operator satisfies the weak bound `eq:one_fiber`.
Everything between the per-level budgets and the weak norm -- the countable
decomposition, the generic three-budget assembly, the combination of budgets
and the supremum over levels -- is discharged.

What the theorem still takes as input is exactly the source's own arithmetic:
choosing the height from the level and checking the three budgets there.  The
estimates that arithmetic uses are all available; what is missing is their
instantiation at `H` expressed through the level, together with the
normalisation of the input norms that makes the three constants absolute.

The exceptional budget now exists in the countable form the source uses
(`weakOne_exception_budget_coordinateCountable`), with its two supporting
transport lemmas.  The file had only the finite-family version; the countable
selected-length estimate it rests on was already present, so the addition is
the transport across the coordinate split and the height substitution, in the
same shape as the finite case.

All three budgets are therefore available in countable form at the height
`H = (lam / A) / 2`.  The remaining step is the one the source states as
normalisation: choosing the constant so that the three budgets' masses are at
most one, which is what makes their bounds absolute and lets the level-wise
theorem be applied.

The exceptional budget now holds at the canonical stopping data
(`weakOne_exception_budget_canonical`): with the input's `p`-th mass normalised
to at most one, the countable exceptional set of the canonical selection obeys
the budget at the height read off the level.  This is the first of the three
budgets instantiated at data the argument actually constructs, rather than at
an arbitrary stopping family.

The finiteness of that exceptional set is carried as a hypothesis, matching how
the file states the finite-family version.  It is not free: the set is a
countable union of selected rectangles, and its finiteness comes from the same
summation the length estimate performs, so it deserves its own lemma rather
than being smuggled in.  Two instance mismatches had to be routed around, both
the familiar one between the product measurable space and the one `Measure.prod`
carries; stating the integrability over the plain product measure first and
rewriting afterwards avoids them.

The finiteness I had to assume last pass is now proved in general
(`aux_measure_iUnion_ne_top_of_pairwise_disjoint`): a countable disjoint union
whose finite partial masses are bounded has finite measure.  The point worth
recording is why the existing real-valued estimate could not be reused.  Its
proof goes through `ENNReal.tsum_toReal_eq`, which needs each piece finite but
says nothing about the sum; if the total were infinite the real measure would be
zero and the bound would hold vacuously.  Finiteness therefore has to be argued
in `ENNReal`, by bounding the supremum of finite partial sums.

The same shape of reasoning is what makes the exceptional set's own finiteness
available, and the bound on its partial sums is exactly the one the length
estimate already establishes.

The countable exceptional set's finiteness is proved
(`measure_fiberDyadicExceptionalSet_ne_top`), so the hypothesis carried in the
canonical exceptional budget can now be discharged rather than assumed.  The
partial masses are handled by summing over a finite family of disjoint
rectangles and quoting the finite-family length estimate; there was no
`_eq_sum_` form of the finite exceptional mass in the file, but Mathlib's
`measureReal_biUnion_finset` supplies it directly from disjointness, which is
simpler than routing through the selected-length density.

The exceptional budget is now unconditional at the canonical stopping data
(`weakOne_exception_budget_canonical_unconditional`): given only that the
input's `p`-th mass is at most one and the height is read off the level, the
budget holds.  Every side condition it used to carry -- the exceptional set's
finiteness, the selection sets' finiteness, the fiberwise integrability -- is
discharged internally from the input's integrability.

This is the first of the three budgets in the form the outer argument can use
without further obligations.  The good and bad budgets exist in countable form
but still quote their own hypotheses, and bringing them to the same standard is
the next step.

A mismatch between the file and the source is now resolved.  The
finite-to-countable passage already present bounds the bad part's level set
over all of space, but the source only ever bounds it outside the exceptional
set, and outside is where the cancellation estimate holds; requiring the global
bound would have been asking for something the argument does not provide.

The fix is small because the underlying limit lemma is stated for an arbitrary
measure: restricting the measure to the complement turns it into exactly the
restricted statement (`weakBound_restrict_of_ae_tendsto`), and the operator-level
passage follows with the same proof
(`ModelTruncatedOperator_weakOne_countable_of_finite_restrict`).  Noticing that
the generality was already there avoided reproving the convergence argument.

The bad budget witness now exists in the form the source can actually supply
(`weakOne_bad_budget_countableBadField_of_finite_outside`): the finite input is
required only outside the exceptional set.  The earlier witness, which demanded
the finite bound over all of space, is superseded; it was provable but its
hypothesis was not, since the bad part is only controlled where the
cancellation estimate applies.

All three witnesses of the generic assembly are therefore available with
hypotheses the argument supplies, rather than merely stated.  The remaining
input is the finite-family bad bound outside the exceptional set at each stage,
which is the pointwise tail estimate combined with the weighted tail budget --
both already proved.

The step that turns a pointwise product bound outside a set into a level budget
is now a lemma (`weakOne_level_budget_of_pointwise_outside`).  It is the last
link in the bad chain: the pointwise tail estimate holds outside the
exceptional set, the level set there is contained in the level set of the
product, and the weighted tail budget bounds that.  Stating it for an arbitrary
function and an arbitrary set keeps it independent of the Calderon--Zygmund
construction, which is what lets it serve the finite families at every stage.

The chain for the bad part is therefore closed in principle: pointwise estimate
outside the exceptional set, level budget there, finite-to-countable passage
respecting the restriction, and the assembly's witness.

A hygiene defect found and fixed by a consistency check rather than by a build
failure.  The two per-section modules are compiled against `Twisted.olean`, and
every promotion since they were written had left their compiled artifacts
stale.  Nothing errored -- the top-level module still built -- but `thm:cone`
had silently stopped resolving, so an audit of the section modules' theorems
would have reported an unknown constant rather than a clean result.  Rebuilding
both modules restores them, and all five headline theorems audit clean.

The lesson for the remaining work is that promoting into `Twisted.lean` is not
self-contained: anything compiled against it has to be rebuilt in the same
pass, and the absence of an error is not evidence that it was.

The passive product is now splittable into its two named factors
(`aux_prod_erase_fin3`).  The bad part's pointwise bound carries a product over
the two coordinates other than the active one, while the level budget consumes
three separate factors, so the pair has to be named before the two can meet.

A small tactic note worth keeping: after `fin_cases` on a `Fin 3` variable the
goal shows the index in its anonymous-constructor form, and a rewrite against
the numeral fails to match.  Prefacing each branch with an explicit `show` of
the numeral form restores the match; this is a presentation mismatch rather
than a defeq one.

A genuine gap, found by tracing where the far-field hypothesis is meant to come
from.  Every tail estimate in the file takes `2 r_I <= |x - c_I|` as an explicit
hypothesis supplied by its caller, and in the source that hypothesis is
discharged by the point lying outside the exceptional set.  But the exceptional
set the file defines, `fiberDyadicExceptionalSet`, is the union of the
*undoubled* selected rectangles, whereas `eq:cz_exceptional_set` takes the union
of the doubled ones.  Lying outside the undoubled set gives only
`r_I <= |x - c_I|`, which is not what the cancellation estimate needs.

This is not an error in the manuscript, which is explicit that `E` is built from
`2I` and that its mass is at most `2H^{-1}`; it is a piece the formalization has
not yet built.  What is needed is the doubled exceptional set, its measure
estimate -- twice the undoubled one, which the existing selected-length bound
already supplies -- and the implication from lying outside it to the far-field
condition.  Until that exists the bad chain cannot actually be threaded, however
complete its individual links look.

The gap identified last pass is closed at its most important point.  The
doubled interval and the doubled exceptional set of `eq:cz_exceptional_set` are
now defined, and lying outside that set yields the far-field condition
`2 r_I <= |y - c_I|` for every selected fiber
(`far_of_notMem_fiberDyadicDoubledExceptionalSet`).  That is the hypothesis
every cancellation estimate in the file takes on trust from its caller, so the
bad chain now has a way to discharge it rather than merely to state it.

What remains of the gap is the doubled set's measure, which should come to twice
the undoubled bound since each doubled interval has twice the length.  The
existing selected-length estimate supplies the undoubled bound, so this is a
factor-of-two computation rather than a new argument.

The gap is now fully closed.  The doubled exceptional set's mass is at most
twice the undoubled one
(`measure_fiberDyadicDoubledExceptionalSet_le`), which with the existing
selected-length estimate reproduces the source's `|E| <= 2 H^{-1}` exactly.

The proof had to differ from the undoubled case in one respect worth noting.
The undoubled rectangles are pairwise disjoint and their measure is the sum;
the doubled ones overlap, so the comparison goes by subadditivity to the sum of
the doubled masses, each of which is twice the corresponding undoubled one, and
the disjointness is then used on the undoubled union.  Reaching for the
disjointness of the doubled family would have been wrong.

The exceptional budget now exists for the set that actually supplies the
far-field condition (`weakOne_exception_budget_doubled`), with the transport of
the doubled mass comparison into the ambient space
(`measure_coordinateDoubledExceptional_le`).  Its constant is four times the
anisotropy constant rather than two, which is the factor the source carries
when it doubles the intervals; the budget is otherwise the undoubled one.

A first draft of this went the wrong way: it tried to feed the doubled mass
into the height lemma directly, but that lemma requires the normalised mass to
be at most one and doubling breaks exactly that.  Multiplying the finished
undoubled budget by two instead is both correct and shorter.

The exceptional budget is now complete in the form the argument uses
(`weakOne_exception_budget_doubled_canonical`): at the canonical stopping data,
for the doubled set whose complement supplies the far-field condition, with no
side conditions remaining and the constant the source's doubling produces.

Of the three budgets, the exceptional one is therefore finished.  The good
budget is available at the countable good field and needs only the input data.
The bad budget's chain is assembled but its innermost input, the finite-family
pointwise bound, must now be instantiated with the far-field condition read off
the doubled set rather than assumed -- which is what the past few passes were
for.

The bad tail's side condition is now available in the form the argument can
supply it (`integrableOn_scaleTail_fiberCZBadAtom_outside`): outside the
doubled exceptional set the scale tail converges for every selected interval.
The proof splits on whether the transverse point is selected.  When it is, the
far-field condition is read off the exceptional set and the earlier convergence
result applies; when it is not, the atom is identically zero on that fiber, so
the integrand vanishes and integrability is trivial.

That second case is the reason the statement can be uniform over all intervals
of the family rather than only the selected ones, which is what the pointwise
bad estimate quantifies over.

The bad part's pointwise estimate now holds outside the doubled exceptional set
with no analytic side conditions left
(`abs_ModelTruncatedOperator_bad_le_outside`).  All three of its obligations are
discharged there: the convolution's measurability in the scale, the atom's
integrability against the dilated kernel, and the scale tail's convergence,
the last of these using the far-field condition read off the exceptional set.

This is the point the last several passes were aimed at.  The three side
conditions were proved separately, then the exceptional set that makes the
third of them available had to be built, and only now do they compose into an
estimate whose hypotheses are the input data alone.

A quantifier-order defect in the passive-pair helper, caught before it was
used.  The first version named the two coordinates after the function being
multiplied, so formally the pair could differ from one function to the next --
and since the estimate is applied at every point, the pair could have varied
with the point.  The witnesses happen to depend only on the active coordinate,
but the statement did not say so.  `aux_prod_erase_fin3_uniform` chooses the
pair for the coordinate alone and then quantifies over functions, which is what
the level budget needs, since its three factors must be fixed functions.

The earlier version is harmless but useless; it stays only because removing a
promoted declaration costs a rebuild for no gain.

The bad level budget now holds at a finite family outside the doubled
exceptional set (`weakOne_bad_level_budget_finite_outside`), and it went through
on the first attempt.  It is the pointwise estimate of the previous pass, split
into its two maximal factors and the scale tail by the uniform passive pair,
fed to the generic level budget; the three measurability obligations are the
maximal functions', which the file already had, and the tail's, proved earlier.

This is the input the finite-to-countable passage wants.  With it the bad
branch runs from the pointwise cancellation estimate all the way to the
assembly's witness without an unproved link.

The next obstacle is identified and it is not a missing estimate but a
uniformity question.  The finite bad level budget bounds the level set by the
scale tail's norm at that family, and the tail grows with the family, so the
passage to the countable limit needs a bound independent of it.  The source
supplies exactly this: the tail function of `lem:interval_tails` has `L^p` norm
controlled by the total selected length, which the stopping construction bounds
by the inverse height regardless of how many intervals are taken.

The file has the corresponding pieces -- the countable interval-tail sum, its
total mass as twice the summed radii, and the selected-fiber version -- so what
remains is to dominate the finite scale tail by that countable tail and read off
the uniform bound.  That is the next step, and it is the last one before the
three budgets can be quoted at a single constant.

The scale tail at a finite family is now dominated by the interval-tail sum of
`lem:interval_tails` (`selectedFiberScaleTail_le_intervalTail_sum`).  This is
the step that begins to remove the family from the estimate, since the
interval tails are what the source bounds by the total selected length.

Two details shaped the statement.  The far-field condition is required only on
intervals whose fiber is actually selected, because the others contribute a
vanishing atom; restricting the sum to the selected ones and comparing back is
what lets the hypothesis be that weak.  And the atom's integrability against
the kernel needs the input bounded globally rather than on the one fiber, so
the hypothesis is stated that way rather than being weakened to match the rest.

A `Status.md` entry was wrong and is corrected.  `lem:interval_tails` was
recorded as proof-complete against `intervalTailTsum`, which is a definition,
not an estimate; the lemma's content is the norm bound on the tail function.
The entry now names `integral_finset_double_intervalTails_le_of_radius_sum`,
which is the `p = 1` clause the source states first, and the general exponent is
carried by the `scratchLp_intervalTail` machinery through the Hoelder-cutoff
lemma.  The error came from the original audit matching a label to the nearest
declaration sharing its vocabulary rather than to one whose statement is the
lemma.

The scale tail is now bounded by the interval tails of the *selected*
intervals only (`selectedFiberScaleTail_le_selected_intervalTail_sum`), which
is the form that can become uniform.  The previous version summed over the
whole family, and that bound cannot be made family-independent, because the
unselected intervals still contribute positive interval tails even though their
atoms vanish.  Restricting to the selected subfamily leaves a subsum of a single
series indexed by the selected intervals, and it is that series the source
bounds by the total selected length.

Incidentally the restriction is free: the terms dropped are exactly the ones
already shown to vanish, so the refined statement has the same proof as the
coarse one with the comparison step removed.

The family now drops out of the tail estimate entirely
(`finset_selected_intervalTail_le_intervalTailTsum`): a finite family's
selected interval tails are a subsum of the single series indexed by the
selected intervals, so the bound is the same for every family.  Composing this
with the previous pass gives a scale-tail bound whose right-hand side mentions
only the stopping data and the point, which is what the passage to the
countable limit needs.

The step is elementary but the plumbing was not: the finite sum is over a
filtered family of intervals while the series is over the subtype of selected
ones, so the two are related by the subtype-sum identity before the
subsum-of-a-series bound can apply.

The scale tail is now bounded uniformly in the finite family
(`selectedFiberScaleTail_le_intervalTailTsum_uniform`), by a quantity that
mentions only the stopping data, the point and the summability of the selected
tails.  This resolves the obstacle recorded several passes ago: the finite bad
level budget could not be carried to the countable limit because its bound grew
with the family, and now it does not.

The route was worth the detour it took.  The first attempt bounded the tail by
a sum over the whole family, which cannot be uniform; restricting to the
selected subfamily and recognising that as a subsum of one series is what makes
the family disappear.

The next obstacle on the bad branch is identified and it is genuine content,
not plumbing.  The uniform tail bound assumes the selected interval tails are
summable at the point; that does not follow from the radii being summable,
because a tail term is close to one whenever the point sits inside its own
interval.  What makes the series converge is that the selected intervals are
pairwise disjoint, so only boundedly many can be close to the point at each
scale.  That is precisely the content of `lem:interval_tails`, whose `p = 1`
clause the file proves by integrating each summand; the pointwise statement is
the other half.

Recording it as the next piece rather than assuming it: the hypothesis is
stated in the uniform bound, so nothing proved so far depends on it being free.

A better route around the summability obstacle.  Rather than dominating the
finite tail sum by a series and then needing that series to converge at the
point, the `p = 1` clause of `lem:interval_tails` applies to the finite sum
directly: its mass is twice the total length, whatever the family.  Stated as
an `eLpNorm` bound (`eLpNorm_one_finset_double_intervalTails_le`) this is already
uniform, and pointwise summability never arises.

So the obstacle recorded last pass is avoidable at this exponent rather than
something to prove.  It would return at a general exponent, where the source's
argument is the duality one against the maximal function; the file carries that
in paired form through the Hoelder-cutoff lemma.

The fiberwise tail mass is now expressed through the selected-length density
(`eLpNorm_one_selected_intervalTail_fiber_le`), together with the identity that
the selected radii at a transverse point sum to half that density.  That
identity is what connects the interval-tail estimate, which is stated in terms
of radii, to the stopping construction, which is stated in terms of lengths;
without it the two halves of the argument speak about different quantities.

The remaining step on this branch is Tonelli: integrating the fiberwise mass
over the transverse variable turns it into the ambient mass, and the
selected-length estimate bounds that integral by the inverse height.

Ambient mass is now identified with iterated fiber mass through the coordinate
split (`lintegral_enorm_comp_coordinateSplit_eq_iterated`).  The split is
measure preserving, so the ambient lower integral equals the one over the fiber
product, and Tonelli in the order that puts the transverse variable outside
gives the iterated form the fiberwise estimate is stated in.

With this the tail's ambient mass is the transverse integral of its fiber
masses, each of which is the selected-length density times the universal tail
mass; the selected-length estimate then bounds the whole by the inverse height.

The selected fiber tail now has a form whose joint measurability is visible
(`aux_selectedFiberIntervalTail`, with its agreement with the filtered sum and
its measurability).  The obstacle was presentational rather than mathematical:
written as a sum over a family filtered by the transverse point, the dependence
on that point sits inside the index set, where no measurability argument can
reach it.  Writing the same quantity as a sum of indicators over the fixed
family exposes the dependence as a factor, and measurability is then routine.

This is what the Tonelli step needs as input, since that step is stated for a
measurable function on the fiber product.

The ambient tail mass is now bounded by the total selected length
(`eLpNorm_one_ambient_selectedFiberIntervalTail_le`).  This closes the chain the
last several passes built: the mass through the split is the iterated fiber
mass, each fiber mass is the selected length there times the universal tail
mass, and integrating transversally gives the total selected length.  The
remaining input is the selected-length estimate, which the file already proves
and which the exceptional budget already uses.

So both budgets that depend on the stopping construction -- exceptional and
tail -- now rest on the same single estimate, which is how the source organises
them.

The selected-length density's integrability is now available
(`aux_integrable_fiberDyadicSelectedLengthDensity`), which is the last
hypothesis the ambient tail mass bound assumed without proof.  The density is a
finite sum of constants on the selected fiber sets, so integrability reduces to
each of those sets being finite -- the same condition the exceptional budget
already needs and the stopping construction already supplies.

Both of the stopping-dependent budgets now depend on exactly one fact about the
construction: that each selected fiber set has finite measure.

The tail branch reaches its target: the ambient tail mass is bounded by the
inverse stopping height (`eLpNorm_one_ambient_tail_le_inv_height`), which is
the source's `‖h_m‖_1 <= C H^{-1}`, uniformly in the finite family.  Its
hypotheses are the input's integrability and nonnegativity on the fiber
product, the measurability of the stopping set, and the finiteness of the
selected fibers -- nothing about the family.

That completes the estimate the bad budget needs on the tail factor.  What the
bad branch still lacks is the corresponding control of the two maximal factors,
which the source gets from the maximal theorem quoted as `ext:maximal`.

A correction to the exponent reasoning of the last few passes.  The tail budget
pairs three factors whose exponents are conjugate to one, since the level bound
it produces is a Chebyshev estimate on their product.  Two of those exponents
belong to the maximal factors, so the tail's exponent is determined by them and
is in general strictly above one.  The `L^1` bound proved two passes ago
therefore does not suffice on its own: it is the right estimate only in the
degenerate case where the other two exponents are infinite.

So the general-exponent clause of `lem:interval_tails` is needed after all,
which is the duality argument against the maximal function that the file
carries in the `scratchLp` development.  The `L^1` bound remains correct and is
the source's own first clause; it simply is not the one this budget consumes.
The maximal factors themselves are already controlled, by the dyadic maximal
estimate the file proves with an explicit constant.

The bad budget's two passive factors are now controlled
(`eLpNorm_weighted_coordinateDyadicBallMaximal_le`): the coordinate maximal
function carried with its translation weight has the maximal estimate's norm
with that weight in front.  This holds at every exponent above one, so it is
independent of how the tail's exponent resolves, which is why it was worth
proving while that question is open.

The maximal estimate it rests on is already in the file with an explicit
constant, so `ext:maximal` enters through a proved consequence rather than as a
carried hypothesis.

The route from the paired estimate to the norm bound is now clear, and worth
recording before it is built.  The Hoelder-cutoff lemma bounds the pairing of
the scale tail against a bounded measurable test function by two factors: the
test function's dyadic maximal norm over the selected intervals, and the
measure of their union raised to the conjugate power.  The first is controlled
by the maximal estimate already proved, and the second is the total selected
length.  So the pairing bound has exactly the shape
`|<tail, g>| <= C * ‖g‖_q * (selected length)^{1/p}`, which is the dual form of
the general-exponent clause of `lem:interval_tails`.

Feeding that to the Lebesgue duality proved earlier in this session turns it
into the norm bound the tail budget wants.  Duality against Schwartz functions
alone suffices, and that version is also already available, which avoids having
to extend the cutoff lemma's hypotheses to a general test class.

The one-dimensional maximal estimate now exists in norm form
(`eLpNorm_line_dyadicBallMaximal_le`), mirroring the ambient version already in
the file.  This is the factor the duality route needs: the cutoff lemma's
right-hand side carries the test function's dyadic maximal norm, and this turns
that into the test function's own norm.

The maximal estimate itself comes from the pinned dependency's
Hardy--Littlewood development, so `ext:maximal` continues to enter through
proved consequences rather than as a hypothesis.  Three deprecated names had to
be updated along the way, which is worth noting only because the surrounding
file still uses the old ones and will warn similarly if touched.

The maximal factor of the cutoff estimate is now bounded by its value on the
whole line (`aux_setIntegral_line_maximal_le`): restricting to the selected
union only decreases the integral, and the fiber-line coordinate map is measure
preserving.  Together with the norm form of the maximal estimate this turns the
cutoff estimate's first factor into the test function's own norm, which is what
the duality step needs.

One hypothesis had to be added rather than derived: the test function's
membership in the relevant space.  Boundedness alone does not give it on a
space of infinite measure, and the underlying memLp lemma asks for it
explicitly; Schwartz test functions will supply it when the duality is applied.

The cutoff pairing now carries its maximal factor on the whole line
(`selectedFiber_scaleTail_pairing_le_line_maximal`), so the selected family
survives only in the measure of its union.  That measure is the total selected
length, which the stopping estimate controls, so the pairing bound has reached
the shape duality consumes.

A tactic note: the final step is a monotone congruence through a nested
product, and `gcongr` closes it and its positivity side goals in one call,
where an arithmetic tactic could not find the path.  Worth reaching for
whenever the goal is an inequality that differs from a hypothesis in one factor.

The cutoff estimate's maximal factor is now named as a norm
(`aux_line_maximal_integral_eq_lpNorm`), which is what lets the maximal
estimate apply to it.  The factor appears in the estimate as a root of an
integral of a power, and the identification uses only that the maximal function
is nonnegative.

Its measurability is taken as a hypothesis rather than derived, because the
file's proof of it is private to an internal namespace and the pinned
dependency does not export one; supplying it at the call site is cheaper than
reproving it.  A recurring Lean detail also cost a few attempts here:
`integral_congr_ae` leaves the goal with unreduced applications, where `rw`
cannot match but `simp only` can, since it beta-reduces first.

The maximal estimate is now available in the real normalization
(`lpNorm_line_dyadicBallMaximal_le`), with its constant named
(`aux_lineMaximalConst`).  The cutoff estimate's factors are real, so this is
the form the duality step needs; the passage from the extended-valued statement
required checking that the constant is finite, which it is as a product of
finite factors raised to a positive power.

With this the cutoff pairing's maximal factor is bounded by a constant times
the test function's own norm, and the pairing bound is in the exact dual form
of the tail's norm estimate.

The cutoff pairing is now stated against the test function's own norm
(`selectedFiber_scaleTail_pairing_le_norm`).  This is the dual form of the
general-exponent clause of `lem:interval_tails`: the scale tail paired with any
bounded test function of the conjugate exponent is at most a constant times
that function's norm times a power of the total selected length.

The remaining step on this branch is to read that as a norm bound on the tail,
which is what Lebesgue duality does and what the earlier passes of this session
already proved in the form that takes Schwartz test functions only.

Lebesgue duality is now available on an arbitrary measure space
(`lpNorm_le_of_forall_integral_mul_le_general`, with the norm identity it rests
on).  The version proved earlier in this session was stated on the ambient
space, but the tail's pairing estimate is fiberwise and lives on the line, and
nothing in the argument is special to either space.

The generalisation was free: the dual test function and its three properties
were already stated for an arbitrary type, so only the norm identity had to be
restated, and the duality proof then transcribes unchanged.  That the earlier
version was written for one space was an accident of where it was first needed.

Complexification is now known to be an isometry, and to preserve membership, on
an arbitrary measure space.  Both facts existed only on the ambient space; the
pairing estimates take complex test functions while duality supplies real ones,
so the two normalizations have to be identified wherever that meeting happens,
and it happens on the fiber line as well.

This is the third piece this session that had to be generalised away from the
ambient space.  The pattern is consistent: the earlier development was written
where each fact was first needed, and the fiberwise argument needs the same
facts one level down.  Generalising has been cheap each time, since the proofs
never used anything about the space.

## 2026-09-12T18:55-0700

Closed the general-exponent half of `lem:interval_tails`, which the earlier
`Auto.integral_finset_double_intervalTails_le_of_radius_sum` covered only at
`p = 1`.  Route: a clamping bridge carrying a pairing bound proved for bounded
test functions to all of `L^{p_0}`
(`aux_abs_integral_mul_le_of_bounded_test`), then Lebesgue duality applied to
the existing bounded-cutoff dual test
(`scratchLp_finset_pairwiseDisjoint_intervalTail_holder_cutoff_le`).  The
blueprint normalization `(∑_I |I|)^{1/p}` is recovered from the union measure
by disjointness.  New: `aux_clampSeq` and its five lemmas,
`aux_memLp_of_le_one_of_integrable`, `aux_memLp_intervalTail(_line)`,
`aux_lineIntervalTailSum` with measurability/`MemLp`,
`aux_lpNorm_lineIntervalTailSum_le`,
`lpNorm_finset_double_intervalTails_le_of_radius_sum`.

## 2026-09-12T19:20-0700

Carried the general-exponent interval-tail estimate to the ambient space,
mirroring the `L^1` chain: `lpNorm_selectedFiberIntervalTail_fiber_le`
(fiberwise, from the disjointness of the selected dyadic intervals),
`aux_lintegral_rpow_enorm_comp_coordinateSplit_eq_iterated` (Tonelli through
the coordinate split at exponent `p`),
`eLpNorm_ambient_selectedFiberIntervalTail_le`, and
`eLpNorm_ambient_tail_le_inv_height` -- the source's `‖h_m‖_p ≤ C_p H^{-1/p}`.

Scoping note found while planning the next step: the existing weak-norm
assembly (`ModelTruncatedOperator_weakNorm_one_le_of_budgets` and everything
above it) is stated at `R = 1`, while `lem:one_fiber` asserts a weak-`L^R`
bound for the `R` determined by `R^{-1} = p^{-1} + Σ_{j≠m} P_j^{-1}`.  The
three-set inclusion argument generalizes -- subadditivity of `t ↦ t^{1/R}`
for `R ≥ 1` -- but the general-`R` budget assembly is still to be written, and
each of the three budgets needs its `τ · |·|^{1/R}` form.

## 2026-09-12T19:45-0700

Opened the general-`R` side of `lem:one_fiber`, whose existing assembly was at
`R = 1` only.  Both ends are now in place:

- assembly: `aux_rpow_inv_add_three_le` (subadditivity of `t ↦ t^{1/R}` for
  `R ≥ 1`), `fiberCZ_weak_assembly`, `weakNorm_le_of_forall_level`,
  `aux_combine_normalized_budgets`, `weakNorm_le_of_canonical_budgets`;
- budget: `aux_level_le_eLpNorm` (Chebyshev at exponent `R`),
  `aux_eLpNorm_threefold_product_le` (three-factor Hoelder at a general output
  exponent -- the previous version fixed the output at one),
  `weak_weighted_tail_budget`, `weak_level_budget_of_pointwise_outside`.

What remains on this side is the three concrete budgets in their `τ · |·|^{1/R}`
form, and the operator-level wiring that currently instantiates the `R = 1`
chain.

## 2026-09-12T20:05-0700

The exceptional budget now runs at a general output exponent.  The height
changes from `H = (λ/A)/2` to `H = (λ/A)^R/2`, and the arithmetic that made the
endpoint budget level-independent becomes `λ · H^{-1/R} = 2^{1/R}A ≤ 2A`:
`aux_two_rpow_inv_le_two`, `aux_inv_selectionHeight_rpow`,
`weak_exception_budget_of_inv_height`, `aux_two_mul_rpow_inv_le`,
`weak_exception_budget_doubled`, and then the four-step canonical chain
(`_coordinateCountable`, `_canonical`, `_canonical_unconditional`,
`_doubled_canonical`), whose proofs carry over verbatim once the height and the
conclusion are restated.

Remaining on the general-`R` side: the good budget (whose height exponent
`H^{1/p-1/P}` must be rebalanced against the new height) and the bad budget,
then the operator-level wiring.

## 2026-09-12T20:25-0700

The good budget now runs at a general output exponent.  The pleasant fact is
that the level arithmetic is the endpoint arithmetic with `R_0` replaced by
`R_0/R`: writing the `R`-th root of the Chebyshev quotient as a quotient at
exponent `R_0/R` reduces `weak_good_budget_normalization` to the existing
`weakOne_good_budget_normalization`, and the constant is `2^{R_0/R - 1}·A`.
New: `weak_good_budget_of_lintegral_le`, `weak_good_budget_normalization`,
`weak_goodExponent_spec` (the blueprint's `δ = 1/R - 1/R_0` satisfies
`R·R_0·δ = R_0 - R`), `weak_goodExponent_mul`, and
`weak_selectionHeight_pow_eq_goodConstant`.

Remaining on the general-`R` side: the bad budget, then the operator-level
wiring.

## 2026-09-12T20:45-0700

The bad budget at a general output exponent, plus a structural correction to
its third Hoelder factor.

`weak_bad_level_budget_finite_outside` is the direct general-`R` restatement.
But its third factor is the *global* norm of the scale tail, and the scale tail
is only controlled outside the doubled exceptional set -- so that factor is not
the one the blueprint bounds.  The blueprint's third factor is the interval-tail
majorant `h_m`, whose norm is `eLpNorm_ambient_tail_le_inv_height`.  Since the
level budget only ever uses its pointwise hypothesis outside the exceptional
set, the majorant can be substituted there:
`selectedFiberScaleTail_le_tail_majorant_outside` (the far-field condition
holds on every selected interval outside the doubled set) and
`abs_ModelTruncatedOperator_bad_le_majorant_outside` (the blueprint's
`eq:cz_bad_pointwise`).

Next: the bad level budget stated against the majorant, which is what closes
the gap to the tail norm proved earlier.

## 2026-09-12T21:05-0700

Two steps this tick.

`weak_bad_level_budget_majorant_outside`: the bad branch's Hoelder step in the
blueprint's own shape -- two passive maximal functions and the interval-tail
majorant -- at a general output exponent.  This is the join: its third factor
is the function whose norm `eLpNorm_ambient_tail_le_inv_height` bounds.

The operator-level wiring at a general output exponent:
`ModelTruncatedOperator_fiberCZ_weak_of_good_bad_data`,
`ModelTruncatedOperator_weak_countable_of_budgets`,
`ModelTruncatedOperator_weakNorm_le_of_budgets`, and
`ModelTruncatedOperator_weakNorm_le_of_countable_stopping_data`.  All four are
the `R = 1` proofs with the level quantity carrying `^(1/R)`; generated from the
originals by substitution and checked before promotion.

The chain from the three budgets to a weak-`L^R` bound for the truncated
operator is therefore complete at a general exponent.  What is left for
`lem:one_fiber` is supplying the three budgets at the canonical stopping data
with a common constant -- the normalisation `A_u = C_1 U(u)^{100}` -- and the
finite-to-countable passage for the bad part.

## 2026-09-12T21:25-0700

The instantiation went through.

`ModelTruncatedOperator_weak_finite_of_generic_data` states the three budgets at
one level for an arbitrary good/bad decomposition and an arbitrary three-factor
domination of the bad part outside the exceptional set -- nothing in it is
specific to the Calderon--Zygmund data, and it is assembled directly from
`ModelTruncatedOperator_fiberCZ_weak_of_good_bad_data`,
`weak_good_budget_of_lintegral_le` and `weak_weighted_tail_budget`.

`ModelTruncatedOperator_weak_finite_of_czData` instantiates it at the fiberwise
Calderon--Zygmund data: exceptional set the doubled one, bad factors the
interval-tail majorant and the two passive maximal functions.  Both compiled on
the first attempt, so the hypotheses of the separately generalised pieces did
in fact line up.

Next: the constants.  The level bound's three terms have to be brought to a
common multiple of `A_u = C_1 U(u)^{100}` at the height `H = (lam/A_u)^R/2`,
using `weak_exception_budget_doubled_canonical`, the good part's normalisation
and the tail norm.

## 2026-09-12T21:45-0700

Constant extraction: `aux_eLpNorm_const_mul`, `weak_good_budget_term_eq`,
`aux_eLpNorm_const_mul_ambient_tail_le`,
`aux_eLpNorm_const_mul_coordinateMaximal_le`.

While computing the bad budget's constant these turned up a genuine gap, and it
is not one the general-`R` work introduced -- it is pre-existing and holds at
every exponent.

The bad branch's atom mass is currently bounded using the *sup bound* on the
input: `selectedFiberScaleTail_le_selected_intervalTail_sum` assumes
`∀ yz, |F yz| ≤ B` and carries the constant `4·B`.  The blueprint instead
bounds it by the *stopping* property: on a selected interval the parent's
average of `|f_m|^p` is at most `H`, so Hoelder gives
`∫_I |f_m| ≤ |I|·(2H)^{1/p}`, and `eq:cz_bad_pointwise` carries `H^{1/p}`.

That factor is exactly what cancels the tail's `H^{-1/p}` from
`eLpNorm_ambient_tail_le_inv_height`, leaving a level-independent budget.  With
`B` in its place the third budget reads `C·B·H^{-1/p}`, which blows up as the
level tends to zero -- so it is not a budget at all.

Note that the `R = 1` chain never discharged this budget either:
`weakOne_bad_budget_countableBadField_of_finite_outside` is parametric in its
bound `Kbound` and simply transfers it to the countable limit.  So the concrete
bad budget has not been established at any exponent, and the missing ingredient
is the same in both cases.

Next: the atom mass bound from the stopping property.  The maximality the
argument needs is already present -- `fiberDyadicSelection_ancestor_average_le`
is what the disjointness proof uses.

## 2026-09-12T22:05-0700

The gap found last tick is closed at its root.

`aux_setIntegral_le_of_average_rpow_le`: a nonnegative function whose `p`-th
average over a set of measure `L` is at most `H` has integral at most
`L·H^{1/p}` there -- Hoelder against the constant one on the restricted
measure.

`aux_setIntegral_abs_le_of_selected`: on an interval selected at height `H`
the input's mass is at most `|I|·(2H)^{1/p}`.  This is the blueprint's bound,
and it is what carries the `H^{1/p}` the bad budget needs.  Everything it
relies on was already in the file: `fiberDyadicSelection_average_lt_and_le_two_of_nonneg`
supplies `A_F(I,z) ≤ 2H` from the maximality of the selection, which is the
same fact the disjointness proof uses.

Also `aux_volume_fiberDyadicInterval`.

Next: re-derive the scale-tail domination with this mass bound in place of the
sup bound `4·B`, which means revisiting
`selectedFiberScaleTail_le_selected_intervalTail_sum` and the chain below it
down to `scratchAssembly_finset_scaleTail_holder_cutoff_le`, whose atom
hypothesis is `(∀ k ∈ S, (∫ y, |b k y|) ≤ A * r k)` -- already in the right
shape, so the substitution is `A := 2·(2H)^{1/p}` rather than a restructuring.

## 2026-09-12T22:25-0700

The atom mass now reaches the shape the scale-tail chain consumes.

`aux_integral_abs_fiberCZBadAtom_le_of_setIntegral`: the atom is the input
minus its average on the interval, so its mass is at most twice the input's
mass there -- no sup bound needed.

`aux_integral_abs_fiberCZBadAtom_le_stoppingHeight`: composing with the
stopping bound gives `∫|b_I| ≤ 4·(2H)^{1/p}·r_I`, which is the blueprint's
`C·|I|·H^{1/p}` written in the `A · r_I` form that
`scratchAssembly_finset_scaleTail_holder_cutoff_le` takes, with
`A = 4·(2H)^{1/p}`.

Next: route this `A` through the scale-tail chain in place of `4·B`, giving a
scale-tail domination whose constant carries `H^{1/p}`, and then the bad budget
is level-independent.

## 2026-09-12T22:45-0700

The atom mass is routed through the scale-tail chain.

`selectedFiberScaleTail_le_selected_intervalTail_sum_of_mass` and
`selectedFiberScaleTail_le_tail_majorant_outside_of_mass` take the atoms' mass
constant `A` as a hypothesis instead of deriving `4·B` from a sup bound, and
carry it into the conclusion.  Only one hypothesis of the original proof
actually used the sup bound for the constant; the remaining uses of `B` are
integrability side conditions for the kernel convolution, which is a fair place
for it.

Composed with `aux_integral_abs_fiberCZBadAtom_le_stoppingHeight`, the
available constant is now `A = 4·(2H)^{1/p}`, so the scale-tail domination
carries `H^{1/p}` exactly as the blueprint's `eq:cz_bad_pointwise` does.

Next: the bad pointwise bound and level budget with this constant, which
replaces `abs_ModelTruncatedOperator_bad_le_majorant_outside` and
`weak_bad_level_budget_majorant_outside`.  At that point the tail's
`H^{-1/p}` and the atom's `H^{1/p}` meet and the bad budget is
level-independent.

## 2026-09-12T23:05-0700

The bad budget is level-independent.

`abs_ModelTruncatedOperator_bad_le_majorant_outside_of_mass` and
`weak_bad_level_budget_majorant_outside_of_mass`: the bad pointwise bound and
level budget with the atoms' mass constant `A` in place of the sup-bound
constant `4·B`.  Then `aux_eLpNorm_tail_mul_stoppingMass_le`: with
`A = 4·(2H)^{1/p}` the tail factor of the bad budget is at most
`4·2^{1/p}·C_q`, with no dependence on the height -- the atom's `H^{1/p}` and
the tail's `H^{-1/p}` cancel exactly as in the blueprint.

This closes the obstruction recorded at 21:45.  All new declarations sit
directly in `Auto.Twisted`, per the instruction received this tick.

Next: the level bound at the canonical stopping data with the mass constant,
then the three budgets at the common constant `A_u`.

## 2026-09-12T23:25-0700

The Calderon--Zygmund level bound now takes the atoms' mass as data, and the
canonical stopping data supplies it.

`ModelTruncatedOperator_weak_finite_of_czData_of_mass`: the general-exponent
level bound at the fiberwise CZ data, with the bad branch's tail factor
carrying an abstract mass constant `A` instead of the sup-bound constant.
Generated from `ModelTruncatedOperator_weak_finite_of_czData` by substitution,
checked before promotion.

`aux_canonical_atom_mass_le`: at the canonical data -- fibers of finite
`p`-mass, averages of `|f_m|^p` -- every selected atom has mass at most
`4·(2H)^{1/p}·r_I`.  Membership in the selection set gives membership in the
finite-mass fiber set for free (`hz.1.1`), which is what makes `|f_m(·,z)|^p`
integrable there.

Next: instantiate the level bound at the canonical data with
`A = 4·(2H)^{1/p}`, then bound its three terms by `aux_eLpNorm_tail_mul_stoppingMass_le`,
the good normalisation and the exception budget, all at `H = (lam/A_u)^R/2`.

## 2026-09-12T23:45-0700

`ModelTruncatedOperator_weak_finite_of_canonical_czData`: the general-exponent
level bound at the canonical stopping data, with the tail factor carrying the
stopping mass `4·(2H)^{1/p}`.  The abstract `Zf`, `Astop`, `A` of the
mass-parametrised bound are instantiated at
`coordinateSourceFiberFiniteMassSet`, `coordinateSourceFiberAverage` and the
canonical mass; the fiber-integrability hypothesis is now indexed by the
transverse point rather than by the ambient point, which is the form the
canonical mass lemma consumes.

One orientation caught by the checker: the level budgets state their conjugate
pair as `q.HolderConjugate p` with `p` the Calderon--Zygmund exponent, while
the mass lemma takes `p.HolderConjugate q`; the instantiation needs `hpq.symm`.

The three terms of this bound are now each matched by a normalisation lemma:
the exception term by `weak_exception_budget_doubled_canonical`, the good term
by `weak_good_budget_term_eq`, and the tail factor by
`aux_eLpNorm_tail_mul_stoppingMass_le`.  Next: apply them at
`H = (lam/A_u)^R/2` and combine with `aux_combine_normalized_budgets`.

## 2026-09-13T00:05-0700

The bad term of the canonical level bound is a real constant.

`aux_ofReal_lineMaximalConst`: the maximal estimate's extended constant is
finite, so it is the extension of its real value -- the same finiteness
argument as in `lpNorm_line_dyadicBallMaximal_le`, now stated once.
`aux_eLpNorm_const_mul_coordinateMaximal_le_of_normalized`: at a normalised
input the maximal factor is at most `|C|·aux_lineMaximalConst P`.

`aux_canonical_bad_term_le`: the product of the three Hoelder factors of the
canonical level bound -- the stopping-mass tail factor and the two passive
maximal factors, all with their constants -- is at most the extension of a
single real constant.  That constant carries `sourceWeight u ^ 30` from the
three `w^10` factors, the power the blueprint absorbs into
`A_u = C_1 U(u)^{100}`.  The fiber integrability and the finiteness of the
selection sets are derived inside from the product-measure integrability of
`|f_m|^p`, so the statement assumes only that and the mass normalisation.

With this, all three terms of `ModelTruncatedOperator_weak_finite_of_canonical_czData`
have real-constant bounds.  Next: the assembly at `H = (lam/A_u)^R/2` with
`aux_combine_normalized_budgets`, which needs `A_u` chosen to dominate the bad
constant's `w^30` -- the blueprint's choice of `C_1`.

## 2026-09-13T00:30-0700

Planning correction before assembling: the good part's strong bound exists
only for the *countable* good field (`lintegral_rpow_ModelTruncatedOperator_countableGoodField_le`,
`…_le_of_normalized`), as the blueprint states it, so the final assembly runs
through `ModelTruncatedOperator_weak_countable_of_budgets` -- countable good
and bad fields -- with the bad budget transferred from the finite families.
The finite-level `ModelTruncatedOperator_weak_finite_of_canonical_czData`
therefore serves as the *finite* bad-budget input, not as the assembly object.

The transfer at a general exponent: `weakBound_rpow_of_ae_tendsto` (the
endpoint proof with the `R`-th root, whose only new ingredient is
`ENNReal.continuous_rpow_const`), `weakBound_rpow_restrict_of_ae_tendsto`, and
`ModelTruncatedOperator_weak_countable_of_finite_restrict`, generated from the
`R = 1` proof by substitution.  Also `aux_one_le_sourceWeight`, needed to let
`A_u = C_1 U(u)^{100}` dominate the bad constant's `U(u)^{30}`.

Next: the good budget at the canonical data -- `Kgood = 64·C·w^100·(2H)^{(P-p)/(pP)}`
from the strong bound and the normalised good-field norm -- in the
`A·(lam/A)^e` shape `weak_good_budget_normalization` consumes.

## 2026-09-13T00:50-0700

`lintegral_rpow_goodField_le_goodConstant_rpow`: at `H = (lam/A)^R/2` the
good field's `P`-th power integral is at most `((lam/A)^{R(1/p - 1/P)})^P`,
the general-exponent form of `lintegral_rpow_goodField_le_goodConstant`
(which fixed `p = 1`).  Note that the endpoint lemma was never consumed --
the conversion from its power-integral form to the `L^P` norm the strong bound
takes did not exist; `aux_lpNorm_le_of_lintegral_rpow_le` supplies it.

## 2026-09-13T01:15-0700

`weak_good_budget_canonical`: the good budget at the canonical stopping data,
at a general output exponent.  Under the normalisation `‖f_j‖_{P_j} ≤ 1`, the
choice `64·C·U(u)^{100} ≤ A_u`, and the scaling identity
`R·(1/p - 1/P_m)·R_0 = R_0 - R`, the good part's level quantity at `H = (lam/A_u)^R/2`
is at most `2^{R_0/R - 1}·A_u`.  Assembled from the strong bound
(`lintegral_rpow_ModelTruncatedOperator_countableGoodField_le`), the good
field's norm at the chosen height, the lpNorm conversion, and
`weak_good_budget_of_lintegral_le` with `weak_good_budget_term_eq`.

The product of norms in the strong bound splits at the distinguished slot via
`Finset.mul_prod_erase`; the two passive slots are the normalised inputs.  The
membership `f_m ∈ L^p` is taken as its own hypothesis, as it must be on
infinite measure.

Two of the three budgets are now discharged at the canonical data with the
common constant: exception (`weak_exception_budget_doubled_canonical`, `4·A_u`)
and good (`2^{R_0/R-1}·A_u`).  Next: the bad budget's real constant
(`aux_canonical_bad_term_le`, carrying `U(u)^{30}`) dominated by `A_u`, then
the countable transfer and the assembly.

## 2026-09-13T01:40-0700

The bad budget is discharged at the canonical data for a finite family.

`aux_sourceWeight_pow_le_pow` and `aux_canonical_bad_term_le_of_weight`: the
bad term's constant is `D·U(u)^{30}`, and since the source weight is at least
one, `A_u ≥ D·U(u)^{100}` dominates it.  The rearrangement of the three
factors' constants into `D·U(u)^{30}` is a `ring` step once the factors are
named.

`weak_bad_budget_canonical_finite`: combining the level budget (with the
stopping atom mass `4·(2H)^{1/p}`) with that domination gives
`τ/2 · |{|U(f^b)| > τ/2} \ E|^{1/R} ≤ A_u` for a finite family.  The Hoelder
triple is instantiated with the tail at the *third* slot, so the product needs
one commutation (`ring` in `ℝ≥0∞`) to meet the constant lemma, which states the
tail first.

All three budgets now hold at the canonical data with the common constant
`A_u`: exception `4·A_u`, good `2^{R_0/R-1}·A_u`, bad `A_u` (finite family).
Next: the countable transfer for the bad budget, then
`ModelTruncatedOperator_weakNorm_le_of_countable_stopping_data`.

## 2026-09-13T02:00-0700

`aux_fiberDyadicExhaustion`: the finite subfamilies of a fixed enumeration of
`FiberDyadicInterval = ℤ × ℤ`, with monotonicity and exhaustion.  This supplies
the `Tn`, `hmono`, `hexh` that the finite-to-countable transfer assumes; the
index type is denumerable, so the enumeration is `Denumerable.ofNat`.

## 2026-09-13T02:15-0700

`weak_bad_budget_canonical_countable`: the bad budget at the canonical data for
the countable bad field.  The finite budget is uniform in the family -- its
constant does not mention `T` -- so the transfer applies with the enumeration's
finite subfamilies, at level `lam/2` and outside the doubled exceptional set.

That is the last of the three budgets in the form the assembly consumes.  Next:
`ModelTruncatedOperator_weakNorm_le_of_countable_stopping_data`, whose three
budget hypotheses are now exactly `weak_exception_budget_doubled_canonical`,
`weak_good_budget_canonical`, and this one -- modulo the exceptional set, which
the assembly takes as an arbitrary `Eset` and which here is the doubled
preimage.
