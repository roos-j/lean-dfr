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

## 2026-09-13T02:35-0700

`aux_canonical_mass_forms`: the distinguished input's normalisation in the four
shapes the budgets consume -- ambient lower integral, `L^p` membership,
integrability over the fiber product, and the product integral -- all derived
from the ambient statement `∫|f_m|^p ≤ 1` with `|f_m|^p` integrable.  The
product forms transfer along the measure-preserving coordinate join, as in
`weak_exception_budget_canonical`.

This removes the last mismatch between the three budgets' hypotheses: they
differ only in how they ask for the normalisation, and now one hypothesis
serves all three.

## 2026-09-13T02:55-0700

`ModelTruncatedOperator_weakNorm_le_canonical`: the weak-`L^R` bound for the
truncated operator at the canonical stopping data.  At each level the height is
`H = (τ/A_u)^R/2` and the three budgets are supplied by
`weak_exception_budget_doubled_canonical` (`4·A_u`),
`weak_good_budget_canonical` (`2^{R_0/R-1}·A_u`) and
`weak_bad_budget_canonical_countable` (`A_u`), so the conclusion is
`‖U(f)‖_{R,∞} ≤ (4 + 2·2^{R_0/R-1} + 2)·A_u`.

This is `eq:one_fiber` for the truncated operator, under the manuscript's own
normalisations.

One honesty note on the statement: the bad branch is assumed integrable on
*every* fiber (`∀ z, Integrable (fun y ↦ coordinateFiberInput m (f m) (y, z))`),
which is stronger than the source needs.  Off the finite-mass set `Z_f` the
selection sets are empty, so the bad field vanishes on that fiber and the
estimate is trivial there; the present chain nonetheless asks for integrability
at every `z`.  Weakening this to `z ∈ Z_f` is a clean follow-up and is recorded
here so it is not mistaken for faithfulness to the manuscript.

## 2026-09-13T03:15-0700

Weakening the fiber-integrability hypothesis flagged last tick.

`aux_fiberDyadicSelectionSet_subset`, `aux_fiberCZBadAtom_eq_zero_of_notMem`,
`aux_selectedFiberScaleTail_eq_zero_of_notMem`: the selection sets lie in the
finite-mass fiber set, so on a fiber outside it every selected atom vanishes
and the scale tail is zero.

`selectedFiberScaleTail_le_tail_majorant_outside_of_mass_weak`,
`integrableOn_scaleTail_fiberCZBadAtom_outside_weak`, and
`abs_ModelTruncatedOperator_bad_le_outside_weak` then ask for fiber
integrability only on `Z_f`.  The original integrability lemma already branched
on membership in the selection set and used the hypothesis on one branch only,
so the weakening is a matter of supplying it there.

Next: carry the weakened hypothesis up through the majorant bound, the level
budget, the canonical bad budget and the assembly, so that
`ModelTruncatedOperator_weakNorm_le_canonical` asks only what the manuscript
establishes.

## 2026-09-13T03:35-0700

The weakening is carried to the top.  `..._weak` variants of the bad pointwise
bound, the level budget, the canonical finite and countable bad budgets, and
the assembly: `ModelTruncatedOperator_weakNorm_le_canonical_weak` asks fiber
integrability only for `z ∈ Z_f`, which is what `f_m ∈ L^p` supplies and what
the manuscript establishes.

The atom-mass hypothesis feeds the integrability through the selection: a
selected `z` lies in `Z_f` by `aux_fiberDyadicSelectionSet_subset`, so the
canonical mass lemma still applies at exactly the points where it is used.

With that, `lem:one_fiber` holds for the truncated operator with no hypothesis
beyond the manuscript's.  Remaining for the label itself: the statement is for
`ModelTruncatedOperator` with normalised inputs, whereas `eq:one_fiber` is for
`U` with the input norms restored.

## 2026-09-13T03:55-0700

Restoring the input norms needs two homogeneities, and both are now in place.

`weakNorm_const_mul`: the weak norm scales, `‖k·v‖_{R,∞} = k·‖v‖_{R,∞}` for
`k > 0`.  Proved by reindexing the supremum over levels, `τ ↦ τ/k` in one
direction and `σ ↦ kσ` in the other.

`modelOperatorRealRescale`, `modelTruncatedOperatorIntegrand_rescale`,
`ModelTruncatedOperator_rescale`: the truncated operator is trilinear in its
three inputs.  The convolution's scaling law `ModelCoordinateConvolution_smul`
was already present -- it had been proved for the four-input Schwartz form
(`ModelSpatialIntegrand_rescale`) but not for the three-input real form the
weak bound uses, so this is the same argument at the operator's own integrand.

Next: combine them.  Given the normalised bound and nonzero inputs, rescale by
`k_j = ‖f_j‖^{-1}` to reach `eq:one_fiber` with the norms restored; the
manuscript treats zero inputs separately, and there the operator vanishes.

## 2026-09-13T04:15-0700

`weakNorm_ModelTruncatedOperator_rescale` and
`weakNorm_ModelTruncatedOperator_of_rescaled`: combining the operator's
trilinearity with the weak norm's homogeneity, a bound proved for rescaled
inputs gives the bound for the originals, scaled by the reciprocal product.
With `aux_modelOperatorRealRescale_inv` this is the manuscript's "restore the
input norms" step, in the form the de-normalised statement will use.

## 2026-09-13T04:35-0700

`aux_lpNorm_const_mul`, `aux_integral_abs_rpow_const_mul`,
`aux_integrable_abs_rpow_const_mul`, `aux_eLpNorm_complex_const_mul`: how the
normalisation quantities scale under rescaling an input -- the `L^p` norm by
`|k|`, the `p`-th mass by `|k|^p`, and the same for the complexified input the
maximal factors are stated over.

These are the translations the de-normalised statement needs: each normalised
hypothesis about the rescaled inputs comes from the corresponding
un-normalised one by one of these.

## 2026-09-13T04:55-0700

Both halves of "normalize all input norms to one, with zero inputs treated
separately" are now available.

`weakNorm_ModelTruncatedOperator_denormalized`: a weak bound for the inputs
rescaled by `‖f_j‖^{-1}` gives the bound for the originals, scaled by
`∏_j ‖f_j‖`.

`aux_ModelCoordinateConvolution_zero`,
`ModelTruncatedOperator_eq_zero_of_input_zero`, `weakNorm_zero`: at a zero
input the operator vanishes identically and its weak norm is zero, so
`eq:one_fiber` is trivial there -- the manuscript's separate treatment of zero
inputs.

What remains for the label is the hypothesis translation: instantiating
`ModelTruncatedOperator_weakNorm_le_canonical_weak` at the rescaled inputs and
discharging each normalised hypothesis through the four scaling lemmas.

## 2026-09-13T05:15-0700

A discrepancy found while setting up the de-normalisation, and fixed.

The canonical statement required `‖f_jj‖_{P_jj} ≤ 1` for *all three* slots,
but `lem:one_fiber` normalises `‖f_m‖_p = 1` and `‖f_j‖_{P_j} = 1` only for
`j ≠ m` -- the distinguished slot's `L^{P_m}` norm is not normalised.  As
stated, the two normalisations at slot `m` would have to agree, which they
cannot: one is at exponent `p`, the other at `P_m`.  That would have made the
de-normalisation impossible rather than merely tedious.

Inspecting the good budget's proof showed the hypothesis was never used at
slot `m`: the product over the passive slots is the only place it enters.
`weak_good_budget_canonical_passive` and
`ModelTruncatedOperator_weakNorm_le_canonical_passive` ask for it only at
`jj ≠ m`, which is what the manuscript assumes.

## 2026-09-13T05:35-0700

`aux_coordinateFiberInput_const_mul`,
`aux_lintegral_fiber_abs_rpow_const_mul`,
`aux_coordinateSourceFiberFiniteMassSet_const_mul`: rescaling an input passes
through the fiber data.  The fiber input scales, the fiber mass scales by
`|k|^p`, and -- the point -- the finite-mass fiber set is *unchanged* for
`k ≠ 0`.

That last fact is what makes the de-normalisation tractable: the canonical
stopping data of the rescaled input is built over the same `Z_f` as the
original's, so the fiber-integrability hypothesis transfers without
re-deriving the stopping set.

On the exponents: identifying the bad budget's `P₁, P₂` with the good budget's
`q j₁.succ, q j₂.succ` needs no change to the statements -- they are free
parameters, so the de-normalised theorem simply instantiates them there and
takes the two Hoelder-triple instances at the identified exponents.

## 2026-09-13T05:55-0700

`ModelTruncatedOperator_weakNorm_le_one_fiber`: the weak-`L^R` bound with the
input norms restored --

  ‖U(f_1,f_2,f_3)‖_{R,∞} ≤ (∏_j N_j) · (4 + 2·2^{R_0/R-1} + 2) · A_u

where `N_j` bounds the `j`-th input's norm (`(∫|f_m|^p)^{1/p}` at the
distinguished slot, `‖f_j‖_{P_j}` at the passive ones).  This is
`eq:one_fiber` for the truncated operator.

Every normalised hypothesis of the canonical bound is discharged from its
un-normalised counterpart through the scaling lemmas: measurability and bounds
directly, the masses through `aux_integral_abs_rpow_const_mul` and
`aux_lpNorm_const_mul`, the complex passive norms through
`aux_eLpNorm_complex_const_mul`, and -- the step that would otherwise have been
circular -- the fiber integrability through
`aux_coordinateSourceFiberFiniteMassSet_const_mul`, since the rescaled input's
stopping set is literally the original's.

## 2026-09-13T06:15-0700

Checked the blueprint before proceeding, and the reading matters: in
`lem:one_fiber` the operator `U` *is* the truncated operator -- `thm:extended_model`
applies the lemma as `‖U^{a,b}_{u,c}(f_1,f_2,f_3)‖_{1,∞} ≤ …`, with the
constants independent of `a, b`.  So there is no separate passage from the
truncated operator to `U` to be made here; the bound proved last tick is
already at the right object.

`C_ModelTruncatedOperator_weakNorm_le_one_fiber` and
`ModelTruncatedOperator_weakNorm_le_one_fiber_explicit`: the manuscript's
`A_u = C_1U(u)^{100}` with `C_1` named -- the maximum of the starting
estimate's constant and the bad branch's kernel constants, plus one.  Both
domination hypotheses are then discharged, so the statement reads

  ‖U^{a,b}(f)‖_{R,∞} ≤ (∏_j N_j) · C · C_1 · U(u)^{100}

with no side conditions on `A_u`.  The distinguished slot `m` and the passive
pair are now parameters rather than being quantified inside, since `C_1`
depends on them -- which is the manuscript's "fix `m`".

## 2026-09-13T06:35-0700

Verified `ModelTruncatedOperator_weakNorm_le_one_fiber_explicit` against
`lem:one_fiber` hypothesis by hypothesis before recording it.

Matching: the exponent data (`hsum` gives `R_0^{-1} = Σ_j P_j^{-1}` with
`R_0 = (q 0).conjExponent` and `P_j = q j.succ`); `1 ≤ p ≤ P_m`; `1 ≤ R`; and
`hexp`, which is `R·R_0·(1/p - 1/P_m) = R_0 - R`, equivalent to the source's
`R^{-1} = p^{-1} + Σ_{j≠m}P_j^{-1}`.  The conclusion matches `eq:one_fiber`,
with the `N_j` bounding the norms rather than equalling them.  The starting
estimate, which the source *assumes*, is derived here from
`thm:initial_model` -- so the Lean statement is the lemma specialised to the
operator the manuscript applies it to.

Not matching: two hypotheses the source does not carry -- the inputs are
pointwise bounded (`|f_jj y| ≤ Bd jj`), and the distinguished input is
integrable on each finite-mass fiber.  The boundedness comes from the file's
operator machinery, and removing it is the manuscript's Schwartz-approximation
step, not yet formalised for this statement.

Status.md accordingly records `lem:one_fiber` as `Statement completed` against
the new name, with the discrepancy spelled out, rather than `Proof completed`.

## 2026-09-13T06:55-0700

Started on the boundedness hypothesis.  First finding: the existing limit
lemma `tendsto_ModelTruncatedOperator_replace_of_tendsto` requires a *uniform*
bound on the approximants, so the pointwise route cannot remove boundedness --
approximating an unbounded input by clamps has no uniform bound.  The
manuscript's own route is the norm route: approximate in `L^{P_m}`, and use the
starting estimate to identify the limit.

`aux_exists_subseq_ae_of_eLpNorm_tendsto` and `weakNorm_le_of_eLpNorm_tendsto`:
a weak-`L^R` bound holding for each of a sequence of functions passes to a
limit in `L^p` norm, via convergence in measure and an almost-everywhere
convergent subsequence.  This is the transfer the approximation argument needs
at its last step.

What remains for the boundedness removal: the operator's continuity in each
slot, i.e. that `Op(f) - Op(g)` is bounded in `L^{R_0}` by the starting
estimate applied to the slotwise differences.  Additivity is available
(`ModelCoordinateConvolution_add`); the multilinear expansion of the difference
is the next piece.

## 2026-09-13T07:15-0700

`ModelTruncatedOperator_replace_sub`: the operator's difference in one slot,
`Op(…g…) - Op(…h…) = Op(…g-h…)`, from the existing slotwise additivity read
backwards.  This is the atom of the three-term telescoping the approximation
argument needs.

Scope note for the remaining work on task 3, recorded so the shape is visible
rather than discovered late:

1. Removing boundedness from `lem:one_fiber` -- the telescoping expansion of
   `Op(f) - Op(g)` across three slots, each term bounded by the starting
   estimate, then `weakNorm_le_of_eLpNorm_tendsto`.  Every step carries
   integrability side conditions, so this is several ticks.
2. `thm:extended_model` -- the three shifted-vertex weak endpoints from
   `lem:one_fiber`, then the interpolation assembly, which already exists as
   `exists_strong_bound_at_simplex_interior` and consumes `ext:interpolation`
   by design.
3. `thm:main` -- discharging `UniformConeModeFormBound`.
4. The section modules for sections 2-7.  `task_3_Instructions.md` asks for one
   file per leaf subsection with every non-temporary file imported in the
   top-level module; only sections 1 and 8 exist.  This is independent of the
   mathematics and is still outstanding.

## 2026-09-13T07:35-0700

Turned to the outstanding structural requirement rather than pushing further
into the approximation plumbing this tick.

`DFR/Auto/Twisted/FunctionSpacesAndFixedBumps/FunctionSpacesAndFixedBumps.lean`:
section 2's labelled theorems in the blueprint's wording -- `lem:schwartz`
(the `L^p` half; the bounded-continuous half is carried by the type),
`lem:bumps` (three assertions: the bump's normalisation, `c_Ψ > 0`, and
`Φ = c_Ψ` on `[-1,1]`), and `lem:domination` (`eq:superposition`).  Added to
the top-level module and recorded in Status.md as the section's Lean file.

Sections 3-7 remain.  Each is the same shape: restate that section's labelled
results by delegation, with the LaTeX statement as the docstring.

## 2026-09-13T07:55-0700

`DFR/Auto/Twisted/DyadicGeometryAndLocalSizes/DyadicGeometryAndLocalSizes.lean`:
section 3's labelled theorems -- `lem:geometry` (the `2^A` children, and the
measure additivity the leaf partition gives), `lem:size` (the comparison at a
point of the closure, in the product form the cubical estimates use), and
`lem:bl` at `eq:bl2`.  Wired into the top-level module and recorded in
Status.md.

Sections 4-7 remain.

## 2026-09-13T08:15-0700

`DFR/Auto/Twisted/CubicalTelescopingWithBoundaryTerms/CubicalTelescopingWithBoundaryTerms.lean`:
section 4's labelled theorems -- `lem:local_integrability`,
`lem:telescoping_identity` (the weighted single-box identity `eq:single_tel`),
`lem:face_cancellation` (`eq:boundary_face_expansion`),
`cor:remainder_norms`, `lem:cube_cs` in its two halves, `prop:cube_tree`
(`eq:cube_tree`) and `prop:edge_tree`.

Two notes from writing it.  The telescoping identity's Lean statement is in
explicit integral form with an extra outer-integrability hypothesis, so its
signature is reproduced verbatim rather than paraphrased -- paraphrasing it
had produced names that do not exist.  And `lem:remainder` and
`lem:oned_telescoping` are not carried here: the first is subsumed by
`cor:remainder_norms`, which is what the development proves and what
Status.md records; the second is a step inside the box identity.

## 2026-09-13T08:35-0700

`DFR/Auto/Twisted/TheModelFormAndItsLocalization/TheModelFormAndItsLocalization.lean`:
section 5's labelled theorems -- `lem:localization` (the signed joint-integral
expansion), `lem:local_cs`, `lem:global_energy` (the joint-integral form of the
second energy on a region, from which the additivity is read) and
`cor:local_model`.

These signatures are long and hypothesis-heavy, so the module is generated by
extracting each theorem's signature verbatim from `Twisted.lean` and
delegating, rather than by paraphrase.  The generator is a scratch script; the
generated file is the artefact.  Section 4's experience -- a paraphrase that
named three nonexistent constants -- is what prompted this.

## 2026-09-13T08:55-0700

Sections 6 and 7 generated: `StoppingTimeAndTheInitialExponentRange` (
`lem:maximal_size`, `lem:stopping`, `lem:forest_bound`,
`lem:model_convergence`, `thm:initial_model`) and
`FiberwiseCalderonZygmundDecomposition` (`lem:fiber_kernel`, `lem:fiber_cz`,
`lem:interval_tails`, `lem:one_fiber`, `lem:exponent_simplex`).  Both wired
into the top-level module and recorded in Status.md.

All eight blueprint sections now have their own module.  The generator needed
three fixes along the way, each caught by the compiler: implicit binders must
not be passed positionally, the `Topology` and `Set` scopes are needed for the
statements that mention `𝓝` and `Ioo`, and the one-fiber statement's `r23`
cannot be inferred from the instance arguments and is passed by name.

`lem:one_fiber`'s docstring in the module repeats the caveat recorded in
Status.md, so the discrepancy is visible at the statement rather than only in
the ledger.

## 2026-09-13T09:15-0700

A finding that changes the assessment of what blocks `thm:extended_model`.

The interpolation assembly `exists_strong_bound_at_simplex_interior` takes its
weak endpoints only for `f : Fin 3 → SimpleFunc X ℝ` with finite-measure
support.  Such inputs are *bounded*, so `lem:one_fiber`'s boundedness
hypothesis -- the one recorded as a discrepancy against the source -- is not an
obstruction to the downstream use.  The fiber-integrability hypothesis is
likewise dischargeable there: a simple function's fiber takes finitely many
values, so finite `p`-mass forces its support to have finite measure, and
boundedness then gives integrability.

So `thm:extended_model` can be assembled from `lem:one_fiber` as it stands.
The boundedness caveat remains a genuine gap against the *label*, but it does
not block the theorem that consumes it.

Worth recording a claim I nearly made and had to withdraw: bounded plus
`L^p` does not give `L^1` on infinite measure -- `|y|^{-2/p}` on `|y| ≥ 1` is a
counterexample for `p ≥ 2`.  The lemma needs the nonzero values bounded away
from zero, which is what a simple function supplies.
`aux_integrable_of_uniform_lower_bound` is stated that way.

## 2026-09-13T09:35-0700

`aux_exists_bound_of_simpleFunc`, `aux_exists_lower_bound_of_simpleFunc`,
`aux_integrable_fiber_of_simpleFunc`: a simple function is bounded, its
nonzero values are bounded away from zero, and consequently a fiber of finite
`p`-mass is integrable.

With these, both of `lem:one_fiber`'s side conditions are discharged on the
class `exists_strong_bound_at_simplex_interior` consumes, so the three
shifted-vertex weak endpoints can be produced without touching the
approximation argument.

## 2026-09-13T09:55-0700

`weakNorm_le_of_lpNorm_bound`: a strong `L^R` bound read as the weak bound the
interpolation consumes -- the blueprint's "the base strong bound is also a weak
bound at `b`", i.e. the fourth vertex of the simplex.

Caught while writing it: `weakNorm_le_eLpNorm` already existed (at line 73179,
with `AEMeasurable` rather than `AEStronglyMeasurable`), and I had started to
re-prove it.  Deleted and delegated.  That is the second time in this session
that a Chebyshev-flavoured fact was already present under a name I did not
recall; the pattern is that the general measure-theoretic facts tend to exist
and the operator-specific ones do not.

## 2026-09-13T10:15-0700

Checked the shifted-vertex exponent bookkeeping against `lem:one_fiber`'s
hypotheses before writing the instantiation, and it lines up:

- the vertex `b + b₀e_m` has input exponents `(b_m+b₀)^{-1}` at slot `m` and
  `b_j^{-1}` elsewhere (`aux_simplexVertexExponent_succ_self`,
  `aux_simplexVertexExponent_succ_ne`), and output exponent `1`
  (`simplexVertexOutput_succ`, already present);
- so `lem:one_fiber` is applied with `p = (b_m+b₀)^{-1}`, `P_j = b_j^{-1}`,
  `R = 1`, and `1/p - 1/P_m = b₀`;
- its scaling identity `R·R_0·(1/p - 1/P_m) = R_0 - R` then reads
  `b₀R_0 = R_0 - 1`, i.e. `R_0 = (1-b₀)^{-1}` -- exactly the manuscript's
  choice of `R_0` (`aux_shifted_vertex_scaling`);
- the Hoelder triples encode `1/P_1 + 1/P_2 + 1/p = 1`, which is
  `∑_j b_j + b₀ = 1`, i.e. the definition of `b₀`
  (`aux_shifted_vertex_reciprocal_sum`).

No mismatch found, which is worth saying explicitly since the two
parameterisations were developed independently.

## 2026-09-13T10:35-0700

`aux_le_ofReal_of_forall_pos` and `aux_tendsto_prod_add_const`: a bound proved
with a strictly positive margin passes to the limit as the margin vanishes.

This is needed because `lem:one_fiber` requires strictly positive norm bounds
`N_j`, while the interpolation's endpoints are stated with the norms
themselves, which vanish when an input is zero.  Proving the endpoint with
`N_j + δ` and letting `δ → 0⁺` avoids a separate zero-input analysis -- which
would otherwise need the operator to be determined by the inputs' a.e. class,
since `lpNorm f = 0` gives only `f = 0` almost everywhere and
`ModelTruncatedOperator_eq_zero_of_input_zero` wants it pointwise.

## 2026-09-13T10:55-0700

`aux_memLp_of_simpleFunc_finMeasSupp`,
`aux_integrable_rpow_of_simpleFunc_finMeasSupp`,
`aux_fiber_integrable_of_simpleFunc_mem`: the `L^{P_j}` membership, the
integrability of the distinguished input's `p`-th power, and the fiber
integrability on the stopping set -- all from the support having finite
measure, via Mathlib's `SimpleFunc.memLp_iff_finMeasSupp`.

With these, every hypothesis of `lem:one_fiber` is now available for the
simple-function tuples the interpolation quantifies over.  What is left for the
endpoint is the instantiation itself: choosing
`N_j = ‖f_j‖_{simplexVertexExponent} + δ`, checking the three norm hypotheses
against that choice, and letting `δ → 0⁺`.

## 2026-09-13T09:05-0700 — the three shifted-vertex weak endpoints and the extended operator bound

`weakNorm_ModelTruncatedOperator_simplexVertex_succ` instantiates
`ModelTruncatedOperator_weakNorm_le_one_fiber_explicit` at the shifted vertex
`b + b_0 e_m` of `lem:exponent_simplex`: the exponent tuple is
`q = (b_0^{-1}, b_1^{-1}, b_2^{-1}, b_3^{-1})`, the distinguished exponent is
`p = P_m^{(m)} = (b_m + b_0)^{-1}`, the two passive exponents are `P_j = b_j^{-1}`
and the output exponent is `R = 1`.  The Hoelder relation `1/P_1 + 1/P_2 + 1/p = 1`
is `aux_shifted_vertex_reciprocal_sum`; the scaling identity is
`aux_shifted_vertex_scaling` with `R_0 = (1-b_0)^{-1} = conjExponent (b_0^{-1})`;
the initial-range conditions `b_0, b_1, b_2 < 1/4` and `b_3 < 1/2` become
`activeSourceStoppingExponent 2 < q`.  Every side condition of `lem:one_fiber` is
discharged on the class the interpolation quantifies over — simple functions of
finite-measure support — using the aux lemmas built over the preceding ticks.
The strictly positive norm bounds `lem:one_fiber` requires are supplied with a
margin `delta` and removed by `weakNorm_le_prod_of_margin`.

`exists_ModelTruncatedOperator_extended_strong_bound` is
`eq:extended_operator_bound`.  It needed one change to the recorded form of
`ext:interpolation`: the per-operator reading `FourVertexMarcinkiewicz` fixes the
operator before producing the constant, so the constant may depend on `u`, while
`UniformConeModeFormBound` — and the source — require one constant for the whole
family.  `FourVertexMarcinkiewiczUniform` states the source's own reading, with
the constant depending only on the exponent vectors and the weights;
`fourVertexMarcinkiewicz_of_uniform` shows it implies the earlier form, so nothing
downstream is affected.

Remaining for `thm:extended_model`: the base vertex's strong `L^{R_0}` bound
(from `thm:initial_model` by duality) and the truncated operator's measurability
and `L^{R_0}` membership are still hypotheses; after that come the Hoelder step to
the truncated form, the scale limit (`lem:model_convergence`), density, and
`lem:permutation`, which together discharge `UniformConeModeFormBound`.

## 2026-09-13T09:55-0700 — the base vertex, the unconditional operator bound, and the form bound

`exists_lpNorm_ModelTruncatedOperator_le_of_simpleFunc` closes the base vertex.
The strict-range output estimate was already available for bounded measurable
fields of finite `L^{P_j}` norm (`lintegral_rpow_ModelTruncatedOperator_le_of_
boundedMeasurable`, which mollifies the Schwartz-only duality step of
`thm:initial_model`); simple functions of finite-measure support are exactly such
fields, so no new density argument was needed.  `aux_memLp_of_lintegral_rpow_lt_top`
converts the finite `R_0`-th power integral into the `L^{R_0}` membership the
interpolation also consumes.

With that, `exists_ModelTruncatedOperator_extended_strong_bound_unconditional`
carries no hypotheses beyond the exponent conditions and `ext:interpolation`, and
`exists_abs_formPairing_ModelTruncatedOperator_le_extended` is the closing Hoelder
display of `thm:extended_model`.

One further correction to the recorded external hypothesis: the conclusion of
`FourVertexMarcinkiewiczUniform` now asserts `MemLp (T f) (ofReal R)` alongside the
norm inequality.  `lpNorm` is zero off `L^R`, so the inequality alone is vacuous
about membership, while the source's `‖T f‖_R ≤ C ⋯` asserts finiteness; without
the conjunct the Hoelder step to the form could not be taken.  The per-operator
reading `FourVertexMarcinkiewicz` is unchanged and is still implied.

Remaining for `thm:extended_model`: density in the three active slots,
complexification, the scale limit, and `lem:permutation`.

## 2026-09-13T10:45-0700 — density in the active slots, and the extended full-scale form bound

`exists_ModelTruncatedOperator_extended_strong_bound_boundedMeasurable` lifts the
interpolated operator bound off the simple functions `ext:interpolation` is stated
for.  `SimpleFunc.approxOn (h j) _ (range (h j) ∪ {0}) 0 _ n` converges pointwise
everywhere, satisfies `|s_n| ≤ 2|h_j|` (so the sup bound survives with a factor two
and the `L^{p_j}` norm with the same factor), and is of finite-measure support
because it lies in `L^{p_j}`.  Fatou through
`lintegral_rpow_ModelTruncatedOperator_le_of_ae_tendsto_all` then gives the bound
for the limit with the constant multiplied by `2^3`; the statement is an `∃ C`, so
the loss is free.

`exists_abs_formPairing_ModelTruncatedOperator_le_extended_boundedMeasurable` is the
Hoelder display on that class, and `exists_abs_ModelFullForm_le_extended` is the
full-scale real form bound: the interval form is controlled uniformly in the
truncation by `abs_ModelScaleIntervalTruncation_le_of_extended_operator_bound`
(which was already in place, waiting for exactly this operator estimate), and
`tendsto_ModelScaleTruncation_of_realSchwartz` supplies the scale limit.

That statement is the exact analogue of
`exists_uniform_initialModelFullForm_bound_weight100` at the extended exponents.
The remaining work is the chain from it to `UniformConeModeFormBound`:
complexification, `lem:permutation`, and the mode-sum bookkeeping.  That chain
exists for the initial range but is phrased in terms of the strict-range hypothesis,
so it has to be re-derived with the form bound as an input hypothesis.

## 2026-09-13T11:35-0700 — the complex bridges, and locating the last structural gap

Traced the chain from the real full-scale model form to `UniformConeModeFormBound`
and found most of it already parametric in the model bound:
`UniformActiveModelBound` and `exists_norm_tsum_coneModeExpansion_le_of_modelBound`
take the model estimate as a hypothesis, and
`norm_LiteralModelFullForm_le_weight100` takes the *real* bound as a hypothesis and
supplies the `2^5` real/imaginary expansion.  So the complexification and the
coordinate relabeling are exponent-blind.

Added `UniformRealModelFormBound` and the two bridges it feeds:
`exists_uniform_LiteralModelFullForm_bound_of_real` (real to complex, factor `32`)
and `exists_uniform_LiteralActiveModelFullForm_bound_of_real` (to every active
coordinate, via `LiteralActiveModelFullForm_permute_to_third`).  Both are stated
against the hypothesis, so the extended range and the initial range use the same
passage.

The remaining structural gap is on the frequency side, and it is the same gap for
the initial range as for the extended one — nothing in the development yet produces
`UniformConeModeFormBound`.  What is missing is the general-`i` identification

  coneModeForm α i ν t F
    = thirdModeFrequencyForm (conePermutedAnisotropy α i) (standardModeOfInt ν) t
        (complexPermutedModelInput (Equiv.swap 2 i) F),

after which `thirdModeFrequencyFullForm_eq_LiteralActiveModelFullForm_permuted`
closes it.  At `i = 2` the identification is `thirdModeFrequencyFullForm_eq_
LiteralActiveModelFullForm`; for general `i` it is a change of variables on
`Frequency9`.  The map is
`(Φ_σ ζ)^j = coordinatePermutation σ (ζ^{σ j})`, which satisfies
`frequencyDiagonal ∘ Φ_σ = coordinatePermutation σ ∘ frequencyDiagonal` (both sides
have `j`-th component `ζ^{σ j}(σ j)`), is measure preserving on the product measure,
and carries `frequencyKernel F` to `frequencyKernel (permuted F)` once one knows
`schwartzFourier (f ∘ P) = schwartzFourier f ∘ P` for a coordinate permutation `P`
— which is not in Mathlib here and has to be proved from
`MeasurePreserving.integral_comp` plus `P* = P⁻¹`.

## 2026-09-13T12:25-0700 — the coordinate relabeling, on the multiplier side

Rather than a change of variables on `Frequency9`, the relabeling is cleaner on the
spatial side, where the multiplier form is defined.  Three steps, all verified:

`aux_schwartzFourier_comp_isometry`: for an isometric equivalence `P` of `E_3`,
`𝓕(f∘P) = (𝓕 f)∘P`.  The adjoint of an isometry is its inverse, so the character
transfers (`aux_frequencyPhase_isometry`), and `P` is measure preserving.  Mathlib
does not carry this for the Schwartz Fourier transform in this snapshot.

`twistedProduct_complexPermutedModelInput`: the translated product `P_f` of
`def:multiplier` satisfies
`P_{permuted F}(s) = P_F((coordinatePermutation σ).symm s)`.  The computation is a
substitution `x = Qy` inside the defining integral together with
`Q⁻¹ e_j = e_{σ j}`, after rewriting the three-factor product as a `Finset` product
so that `Equiv.prod_comp σ` can reindex it.

`multiplierForm_comp_coordinatePermutation`: consequently
`Λ_{S∘Q}(F) = Λ_S(permuted F)`.  This is `lem:permutation` in the form the transport
needs, and it is exactly what was missing to identify `coneModeForm α i ν t F` with a
third-coordinate mode form in permuted coordinates.

Next: convert both sides between `multiplierForm` and `frequencyForm` using the
certificates (`exists_isAnisotropicMultiplier_thirdModeFrequencySymbol` for the
third-coordinate symbol, and `IsAnisotropicMultiplier_permute` with
`permutedAnisotropy_swap_involutive` / `coordinatePermutation_swap_involutive` for
the relabeled one), integrate in the scale, and compose with
`thirdModeFrequencyFullForm_eq_LiteralActiveModelFullForm_permuted` to reach
`LiteralActiveModelFullForm`, which the bridges of the previous tick already bound.

## 2026-09-13T13:20-0700 — `thm:main` closed, conditional only on `ext:interpolation`

The remaining chain fell into place in one pass.

`coneModeForm_eq_thirdModeFrequencyForm_permuted`: the `i`th cone's mode form is
the third-coordinate mode form of the relabeled tuple.  The proof runs
`frequencyForm → multiplierForm → (relabel) → multiplierForm → frequencyForm`,
using `multiplierForm_comp_coordinatePermutation` from the previous tick and the
certificates `exists_isAnisotropicMultiplier_thirdModeFrequencySymbol` and
`IsAnisotropicMultiplier_permute` (the latter with
`permutedAnisotropy_swap_involutive` and `coordinatePermutation_swap_symm_apply`,
since `swap 2 i` is its own inverse).

`coneModeFullForm_eq_LiteralActiveModelFullForm`: integrating that in the scale and
composing with `thirdModeFrequencyFullForm_eq_LiteralActiveModelFullForm_permuted`
identifies the cone mode full form with a literal complex active-coordinate model
form at the mode's translation, with the coefficient negated.

`uniformConeModeFormBound_of_real`: hence the real model bound gives
`UniformConeModeFormBound`.  The translation is `(coordPerm σ).symm (standardModeTranslate ν)`,
whose weight is the mode's by `sourceWeight_coordinatePermutation` and
`sourceWeight_standardModeTranslate_pow_le`; the three per-coordinate constants are
summed.

`uniformRealModelFormBound_permuted_of_main_bounds`: for every relabeling `σ`, the
hypotheses of `thm:main` put the permuted reciprocals in `eq:extended_region`
(`extendedRegion_of_main_bounds`, since `4 < p_0` and `1 < p_j < 4` give
`beta_0 < 1/4` and every `beta_j > 1/4`), so `exists_exponentSimplex_base` produces a
base point adapted to that relabeling and `exists_abs_ModelFullForm_le_extended`
applies.  The base point genuinely has to depend on `σ`: the simplex needs one
coordinate in `(1/4, 1/2)` and the other two below `1/4`, and which coordinate that
is moves with the relabeling.

`anisotropicParaproduct_of_interpolation` and the section-1 `thm_main` now carry
only `hU : FourVertexMarcinkiewiczUniform volume`, which is `ext:interpolation`.
Both audit to `propext, Classical.choice, Quot.sound`.

## 2026-09-13T14:05-0700 — verification pass, and the remaining faithfulness gap

`lake build` completes successfully (3343 jobs) on the pinned toolchain
`leanprover/lean4:v4.33.0-rc1`; `Auto` remains outside `lakefile.toml` and is
checked with `lake env lean`.  `Auto.Twisted.thm_main` audits to
`propext, Classical.choice, Quot.sound`.  All eight section modules and
`DFR/Auto/Twisted.olean` rebuild clean; `git diff --check` is clean; no `sorry`.

Every labelled item in `automation/Status.md` is now `Proof completed` or
`Completed` except one: `\label{lem:one_fiber}` remains `Statement completed`.
The Lean statement carries two hypotheses the manuscript's does not — the inputs
are pointwise bounded, and the distinguished input is integrable on each
finite-mass fiber.  Where `lem:one_fiber` is used (the three shifted-vertex weak
endpoints of `thm:extended_model`, on simple functions of finite-measure support)
both hypotheses are free, so `thm:main` is unaffected; the gap is one of
faithfulness to the lemma as stated.

Removing the boundedness is the manuscript's approximation step, and the obstacle
is precise: `ae_tendsto_ModelTruncatedOperator_of_ae_tendsto_all` dominates the
scale integrand by a constant built from a uniform sup bound on the inputs.  With
`SimpleFunc.approxOn` approximants the domination is by twice the limit, not by a
constant, so two replacements are needed.

`tendsto_ModelCoordinateConvolution_of_ae_line_dominated` is the first of them:
the convolution's inner dominated-convergence step now runs against the majorant
`2|f_j(x - r e_j)| |kernelDilate k s r|` instead of a constant.  What remains is
the outer step, the domination in the scale variable `t` over `Ioc a b`.  The
right tool is the scale-uniform maximal bound
`abs_activeModelCoordinateConvolution_le_coordinateDyadicBallMaximal`, which is
already proved but currently assumes a sup bound; its own ingredient
`abs_activeModelCoordinateConvolution_le_coordinateBracketConvolution_of_integrable`
assumes only line integrability, so a boundedness-free version looks reachable.
It then needs the almost-everywhere finiteness of the coordinate maximal function
for `L^{P_j}` inputs with `P_j > 1`.

## 2026-09-13T14:50-0700 — toward removing `lem:one_fiber`'s side hypotheses

Two ingredients, both verified.

`exists_uniform_scale_majorant_activeModelKernel`: for scales in a compact
interval away from zero, `|kernelDilate (activeModelKernel i j u) s r| ≤
C U(u)^{10} (b/a) bracketKernelAt b 0 r`, uniformly in `s ∈ [a,b]`.  This replaces
the maximal-function route sketched last tick: the scale range in
`ModelTruncatedOperator` is `Ioc a b` with `0 < a`, so `s⁻¹ ≤ a⁻¹` and the bracket
profile is antitone (`aux_bracketKernel_anti`), which is all that is needed.  No
maximal theorem, no a.e. finiteness of a maximal function.

`ae_mem_coordinateSourceFiberFiniteMassSet`: for an `L^p` input, almost every
transverse fiber carries finite `p`-mass.  Tonelli through the measure-preserving
coordinate split (`aux_lintegral_rpow_enorm_comp_coordinateSplit_eq_iterated`) plus
`ae_lt_top`.

With these, the remaining step for the boundedness-free `lem:one_fiber` is the
outer dominated convergence in the scale variable: for almost every `x`, the line
restriction of each `f_j` is in `L^{P_j}(ℝ)` (the same Tonelli argument), Hoelder
against the fixed majorant `bracketKernelAt b 0` gives a bound on
`|ModelCoordinateConvolution j (f_j) k_j s x|` independent of `s ∈ [a,b]`, and the
product of the three is then a constant dominating function on a finite measure
space.

Separately, the second side hypothesis — global integrability of the distinguished
input on each finite-mass fiber — looks stronger than the source needs: the atoms
only require local integrability on the selecting interval, which Hoelder gives from
finite `p`-mass on a bounded interval.  Removing it would mean localizing that
hypothesis inside the atom construction, which is a deeper refactor than the
boundedness removal.

## 2026-09-13T15:35-0700 — the scale-uniform convolution bound and the line restrictions

`aux_memLp_bracketKernelAt`: the bracket profile at a fixed positive scale lies in
every `L^q`, `q ≥ 1` (bounded by `b⁻¹` and integrable, via
`aux_memLp_of_le_one_of_integrable`).

`exists_uniform_scale_bound_ModelCoordinateConvolution`: for `a ≤ s ≤ b` with
`0 < a`,
`|ModelCoordinateConvolution j f (activeModelKernel i j u) s x|
  ≤ C U(u)^{10} (b/a) ∫ |f(x - r e_j)| bracketKernelAt b 0 r dr`,
the right side independent of `s`.  That is the dominating function the scale
integral needs.

`ae_memLp_line_of_memLp`: for an `L^P` input and almost every `x`, the restriction
`r ↦ f(x - r e_j)` is in `L^P(ℝ)`.  Three small steps: sliding along `e_j` only
shifts the active coordinate (`aux_coordinateSplit_sub_smul`), so the line
restriction is a fiber of `coordinateFiberInput` read backwards
(`aux_line_eq_coordinateFiberInput`); a full-measure transverse set pulls back to a
full-measure ambient set through the measure-preserving split
(`aux_ae_coordinateSplit_snd_mem`); and the fibers of an `L^P` input carry finite
mass almost everywhere (previous tick).

What remains is mechanical: Hoelder turns the line restriction and the bracket
profile into the integrability hypothesis that
`exists_uniform_scale_bound_ModelCoordinateConvolution` asks for, the three slot
bounds multiply to a constant dominating function on the finite scale measure, and
the resulting dominated convergence replaces the uniform-bound hypothesis in
`ae_tendsto_ModelTruncatedOperator_of_ae_tendsto_all`.

## 2026-09-13T16:15-0700 — Hoelder pairing and the slot-bound integrand estimate

`ae_integrable_line_mul_bracketKernelAt`: for an `L^P` input with `P > 1` and almost
every `x`, the line restriction pairs integrably with the bracket profile.  Hoelder
against `aux_memLp_bracketKernelAt` at the conjugate exponent.

`aux_integrable_line_mul_kernelDilate_of_bracket`: that pairing dominates the actual
model kernel at every scale in `[a, b]`, which is exactly the majorant hypothesis of
`tendsto_ModelCoordinateConvolution_of_ae_line_dominated`.

`abs_modelTruncatedOperatorIntegrand_le_of_slot_bounds`: the scale integrand is
bounded by the product of any three per-slot convolution bounds.  Stated against
supplied bounds rather than derived ones, so the scale-uniform bound of the previous
tick plugs straight in and the result is a constant in `t`.

Remaining for the boundedness-free `lem:one_fiber`: assemble these into
`ae_tendsto_ModelTruncatedOperator_of_ae_tendsto_all` without the uniform sup
hypothesis, then re-run the `approxOn` argument on the weak-norm conclusion.

## 2026-09-13T16:55-0700 — the sup-free convergence lemma

`tendsto_ModelTruncatedOperator_of_ae_line_all_dominated` and its almost-everywhere
form `ae_tendsto_ModelTruncatedOperator_of_ae_tendsto_all_dominated` replace the
uniform sup hypothesis of `ae_tendsto_ModelTruncatedOperator_of_ae_tendsto_all` by
pointwise domination `|g_n j| ≤ 2|f_j|` together with `f_j ∈ L^{P_j}`, `P_j > 1`.

The majorant is assembled exactly as planned: for `t ∈ Ioc a b` the scale
`t^{α_j}` lies in `[a^{α_j}, b^{α_j}]`, the bracket profile at `b^{α_j}` dominates the
model kernel there, Hoelder against the line restriction bounds each slot's
convolution by a constant in `t`, and the product of the three bounds the scale
integrand.  Dominated convergence in `t` then runs on the finite logarithmic scale
measure.

What remains is the instantiation: run `SimpleFunc.approxOn` on all three slots,
check the hypotheses of `ModelTruncatedOperator_weakNorm_le_one_fiber_explicit` for
each approximant (the norms cost a factor two per slot, so the constant grows by
`2^3`), and transfer the weak bound to the limit with `weakNorm_le_of_ae_tendsto`.

## 2026-09-13T17:40-0700 — `lem:one_fiber` closed; every labelled item is now proved

`exists_simpleFunc_approx_of_memLp` packages the `SimpleFunc.approxOn`
approximants of one slot: finite-measure support, `|s_n| ≤ 2|f|`, pointwise
convergence, `L^P` membership, and `‖s_n‖_P ≤ 2‖f‖_P`.

`ModelTruncatedOperator_weakNorm_le_one_fiber_unbounded` applies that in all three
slots.  Each approximant satisfies every hypothesis of the bounded estimate — it is
bounded because it is simple, its `p`-mass is dominated because `|s_n| ≤ 2|f|`, and
its fibers are integrable because a simple function of finite-measure support has
integrable fibers on its finite-mass set — at the cost of doubling each input norm,
so the constant grows by `2^3`.  The weak bound then passes to the almost-everywhere
limit through `ae_tendsto_ModelTruncatedOperator_of_ae_tendsto_all_dominated` and
`weakNorm_le_of_ae_tendsto`.  Both the boundedness hypothesis and the
fiber-integrability hypothesis are gone; the statement is now the manuscript's.

`automation/Status.md` has no `Statement completed` entries left.  Every labelled
definition is `Completed` and every labelled theorem is `Proof completed` or
`External`, the two external ones being `ext:maximal` (Mathlib's
Hardy--Littlewood theory) and `ext:interpolation` (the four-vertex Marcinkiewicz
hypothesis the manuscript quotes without proof).  `Auto.Twisted.thm_main`,
`Auto.Twisted.thm_cone` and `Auto.Twisted.lem_one_fiber` all audit to
`propext, Classical.choice, Quot.sound`.

## 2026-09-13T18:30-0700 — new task: prove the two external theorems

Survey first.  `ext:maximal` is not a hypothesis anywhere; it is cited as available
Mathlib/`lean_spherical` machinery, so proving it means stating the blueprint's own
wording and deriving it.  `ext:interpolation` is a genuine `Prop` hypothesis
(`FourVertexMarcinkiewicz`, `FourVertexMarcinkiewiczUniform`) that `thm:main`
depends on.

Available: `lean_spherical` has the dyadic Hardy--Littlewood maximal theory
(`Auto.HardyLittlewoodMaximal.dyadicBallMaximalRaw`, weak (1,1) and strong (p,p)),
and this repo already wraps its one-dimensional strong bound as
`eLpNorm_line_dyadicBallMaximal_le`.  Mathlib has Vitali/Besicovitch covering and
`VitaliFamily.ae_tendsto_average_norm_sub`, i.e. Lebesgue differentiation.  Mathlib
has *no* Marcinkiewicz or real interpolation in this snapshot; `lean_spherical` has
Riesz--Thorin and Stein interpolation, both for the complex method with strong
endpoints, so neither applies to the weak multilinear statement.

First piece of `ext:maximal`: `lineMaximalRaw` is the blueprint's operator, the
supremum over *all* positive radii.  `lineMaximalRaw_le_two_mul_dyadicBallMaximalRaw`
compares it to the dyadic one — for `r > 0` take `n = Int.log 2 r + 1`, so
`r < 2^n ≤ 2r`, giving a factor two — and `eLpNorm_lineMaximal_le` transfers the
strong `(q,q)` bound.

Remaining for `ext:maximal`: Lebesgue differentiation for locally integrable
functions, the same along nested standard dyadic intervals, and the fiber versions
(Fubini, for which `ae_memLp_line_of_memLp` and `aux_ae_coordinateSplit_snd_mem`
are already in place).

## 2026-09-13T19:20-0700 — `ext:maximal`: Lebesgue differentiation

`ae_tendsto_setAverage_norm_sub` is the ball statement, for any metric measure
space with the Besicovitch covering property: Mathlib's
`VitaliFamily.ae_tendsto_average_norm_sub` on `Besicovitch.vitaliFamily`, composed
with `Besicovitch.tendsto_filterAt` to convert the Vitali filter into `r → 0⁺`.
It applies to `E3` and to the fiber line alike.

`ae_tendsto_dyadic_average_norm_sub` is the dyadic statement on the line.
`dyadicIntervalAt k x = (k, ⌊x / 2^k⌋)` is the standard dyadic interval of scale `k`
containing `x`; it is contained in the closed ball of radius `2^k` about `x`, whose
measure is exactly twice its own, so the dyadic average is at most twice the ball
average and the ball limit squeezes it to zero.

Remaining for `ext:maximal`: the fiber versions on `E3`, which are Fubini over the
coordinate split — `ae_memLp_line_of_memLp` and `aux_ae_coordinateSplit_snd_mem`
already carry that transfer.

## 2026-09-13T20:05-0700 — `ext:maximal` proved

The fiber statements are immediate once the one-dimensional ones are in place: a
fiber of a function on `E_3` is a function on the line, so
`ae_ae_tendsto_setAverage_norm_sub_fiber` and
`ae_ae_tendsto_dyadic_average_norm_sub_fiber` are the line statements applied under
the almost-everywhere fiber hypothesis.  The fiber maximal estimate was already in
the repository as `coordinateDyadicBallMaximal_lintegral_bound`.

Section 6's module now carries `ext:maximal` in five pieces —
`ext_maximal_strong_type`, `ext_maximal_lebesgue_differentiation`,
`ext_maximal_dyadic_differentiation`, `ext_maximal_fiber_strong_type`,
`ext_maximal_fiber_differentiation` — all auditing to
`propext, Classical.choice, Quot.sound`.  `automation/Status.md` records it as
`Proof completed`.

One external theorem remains: `ext:interpolation`.

## 2026-09-13T21:05-0700 — `ext:interpolation`: the geometric core

Multilinear Marcinkiewicz has to be built from scratch — Mathlib has no real
interpolation in this snapshot, and `lean_spherical`'s Riesz--Thorin and Stein
interpolation are the complex method with strong endpoints.  `lean_spherical` does
have `marcinkiewicz_weak_one_top`, the sublinear weak-(1,1) plus `L^∞` case, which is
a useful template for the distribution-function machinery but not the statement
needed.

The distinctive geometric input is that the interpolated exponent vector lies in the
*interior* of the tetrahedron spanned by the four vertices, and that is what produces
geometric decay when the three-parameter level sum is split across vertices.  Two
lemmas, both verified:

`eq_zero_of_forall_gapPairing_nonpos`: if a covector `w` pairs non-positively with
every vertex measured from a strictly positive barycentre, then `w = 0`.  The
weighted sum of the pairings is zero, so with positive weights each pairing is zero;
the vertex differences are linearly independent and three of them live in a
three-dimensional space, so they span, and a functional vanishing on a spanning set
vanishes.

`exists_gap_of_affineIndependent`: the quantitative form.  The maximum over the four
vertices is continuous and positively homogeneous and, by the previous lemma,
strictly positive off the origin, so its minimum `δ` over the (compact, nonempty)
unit sphere is positive and `δ‖w‖ ≤ max_a ⟨w, v_a - x⟩` for every `w`.

Next: the distribution-function layer of the proof — the layer-cake formula, the
dyadic level decomposition of a simple function, and the estimate of each
`T(f_1^{k_1}, f_2^{k_2}, f_3^{k_3})` against the four vertex bounds.

## 2026-09-13T22:00-0700 — defect found in the recorded form of `ext:interpolation`

Beginning the analytic layer of the interpolation proof exposed a defect in the
definitions `FourVertexMarcinkiewicz` and `FourVertexMarcinkiewiczUniform`: they
quantify over *every* operator `T : (Fin 3 → (X → ℝ)) → (X → ℝ)`, whereas the
manuscript's `ext:interpolation` opens "Let `T` be a *trilinear* operator on complex
simple functions of finite measure support".  The trilinearity hypothesis was
dropped when the external theorem was recorded.

This matters.  Marcinkiewicz interpolation is false without some linearity or
sublinearity structure, and the standard proof uses trilinearity essentially, to
split `T(f)` over the dyadic level decomposition of the three inputs.  As recorded,
the hypothesis is strictly stronger than the manuscript's, so `thm:main` currently
rests on an assumption the manuscript does not make and which may well be false.
The fix is to add the trilinearity hypothesis to the definitions and supply it at
the point of use.

The supply side is now in place.  `ModelTruncatedOperator_replace_add_of_bounded`
gives additivity in one slot for bounded measurable inputs — the line integrands are
integrable because the inputs are bounded and the kernels integrable, and the scale
integrand is integrable on `Ioc a b` because it is bounded and the logarithmic scale
measure is finite there — and `ModelTruncatedOperator_replace_smul` gives
homogeneity, unconditionally, from `ModelTruncatedOperator_rescale` at the vector
`fun j ↦ if j = m then k else 1`.

Next: add trilinearity to the two definitions, thread it through
`exists_strong_bound_at_simplex_interior_uniform` and
`exists_ModelTruncatedOperator_extended_strong_bound`, and discharge it at the model
operator with the two lemmas above.

## 2026-09-13T22:45-0700 — the trilinearity correction landed

`TrilinearOnSimple μ T` now states additivity and homogeneity in each slot on simple
functions of finite-measure support, and it is a hypothesis of both
`FourVertexMarcinkiewicz` and `FourVertexMarcinkiewiczUniform`, as the manuscript
states.  The change was threaded through `fourVertexMarcinkiewicz_zero`,
`strong_bound_of_fourVertexMarcinkiewicz`, `exists_strong_bound_at_simplex_interior`,
`fourVertexMarcinkiewicz_of_uniform` and
`exists_strong_bound_at_simplex_interior_uniform`, and discharged at the point of use
by `trilinearOnSimple_ModelTruncatedOperator`.

`Auto.Twisted.thm_main` is unchanged in statement and still audits to
`propext, Classical.choice, Quot.sound`; its proof now also verifies that the model
truncated operator is trilinear, which the manuscript takes for granted.  The whole
file compiles with no `sorry`, and all eight section modules rebuild.

The external hypothesis is now the manuscript's, so proving it is proving the right
theorem.

## 2026-09-13T23:25-0700 — `ext:interpolation`: the dyadic level decomposition

`dyadicLevelSet f k = {x | 2^k ≤ |f x| < 2^{k+1}}` and
`dyadicLevelPiece f k = f · 1_{dyadicLevelSet f k}`, with measurability, pairwise
disjointness of distinct bands, and the pointwise bound `|piece| ≤ 2^{k+1}`.

For a simple function the relevant bands are indexed by
`dyadicLevelIndices f = (f.range.filter (· ≠ 0)).image (fun v ↦ Int.log 2 |v|)`,
a finite set, and `sum_dyadicLevelPiece` shows the pieces over that set reconstruct
`f` pointwise: at a point where `f` vanishes every piece vanishes, and elsewhere the
point lies in exactly the band `Int.log 2 |f x|`, which is one of the indices.

The two quantitative inputs the vertex estimates need are
`measure_dyadicLevelSet_le` — `(2^k)^q μ(band) ≤ ∫⁻ ‖f‖ₑ^q`, so bands of high index
are small — and `eLpNorm_dyadicLevelPiece_le` —
`‖piece‖_q ≤ 2^{k+1} μ(band)^{1/q}`, which is what turns a vertex weak bound into a
bound in terms of band measures alone.

## 2026-09-13T23:55-0700 — `ext:interpolation`: the trilinear expansion

`trilinearOnSimple_update_zero` — a trilinear operator vanishes when a slot is zero
(homogeneity at the scalar zero) — and `trilinearOnSimple_sum_slot` — one slot
expands over any finite decomposition into simple functions, by induction on the
`Finset` with additivity at each step and the zero case as base.  The tail of the
induction is handled as a single simple function `∑ b ∈ s, g b`, whose
finite-measure support comes from `simpleFunc_finMeasSupp_sum` and whose coercion is
`simpleFunc_coe_sum`.

`dyadicLevelPieceSimple f k = f.restrict (dyadicLevelSet f k)` realises a level piece
as a simple function; its support is contained in that of `f`, so it inherits
finite-measure support.  `trilinearOnSimple_sum_levels` then expands one slot over
its own dyadic bands.

Applying that in all three slots gives the three-parameter expansion the vertex
bounds are applied to; that iteration, and then the summation where the interior gap
supplies geometric decay, is what remains.

## 2026-09-14T00:25-0700 — `ext:interpolation`: the three-slot expansion

`trilinearOnSimple_expand_three` writes `T(f_1,f_2,f_3)` as the finite triple sum
over the dyadic bands of the three inputs, each term being `T` applied to the tuple
with all three slots replaced by level pieces.  The iteration is three applications
of `trilinearOnSimple_sum_levels`, each preceded by rewriting the tuple as an update
at that slot by its own entry (`Function.update_eq_self`) and followed by
`coe_update_eq`, which moves the update across the coercion from simple functions to
functions.  `update_three_apply` reads the triple update back slot by slot, which is
how the vertex bounds will address the individual pieces.

The scaffolding for `ext:interpolation` is now complete: the interior gap, the band
decomposition with its measure and norm bounds, trilinearity, and this expansion.
What is left is the estimate itself — attaching the four vertex weak bounds to each
term and summing over the three-parameter index set, where the gap gives geometric
decay.  That is the substantial remainder.

## 2026-09-14T00:55-0700 — `ext:interpolation`: vertex bounds on the expansion terms

`measure_dyadicLevelSet_lt_top` — a band of a simple function of finite-measure
support has finite measure, since the band sits inside the support.

`lpNorm_dyadicLevelPiece_le` is the real-valued form of the band norm estimate:
`‖piece‖_q ≤ 2^{k+1} μ(band)^{1/q}`, obtained from the extended-valued form by
`toReal`, which is legitimate because both sides are finite.

`weakNorm_expansion_term_le` attaches the vertex bounds: for every vertex `a` and
every triple of bands `k`, the corresponding term of the expansion satisfies
`‖T(pieces)‖_{r_a,∞} ≤ A_a ∏_j (2^{k_j+1} μ(band_j)^{1/P_{a,j}})`.  The right-hand
side now involves only the band heights and the band measures, which is the form the
summation consumes.

What remains is the summation: choosing, for each `k`, the vertex that makes the
bound smallest — which is where `exists_gap_of_affineIndependent` supplies geometric
decay in `k` — and assembling the weak bounds on the terms into a strong `L^R` bound
on the sum.

## 2026-09-14T01:30-0700 — survey correction: much of the interpolation machinery already existed

A process mistake to record.  Before building the level decomposition this session I
did not survey what the repository already contained for `ext:interpolation`.  It
contains a great deal, built in an earlier session and sitting between lines 71292
and 72672:

* `dyadicLayer` / `dyadicLayerSet` with measurability, the indicator form, the
  strict bounds `2^k ≤ |layer| < 2^{k+1}`, `finite_dyadicLayer_support`,
  `dyadicLayerIndices` and `sum_dyadicLayerIndices` (the finite reconstruction), and
  the two-sided layer norm bounds `eLpNorm_dyadicLayer_le` and
  `le_eLpNorm_dyadicLayer`.
* `weakNorm` with `meas_lt_le_of_weakNorm_le` (the Chebyshev form) and
  `lintegral_rpow_le_of_two_weakNorm`, the two-point weak-to-strong passage with the
  geometric-mean constant.
* The exponent bookkeeping: `dyadicLevel_measure_rpow_exchange`,
  `sum_weights_exchange_eq_zero`, `prod_dyadicLevel_exchange_eq_one`,
  `rpow_four_weighted_mean_eq`, `outputReciprocal_identities`,
  `one_lt_outputExponent_lt`.
* The summation frame: `meas_lt_of_triple_expansion_bounds` (splitting a level
  across a triple sum) and `sum_weighted_levels_le`.

So this session's `dyadicLevelSet`, `dyadicLevelPiece`, `dyadicLevelIndices`,
`sum_dyadicLevelPiece`, `measure_dyadicLevelSet_le` and
`eLpNorm_dyadicLevelPiece_le` duplicate existing lemmas under different names.  They
are correct and harmless but redundant; the `dyadicLayer` API is the one the rest of
the argument is written against and is what later work should use.

What this session added that is genuinely new: the `TrilinearOnSimple` correction and
its discharge at the model operator; `dyadicLevelPieceSimple`, realising a layer as a
simple function; the trilinear expansion lemmas up to
`trilinearOnSimple_expand_three`; `weakNorm_expansion_term_le`; and the interior gap
lemmas `eq_zero_of_forall_gapPairing_nonpos` and `exists_gap_of_affineIndependent`,
which have no counterpart in the earlier work.

The remaining gap for `ext:interpolation` is therefore smaller than it looked: the
pieces to connect are the expansion, the per-term vertex bounds, the level splitting
of `meas_lt_of_triple_expansion_bounds`, the exponent exchange, and
`lintegral_rpow_le_of_two_weakNorm`.  The choice of weights `w k1 k2 k3` and the
per-term vertex selection remain to be made.

## 2026-09-14T02:05-0700 — the intended architecture, recovered

Reading the existing sections end to end makes the earlier session's plan for
`ext:interpolation` explicit, and it is a good one:

1. `trilinear_expand_three_finsets` expands `T(∑ f_1^{k}, ∑ f_2^{k}, ∑ f_3^{k})` into
   the finite triple sum over layer multi-indices.
2. `sum_weighted_levels_le` splits a level `t` across that sum in proportion to
   weights summing to one, and `meas_lt_of_triple_expansion_bounds` converts
   per-term level-set bounds into a level-set bound for the whole sum.
3. `meas_lt_le_of_weakNorm_le` turns each of the four vertex weak bounds into a
   level-set bound for each term, and
   `norm_triple_finset_sum_le_geometric_mean` combines the four by weighted
   geometric mean.
4. `dyadicLevel_measure_rpow_exchange` and `prod_dyadicLevel_exchange_eq_one` make
   the pure powers of the dyadic level cancel in that four-fold mean, leaving the
   target-exponent size.
5. `summable_min_two_rpow` — "along each simplex edge the smallest of the four
   vertex bounds is a two-sided geometric minimum, which is summable" — supplies the
   convergence of the multi-index sum.
6. `lintegral_rpow_le_of_two_weakNorm` performs the final weak-to-strong passage,
   using that the target output exponent is straddled (`one_lt_outputExponent_lt`).

The step that was never carried out, and that remains, is the choice of the weights
`w k1 k2 k3` in (2) together with the verification that the resulting per-term bound
really has the two-sided geometric form (5) demands.  That is where this session's
`exists_gap_of_affineIndependent` belongs: it is exactly the statement that along
every direction in the multi-index lattice some vertex gives strictly positive decay,
which is what makes the minimum two-sided.

Note that step (5) cannot be replaced by summing the geometric means of the four
*norm* bounds: that product is the target-exponent size, whose sum over the layers
is not controlled by the target norm.  The weak norms and the level splitting are
essential, which is consistent with the design above.

## 2026-09-14T02:40-0700 — the decay bridge: the gap becomes geometric decay

`exchange_exponent_eq_neg_gapPairing` identifies the exchange exponent with the gap
pairing: after `dyadicLevel_measure_rpow_exchange` the `a`-th vertex bound carries
the pure level factor `2` to the power `∑_j (β_j w_j)(1 - v_{a,j}/β_j)`, and that
exponent is exactly `-⟨w, v_a - β⟩`, where `w` is the multi-index rescaled by the
target reciprocals.

`exists_vertex_geometric_decay` then converts the interior gap into geometric decay:
for every `w` some vertex has `⟨w, v_a - β⟩ ≥ δ‖w‖`, hence carries a level factor at
most `2^{-δ‖w‖}`.  That is precisely the two-sided geometric minimum
`summable_min_two_rpow` is stated for, now in the three-dimensional form the
multi-index sum needs.

So the hinge the earlier session left open is supplied.  What remains to assemble:
the lattice summability over `Fin 3 → ℤ` of `2^{-δ‖k‖}` (a product of three
one-dimensional geometric sums, via `Summable.mul_of_nonneg` and the equivalence
`(Fin 3 → ℤ) ≃ ℤ × ℤ × ℤ`), then the choice of weights in
`sum_weighted_levels_le` proportional to that summable family, and finally the
composition with `meas_lt_of_triple_expansion_bounds` and
`lintegral_rpow_le_of_two_weakNorm`.

## 2026-09-14T03:20-0700 — lattice summability, and a limit of the term-by-term route

Two results are in.

`summable_two_rpow_neg_norm` supplies the lattice summability the previous entry
named: over `Fin 3 → ℤ` the family `2^{-δ‖k‖}` is summable, with `‖·‖` the
supremum norm.  The proof dominates the supremum norm by a third of the sum of
the coordinates, so the family is dominated by a product of three one-dimensional
geometric series; the one-dimensional factor `summable_two_rpow_neg_abs` is the
existing `summable_min_two_rpow` rewritten through the absolute value, and the
product is transported from `ℤ × ℤ × ℤ` along the injection that reads off the
three coordinates.

`weakNorm_le_of_four_weakNorm` combines the four endpoint weak bounds into one at
the interior exponent: if `weakNorm v (r_a) ≤ Γ_a` for each vertex, then
`weakNorm v R ≤ ∏_a Γ_a^{ϑ_a}`.  The combining weights are `ϑ_a R / r_a`, which
sum to one exactly because `R^{-1} = ∑_a ϑ_a r_a^{-1}`; the proof is the
elementary one, splitting `μ{τ < |v|}` as the product of its own `ϑ_a R / r_a`
powers and applying the `a`-th Chebyshev bound to each factor.

That second lemma also settles, negatively, a question the architecture left
open, and the finding is worth stating precisely because it redirects the work.

Fix a layer triple and write `Γ_a` for the `a`-th endpoint bound on it.  The four
hypotheses give `μ{|W| > s} ≤ (Γ_a/s)^{r_a}` for each `a`, and nothing more.  The
best bound on the interior weak norm derivable from those four is
`sup_s s·μ(s)^{1/R}`, and taking logarithms this supremum is a finite linear
program whose dual is: minimise `∑_a κ_a r_a log Γ_a` over probability vectors
`κ` with `∑_a κ_a r_a = R`.  The value `∏_a Γ_a^{ϑ_a}` is attained at
`κ_a = ϑ_a R / r_a`, so the lemma above is sharp, and — this is the point — the
dual optimum can be *exactly* that value even when one vertex bound is very
small.  A concrete configuration: three vertices with `r_a = 1` and one with
`r_a = 2`, and a layer triple whose three equal-`r` endpoint bounds coincide.
There the geometric decay carried by the fourth vertex cancels identically
against the other three in the dual, and the interior bound on that triple shows
no gain at all.

Such configurations form a one-dimensional cone of directions in the multi-index
lattice, so the layer sum over that cone has bounded terms and diverges.  The
consequence is architectural: `ext:interpolation` cannot be proved by bounding
each layer triple's contribution to the interior norm and summing.  The level
splitting has to be chosen as a function of the level `τ` itself — as it is in
the classical two-endpoint argument, where the cut level depends on `τ` — so
that for each `τ` only boundedly many layer triples contribute.  The pieces now
in the file (`meas_lt_of_triple_expansion_bounds`, `sum_weighted_levels_le`,
`lintegral_rpow_le_of_two_weakNorm`) already admit a `τ`-dependent weight family;
what has to be built is the choice of centre.

## 2026-09-14T03:55-0700 — the interior bound on a single expansion term

A survey of the file first, following the rule the error report now carries
twice.  The expansion machinery for `ext:interpolation` is already complete and
already wired to `TrilinearOnSimple`: `dyadicLevelPieceSimple` realizes a level
piece of a simple function as a simple function of finite measure support,
`trilinearOnSimple_sum_levels` expands one slot, `trilinearOnSimple_expand_three`
expands all three into the finite triple sum, and `weakNorm_expansion_term_le`
applies each of the four endpoint hypotheses to a term, in the form

  weakNorm (T (level pieces)) (r a) ≤ A a * ∏_j 2^{k_j+1} m_{j,k_j}^{1/P_{a,j}}

with `m_{j,k}` the measure of the `k`-th band of the `j`-th input.  So the
`dyadicLayer` family is the one that is not wired in; the `dyadicLevel` family
is.

On top of that, `weakNorm_expansion_term_interior_le` now gives each term its
interior bound:

  weakNorm (T (level pieces)) R ≤ (∏_a A_a^{ϑ_a}) * ∏_j 2^{k_j+1} m_{j,k_j}^{1/p_j}.

The proof feeds the four endpoint sizes to `weakNorm_le_of_four_weakNorm` and
then collapses their weighted geometric mean with `aux_prod_endpoint_sizes`:
the four sizes differ only in the exponent of `m_{j,k_j}`, and those exponents
average to `1/p_j` by the definition of the target reciprocal, while the level
factors carry total weight one.  This is the same cancellation
`rpow_four_weighted_mean_eq` performs in `ℝ≥0∞`, done here in the real
normalization the expansion bound produces.

What this does not do — and the previous entry explains why it cannot — is give
the term any decay in the multi-index.  The remaining work is the choice of the
level splitting, which has to depend on the level.

## 2026-09-14T04:30-0700 — band orthogonality: the bands of one input sum against its norm

`sum_measure_dyadicLevelSet_le` and its seminorm form
`sum_measure_dyadicLevelSet_le_eLpNorm` supply the orthogonality any
level-dependent splitting consumes: for a single input `f` and any finite
family `S` of bands,

  ∑_{k ∈ S} (2^k)^q · μ(band k) ≤ ∫ ‖f‖^q = ‖f‖_q^q.

The proof is the disjointness of the bands: on band `k` the integrand `‖f‖^q`
dominates `(2^k)^q`, so each summand is bounded by the band's integral, and the
bands being pairwise disjoint the sum of the band integrals is the integral over
their union (`lintegral_biUnion_finset`), which is at most the whole integral.

This is the missing quantitative input.  The per-term interior bound from the
previous tick controls a single layer triple by the product of the three band
sizes `2^{k_j+1} m_{j,k_j}^{1/p_j}`; this lemma says those band sizes are
`ℓ^{p_j}`-summable in `k_j` with total `‖f_j‖_{p_j}`.  What connects them is
still the level-dependent centring: at level `τ` only the bands with
`∑_j (k_j+1)/p_j` near `log τ` contribute, and the geometric decay from
`exists_vertex_geometric_decay` makes the off-centre bands sum to a convergent
tail.  That assembly is the next tick.

## 2026-09-14T05:05-0700 — triple band orthogonality: layer triples sum against the product of norms

`sum_triple_product_factor` and `sum_triple_dyadicLevelSet_le` lift the
single-input band orthogonality of the previous tick to the three inputs
together.  The first is the elementary factorization of a triple sum of a
separable product into the product of the three one-dimensional sums (over
`ℝ≥0∞`); the second applies it to the band sizes, giving

  ∑_{k1,k2,k3} ∏_j (2^{k_j})^{q_j} μ(band_{j,k_j})
    ≤ ∏_j ∫ ‖f_j‖^{q_j} = ∏_j ‖f_j‖_{q_j}^{q_j}.

Taking `q_j = p_j` this is the total `ℓ^1` mass of the target sizes of the
layer triples: the product of the three input `L^{p_j}` norms.  This is the
budget the level-dependent argument spends — the geometric decay of
`exists_vertex_geometric_decay` weights this convergent family, and the min over
the four vertices per triple picks, in each lattice direction, the vertex whose
size is smallest.  With the budget and the decay both in hand, the remaining
assembly is the arrangement that pays the decay against the budget at each output
level; that is what the next ticks build, on top of `meas_lt_of_triple_expansion_bounds`.

## 2026-09-14T05:40-0700 — the expansion bridge: operator level set → term level sets

`trilinearOnSimple_expand_three_multiIndex` restates the three-slot expansion
with each term written as `T (fun j ↦ dyadicLevelPiece (⇑(f j)) (![k0,k1,k2] j))`,
the exact form the vertex bound `weakNorm_expansion_term_le` and the interior
bound `weakNorm_expansion_term_interior_le` are stated in.  The reindexing
lemma `aux_expansion_tuple_eq` identifies the triple-`Function.update` tuple of
`trilinearOnSimple_expand_three` with the `Fin 3 → ℤ` multi-index tuple, slot by
slot through `update_three_apply` and `coe_dyadicLevelPieceSimple`.

`meas_lt_operator_expansion` then connects the expansion to the level-set
splitting: for any budget family `s k0 k1 k2` whose split levels sum (over the
finite index set of nonzero bands) to the target level `t`, and any per-term
level-set bounds `B`, the operator's level set measure is at most `∑ B`.  It is
`meas_lt_of_triple_expansion_bounds` with `V = T(f)` and the pointwise
reconstruction `V x = ∑ (term x)` supplied by the multi-index expansion.

So the two ends now meet at the term level set: on one side
`meas_lt_operator_expansion` reduces the operator to its terms under a budget;
on the other, `weakNorm_expansion_term_le` bounds each term's level set by the
vertex sizes and `sum_triple_dyadicLevelSet_le` sums those sizes against the
input norms.  The remaining tick chooses the budget `s` — the level split — and
the per-term vertex, spending the geometric decay against the summed sizes.

## 2026-09-14T06:15-0700 — affine independence straddles the target output exponent

`exists_straddling_output_exponents` records a structural consequence of the
hypotheses that the earlier design had not isolated: the four output exponents
`r_a` are never all equal, so the target `R` is *strictly* straddled — some
vertex has `r_a < R` and some has `r_a > R`.

The reason is the relation `r_a^{-1} = ∑_j P_{a,j}^{-1}` that
`ext:interpolation` imposes on each vertex.  If all four `r_a` agreed, the four
input reciprocal vectors would all lie in the plane `{x : x_0+x_1+x_2 = c}` of
`ℝ³`, and four points of a plane are never affinely independent.
`aux_exists_ne_coordSum` makes this precise by reusing
`eq_zero_of_forall_gapPairing_nonpos`: the constant covector `1` would pair to
zero with every vertex offset from the barycentre, forcing `1 = 0`.
`aux_exists_gt_and_lt_of_weighted_mean` then converts "not all equal" into
strict straddling, since `R^{-1}` is the strict convex combination
`∑_a ϑ_a r_a^{-1}`.

This matters because `lintegral_rpow_le_of_two_weakNorm` needs exactly two
exponents straddling `R`, and until now nothing in the file supplied them.

A second finding, recorded so it is not rediscovered.  With the straddling pair
in hand one can bound each expansion term's *strong* norm,
`‖W_k‖_R ≲ Γ_{a₁,k}^{α₁} Γ_{a₂,k}^{α₂}` with `α₁+α₂ = 1`, and then try
`‖T f‖_R ≤ ∑_k ‖W_k‖_R`.  That fails, and quantitatively: the mixed exponent
vector `α₁ v_{a₁} + α₂ v_{a₂}` lies on the edge between the two chosen vertices,
not at the target `β`, so the per-input factor becomes `∑_k 2^k m_k^{w_j}` with
`w_j ≠ β_j`, which the `ℓ^{p_j}` band orthogonality does not control.  Even at
`w = β` it fails: for an input with `M` bands of equal size the triple sum is
`M^{3 - 1/R}`, which diverges since `R > 1`.  So no route that sums a per-term
norm can work — neither the strong norm, nor the interior weak norm of the
previous entries.  The level split has to be made before the norms are taken.

## 2026-09-14T06:50-0700 — restricted weak type at the interior point, with the exact constant

`weakNorm_interior_le_of_indicator_inputs` proves the interior conclusion of
`ext:interpolation` on inputs that are constant multiples of indicators:

  weakNorm (T f) R ≤ (∏_a A_a^{ϑ_a}) · ∏_j ‖f_j‖_{p_j}.

This is the restricted weak type of the interpolated point, and it costs
nothing: on such an input all four endpoint norms of `f_j` are powers of the
single number `μ(E_j)` (`aux_lpNorm_indicator_const`), so their weighted
geometric mean is exactly the target norm — the same collapse
`aux_prod_endpoint_sizes` performs — and `weakNorm_le_of_four_weakNorm`
supplies the combination.  Neither the level decomposition nor the geometric
decay is used.

Two things worth recording.  First, the constant that comes out is exactly the
`∏_a A_a^{ϑ_a}` the theorem asserts, with no slack, which confirms the constant
in the statement is the right one.  Second, the same argument runs at *every*
interior point of the simplex, not just the target: any positive weights
summing to one give the restricted weak bound at the point they define.

So the theorem is proved on multiples of indicators.  What remains is the
passage from restricted weak type on an open set of exponents to the strong
bound at the target — the classical Lorentz-space step.  The obstruction
already recorded stands: on general simple inputs the endpoint norms are no
longer powers of one number, the geometric mean of the endpoint norms exceeds
the target norm by log-convexity, and the layer decomposition that repairs this
cannot be summed term by term.

## 2026-09-14T07:25-0700 — the symmetric pair: a lossless strong bound at every weight vector

`lintegral_rpow_le_of_symmetric_weight_pair` is the step the previous entries
were missing, and it removes the obstruction they recorded.

Combining the four endpoint weak bounds with a weight vector `ψ` gives a weak
bound at the exponent `R_ψ` with `R_ψ^{-1} = ∑_a ψ_a r_a^{-1}`, with constant
the geometric mean `∏_a Γ_a^{ψ_a}`.  Place two weight vectors symmetrically
about `χ`, so `ψ⁺ + ψ⁻ = 2χ`.  Then `R^{-1}` is the average of `R_{ψ⁺}^{-1}` and
`R_{ψ⁻}^{-1}`, so the two exponents straddle `R`, and the two-sided passage
returns the geometric mean at `χ` *exactly*: the two interpolation exponents
come out both equal to `R/2`, and

  (∏ Γ^{ψ⁺})^{R/2} · (∏ Γ^{ψ⁻})^{R/2} = ((∏ Γ^{χ})^2)^{R/2} = (∏ Γ^{χ})^R.

So `‖W‖_R ≤ C · ∏_a Γ_a^{χ_a}` for *every* weight vector `χ` whose exponent is
`R`, with `C` depending only on how far apart the symmetric pair is placed —
not on `χ`.  Nothing is lost in the passage from weak to strong.

Why this unblocks the argument.  The earlier entries kept failing because the
weight vector was fixed at `ϑ`, which makes the per-term bound the target size
with no decay.  Being free to move `χ` per multi-index changes the picture: the
term bound becomes

  (∏_a A_a^{ϑ_a}) · N_k · 2^{⟨e, α⟩ + ⟨Φ e, L(k)⟩},  χ = ϑ + e,

with `α_a = log_2 A_a`, `Φ e = ∑_a e_a v_a`, and `L(k)` the log band measures.
Minimising the linear functional over a small ball `‖e‖ ≤ ε` gives
`-ε‖P α + Φ* L(k)‖`, and since `Φ*` is an isomorphism (affine independence) this
is a genuine geometric decay `2^{-δ‖L(k) - L₀‖}` — centred not at the origin but
at the fixed point `L₀` determined by the constants `A_a`.  So the dependence on
the `A_a`, which the earlier attempts could not keep out of the constant, is
absorbed into a *translation of the decay centre*, and the convergence estimate
for `∑_k N_k 2^{-δ‖L(k) - L₀‖}` is translation invariant.

The remaining pieces are the tilt construction, the identification of the decay,
and the summation, all against the toolkit now in place.

## 2026-09-14T08:00-0700 — correction to the previous entry, and the grouping that replaces it

The previous entry claimed the symmetric-pair lemma removes the obstruction.
That claim was too strong and is withdrawn; the lemma itself stands and is
correct, but it does not by itself close the argument.  The reason is a
constraint I had not accounted for.

The symmetric pair forces `∑_a χ_a r_a^{-1} = R^{-1}`, because `R^{-1}` is the
average of the two exponents' reciprocals.  So the admissible tilts `e = χ - ϑ`
satisfy two linear constraints, `∑_a e_a = 0` and `∑_a e_a r_a^{-1} = 0`, and
form a *two*-dimensional space, not three.  Minimising the tilt functional over
a ball in that space gives decay proportional to the norm of the projection of
`α + Φ* L` onto it, and that projection vanishes on a line in `L`-space.
Working out which line: since `∑_j v_{a,j} = r_a^{-1}`, the degenerate set is
exactly `L ∈ ℝ·(1,1,1)` when the constants `A_a` are equal, and a translate of
it otherwise.  So the diagonal direction — all three bands of equal measure —
carries no gain.

And on that diagonal the term-by-term sum really does diverge.  Take all
`p_j = p` equal and all three inputs equal, with `M` bands, the `k`-th of
measure `2^{-pk}/M`.  Then `‖f_j‖_p = 1`, each band has target size
`2^k m_k^{1/p} = M^{-1/p}`, the diagonal triples `k_1 = k_2 = k_3` have target
size `M^{-1/R}`, and there are `M` of them, so the sum of the term bounds is
`M^{1 - 1/R}`, which diverges since `R > 1`.

The same example says where the loss is.  The `ℓ^R` sum of the same term bounds
is `∑_k (M^{-1/R})^R = 1`, bounded.  So the term bounds are fine; it is
`‖∑_k W_k‖_R ≤ ∑_k ‖W_k‖_R` that is too lossy, and no choice of per-term bound
can repair a triangle inequality.

What replaces it is grouping.  The four vertex hypotheses apply to any simple
function of finite measure support, so they apply to a *sum* of bands just as
well as to a single band, and a product block of bands is handled by one
application rather than by summing its terms.
`trilinearOnSimple_expand_three_general`, added this tick, is the expansion for
an arbitrary finite decomposition of each slot — the freedom the summation
needs.  Choosing the blocks is the remaining work.

## 2026-09-14T08:35-0700 — the truncation estimates in seminorm form, and where the diagonal degeneracy comes from

`eLpNorm_high_le` and `eLpNorm_low_le` restate the truncation bounds for the
`L^Q` seminorm: the part of an input above a level `lam` satisfies

  ‖f·1_{|f|>lam}‖_Q ≤ lam^{1 - p/Q} ‖f‖_p^{p/Q}   for Q ≤ p,

and the part below satisfies the same bound for `Q ≥ p`.  `aux_eLpNorm_indicator_restrict`
identifies the seminorm of an indicator restriction with the restricted integral,
which is what lets the two lintegral bounds of the previous tick be read as
seminorms.  Note the two bounds have the *same* form; which piece a given
exponent controls is decided only by whether `Q` is below or above `p`.

A computation worth recording, because it explains the diagonal degeneracy in a
way the abstract argument did not.  For three equal inputs with `M` bands, the
`k`-th of measure `M^{-1}2^{-kp}`, the `a`-th endpoint size of the diagonal term
`k_1 = k_2 = k_3 = k` is

  Γ_{a,k} = A_a M^{-1/r_a} 2^{3k(1 - R/r_a)}.

So `Γ_{a,k}` decays in `k` for the vertices with `r_a < R` and grows for those
with `r_a > R` — there is decay available at the individual vertices.  But the
weighted geometric mean that the symmetric pair produces has exponent
`∑_a χ_a (1 - R/r_a) = 1 - R ∑_a χ_a r_a^{-1} = 0`, precisely because
`∑_a χ_a r_a^{-1} = R^{-1}` is what makes the pair land on `R`.  The constraint
that gives the strong bound at the right exponent is exactly the constraint that
cancels the decay.  That is the degeneracy, stated without reference to the
geometry.

It also says what a proof must do: keep the vertex exponents `r_a` rather than
collapsing to `R` per term, which means summing level sets and integrating in the
level, not summing norms.  The level-dependent split remains the open step.

## 2026-09-14T09:10-0700 — corpus consistency check, and a scenario audit of the open step

Housekeeping first, since a batch of results had gone in without one.  All eight
section modules and the top-level module `DFR/Auto/Twisted.lean` were rebuilt
against the current `Twisted.olean`: zero errors, zero failures.  The
development remains sorry-free and every new declaration audits to
`propext, Classical.choice, Quot.sound`.

Then an audit of the open step, by asking what the hypotheses actually force in
the witness example rather than what the available inequalities give.  Recall
the diagonal terms have `Γ_{a,k} = A_a M^{-1/r_a} 2^{3k(1 - R/r_a)}` and the
sum of the per-term `L^R` bounds is `M^{1-1/R}`, divergent.  Three concrete
shapes for the terms `W_k` consistent with the hypotheses were checked:

- `W_k` pairwise disjointly supported: `‖∑ W_k‖_R = (∑ ‖W_k‖_R^R)^{1/R}`, which
  is bounded.
- `W_k` all equal to one `W`: then `‖W‖_{r_a,∞} ≤ min_k Γ_{a,k}`, and for the
  vertices with `r_a < R` that minimum is exponentially small in `M`, so `M‖W‖_R`
  is exponentially small.
- `W_k = c_k ψ` for a common profile, and `W_k = c_k 1_{B_k}` for nested balls:
  in both, `c_k` is forced to be a geometric tent in `k`, so `∑_k c_k` is
  comparable to its peak, and the total comes out `M^{-1/R}` — bounded.

In every shape the truth is bounded, which is consistent with the theorem and
localises the loss precisely in the triangle inequality rather than in any
per-term estimate.  It also shows where the missing mechanism lives: the
hypotheses constrain the terms *jointly*, through the fact that one profile has
to satisfy every `Γ_{a,k}` at once, and none of the inequalities currently in the
file express a joint constraint.  A two-piece split by the multi-index does not
recover it either — splitting the diagonal at `k_0` and using the low vertices on
one side and the high vertices on the other gives `2^{Pk_0} + 2^{P(M-k_0)}` with
`P > 0`, worse than the term-by-term bound.

So the open step is not a missing inequality among the ones tried; it needs a
statement that uses the terms themselves and not only their bounds.

## 2026-09-14T09:45-0700 — the tent sums to a bounded multiple of its peak

`exists_tent_sum_bound` is the summation mechanism the previous audit isolated,
in the form that is uniform in where the peak sits: for rates `α, β > 0` there is
a constant `K` such that for *every* real centre `c` and every finite set `S` of
integers,

  ∑_{k ∈ S} min(2^{-α(k-c)}, 2^{β(k-c)}) ≤ K.

The proof is self-contained and avoids any shift-invariance of infinite sums,
which this Mathlib does not expose for `ℤ` in a convenient form.  The index set
is split at the centre; on the right half the first branch is used and the index
`k` is reindexed injectively by `(k - ⌈c⌉).toNat`, on the left half the second
branch and `(⌊c⌋ - k).toNat`.  Because `c ≤ ⌈c⌉` and `⌊c⌋ ≤ c`, each reindexing
only decreases the exponent, so both halves are dominated by the geometric series
`∑_n (2^{-α})^n` and `∑_n (2^{-β})^n`, summed over the image of an injection and
hence bounded by the whole series.

The point of the uniformity in `c` is that the peak of the tent moves with the
data — in the witness example it sits where the endpoint bounds cross, which
depends on the constants `A_a` and on the input — so a bound that degraded as the
peak moved would be useless.  This is the first statement in the file that is
insensitive to that movement.

## 2026-09-14T10:15-0700 — the two-sided geometric minimum sums to the geometric mean

`min_two_geometric_eq_tent` identifies the minimum of a decaying and a growing
geometric family with a centred tent:

  min(C₁ 2^{-αk}, C₂ 2^{βk})
    = (C₁^{β/(α+β)} C₂^{α/(α+β)}) · min(2^{-α(k-c)}, 2^{β(k-c)}),

with the centre `c = log(C₁/C₂)/((α+β) log 2)` — the crossing point of the two
families — and the peak their weighted geometric mean, weighted by the two rates.
Feeding this to `exists_tent_sum_bound` gives
`exists_sum_min_two_geometric_bound`: for rates `α, β > 0` there is a constant
`K` such that for all positive `C₁, C₂` and every finite set of integer indices,

  ∑_k min(C₁ 2^{-αk}, C₂ 2^{βk}) ≤ K · C₁^{β/(α+β)} C₂^{α/(α+β)}.

So the multi-index sum of the two-sided minimum costs only the geometric mean of
the two constants, with a constant depending on the rates alone.  This is the
quantitative form of `summable_min_two_rpow`, which gave convergence but no
bound, and it is the shape the endpoint sizes present along each lattice
direction: one vertex with `r_a < R` makes the size decay, one with `r_a > R`
makes it grow, and `exists_straddling_output_exponents` guarantees both exist.

Note this avoids `Real.logb`, which the corpus does not import; the centre is
written through `Real.log` directly.

## 2026-09-14T10:50-0700 — a tent weight family on the multi-index lattice

`exists_lattice_tent_sum_bound` lifts the tent bound to the three-dimensional
lattice: for a rate `η > 0` there is a constant `K` such that for every centre
`c` and all finite index sets,

  ∑_{k1,k2,k3} 2^{-η|k1-c₀|} 2^{-η|k2-c₁|} 2^{-η|k3-c₂|} ≤ K,

uniformly in `c`.  The summand factors, so the triple sum factors
(`sum_triple_product_factor_real`) into three one-dimensional tent sums, each
bounded by `exists_sum_abs_tent_bound`, which is the previous tick's bound read
through the absolute value using the file's own `aux_min_two_rpow_eq_abs`.

Why this is the right share.  The level assigned to a layer triple by
`meas_lt_of_triple_expansion_bounds` must be a share of the output level with the
shares summing to at most one, and the choice of share is where the earlier
attempts lost.  A uniform share `1/M` over `M` active triples costs `M^R` in the
level-set bound, which is why the diagonal came out as `M^{R-1}`.  A tent share
costs nothing of the sort: because the tent is normalisable over the *whole*
lattice, every triple near the centre gets a share bounded below by a constant,
and the number of active triples never enters.  The uniformity in the centre is
what lets the centre track the peak of the endpoint sizes, which moves with the
constants `A_a` and with the input.

With this the level-splitting estimate can be assembled at the interior exponent.
What it yields is a weak bound at `R`, not a strong one, and the earlier
computation shows why: the two-sided structure that makes the sum converge is
exactly what forces the exponent to be `R` on the nose.  Bridging that last gap
remains open.

## 2026-09-14T11:20-0700 — the normalized tent, and the level budget it respects

`exists_normalized_lattice_tent` rescales the lattice tent by the reciprocal of
its uniform bound: for a rate `η > 0` there is a constant `C > 0` such that at
every centre, the family

  w(k1,k2,k3) = C · 2^{-η|k1-c₀|} · 2^{-η|k2-c₁|} · 2^{-η|k3-c₂|}

sums to at most one over any finite index sets.  `sum_tent_levels_le` then feeds
this to `sum_weighted_levels_le`: the shares `t · w(k1,k2,k3)` of an output level
`t` sum to at most `t`, which is exactly the budget hypothesis that
`meas_lt_of_triple_expansion_bounds` and `meas_lt_operator_expansion` consume.

So the level split is now available as a drop-in: the level assigned to a layer
triple may be taken proportional to a tent at any centre, with the constant
depending only on the rate.  Every ingredient of the level-set estimate at the
interior exponent is in place — the expansion (`meas_lt_operator_expansion`), the
per-term vertex bounds (`weakNorm_expansion_term_le`), the Chebyshev conversion
(`meas_lt_le_of_weakNorm_le`), the budget (this tick), and the summation
(`exists_sum_min_two_geometric_bound`).

The gap that remains is the one identified two ticks ago and is not a missing
ingredient: the two-sided structure that makes the multi-index sum converge fixes
the output exponent at `R` exactly, so what the assembly yields is weak type at
`R`, and the strong bound needs something further.

## 2026-09-14T11:50-0700 — bands aggregate in ℓ^q, which is the joint constraint

`lintegral_rpow_enorm_sum_dyadicLevelPiece` records the fact the scenario audit
said was missing from the file: because the bands of an input are disjointly
supported, the `L^q` norm of a *group* of bands is the `ℓ^q` aggregate of the
individual band norms,

  ∫ ‖∑_{k ∈ E} band_k‖^q = ∑_{k ∈ E} ∫ ‖band_k‖^q,

not their sum.  `aux_rpow_enorm_sum_dyadicLevelPiece` is the pointwise statement:
at each point at most one band is active, by `dyadicLevelSet_disjoint`, so the
`q`-th power of the sum is the sum of the `q`-th powers with no cross terms.

This is the joint constraint the four endpoint hypotheses place on a grouping.
Applying a vertex bound to a group of bands is strictly stronger than applying it
to each band and adding, and the gap between the `ℓ^q` aggregate and the `ℓ^1`
sum is exactly the slack the term-by-term route discards — in the witness example
that gap is the factor `M^{1-1/R}`.

With this the file now holds both halves of the tension: the one-group bound,
whose cost is the geometric mean `∏_a ‖f_j‖_{P_{a,j}}^{ϑ_a}` and which exceeds
the target norm by log-convexity when the input is spread across scales; and the
all-bands bound, whose cost is an `ℓ^1` sum that diverges.  A correct proof
interpolates between them by grouping adaptively.  The adaptive grouping is the
one thing still missing, and it is the research content of the theorem.

## 2026-09-14T12:20-0700 — a correction, and the ceiling of the level-split route

`weakNorm_le_of_meas_lt_le` supplies the converse of
`meas_lt_le_of_weakNorm_le`: a level-set bound decaying like `D τ^{-R}` is a weak
bound with constant `D^{1/R}`.  That is the packaging the level-splitting
estimate needs, since it produces a level-set bound and the downstream steps are
stated for the weak norm.

A correction to an earlier entry.  The entry of 2026-09-14T09:10 reported that
splitting the level uniformly over `M` active triples costs `M^{R-1}`, and left
the impression that the level-split route is lossy.  That was an artefact of the
uniform share.  Redoing the witness example with the *tent* share now in the file:
the `a`-th term is
`(A_a/(τC))^{r_a} M^{-1} 2^{3(r_a-R)k + η r_a |k - k_0|}`, which decays away from
`k_0` on both sides once `η` is below `3|R - r_a|/r_a`, so the sum over `k` is
comparable to its value at `k_0`; choosing `k_0` at the balance point of the two
straddling vertices gives

  μ{τ < |T f|} ≤ C M^{-1} A_1^{r_1 θ} A_2^{r_2 (1-θ)} τ^{-R},

with no power of `M` left over.  So the level-split with a tent share gives the
right weak bound at `R`, and the earlier `M^{R-1}` was the cost of the wrong
share, not of the route.

What that same computation also shows is the ceiling.  The balance that removes
the `M` is exactly what pins the exponent: off balance the bound is a sum
`D₁(k_0) τ^{-r_1} + D₂(k_0) τ^{-r_2}`, and minimising over `k_0` returns
`A^* τ^{-R}`.  Integrating `τ^{R-1}·τ^{-R}` diverges logarithmically at both ends,
so weak type at `R` is the natural output of this route and the strong bound needs
a further step.  Interpolating between two nearby interior points does not supply
it: the constants there carry `∏_j ‖f_j‖_{p'_j}`, and log-convexity of
`q ↦ ‖f_j‖_q` bounds the target norm *below* the geometric mean of those, which is
the wrong direction.

## 2026-09-14T12:50-0700 — the weak norm is a quasi-norm

`weakNorm_add_le` proves the triangle inequality with a factor two:

  weakNorm (u + v) r ≤ 2 (weakNorm u r + weakNorm v r)   for r ≥ 1.

A point where the sum exceeds a level `σ` is a point where one summand exceeds
`σ/2`, so the level set of the sum at `σ` is covered by the two level sets of the
summands at `σ/2`; the measures add, and the `1/r`-th power is subadditive
because `r ≥ 1`.

The file did not have this, and any aggregation of the layer pieces in the weak
norms has to start from it — in particular the `K`-functional of the couple
`(L^{r₁,∞}, L^{r₂,∞})`, which is the first object the real interpolation route
recorded in ErrorReport.md needs.  Note the factor two is not removable: the weak
norm is genuinely only a quasi-norm, which is one of the reasons that route
cannot be run with the naive subadditive estimates.

## 2026-09-14T13:20-0700 — the K-functional of the weak couple

`weakK μ r₁ r₂ t v` is the `K`-functional of the couple formed by the two weak
spaces, the infimum over decompositions `v = (v - w) + w` of
`weakNorm (v-w) r₁ + t · weakNorm w r₂`.  `weakK_le_left` and `weakK_le_right`
are the two trivial decompositions, and `weakK_le_weakJ` combines them: at any
scale `s`, the `K`-functional at scale `t` is at most the `J`-functional
`max(weakNorm v r₁, s · weakNorm v r₂)` at scale `s`, and also at most `t/s`
times it.  That pair of bounds is the input to the `J`-method estimate the
ErrorReport entry describes.

A near miss worth recording, and the same one as before.  I wrote a
`weakNorm_zero` as a helper and found the file already had it, at line 92402,
stated for `fun _ : X ↦ (0 : ℝ)` rather than `(0 : X → ℝ)` — which is why a
search for the latter spelling missed it.  The duplicate was removed before
promotion and the existing lemma used, bridged by a `have` at the `(0 : X → ℝ)`
spelling since the two are definitionally but not syntactically equal.

## 2026-09-14T13:50-0700 — the K-functional on a sum, and a longer prerequisite chain

`weakK_add_le` estimates the `K`-functional of a sum by testing it against the
sum of any two chosen decompositions, carrying the factor two of
`weakNorm_add_le` in each slot.  This is the honest two-term form: the infimum
form `weakK (v₁+v₂) ≤ 2 (weakK v₁ + weakK v₂)` needs an approximation argument on
the two infima, and the two-term form is what applications use anyway, since the
caller supplies the decompositions.

Working on this turned up a further link in the prerequisite chain, now recorded
in ErrorReport.md.  The `J`-method estimate is applied to a decomposition with
infinitely many pieces and needs `K` to be genuinely subadditive; a factor two
per addition compounds to `2^n`.  The classical repair is that `L^{r,∞}` is
normable for `r > 1`, via `sup_E μ(E)^{1/r-1} ∫_E |f|`, which is equivalent to
the weak quasi-norm with constant the conjugate exponent.  So the chain is
normability, then subadditivity of `K`, then the `J`-method, then the
identification of the interpolation space — four known theorems, none of them in
Mathlib.

## 2026-09-14T14:20-0700 — the candidate norm on weak L^r

`weakNormPrime μ r v` is the classical candidate norm on the weak space: the
supremum, over measurable sets of finite positive measure, of
`μ(E)^{1/r - 1} ∫_E |v|`.  Being a supremum of quantities each of which is
subadditive in `v`, it is a genuine norm, which is what the `K`-functional needs
and what the weak quasi-norm does not supply.

`le_weakNormPrime` is the defining bound, and
`ofReal_mul_rpow_le_weakNormPrime` is the elementary half of the equivalence: if
`E` has finite positive measure and sits inside the level set `{τ < |v|}`, then
`|v| ≥ τ` on `E`, so the normalized average is at least `τ μ(E)^{1/r}` — the
summand of the weak norm at level `τ` computed on `E`.  Both hypotheses `0 < r`
and `0 < τ` turned out to be unnecessary and were dropped.

What remains for the equivalence is the other half, `weakNormPrime ≤ r' · weakNorm`,
which is the layer-cake estimate
`∫_E |v| ≤ ∫_0^∞ min(μ(E), (A/τ)^r) dτ = r' A μ(E)^{1-1/r}`, split at
`τ₀ = A μ(E)^{-1/r}`; and the passage from the level-set summand to the weak norm
itself, which needs an exhaustion of `{τ < |v|}` by sets of finite measure.  The
file already has the two power integrals `lintegral_Ioc_zero_rpow` and
`lintegral_Ioi_rpow` that the split consumes.

## 2026-09-14T14:50-0700 — the layer cake on a set

`lintegral_enorm_restrict_eq_meas_lt` writes the integral of `|v|` over a set as
the integral over levels of the measures of the level sets met with that set:

  ∫_E ‖v‖ₑ = ∫_{t > 0} μ({t < |v|} ∩ E).

It is Mathlib's `lintegral_eq_lintegral_meas_lt` applied to the restricted
measure, with `Measure.restrict_apply` turning the restricted measure of a level
set into the measure of its intersection with `E`.  Measurability of `E` turned
out not to be needed — only the level set has to be measurable — so the
hypothesis was dropped.

This is the first step of the normability estimate.  What follows is bounding
`μ({t < |v|} ∩ E)` in the two available ways, by `μ(E)` and by the weak norm's
`A^r t^{-r}`, and splitting the level integral where the two agree, at
`t₀ = A μ(E)^{-1/r}`; the two pieces are the power integrals
`lintegral_Ioc_zero_rpow` and `lintegral_Ioi_rpow` already in the file, and they
sum to `r' A μ(E)^{1-1/r}`.

## 2026-09-14T15:20-0700 — splitting the level integral

`lintegral_Ioi_le_of_two_bounds` is the split the normability estimate performs:
if a level function `g` is bounded both by a constant `m` and by
`A^r t^{-r}`, then for any splitting level `t₀ > 0`

  ∫_{t > 0} g ≤ m · t₀ + A^r · (-t₀^{1-r} / (1-r)),

the first piece from the constant bound over `Ioc 0 t₀` and the second from the
power bound over `Ioi t₀`, using `lintegral_Ioi_rpow` at exponent `-r < -1`.  The
splitting level is left free so the caller can put it where the two bounds meet.

Composed with `lintegral_enorm_restrict_eq_meas_lt` and the Chebyshev bound
`meas_lt_le_of_weakNorm_le`, this gives `∫_E |v| ≤ μ(E) t₀ + A^r t₀^{1-r}/(r-1)`
for every `t₀`, and at `t₀ = A μ(E)^{-1/r}` the right side is
`r' A μ(E)^{1-1/r}` — the half of the normability equivalence that was named as
remaining two ticks ago.  What is left is the optimisation at that `t₀`, which is
arithmetic in `ℝ≥0∞` with the measure's `toReal`, and then the other direction,
which needs an exhaustion of the level set by sets of finite measure.

## 2026-09-14T15:50-0700 — the integral over a set, from the weak norm

`lintegral_enorm_restrict_le_of_weakNorm` composes the two previous ticks: the
layer cake on a set turns `∫_E |v|` into the level integral of
`μ({t < |v|} ∩ E)`, that measure is bounded by `μ(E)` through one side of the
intersection and by the weak norm's `A^r t^{-r}` through the other, and the split
of the level integral then gives, for every `t₀ > 0`,

  ∫_E ‖v‖ₑ ≤ μ(E) · t₀ + A^r · (-t₀^{1-r} / (1-r)).

Both bounds on the intersection are one-liners — `measure_mono` on the two sides
of `inter_subset` — and the weak side is exactly `meas_lt_le_of_weakNorm_le`,
which is stated in precisely the `A^r τ^{-r}` shape the split consumes.

What remains for this half of the normability equivalence is putting `t₀` at the
crossing, `t₀ = A μ(E)^{-1/r}`, where the two terms become equal and their sum is
`r' A μ(E)^{1-1/r}`.  That step is arithmetic rather than measure theory, but it
has to be done with the measure as an `ℝ≥0∞`, so it needs the finiteness of
`μ(E)` that `weakNormPrime` already carries in its index type.

## 2026-09-14T16:20-0700 — the normalized average, from the weak norm

`lintegral_enorm_restrict_le_conj` puts the splitting level at the crossing,
`t₀ = A μ(E)^{-1/r}`, and gets

  ∫_E ‖v‖ₑ ≤ (r / (r-1)) · A · μ(E)^{1 - 1/r}

for every set of finite positive measure, whenever `weakNorm v r ≤ A` and
`r > 1`.  The constant is the conjugate exponent, as it should be: at that level
the two terms of the split are equal, each `A μ(E)^{1-1/r}` and
`A μ(E)^{1-1/r}/(r-1)`, and they sum to `r/(r-1)` times the first.

Multiplying by `μ(E)^{1/r - 1}` this says the normalized averages that
`weakNormPrime` takes the supremum of are all at most `r' · weakNorm v r`.  That
is one half of the normability equivalence; with
`ofReal_mul_rpow_le_weakNormPrime` giving the other half on subsets of level
sets, what is left is only the passage from those subsets to the level set
itself, which needs an exhaustion by sets of finite measure.

## 2026-09-14T16:50-0700 — one half of the normability equivalence

`weakNormPrime_le_conj_mul_weakNorm` takes the supremum of the previous tick's
estimate over sets of finite positive measure:

  weakNormPrime v ≤ (r / (r-1)) · weakNorm v r,  for r > 1.

Each normalized average is `μ(E)^{1/r-1} ∫_E |v|`, the integral is at most
`r' A μ(E)^{1-1/r}` by `lintegral_enorm_restrict_le_conj`, and the two powers of
`μ(E)` cancel exactly, leaving `r' A` with no dependence on the set — which is
what makes the supremum finite.

This is the direction that says the candidate norm is not larger than the weak
quasi-norm up to the conjugate constant.  The other direction — that it is not
smaller — is `ofReal_mul_rpow_le_weakNormPrime` on subsets of level sets, and
needs only the passage from such subsets to the level set itself, by exhaustion.
With both, weak `L^r` is normable for `r > 1`, which is the first link of the
four-link chain the ErrorReport entry lists.

## 2026-09-14T17:20-0700 — weak L^r is normable for r > 1

`weakNorm_le_weakNormPrime` supplies the direction that was missing: on a
σ-finite measure,

  weakNorm v r ≤ weakNormPrime v.

The approximation is Mathlib's `Measure.exists_subset_measure_lt_top`: every
`c` strictly below the measure of a level set is strictly below the measure of
some measurable subset of finite measure, and on such a subset
`ofReal_mul_rpow_le_weakNormPrime` already gives the bound.  Density of the order
on `ℝ≥0∞` then upgrades "every `c` below" to the level set itself, after
rearranging the target into `μ(level) ≤ (K / τ)^r` so that the approximation can
be applied to a measure rather than to a product.

With the previous tick this closes the first link of the chain:

  weakNorm v r ≤ weakNormPrime v ≤ (r/(r-1)) · weakNorm v r,   r > 1,

so weak `L^r` is normable, and `weakNormPrime` — a supremum of quantities each
subadditive in `v` — is the genuine norm the `K`-functional needs.  Three links
remain: subadditivity of `K` in that norm, the `J`-method estimate, and the
identification of the interpolation space.

## 2026-09-14T17:50-0700 — the candidate norm is subadditive

`weakNormPrime_add_le` proves what the whole detour was for:

  weakNormPrime (u + v) ≤ weakNormPrime u + weakNormPrime v,

with no constant.  Each normalized average is subadditive, because the integral
of `‖u + v‖ₑ` over a set is at most the sum of the two integrals, and a supremum
of subadditive quantities is subadditive.  Measurability of only the first
summand is needed, since `lintegral_add_left` asks for it on one side; the
hypothesis on the second was dropped.

So the first link of the chain is complete and has the shape it needs:
`weakNormPrime` is equivalent to the weak norm for `r > 1`
(`weakNorm_le_weakNormPrime`, `weakNormPrime_le_conj_mul_weakNorm`) and is a
genuine norm.  A `K`-functional built from `weakNormPrime` at the two straddling
exponents is therefore subadditive without the factor two that
`weakNorm_add_le` carries, and the compounding `2^n` over infinitely many pieces
that the ErrorReport entry identified does not arise.

## 2026-09-14T18:20-0700 — the K-functional on the genuine norm

`primeK` is the `K`-functional of the couple of *candidate* norms, and
`primeK_add_le` is the estimate on a sum with **no constant**:

  primeK (v₁ + v₂) ≤ (‖v₁-w₁‖' + t‖w₁‖') + (‖v₂-w₂‖' + t‖w₂‖'),

for any chosen decompositions.  Compare `weakK_add_le`, which carries a factor
two in each slot because the weak quasi-norm does; that factor was the reason an
aggregation over infinitely many pieces was impossible, and it is now gone.
`primeK_le_left` and `primeK_le_right` are the two trivial decompositions, using
`weakNormPrime_zero`.

Only the first summand of each slot needs measurability, inherited from
`weakNormPrime_add_le`.

The chain now stands at: link one complete (normability, both directions and
subadditivity); link two complete (subadditivity of `K`, in the form
applications use).  Remaining: the `J`-method estimate, which aggregates the
pieces in `ℓ^s` against `2^{-νθ} J(2^ν, v_ν)`, and the identification of the
interpolation space of the couple with `L^R`.

## 2026-09-14T18:50-0700 — aggregating finitely many pieces

`weakNormPrime_sum_le` lifts subadditivity to a finite family by induction, with
no constant, and `primeK_sum_le` lifts it to the `K`-functional:

  primeK (∑_{i ∈ S} v i) ≤ ∑_{i ∈ S} (‖v i - w i‖' + t ‖w i‖'),

for any family of decompositions `w`.  The proof tests the infimum at
`∑_{i ∈ S} w i`, splits the difference with `Finset.sum_sub_distrib`, and applies
the finite subadditivity in each slot.

This is the shape the `J`-method estimate consumes, and it is the first point in
the whole development where finitely many pieces can be aggregated without a
constant per piece.  Under the weak quasi-norm the same statement would carry
`2^{|S|}`.

Remaining on the chain: the `J`-method estimate proper, which chooses the
decompositions so that each summand becomes `min(1, t/2^ν) J(2^ν, v_ν)` and then
sums the level parameter in `ℓ^s` by Hardy's inequality; and the identification
of the interpolation space with `L^R`.

## 2026-09-14T19:20-0700 — the J-functional bound on a finite sum

`primeJ` is the `J`-functional of the couple of candidate norms, and
`primeK_sum_le_primeJ` is the estimate the method turns on:

  primeK t (∑_{i ∈ S} v i) ≤ ∑_{i ∈ S} min( J(σ i, v i), (t / σ i) · J(σ i, v i) ).

The decompositions are chosen piece by piece and are the two trivial ones: for a
piece whose own scale `σ i` is below the level `t`, keep it in the first space
(`w i = 0`); for a piece whose scale is above, move it entirely to the second
(`w i = v i`).  In the first case the summand is `‖v i‖'_{r₁}`, which is below
`J`, and `t/σ i ≥ 1` makes the second entry of the minimum the larger; in the
second case the summand is `t ‖v i‖'_{r₂}`, which is `(t/σ i)` times
`σ i ‖v i‖'_{r₂}` and so below `(t/σ i) J`, while `t ≤ σ i` puts it below `J` as
well.  Both cases close by `le_min`.

This is the `J`-method estimate for a finite family.  What is left of the third
link is the passage to infinitely many pieces and the integration of the level
parameter, where the `ℓ^s` aggregation appears through Hardy's inequality; then
the fourth link, the identification of the interpolation space with `L^R`.

## 2026-09-14T19:50-0700 — the profile integral of the J-method

`lintegral_min_one_rpow_div` evaluates the level integral the `J`-method weights
each piece by, after the piece's own scale has been scaled out:

  ∫_{u > 0} (u^{-θ} min(1,u))^s du/u = 1/(s(1-θ)) + 1/(θ s).

The split is at `u = 1`, where the minimum changes branch.  Below it the
integrand is `u^{s(1-θ)-1}`, integrable at the origin exactly because `θ < 1`;
above it the integrand is `u^{-θ s - 1}`, integrable at infinity exactly because
`θ > 0`.  The two pieces are `lintegral_Ioc_zero_rpow` and `lintegral_Ioi_rpow`,
already in the file, and their values are the two terms.

Both conditions are the interior position of the target exponent: `θ` is the
interpolation parameter, and `0 < θ < 1` says the target lies strictly between
the two endpoints.  This is the same fact as
`exists_straddling_output_exponents`, arriving now as the convergence of an
integral rather than as a statement about the simplex.

## 2026-09-14T20:20-0700 — the discrete profile, and a change of route

`exists_discrete_profile_bound` bounds the `J`-method profile taken along the
powers of two:

  ∑_{k ∈ S} (2^{-θk} min(1, 2^k))^s ≤ K(θ, s),  uniformly over finite S,

for `0 < θ < 1` and `s > 0`.  `aux_discrete_profile_eq_min` identifies the
summand with `min(2^{-θsk}, 2^{(1-θ)sk})`, a two-sided geometric minimum with
rates `θs` and `(1-θ)s`, both positive precisely because the target lies
strictly between the endpoints; `exists_tent_sum_bound` at centre zero then
supplies the bound.

This is a deliberate change of route.  The continuous form needs the level
integral against `dt/t` and a change of variables for that multiplicative
measure, which Mathlib supports only through the scaling behaviour of Lebesgue
measure and would have to be assembled by hand on `Ioi 0`.  Taking the level
along `2^n` instead makes the profile a sum, and the sum is exactly the object
`exists_tent_sum_bound` was built for two ticks into this chain — so the whole
interpolation argument can stay discrete, reusing the tent machinery rather than
duplicating it in integral form.

`lintegral_min_one_rpow_div` from the previous tick remains the continuous
statement of the same fact and is kept; it records the two integrability
conditions in the form the literature states them.

## 2026-09-14T20:50-0700 — Minkowski over a finite family

`Lp_finset_sum_le` iterates Mathlib's two-summand Minkowski inequality
(`ENNReal.Lp_add_le`) to a finite family:

  (∑_i (∑_{k ∈ T} F k i)^p)^{1/p} ≤ ∑_{k ∈ T} (∑_i (F k i)^p)^{1/p},  p ≥ 1.

The induction is on `T`; the empty case is `0^p = 0` twice, and the step splits
the inner sum and applies the two-summand form followed by the hypothesis.

This is the last generic tool the `J`-method convolution estimate needs.  That
estimate bounds the level profile of a sum by a convolution of the profile
sequence with the sequence of `J`-values, and `Lp_finset_sum_le` is what turns a
convolution bound into an `ℓ^s` bound: each shift of the profile contributes its
own `ℓ^s` norm, and the shifts are weighted by a sequence whose `ℓ^1` norm is the
constant `exists_discrete_profile_bound` supplies.  That is the `ℓ¹ ∗ ℓ^s ⊆ ℓ^s`
step the ErrorReport entry named.

## 2026-09-14T21:20-0700 — Young's inequality for sequences

`Lp_convolution_le` is the `ℓ¹ ∗ ℓ^s ⊆ ℓ^s` estimate the ErrorReport entry named
as the mechanism that turns the divergent `ℓ¹` sum of the layer bounds into a
convergent `ℓ^s` one:

  (∑_{n ∈ S} (∑_{k ∈ K} a k · b (n-k))^s)^{1/s} ≤ A · B,

whenever every finite sum of `a` is at most `A` and every finite `ℓ^s` norm of
`b` is at most `B`, for `s ≥ 1`.

The proof applies `Lp_finset_sum_le` over the *shift* index `k`, which leaves
`(∑_n (a k · b(n-k))^s)^{1/s} = a k · (∑_n b(n-k)^s)^{1/s}` in each term; the
inner sum is the `ℓ^s` norm of `b` over a translate of `S`, bounded by `B`
uniformly because `hB` is stated for every finite set and translation is an
injection; and the `a k` then sum to `A`.

Summing over the shift is the whole point.  Applying Minkowski over the *piece*
index instead would leave `∑_i b i`, an `ℓ¹` sum — exactly the divergent
quantity the witness example produces.  Summing over the shift keeps `b` in
`ℓ^s` and spends only the `ℓ¹` norm of the profile, which
`exists_discrete_profile_bound` bounds by a constant depending on the exponents
alone.

## 2026-09-14T21:50-0700 — the profile term is a convolution term

`aux_profile_term_eq` is the identity that makes the level profile of a sum a
convolution.  Writing the level as `2^n` and a piece's scale as `2^i`, the
`J`-method term weighted by `2^{-θn}` factors as

  2^{-θn} · min(J, (2^n/2^i) J)
    = [2^{-θ(n-i)} min(1, 2^{n-i})] · [2^{-θi} J],

a factor depending only on the difference of the indices times a factor
depending only on the piece.  `aux_min_mul_right` supplies the elementary step
`min J (c J) = (min 1 c) J`, and the rest is the additivity of the exponent.

With this the pieces fit together: `primeK_sum_le_primeJ` bounds the
`K`-functional of a sum by the sum of the `J`-method terms,
`aux_profile_term_eq` turns each into a convolution term with profile
`a k = 2^{-θk} min(1, 2^k)` and data `b i = 2^{-θi} J_i`,
`exists_discrete_profile_bound` bounds the `ℓ¹` norm of the profile by a
constant of the exponents alone, and `Lp_convolution_le` converts that into the
`ℓ^s` bound.  The remaining work on this link is the bookkeeping that composes
them.

## 2026-09-14T22:20-0700 — the weighted level profile of a sum

`aux_profile_level_le` combines the two previous results: the `J`-method bound
on the `K`-functional of a sum, and the convolution identity for a single term.
The weighted level profile of a sum is then a sum of convolution terms,

  2^{-θn} · primeK(2^n, ∑_{i ∈ T} v i)
    ≤ ∑_{i ∈ T} [2^{-θ(n-i)} min(1, 2^{n-i})] · [2^{-θi} J(2^i, v i)],

one for each piece, with the first bracket depending only on the difference of
the indices.  The proof is `primeK_sum_le_primeJ` at `t = 2^n` and scales
`σ i = 2^i`, distributed over the sum by `Finset.mul_sum`, then
`aux_profile_term_eq` on each term.

What remains to close this link is the reindexing that turns the sum over pieces
into a sum over shifts, so that `Lp_convolution_le` applies: for each level `n`
the map `i ↦ n - i` is injective, and taking the shift index in the fixed finite
set of all differences `n - i` bounds the reindexed sum uniformly in `n`.

## 2026-09-14T22:50-0700 — from a sum over pieces to a sum over shifts

`sum_shift_le_of_subset` is the reindexing the convolution estimate needs: at a
fixed level `n` the map `i ↦ n - i` is injective, so a sum over pieces is a sum
over the shifts it produces, and enlarging the shift index set to any finite set
containing them only increases the sum.

`aux_profile_level_conv_le` applies it to the weighted level profile, giving

  2^{-θn} · primeK(2^n, ∑_{i ∈ T} v i)
    ≤ ∑_{k ∈ K} a k · b (n - k),

with `a k = 2^{-θk} min(1, 2^k)` the profile and
`b i = 2^{-θi} J(2^i, v i)` the data, for any fixed `K` containing every
difference `n - i`.  The only friction was the cast `((n - k : ℤ) : ℝ)`, which
has to be pushed to `(n:ℝ) - (k:ℝ)` on both sides of the reindexing.

This is the shape `Lp_convolution_le` consumes, and with it the third link needs
only the choice of a single `K` serving every level in a given finite set of
levels — the image of `S ×ˢ T` under subtraction — and then one application of
the convolution estimate.

## 2026-09-14T23:20-0700 — the J-method estimate, and the third link closed

`primeJ_method` is the third link of the chain:

  (∑_{n ∈ S} (2^{-θn} primeK(2^n, ∑_{i ∈ T} v i))^s)^{1/s} ≤ A · B,

whenever every finite sum of the profile `2^{-θk} min(1, 2^k)` is at most `A`
and every finite `ℓ^s` norm of the data `2^{-θi} J(2^i, v i)` is at most `B`,
for `s ≥ 1`.

The assembly is: `aux_profile_level_conv_le` at each level, with the shift index
set taken once and for all as the image of `S ×ˢ T` under subtraction so that it
serves every level in `S`; monotonicity of the `s`-th power and of the sum; and
one application of `Lp_convolution_le`.  The only care needed is the cast
`((n - k : ℤ) : ℝ)`, which has to be beta-reduced before it can be rewritten.

So the chain now stands: link one (normability of weak `L^r`) complete, link two
(subadditivity of the `K`-functional in the genuine norm) complete, link three
(the `J`-method estimate) complete.  What remains is link four, the
identification of the interpolation quantity with the `L^R` norm — the step that
says the `ℓ^s` aggregation of the level profile really is the strong norm, and
the only one of the four that is specific to the couple rather than formal.

## 2026-09-14T23:50-0700 — a lower bound for the K-functional

`le_weakK` is the first piece of the fourth link — the `K`-functional bounded
from below by the data it is meant to control:

  λ · min( (μ{2λ < |v|}/2)^{1/r₁}, t (μ{2λ < |v|}/2)^{1/r₂} ) ≤ weakK t v.

The argument is a covering: a point where `|v|` exceeds `2λ` is a point where one
of the two parts of any decomposition exceeds `λ`, so the level set at `2λ` is
covered by the two level sets at `λ`, and whichever part carries at least half of
it pays for that half in its own weak norm through `le_weakNorm`.  The minimum
records which part paid, and taking the infimum over decompositions gives the
`K`-functional.

Two points of technique.  The "at least half" step avoids strict inequalities in
`ℝ≥0∞`, which are awkward at infinity: instead of arguing that both parts cannot
be below half, it takes the larger of the two, bounds `m` by twice it, and
divides.  And the statement is for `weakK` rather than `primeK` precisely because
no measurability is needed — the infimum ranges over all functions, `le_weakNorm`
holds for all of them, and the covering is outer-measure subadditivity.

What remains of this link is the balance: choosing the level `t` for each `λ` so
that the two entries of the minimum agree, which is where the exponent identity
`1/R = (1-θ)/r₁ + θ/r₂` enters and turns the bound into the weak-`R` quantity
`λ μ{2λ<|v|}^{1/R}`.

## 2026-09-15T00:20-0700 — balancing the minimum

`aux_balance_exponent` is the arithmetic heart of the balance:

  (u^{1/r₁ - 1/r₂})^{-θ} · u^{1/r₁} = u^{1/R},   when 1/R = (1-θ)/r₁ + θ/r₂,

and `weakR_le_weighted_weakK` uses it.  At the level `t = u^{1/r₁ - 1/r₂}` the
two entries of the minimum in `le_weakK` agree, so the minimum is either of them,
and weighting by `t^{-θ}` converts `λ u^{1/r₁}` into `λ u^{1/R}`:

  λ u^{1/R} ≤ t^{-θ} · weakK t v,   where u is the half-level-set measure.

So the weighted `K`-functional at the balanced level dominates the weak-`R`
quantity at that level.  This is the sense in which the interpolation quantity
controls the strong norm: each level of the distribution function of `v` is
caught by one term of the level profile, at the level where the two endpoint
exponents trade off.

Two `ring` failures cost a little time here, both from the same cause — after
`congr 1` on an equality of `ENNReal.ofReal`s one is left with an equality of
`rpow`s, not of exponents, and a second `congr 1` is needed before `ring` can
act.  Rewriting the exponent identity with an explicit `show ... by ring` inside
the `rw` chain avoids the issue entirely and is what the file now does.

## 2026-09-15T00:50-0700 — how the K-functional varies with the level

`weakK_mono` and `weakK_le_ratio_mul` are the two standard monotonicity facts:
the `K`-functional increases with the level, and it increases by at most the
ratio of the levels,

  weakK t' v ≤ (t'/t) · (‖v-w‖ + t ‖w‖)   for any decomposition, when t ≤ t'.

Both are one-line consequences of the definition — the first because each
summand increases, the second because scaling the whole summand by `t'/t ≥ 1`
covers the increase in the second term and only enlarges the first.  The second
is stated in the tested form, against a chosen decomposition, which is what the
file consistently uses to avoid manipulating the infimum.

They are needed because the balanced level produced by
`weakR_le_weighted_weakK` is an arbitrary positive real while the level profile
runs along the powers of two.  Together they say that replacing the balanced
level by the nearest power of two costs a factor of at most two in the
`K`-functional and at most `2^θ` in the weight, so the profile at that power of
two still dominates the weak-`R` quantity, up to a constant depending on `θ`
alone.

### ext:interpolation — link four, step one: the balanced level meets the dyadic profile

Three results promoted this tick, all verified against the full corpus with
`[propext, Classical.choice, Quot.sound]`, build clean, zero `sorry`.

`weighted_weakK_le_dyadic` says that for `2^n ≤ t < 2^(n+1)` and `θ > 0`,

    t^(-θ) · K(t, v) ≤ 2 · 2^(-θn) · K(2^n, v).

Two separate monotonicities are at work and they point in opposite directions,
which is why the statement needs the bracket rather than just one inequality.
The weight `t^(-θ)` is decreasing, so `t ≥ 2^n` gives `t^(-θ) ≤ (2^n)^(-θ)`
for free.  The `K`-functional is increasing in the level, so `t < 2^(n+1)`
costs something; `weakK_le_ratio_mul` converts that into the factor
`t/2^n < 2`, and the constant is pulled out through the infimum with
`ENNReal.mul_iInf_of_ne` (`Mathlib/Data/ENNReal/Inv.lean:859`), which applies
because `ofReal 2` is neither `0` nor `∞`.

`aux_exists_dyadic_bracket` supplies the bracket itself: every positive real
lies in `[2^n, 2^(n+1))` for `n = Int.log 2 t`.  Mathlib states this with
`zpow`, so the bridge to the real-exponent `rpow` used throughout this corpus
is `Real.rpow_intCast` on both sides.

`weakR_le_dyadic_weakK` composes the two with `weakR_le_weighted_weakK` from
the previous tick.  The composite says: for every level `lam > 0`, writing
`u` for the real number with `μ{2·lam < |v|}/2 = ofReal u`, there exists an
integer `n` with

    lam · u^(1/R) ≤ 2 · 2^(-θn) · K(2^n, v).

This is the first of the four sub-steps of link four.  The balanced level
`u^(1/r₁-1/r₂)` produced by the exponent balance is an arbitrary positive
real; it has now been replaced by a power of two, at the cost of a factor two
that does not depend on `v`, `lam`, or `u`.  The weak-`R` quantity at every
single level is therefore dominated by a single term of the dyadic weighted
`K`-profile — the same profile that `primeJ_method` estimates.

Remaining in link four: pass from single levels to the layer-cake integral
(`∫|v|^R` against the `ℓ^R` sum of the profile, via
`lintegral_rpow_abs_eq_meas_lt`), relate `weakK` to `primeK`, and assemble.

### ext:interpolation — link four, step two: the geometric grid replaces the partition

Two further results promoted this tick, verified against the full corpus,
axioms `[propext, Classical.choice, Quot.sound]`, zero `sorry`.

The second sub-step of link four is to pass from the single-level bound to the
layer-cake integral.  The textbook route partitions the level axis into the
sets where the distribution function lies between consecutive powers of a
fixed ratio, then integrates over each piece.  That route needs the pieces to
be measurable and pairwise disjoint and needs their union to be the whole
half-line except for two degenerate sets, all of which is unpleasant to set up.

A pointwise substitute avoids the partition entirely.  `aux_le_base_grid_tsum`
says that for any ratio `c > 1` and any `D : ℝ≥0∞`,

    D ≤ c · ∑' n : ℤ, [c^n ≤ D] · c^n,

where the bracket is the indicator of the condition.  Only the single largest
qualifying grid point is used, so no geometric series is needed: if
`c^N ≤ D < c^(N+1)` then `D ≤ c · c^N` and that one term already sits under the
sum.  The two degenerate values are handled separately — `D = 0` is trivial,
and `D = ∞` makes every grid point qualify, so the sum dominates `c^m` for
every `m` and is therefore infinite by Archimedes
(`pow_unbounded_of_one_lt`).

Applied to the distribution function `D(t) = μ{t < |v|}` this turns the layer
cake `∫|v|^R = ∫_{t>0} μ{t<|v|} · R t^(R-1) dt` into a sum over the grid of
integrals of `R t^(R-1)` over the sets `{t > 0 : c^n ≤ μ{t<|v|}}`, and each of
those sets is contained in an interval `(0, Λ_n]` supplied by the single-level
bound proved in the previous ticks.  Each integral is then elementary and the
whole layer cake is bounded by `c · ∑_n c^n Λ_n^R`, with no partition, no
measurability side conditions on the pieces, and no rearrangement.

`aux_exists_base_bracket` is the supporting fact that every positive real lies
in `[c^n, c^(n+1))` for some integer `n`, proved through
`⌊log d / log c⌋` and `Real.rpow_le_rpow_left_iff`.  It generalises the
base-two bracket proved earlier in this link, which came from `Int.log` and is
restricted to natural bases; here the ratio `c` is `2^(1/(1/r₁ - 1/r₂))` and is
not an integer.

Next: assemble the layer-cake bound itself, with the grid sets fed by the
single-level estimate `weakR_le_dyadic_weakK`.

### ext:interpolation — link four, step two completed: the layer cake over the grid

Two results promoted, verified against the full corpus,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.

`lintegral_rpow_le_grid_sum` is the layer-cake estimate itself.  Given a ratio
`c > 1` and a sequence `Λ : ℤ → ℝ` such that every level `t > 0` at which the
distribution function `μ{t < |v|}` still reaches `c^n` satisfies `t ≤ Λ n`, it
concludes

    ∫ |v|^R dμ ≤ c · ∑' n : ℤ, c^n · (Λ n)^R.

The proof is short because the grid lemma from earlier in this tick removes
the need for a partition.  Start from
`lintegral_rpow_abs_eq_meas_lt`, which writes the integral as
`∫_{t>0} μ{t<|v|} · R t^(R-1) dt`.  Bound the distribution function
pointwise by `c · ∑_n [c^n ≤ μ{t<|v|}] · c^n`, and observe that the `n`-th
indicator is supported in `Ioc 0 (Λ n)` precisely by the hypothesis.  The
level integral then splits by `lintegral_tsum` into
`∑_n c^n ∫_{Ioc 0 (Λ n)} R t^(R-1) dt`, and each of those is `c^n (Λ n)^R` by
`lintegral_Ioc_zero_rpow`.  A degenerate `Λ n ≤ 0` makes the interval empty and
contributes nothing.

`lintegral_rpow_le_grid_tsum` is the same statement with `Λ` valued in
`ℝ≥0∞`, which is the shape the assembly needs because the sequence that will
be substituted is built from the `K`-functional and so is extended-valued.  If
some `Λ n` is infinite the right-hand side is infinite and the bound is
vacuous; otherwise the real-valued version applies to `(Λ n).toReal`.

That completes the second of the four sub-steps of link four.  What remains:
substitute `Λ n = 2^(-θ n) · K(2^n, v) · (c^n)^(-1/R)` with ratio
`c = 2^(1/(1/r₁ - 1/r₂))`, checking that the exponent arithmetic collapses to
`1/R = (1-θ)/r₁ + θ/r₂`; then relate `weakK` to `primeK`, which is the
functional that `primeJ_method` estimates; then assemble.

### ext:interpolation — link four, step three: `L^R` is dominated by the dyadic K-profile

Four results promoted this tick, verified against the full corpus,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.  This closes the third
of the four sub-steps of link four, and it is the substantial one.

`le_weakK_of_lower` is the lower bound for the `K`-functional in the form the
grid needs.  The earlier `le_weakK` is stated with a `min` of the two
endpoint contributions; here, when the level `tl` is at least the balanced
value `u^(1/r₁ - 1/r₂)` and the distribution function is at least `u`, the
`min` is the first branch and the bound reads simply
`lam · u^(1/r₁) ≤ K(tl, v)`.

`aux_grid_power` records the base change `(2^(1/κ))^n = 2^(n/κ)`.

`grid_level_bound` is the hypothesis of the layer-cake lemma, instantiated.
With `κ = 1/r₁ - 1/r₂ > 0` and grid ratio `c = 2^(1/κ)`, the `n`-th grid point
`c^n` corresponds to the dyadic level `2^n`, since `(c^n)^κ = 2^n`.  The factor
of two between the layer-cake level `t` and the level `lam = t/2` appearing in
`le_weakK` costs `2^(1 + 1/r₁)`, and the statement is

    t ≤ 2^(1+1/r₁) · (c^n)^(-1/r₁) · K(2^n, v)

whenever `μ{t < |v|} ≥ c^n`.  Choosing `lam = t/2` halves the available mass,
so the value fed to `le_weakK_of_lower` is `u = c^n/2` rather than `c^n`; that
only lowers `u^κ` below `2^n`, which is the direction the hypothesis wants, so
no further adjustment is needed.

`lintegral_rpow_le_dyadic_weakK` is the composite:

    ∫ |v|^R dμ ≤ 2^(1/κ) · 2^((1+1/r₁)R) · ∑' n : ℤ, (2^(-θn) · K(2^n, v))^R

whenever `0 < R` and `1/R = (1-θ)/r₁ + θ/r₂`.  The whole content is one
exponent identity.  Writing `a = n/κ` so that `c^n = 2^a`, the `n`-th term of
the grid sum carries the base-two exponent
`a + (1 + 1/r₁ - a/r₁)R`, and the claim is that this equals
`(1 + 1/r₁)R - θnR`, i.e. that `a(1 - R/r₁) = -θnR`.  Since `a = n/κ` this is
`1 - R/r₁ = -θRκ`, which rearranges to `1 = R((1-θ)/r₁ + θ/r₂)` — exactly the
defining relation for `R`.  So the grid ratio, the weight `2^(-θn)` and the
exponent `R` are forced to fit together, and they do.

This is the statement that was missing from Mathlib and from `lean_spherical`:
the interpolation quantity built from the `K`-functional dominates the genuine
`L^R` norm.  Combined with `primeJ_method`, which bounds that quantity for a
sum of pieces by the `ℓ^R` norm of their `J`-functionals, the real
interpolation machinery is now present in the corpus in the form the
four-vertex Marcinkiewicz statement needs.

Remaining in link four: relate `weakK` to `primeK` — `primeJ_method` is stated
for the latter, which is built from the genuine norm `weakNormPrime` rather
than the quasi-norm `weakNorm`, and the two are comparable by
`weakNorm_le_weakNormPrime` and `weakNormPrime_le_conj_mul_weakNorm` — and then
assemble the four-vertex statement itself.

### ext:interpolation — a defect found in my own definition, and the repair

Six results promoted this tick, verified against the full corpus,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.

While trying to join the two halves of the interpolation argument I found that
the join cannot be made through `primeK` as defined, and the reason is a real
defect rather than a missing lemma.  `weakNormPrime` integrates over measurable
sets, and for a non-measurable integrand Mathlib's `∫⁻` is the lower integral,
which vanishes whenever the integrand has no non-trivial measurable minorant.
Splitting a measurable `v` along a Bernstein set therefore makes both halves
have candidate norm zero, so the unrestricted infimum defining `primeK` is
identically zero on Lebesgue measure.  The full argument is recorded in
ErrorReport.md.  Nothing already proved is wrong — the affected statements are
upper bounds, hence still true — but they are vacuous, and in particular
`weakK ≤ primeK` is false, which is precisely the inequality the chain needs.

The repair is to take the infimum over measurable decompositions only.
`primeKm` is that functional, and `primeK_le_primeKm` records that restricting
can only raise it.  `primeKm_le_left`, `primeKm_le_right`, `primeKm_add_le` and
`primeKm_sum_le` are the ported upper bounds; each existing proof exhibited an
explicit measurable witness (`0`, `v`, `w₁ + w₂`, `∑ w i`), so the ports differ
only in packaging the witness with its measurability proof, plus the extra
hypotheses that makes necessary.

`weakK_le_primeKm` is the bridge that was the point of the exercise: for
measurable `v` on a σ-finite measure,

    weakK μ r₁ r₂ t v ≤ primeKm μ r₁ r₂ t v,

by applying `weakNorm_le_weakNormPrime` to each of the two measurable pieces of
the decomposition.  `weakK` needs no restriction of its own: it is built from
`μ {τ < |f|}`, which is an outer measure on a non-measurable set and therefore
large rather than small.

Next: port `primeK_sum_le_primeJ` and then `primeJ_method` to `primeKm`, after
which the two halves meet.

### ext:interpolation — link four closed: the two halves meet

Five results promoted this tick, verified against the full corpus,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.

`primeKm_sum_le_primeJ`, `aux_profile_level_le_meas`,
`aux_profile_level_conv_le_meas` and `primeJm_method` are the ports of the
`J`-method chain to the restricted `K`-functional.  All four went through
without a single change to the proof scripts: every one of them reaches
`primeK` only through `primeK_sum_le`, whose witness is the explicit truncation
`w i = if σ i ≤ t then 0 else v i`, and that is measurable whenever the `v i`
are.  So the defect found last tick cost nothing beyond the renaming.

`lintegral_rpow_le_J_profile` is the join, and it is the statement the whole
link was for.  For a σ-finite measure, measurable pieces `v i` indexed by `ℤ`,
`1 ≤ R`, `0 < 1/r₁ - 1/r₂` and `1/R = (1-θ)/r₁ + θ/r₂`, if

  * `A` bounds every partial sum of the kernel `2^(-θk) · min(1, 2^k)`, and
  * `B` bounds every partial `ℓ^R` norm of the weighted `J`-functionals
    `2^(-θi) · J(2^i, v i)`,

then

    ∫ |∑ᵢ vᵢ|^R dμ ≤ 2^(1/κ) · 2^((1+1/r₁)R) · (A·B)^R.

Three pieces meet here.  The layer-cake half supplies
`∫|v|^R ≤ C · ∑ₙ (2^(-θn) K(2ⁿ,v))^R` with the quasi-norm functional `weakK`;
`weakK_le_primeKm` converts that functional into the one the `J`-method speaks
about; and `primeJm_method` bounds every partial sum of the resulting profile
by `(A·B)^R`, which passes to the infinite sum because in `ℝ≥0∞` a `tsum` is
the supremum of its partial sums.  The only arithmetic step is undoing the
`1/R` power that `primeJm_method` carries on its left-hand side.

Real interpolation — absent from Mathlib and from `lean_spherical`, which
supplies only the complex method — is therefore now present in the corpus in
the form the four-vertex Marcinkiewicz statement needs: weak endpoint
information in, a genuine `L^R` bound out.

What remains for `ext:interpolation` is the four-vertex statement itself:
choosing the decomposition `v i` from the operator's level sets, verifying the
two hypotheses `A` and `B` from the four weak bounds, and threading the three
input slots through `TrilinearOnSimple`.

### ext:interpolation — the two hypotheses of the interpolation theorem

Four results promoted this tick, verified against the full corpus,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.

`lintegral_rpow_le_J_profile` carries two hypotheses, `A` for the kernel and
`B` for the data.  This tick discharges the first outright and prepares the
second.

`exists_kernel_sum_bound` says that for `0 < θ < 1` there is a finite `A` with
`∑_{k ∈ K} 2^(-θk) · min(1, 2^k) ≤ A` for every finite `K ⊆ ℤ`.  This is the
tent sum from earlier in the task at exponent one: the kernel decays like
`2^((1-θ)k)` on the left and like `2^(-θk)` on the right, and both exponents
are strictly positive exactly when `θ` is strictly between zero and one.  The
existing `exists_discrete_profile_bound` supplies it once the `^s` is
specialised to `s = 1`.

`exists_lintegral_rpow_le_J_profile` folds that constant into the statement, so
what is left is a single clean implication: any bound `B` on the weighted
`ℓ^R` norms of the `J`-functionals of a measurable decomposition yields

    ∫ |∑ᵢ vᵢ|^R dμ ≤ C · B^R

with `C` depending only on `r₁`, `θ` and `R`.

`primeJ_le_of_weak_bounds` prepares the other hypothesis.  The `J`-functional
is built from the candidate norm `weakNormPrime`, but what the four vertices
supply is weak quasi-norm information.  If `weakNorm v r₁ ≤ Γ₁` and
`weakNorm v r₂ ≤ Γ₂` with both exponents above one, then

    J(s, v) ≤ max(r₁/(r₁-1), r₂/(r₂-1)) · max(Γ₁, s·Γ₂),

the constant being the one from `weakNormPrime_le_conj_mul_weakNorm`, which is
where the restriction `r > 1` — and hence `R > 1` in the blueprint — comes
from.  The right-hand side is exactly the weak-quasi-norm `J`-functional, so
from here on the data hypothesis can be checked entirely in terms of weak
bounds on the pieces, which is what the four vertices give.

### ext:interpolation — the real interpolation theorem in usable form

Two results promoted this tick, verified against the full corpus,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.

`primeJ_profile_le_of_weak_bounds` converts the data hypothesis of the
interpolation theorem into weak-bound form.  If the pieces `v i` satisfy
`weakNorm (v i) r₁ ≤ Γ₁ i` and `weakNorm (v i) r₂ ≤ Γ₂ i`, and the real
sequence `2^(-θi) · max(Γ₁ i, 2^i · Γ₂ i)` has `ℓ^R` norm at most `Bw`, then
the weighted `ℓ^R` norm of the `J`-functionals is at most
`C_primeJ_le_of_weak_bounds r₁ r₂ · Bw`.  Both the passage from the candidate
norm to the quasi-norm and the extraction of the constant from the sum happen
here, so the constant appears exactly once.

`exists_lintegral_rpow_le_of_weak_pieces` is the composite, and it is the
interpolation theorem in the shape the four-vertex argument will consume:

  given `1 < r₁`, `1 < r₂` with `1/r₁ > 1/r₂`, `0 < θ < 1`, `1 ≤ R` and
  `1/R = (1-θ)/r₁ + θ/r₂`, there is a constant `C` depending only on those
  numbers such that for every measurable decomposition `v : ℤ → X → ℝ` with
  weak endpoint bounds `Γ₁`, `Γ₂` on the pieces and every `Bw` dominating the
  `ℓ^R` norm of `2^(-θi) · max(Γ₁ i, 2^i Γ₂ i)`,

      ∫ |∑_{i ∈ T} v i|^R dμ ≤ C · Bw^R

  for every finite `T`.

Nothing about the operator enters; this is a statement about decompositions of
a single function.  What the four-vertex argument has to supply is the
decomposition itself and the two families of weak bounds on its pieces, which
is where the level sets of the three inputs and the four vertex estimates come
in.

### ext:interpolation — surveying the four-vertex side, and one result

One result promoted this tick, verified against the full corpus,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.

With the real interpolation machinery finished, this tick was mostly spent
matching it against what the four-vertex statement needs, so the plan below is
recorded as much as the lemma is.

What the corpus already has on the four-vertex side:
`weakNorm_expansion_term_interior_le` gives, for a single layer multi-index
`k`, the weak-`R` bound on `T` applied to the three layer pieces, with the
sharp constant `∏ A_a^ϑ_a` and the target measures `m_j^{1/p_j}`;
`meas_lt_operator_expansion` expands the operator over the layer lattice and
distributes a level among the terms; `exists_normalized_lattice_tent` and
`sum_tent_levels_le` supply a summable share of the level for each layer
triple; `exists_vertex_geometric_decay` says that for every direction some
vertex bound beats the barycentric one by `2^(-δ‖w‖)`.

What the interpolation machine consumes is different in shape: a decomposition
indexed by `ℤ`, with weak bounds at two exponents straddling `R` on each piece,
and control of the `ℓ^R` norm of `2^(-θi) · max(Γ₁ i, 2^i Γ₂ i)`.  The natural
grouping sends a layer multi-index `k` to `i(k) = ⌊log₂(Γ₁(k)/Γ₂(k))⌋`, which
is where the two endpoint bounds balance.  Worth recording: in that ratio the
heights `2^(k_j)` cancel — they carry the same power at both endpoints — so
`i(k)` is a function of the layer measures alone.  The piece `v i` is then the
sum of the layer terms in one fibre, and a weak bound on it needs the weak
norms of the terms to add.

`weakNorm_sum_le_of_weak_bounds` is that addition.  The weak quasi-norm is not
subadditive, but above exponent one it is equivalent to the genuine norm
`weakNormPrime`, which is; so a finite family of weak bounds `Γ i` yields

    weakNorm (∑_{i ∈ S} v i) r ≤ (r/(r-1)) · ∑_{i ∈ S} Γ i,

with the constant independent of the number of summands.  That is what makes
the fibre sums usable, and it is another place where the blueprint's `r > 1` is
doing real work.

This does not by itself settle the `ℓ^R` bound on the fibre profile, which is
the remaining mathematical content: the fibres have to be thin enough that the
within-fibre `ℓ¹` sums do not destroy the `ℓ^R` gain.  That is where the
geometric decay from `exists_vertex_geometric_decay` has to enter.

### ext:interpolation — the interpolation pair inside the simplex

Two results promoted this tick, verified against the full corpus,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.  A design question was
settled first, and the answer determines the shape of the rest of the argument.

The interpolation theorem needs two exponents straddling `R`.  The obvious
candidates are two of the four vertex exponents `r a`, and
`exists_straddling_output_exponents` already produces such a pair.  But that
choice is wrong: interpolating between two vertices reaches only points of the
segment joining them, so the input exponents that come out are those of the
segment, not the target's.  The target is interior to the tetrahedron and in
general lies on no such segment.

The right pair is not two vertices but two *interior* points, placed
symmetrically about the target.  Write `ϑ` for the target weights and let
`ϑ₁ = ϑ + εe`, `ϑ₂ = ϑ - εe` where `e` is the difference of two coordinate
indicators and `ε` is half the smallest weight.  Both stay in the open simplex,
their midpoint is `ϑ`, and therefore *both* the input reciprocals and the
output reciprocal interpolate correctly:

    (1-θ)/p₁ⱼ + θ/p₂ⱼ = 1/pⱼ    and    (1-θ)/ρ₁ + θ/ρ₂ = 1/R

at `θ = 1/2`, because all of these are linear in the weights.  The endpoint
constants multiply to `∏ A_a^(ϑ_a)` for the same reason.  So the geometric mean
of the two interior bounds is exactly the target bound, constant included, and
nothing has to be re-derived at the target point itself.

The one thing that must be checked is that the two output exponents differ,
since otherwise the interpolation is vacuous.  That is where affine
independence enters, through `aux_exists_ne_coordSum`: the four vertices span
an affine three-space, so the linear functional `∑ⱼ` cannot be constant on
them, hence two vertices have different `1/r`, and choosing `e` as the
difference of those two indicators makes `∑_c ϑ₁_c/r_c - ∑_c ϑ₂_c/r_c
= 2ε(1/r_a - 1/r_b) ≠ 0`.

`exists_straddling_weights` is the construction and
`exists_straddling_weight_pair` packages it with the blueprint's hypotheses.

With this, the two families of weak bounds that the interpolation machine
consumes are both instances of `weakNorm_expansion_term_interior_le`, at the
two perturbed weight vectors, and their geometric mean is the target bound.
What is still missing is the `ℓ^R` estimate on the resulting profile, and the
survey of the last tick shows why it cannot be avoided: with the layer bounds
alone, and no gain, the profile is an `ℓ^R` norm of a product of sequences that
sits in `ℓ^{p_j}` with `p_j > R`, which does not converge.  The gain has to
come from the duality gap between the best straddling pair and the barycentric
mean, which is exactly what `exists_vertex_geometric_decay` quantifies.

### ext:interpolation — the face of weight vectors that keep `R` fixed, and the full architecture

Five results promoted this tick (`pairWeight` and three facts about it, plus
`mixWeight_spec`), verified against the full corpus,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.  The architecture of
the remaining argument is now clear enough to record in full.

**Where the gain lives.**  `weakNorm_expansion_term_interior_le` holds for
*every* weight vector `ϑ'` with positive entries summing to one; the output
exponent it produces is `R' = (∑_a ϑ'_a/r_a)⁻¹` and the input exponents are
`1/p'_j = ∑_a ϑ'_a/P_{a,j}`.  So for a fixed `R` the usable weight vectors form
the face

    F = {ϑ' ≥ 0 : ∑_a ϑ'_a = 1, ∑_a ϑ'_a/r_a = 1/R},

a two-dimensional polygon containing the target `ϑ` in its relative interior.
Each `ϑ' ∈ F` gives a valid weak-`R` bound on the layer term, with constant
`∏_a A_a^(ϑ'_a)` and measures `m_j^(1/p'_j)`.  The best of them is what the
layer-cake actually yields — a fact from LP duality: with `Γ_a` the four
endpoint sizes, the achievable weak-`R` bound is
`min over ϑ' ∈ F of ∏_a Γ_a^(ϑ'_a)`, and taking `ϑ' = ϑ` shows this is at most
the barycentric value.  The *gap* between the two is the gain, and it is
`2^(-⟨ℓ, x - y'⟩)` where `ℓ_j = log m_j`, `x = ∑ ϑ_a v_a`, `y' = ∑ ϑ'_a v_a`.

**How big the gain is.**  As `ϑ'` runs over `F`, `y'` runs over a
two-dimensional polytope around `x` inside the plane `∑_j y_j = 1/R`.  So the
gain is bounded below by `δ‖ℓ_⊥‖` where `ℓ_⊥` is the component of `ℓ`
orthogonal to `(1,1,1)`, and `δ > 0` comes from `x` being interior — the same
compactness argument as `exists_gap_of_affineIndependent`, run on the face
instead of the whole simplex.  There is deliberately *no* gain in the
`(1,1,1)` direction: that is the degenerate direction identified earlier in
this task, where all three layer measures move together.

**Where the missing direction comes from.**  The `J`-method index supplies it.
Grouping layer multi-indices by `i(k) = ⌊log₂(Γ⁽¹⁾(k)/Γ⁽²⁾(k))⌋` separates
them along the direction `x₁ - x₂`, and that direction has a nonzero
`(1,1,1)`-component precisely because `∑_j (x_m)_j = 1/ρ_m` and the two output
exponents were arranged to differ.  So the two mechanisms are complementary:
the face gain controls the two directions orthogonal to the diagonal, the
interpolation index controls the diagonal, and together they control all three.

**This tick's results.**  The extreme points of `F` are the weight vectors
supported on a straddling pair of vertices.  `pairWeight r R a b` is that
vector, and `pairWeight_nonneg`, `pairWeight_sum`, `pairWeight_output` verify
that it is nonnegative, sums to one, and reproduces `1/R`, under
`1/r_b < 1/R < 1/r_a`.  Its entries at the other two vertices are zero, which
the layer bound does not permit, so `mixWeight_spec` records that mixing any
face weight with the target weight — `(1-η)σ + ηϑ` — stays on the face and
becomes strictly positive, at the cost of a factor `(1-η)` in the gain.

### ext:interpolation — the face gain, qualitative half

Nine results promoted across this tick (`minWeight`, `minWeight_le`,
`minWeight_pos`, `maxAbs`, `le_maxAbs`, `maxAbs_nonneg`,
`face_functional_zero_of_nonpos`, `exists_zero_sum_combination`,
`eq_zero_of_forall_face_nonpos`), all verified against the full corpus,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.

The face gain has a qualitative half and a quantitative half.  The
quantitative half is a compactness argument identical in shape to
`exists_gap_of_affineIndependent`; what that argument needs as input is the
qualitative statement that a covector with *no* gain is zero.  This tick proves
that statement.

`face_functional_zero_of_nonpos` is the algebraic core, and it is a fact about
four real numbers and nothing else.  If a linear functional `∑ ϑ'_a g_a` is
nonpositive on the whole face `{ϑ' ≥ 0, ∑ ϑ' = 1, ∑ ϑ'_a s_a = S}` and vanishes
at a point `ϑ` of the face with all coordinates positive, then it vanishes in
every direction `e` tangent to the face (`∑ e = 0`, `∑ e_a s_a = 0`).  The
proof is one line of geometry: `ϑ ± εe` stays on the face for small `ε`, so
`±ε ∑ e_a g_a ≤ 0`.  The `ε` is `minWeight ϑ / (maxAbs e + 1)`.

`exists_zero_sum_combination` supplies the tangent directions.  For affinely
independent `v`, every `z ∈ ℝ³` is `∑ e_a • v_a` with `∑ e_a = 0`: the
differences `v_{i+1} - v_0` are three linearly independent vectors in `ℝ³`,
hence span, and the coefficient of `v_0` is set to balance the sum.  The
reindexing from the subtype `{a // a ≠ 0}` to `Fin 3` is done through
`Fin.succ`, which lets `Fin.sum_univ_succ` and `Fin.cons` do the bookkeeping.

`eq_zero_of_forall_face_nonpos` composes them.  Take `w` with `∑ w_j = 0` that
pairs nonpositively with every face point measured from the barycentre.  Write
`w` itself as `∑ e_a • v_a` with `∑ e_a = 0`; then `∑ e_a s_a = ∑_j w_j = 0`
automatically, since `s_a = ∑_j v_{a,j}`, so `e` is tangent to the face and the
core lemma gives `∑ e_a ⟨w, v_a - x⟩ = 0`.  But that sum is
`⟨w, ∑ e_a v_a⟩ - (∑ e_a)⟨w, x⟩ = ⟨w, w⟩`, so `w = 0`.

The hypothesis `∑ w_j = 0` is exactly the diagonal exclusion.  Without it the
statement is false — `w = (1,1,1)` pairs to zero with every face point, since
the face lies in a plane `∑ y_j = 1/R` — and that is the degenerate direction
that the interpolation index, not the face gain, has to control.

Next: the quantitative half — the minimum of the face maximum over the unit
sphere of the plane `∑ w_j = 0` is positive, by compactness — giving
`δ > 0` with gain at least `δ‖w‖` for every `w` in that plane.

### ext:interpolation — the face gain, quantitative half, with an explicit constant

One result promoted this tick, `exists_face_gain`, verified against the full
corpus, `[propext, Classical.choice, Quot.sound]`, zero `sorry`.

The plan had been to run the same compactness argument as
`exists_gap_of_affineIndependent` on the unit sphere of the plane
`∑ w_j = 0`.  It turned out not to be needed.  The face is two-dimensional,
and `exists_zero_sum_combination` realises any two tangent directions of it
explicitly; taking `z₁ = (1,-1,0)` and `z₂ = (0,1,-1)` gives zero-sum
coefficient vectors `e₁`, `e₂` with `∑ eᵢ_a v_a = zᵢ`.  Both are automatically
tangent to the face, since `∑_a e_a s_a = ∑_j z_j = 0`.  The test weights are
then the four points `ϑ ± ε e₁`, `ϑ ± ε e₂`, with
`ε = minWeight ϑ / (max(maxAbs e₁, maxAbs e₂) + 1)` keeping all entries
strictly positive.

For `w` with `∑ w_j = 0` the pairing at `ϑ ± ε eᵢ` is `±ε ⟨w, zᵢ⟩`, i.e.
`±ε (w₀ - w₁)` or `±ε (w₁ - w₂)`.  Writing `A = w₀ - w₁`, `B = w₁ - w₂`, the
zero-sum condition gives `3w₀ = 2A + B`, `3w₁ = -A + B`, `3w₂ = -A - 2B`, so
`‖w‖ ≤ max(|A|, |B|)` in the sup norm, and choosing the sign and direction that
attains the max yields

    δ‖w‖ ≤ ∑_a ϑ'_a ⟨w, v_a - x⟩    with δ = ε.

The statement returns the witness `ϑ'` together with its three properties —
strictly positive, summing to one, same output exponent as `ϑ` — which is
exactly the form `weakNorm_expansion_term_interior_le` consumes.  So the gain
is now available as a *choice of weight vector per layer*: for each layer
multi-index, with `ℓ_j = log m_j` and `w` its zero-sum part, some face weight
improves the barycentric bound by a factor `2^(-δ‖w‖)`.

The qualitative lemma `eq_zero_of_forall_face_nonpos` of the previous tick is
thereby superseded for the purposes of the argument, though it remains as the
conceptual statement.  The constant `δ` here is explicit in the geometry of the
vertices, which will matter when the final constant `C` is assembled.

Next: apply the gain to a layer term.  For a multi-index `k`, take
`ℓ_j = log₂ m_j(k_j)`, split off the diagonal part, choose `ϑ'` by
`exists_face_gain` for the zero-sum part, and compare the resulting bound from
`weakNorm_expansion_term_interior_le` at `ϑ'` with the barycentric one.

### ext:interpolation — the face gain applied to a layer term

Eight results promoted this tick (`aux_rpow_le_max_of_abs_le_one`,
`C_weights_shift`, `prod_rpow_le_of_weights_close`, `prod_rpow_eq_exp`,
`layerLogDeviation`, `layerLogDeviation_sum`, and the main
`exists_weakNorm_expansion_term_gain_le`), verified against the full corpus,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`, no linter warnings.

`exists_weakNorm_expansion_term_gain_le` is the per-layer bound with the gain
built in.  Under the blueprint's hypotheses (with `0 < A a`), there is
`δ > 0` — the one from `exists_face_gain`, depending only on the exponent
vectors and the weights — such that for every layer multi-index `k` with all
three layer measures `m_j` positive,

    ‖T(layer k)‖_{R,∞} ≤ (∏ A_a^{ϑ_a}) · C_weights_shift A · exp(-δ‖w‖)
                            · ∏_j 2^{k_j+1} m_j^{1/p_j},

where `w = layerLogDeviation m` is the zero-sum part of `(log m_j)_j`.  Compared
with the barycentric bound `weakNorm_expansion_term_interior_le`, the only new
factors are the constant `C_weights_shift A = ∏_a max(A_a, A_a⁻¹)` and the gain
`exp(-δ‖w‖)`.

The proof runs as planned.  Feed `-w` to `exists_face_gain` to get a face
weight `ϑ'`; define `p'` by `1/p'_j = ∑ ϑ'_a/P_{a,j}`; check that `ϑ'` still
produces the output exponent `R` (`hRdef'`, from the face constraint and
`hrsum`); apply the barycentric bound at `ϑ'`.  Then compare factor by factor.
The endpoint constants move by `∏ A_a^{ϑ'_a - ϑ_a} ≤ C_weights_shift A`, since
`|ϑ'_a - ϑ_a| ≤ 1`.  The measure factors are compared through
`∏ m_j^{y_j} = exp(∑ y_j log m_j)`: the exponent difference is
`∑_j (1/p'_j - 1/p_j) log m_j`, and splitting `log m_j = w_j + c` the constant
part drops out because `∑_j (1/p'_j - 1/p_j) = 0` — that is the face constraint
again — leaving `∑_a ϑ'_a ⟨w, v_a - x⟩ ≤ -δ‖w‖`.

Two small facts worth keeping in view.  The constant `C_weights_shift` makes
the final `C` depend on `A`, which the blueprint permits (`C` is quantified
after the endpoint data); when some `A_a = 0` the statement here does not
apply, and that case will have to be handled at the end by noting that the
corresponding weak bound forces `T f = 0` a.e.  And the gain is in the natural
exponential rather than base two, because `Real.logb` is not in the imported
corpus; nothing downstream cares.

Next: the assembly over multi-indices.  The pieces are now: the gain per layer
(this tick), the fibre grouping by the interpolation index, weak-norm
subadditivity for the fibre sums (`weakNorm_sum_le_of_weak_bounds`), and the
interpolation theorem (`exists_lintegral_rpow_le_of_weak_pieces`).  What
connects them is the `ℓ^R` estimate on the fibre profile, which has to use the
gain to control the two non-diagonal directions and the fibre index for the
diagonal one.

### ext:interpolation — the complete plan for the remaining assembly, and its first lemma

One result promoted this tick, `sum_rpow_mul_three_le`, verified against the
full corpus, `[propext, Classical.choice, Quot.sound]`, zero `sorry`.  Most of
the tick went into working out, on paper, how the `ℓ^R` estimate on the fibre
profile is proved.  It closes, and the argument is recorded here in full so it
can be followed tick by tick.

**Two corrections to earlier design decisions.**

(1) The perturbation direction.  `exists_straddling_weights` perturbs the
weights along `δ_a - δ_b`.  The right direction is the one whose image in
exponent space is the diagonal `(1,1,1)`: take `e` from
`exists_zero_sum_combination` with `∑ e_a v_a = (1,1,1)` and set
`ϑ^{1,2} = ϑ ± εe`.  Then `1/p¹_j - 1/p²_j = 2ε` is the same for every `j`,
the two output exponents differ (since `∑_a e_a s_a = ∑_j 1 = 3 ≠ 0`), and the
ratio of the two interior bounds on a layer term is `(D₁/D₂)·(∏_j m_j)^{2ε}`,
a function of the *product* of the three layer measures alone.  So the fibre
index `i(k) = ⌊log₂(Γ¹(k)/Γ²(k))⌋` is a function of `∑_j log m_j(k_j)` — the
diagonal coordinate — and nothing else.  The transverse coordinates are
exactly what the face gain controls.  `exists_straddling_weights` stays in the
corpus but will not be used.

(2) The gain must be taken at both interior points `ϑ¹`, `ϑ²`, not at `ϑ`;
`exists_weakNorm_expansion_term_gain_le` applies to each.  Taking the smaller
of the two `δ`'s for both keeps the ratio `Γ¹/Γ²` free of the gain factor.

**The reduction to a discrete inequality.**  Write `n_j = ⌊log₂ m_j(k_j)⌋` and
`N = ∑_j n_j`.  On the fibre of `k`, `N` is determined up to a bounded number
of values, and conversely — bounded overlap both ways.  The gain factor is
`exp(-δ‖w‖) ≤ C · 2^{-δ' max_j |n_j - N/3|}`.  Within a block of fixed
`(n₁,n₂,n₃)`, the heights `k_j` with `⌊log₂ m_j(k_j)⌋ = n_j` are distinct
integers, so `∑ 2^{k_j} ≤ 2 · max 2^{k_j} ≤ 2 (∑ 2^{k_j p_j})^{1/p_j}`, and
with `b_j(n) := ∑_{k : ⌊log₂ m_j(k)⌋ = n} 2^{k p_j} m_j(k)` (so
`∑_n b_j(n) ≤ ‖f_j‖_{p_j}^{p_j}`) the block contributes at most
`2^{1+1/p_j} b_j(n_j)^{1/p_j}` per slot.  Setting `B_j(n) = b_j(n)^{1/p_j}`,
so that `∑_n B_j(n)^{p_j} ≤ 1` after normalisation, the fibre profile is
bounded by

    ∑_N ( ∑_{n₁+n₂+n₃=N} B₁(n₁) B₂(n₂) B₃(n₃) · 2^{-δ' max_j |n_j - N/3|} )^R.

**The discrete core.**  On the slice `∑ n_j = N` the deviations `n_j - N/3`
sum to zero, so `max_j |n_j - N/3| ≥ (|n₁-n₂| + |n₂-n₃|)/4`, and the decay is
dominated by `e(n₁-n₂) · e(n₂-n₃)` with `e(t) = 2^{-δ't/4}`, a summable
sequence.  Parametrise the slice by `(s,t) = (n₁-n₂, n₂-n₃)`: for fixed
`(s,t)`, as `N` varies the point `n₁ = (N+2s+t)/3` runs over `ℤ` (on one
residue class), so

    ∑_N F_{s,t}(N)^R = ∑_{n} (B₁(n) B₂(n-s) B₃(n-s-t))^R
                     ≤ ∏_j (∑_n B_j(n)^{p_j})^{R/p_j} ≤ 1

by the three-function Hölder inequality — which is exactly where
`∑_j R/p_j = 1`, i.e. `1/R = ∑_j 1/p_j`, is used.  Then the `ℓ^R` triangle
inequality over the `(s,t)` family (`Lp_finset_sum_le`, `R ≥ 1`) gives

    ( ∑_N (∑_{s,t} e(s) e(t) F_{s,t}(N))^R )^{1/R} ≤ ∑_{s,t} e(s) e(t) ≤ E².

So the fibre profile is bounded by a constant depending only on `δ'` and `R`.

**Sanity check against the earlier counterexample.**  Three equal inputs with
`M` bands of measure `2^{-pk}/M`: the fibres are the values of `∑_j k_j`, about
`3M` of them, each fibre sum is `M^{-1/R} · O(1)`, and
`∑_i (M^{-1/R})^R · 3M = O(1)` — the `M^{1-1/R}` loss of the `ℓ¹` route is gone.

**This tick's lemma.**  `sum_rpow_mul_three_le` is the three-function Hölder
inequality on a finite set, in the form
`∑ (fgh)^R ≤ (∑ f^{p₁})^{R/p₁} (∑ g^{p₂})^{R/p₂} (∑ h^{p₃})^{R/p₃}` under
`1/p₁ + 1/p₂ + 1/p₃ = 1/R`, obtained by applying Mathlib's
`Real.Lr_rpow_le_Lp_mul_Lq_of_nonneg` twice through the intermediate exponent
`q = (1/p₂ + 1/p₃)⁻¹`.

**Remaining steps, in order.**  (i) The discrete core as stated above.  (ii) The
block estimate for distinct powers of two.  (iii) The bounded-overlap
bookkeeping between fibres and `N`.  (iv) The diagonal perturbation pair.
(v) Assembly: gains at `ϑ¹`, `ϑ²`, fibre sums via
`weakNorm_sum_le_of_weak_bounds`, then `exists_lintegral_rpow_le_of_weak_pieces`.
(vi) Normalisation by trilinearity, the degenerate cases (`A_a = 0`, an empty
layer), and the translation from `lintegral` to `lpNorm`.

### ext:interpolation — the discrete core, preparatory lemmas

Four results promoted this tick, verified against the full corpus,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`, no warnings:
`real_Lp_finset_sum_le`, `sum_rpow_of_card_le_one`, `sum_shift_le_of_forall`,
`sum_rpow_shifted_three_le`.

These are the four ingredients of the discrete core from the plan recorded
last tick, each a self-contained real-analysis fact.

`real_Lp_finset_sum_le` is Minkowski's inequality for a finite family of
nonnegative real sequences on a finite set — the real-valued twin of the
`ℝ≥0∞` version `Lp_finset_sum_le` already in the corpus — by induction on the
family from Mathlib's two-function `Real.Lp_add_le_of_nonneg`.  It is the
`ℓ^R` triangle inequality over the `(s,t)` family of shifts.

`sum_rpow_of_card_le_one` says that on a set with at most one element a sum
commutes with a positive power.  Each fibre of the slice map
`n ↦ (∑ n_j, n₁ - n₂, n₂ - n₃)` is such a set, which is what lets the inner
sums over fibres be turned into sums of `R`-th powers without loss.

`sum_shift_le_of_forall` records that an `ℓ^p` bound holding on every finite
set is invariant under shifting the index, and `sum_rpow_shifted_three_le`
combines it with `sum_rpow_mul_three_le`: three sequences of `ℓ^{p_j}` norm at
most one, evaluated at three shifts of a common index, have
`∑ (B₁(m+a) B₂(m+b) B₃(m+c))^R ≤ 1` whenever `∑ 1/p_j = 1/R`.  This is the
estimate on a single `(s,t)`-line of the slice; the shifts `a, b, c` will be
`s + t`, `t`, `0` when the line is parametrised by `n₃`.

Next: the discrete core itself — decompose each slice sum by the two
differences, apply Minkowski over the differences, bound each line by the
shifted Hölder estimate, and sum the decay weights.

### ext:interpolation — the discrete core is proved

Three results promoted this tick (`tripleSum`, `tripleDiff`,
`triple_eq_of_sum_diff`, and the main `discrete_core_le`), verified against
the full corpus, `[propext, Classical.choice, Quot.sound]`, zero `sorry`.

`discrete_core_le` is the `ℓ^R` estimate on the fibre profile, stated over a
finite set `Λ ⊆ ℤ³` of multi-indices.  With three sequences `B_j ≥ 0` of
`ℓ^{p_j}` norm at most one, a decay `e ≥ 0` with `∑ e ≤ E` on every finite set,
`R ≥ 1` and `∑_j 1/p_j = 1/R`,

    ( ∑_{N} ( ∑_{n ∈ Λ, n₁+n₂+n₃ = N} B₁(n₁)B₂(n₂)B₃(n₃) · e(n₁-n₂) e(n₂-n₃) )^R )^{1/R} ≤ E².

The proof follows the recorded plan exactly.  Each slice sum is decomposed by
the pair of differences `d = (n₁-n₂, n₂-n₃)` through
`Finset.sum_fiberwise_of_maps_to`; the decay factor is constant on each fibre
and comes out.  Minkowski over the finite set of pairs
(`real_Lp_finset_sum_le`) reduces the claim to one line at a time.  On a line,
each slice meets it in at most one point — `triple_eq_of_sum_diff`: a triple is
determined by its sum and its two differences — so the `R`-th power passes
inside the fibre sum (`sum_rpow_of_card_le_one`), the fibrewise decomposition
is undone, and the line is reparametrised by its third coordinate, giving
`∑_m (B₁(m + s + t) B₂(m + t) B₃(m))^R ≤ 1` by `sum_rpow_shifted_three_le`.
Finally the decay weights `e(s)e(t)` over the set of pairs are dominated by the
product of two one-dimensional sums, each at most `E`.

The statement is over `ℤ × ℤ × ℤ` rather than `Fin 3 → ℤ`, because the
differences are most naturally written with projections; the layer machinery
uses `Fin 3 → ℤ` and a conversion will be needed at the point of use.

This was the step whose mathematics had been in doubt for much of the task —
whether the per-layer bounds could be summed to the strong norm at all.  With
it proved, the remaining steps are bookkeeping of known shape: the block
estimate for distinct powers of two, the bounded overlap between fibres and
slices, the diagonal perturbation pair, and the assembly.

### ext:interpolation — the block estimate

Two results promoted this tick, `sum_zpow_two_le_two_mul_max` and
`block_estimate`, verified against the full corpus,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`, no warnings.

`sum_zpow_two_le_two_mul_max`: a finite set of distinct integer powers of two
sums to at most twice the largest.  Writing each term as `2^M (1/2)^(M-k)` and
using injectivity of `k ↦ M - k` on the set, the sum is dominated by the
finite geometric series `∑_{i<N} (1/2)^i = 2(1 - 2^{-N}) ≤ 2`.  (A first
attempt through `tsum_geometric_two` foundered on the name of the
finite-sum-below-tsum lemma in this Mathlib; the finite geometric sum is more
elementary anyway.)

`block_estimate` is the estimate for one slot and one dyadic range of the
layer measure.  For heights `k ∈ K` whose measures all satisfy
`2^n ≤ m(k) < 2^(n+1)`,

    ∑_{k∈K} 2^k m(k)^{1/p} ≤ 2^(1+1/p) · ( ∑_{k∈K} (2^k)^p m(k) )^{1/p}.

The right-hand side is the `1/p`-th power of the block's share of the `L^p`
budget `∑_k (2^k)^p m(k) ≤ ‖f‖_p^p`.  The proof is the three-line argument
from the plan: bound each `m(k)^{1/p}` by the top of the range, bound the sum
of the `2^k` by twice the largest, and read off the largest from the budget
through its own term `(2^M)^p · 2^n ≤ (2^M)^p m(M)`.

With this, the sequences `B_j(n) := (share of the budget in range n)^{1/p_j}`
satisfy `∑_n B_j(n)^{p_j} ≤ ‖f_j‖_{p_j}^{p_j}`, and the fibre profile is
dominated, block by block, by the quantity the discrete core controls.

Next: the bounded-overlap bookkeeping between the interpolation fibres
(defined through `∏_j m_j`) and the slices `∑_j n_j = N`, and the diagonal
perturbation pair.

### ext:interpolation — the diagonal pair and the fibre/slice overlap

Two results promoted this tick, `exists_diagonal_weight_pair` and
`card_filter_floor_eq_le`, verified against the full corpus,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`, no warnings.

`exists_diagonal_weight_pair` is the corrected straddling pair.  From
`exists_zero_sum_combination` applied to `(1,1,1)` one gets zero-sum
coefficients `e` with `∑ e_a v_a = (1,1,1)`; with
`ε = minWeight ϑ / (maxAbs e + 1)` the vectors `ϑ ± εe` are strictly positive,
sum to one, have midpoint `ϑ`, and satisfy

    ∑_a ϑ₁_a v_{a,j} = ∑_a ϑ_a v_{a,j} + ε,    ∑_a ϑ₂_a v_{a,j} = ∑_a ϑ_a v_{a,j} - ε

for every `j`.  In exponent language: `1/p¹_j = 1/p_j + ε` and
`1/p²_j = 1/p_j - ε` uniformly in `j`, hence `1/ρ₁ = 1/R + 3ε` and
`1/ρ₂ = 1/R - 3ε`.  The ratio of the two interior bounds on a layer term is
then `(D₁/D₂) · (∏_j m_j)^{2ε}`, a function of the product of the layer
measures alone, as the plan requires.

`card_filter_floor_eq_le` is the overlap count.  The interpolation index of a
slice `N` will be `i(N) = ⌊2ε N + c₀⌋`, and since `2ε` need not be an integer
several slices share an index; the lemma bounds their number by
`1/(2ε) + 1`, by trapping the `N` in the interval
`[⌈(i - c₀)/2ε⌉, ⌊(i + 1 - c₀)/2ε⌋]` and counting with `Int.card_Icc`.  That
count is what turns the slice-wise `ℓ^R` bound of `discrete_core_le` into a
fibre-wise one, through `Real.rpow_sum_le_const_mul_sum_rpow` at exponent `R`.

An alternative was considered and set aside: re-deriving the `J`-method with a
general geometric base `2^{2ε}` would make every slice its own fibre and remove
the merging, but it means porting `primeJm_method` and its supporting chain;
the bounded merge is far cheaper.

Next: the assembly proper.  All named ingredients now exist; what remains is
to define the pieces `v_i`, verify the two weak bounds on each from the gain
lemma at `ϑ¹`, `ϑ²` and `weakNorm_sum_le_of_weak_bounds`, and feed the
`ℓ^R` profile bound — block estimate, discrete core, overlap count — into
`exists_lintegral_rpow_le_of_weak_pieces`.

### ext:interpolation — the gain dominates the block decay

Five results promoted this tick (`blockIndex`, `zpow_blockIndex_le`,
`lt_zpow_blockIndex_succ`, `log_sub_blockIndex_mem`, and the main
`exp_gain_le_block_decay`), verified against the full corpus,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`, no warnings.

`blockIndex m = Int.log 2 m` is the dyadic block of a positive layer measure,
with `2^n ≤ m < 2^(n+1)` from Mathlib's `Int.zpow_log_le_self` and
`Int.lt_zpow_succ_log_self`; `log_sub_blockIndex_mem` takes logarithms:
`log m - n log 2 ∈ [0, log 2)`.

`exp_gain_le_block_decay` connects the continuous gain from
`exists_weakNorm_expansion_term_gain_le` to the discrete decay that
`discrete_core_le` consumes.  For `m_j > 0` with blocks `n_j` and `N = ∑ n_j`,

    exp(-δ‖w‖) ≤ 2^δ · 2^(-(δ/4)|n₀-n₁|) · 2^(-(δ/4)|n₁-n₂|),

where `w = layerLogDeviation m`.  The proof: each `w_j` is within `log 2` of
`(n_j - N/3) log 2`, so the sup norm of `w` is at least
`log 2 · max_j |n_j - N/3| - log 2`; the block deviations `n_j - N/3` sum to
zero, so the max is at least a quarter of `|n₀-n₁| + |n₁-n₂|`; then exponentiate.
The `2^δ` is the price of the `log 2` slack and depends only on `δ`.

The right-hand side is exactly `2^δ · e(n₀-n₁) · e(n₁-n₂)` with
`e(t) = 2^(-(δ/4)|t|)`, whose finite sums are bounded uniformly by
`exists_sum_abs_tent_bound` — so the constant `E` of the discrete core is now
available with `c = 0`.

Next: the fibre profile lemma itself, a purely discrete statement over a
product set of heights: block decomposition of each fibre sum via the product
structure, the block estimate per slot, this decay bound, the discrete core,
and the overlap count.

### ext:interpolation — block budgets, and a check on the length of the route

Five results promoted this tick (`blockSet`, `blockBudget`, `blockBudget_nonneg`,
`blockSet_sum_le`, `sum_blockBudget_rpow_le`, `sum_product_three`), verified
against the full corpus, `[propext, Classical.choice, Quot.sound]`, zero
`sorry`.

`blockSet K m n` is the set of heights whose layer measure lies in dyadic block
`n`; `blockBudget K m p n` is the `1/p`-th power of that block's share of the
budget `∑_k (2^k)^p m(k)`.  `blockSet_sum_le` is the block estimate in these
terms, and `sum_blockBudget_rpow_le` says that when the total budget is at
most one, `∑_{n∈S} blockBudget^p ≤ 1` for every finite `S` — the blocks are
disjoint pieces of `K`, collected by `Finset.sum_fiberwise_of_maps_to`.  These
are exactly the sequences `B_j` the discrete core takes as input.
`sum_product_three` factorises a sum over a triple product of a product of
one-variable functions, which is how a block's contribution splits into three
block estimates.

**On the length of the route.**  The user asked, mid-tick, for the shortest
argument and whether the work is taking detours.  The honest assessment: the
`ℓ¹` route — strong-bound each layer term by two straddling weak bounds, then
the triangle inequality in `L^R` — is the only shorter candidate, and it is
wrong: on three equal inputs with `M` bands it gives `M^{1-1/R}`, recorded
earlier in this task.  The restricted-weak-type route of the textbooks needs
an open set of exponents in four dimensions, which the Hölder-surface
hypotheses (`1/r_a = ∑_j 1/P_{a,j}`) do not provide; the degenerate diagonal
direction is real.  So the `ℓ^R` structure through real interpolation is
necessary, and both heavy parts of it — the interpolation theorem and the
discrete core — are proved.  What remains is a fixed list:

  1. `fibre_profile_le`: for `Λ = K₀ ×ˢ (K₁ ×ˢ K₂)`, positive `m_j` with unit
     budgets, and fibres `idx(k) = ⌊ε · N(k) + c₀⌋` with `N(k) = ∑_j blockIndex(m_j(k_j))`,
     `∑_i (∑_{k∈Λ, idx k = i} ∏_j 2^{k_j} m_j(k_j)^{1/p_j} · exp(-δ‖w(k)‖))^R ≤ C(δ,ε,p,R)`.
     Proof: fibres are unions of blocks; per block, `sum_product_three` +
     `blockSet_sum_le` + `exp_gain_le_block_decay`; then
     `Real.rpow_sum_le_const_mul_sum_rpow` with `card_filter_floor_eq_le`,
     and `discrete_core_le` with `sum_blockBudget_rpow_le`.
  2. The balancing: on fibre `i`, `√(Γ¹/Γ²) ≤ 2^{i/2} · 2^{3ε+1/2}` and
     `√(Γ²/Γ¹) ≤ 2^{-i/2} · 2^{1/2}`, so `2^{-i/2} max(Γ¹(i), 2^i Γ²(i))` is at
     most a constant times the fibre sum of `G`.
  3. Weak bounds on the fibre sums, from
     `exists_weakNorm_expansion_term_gain_le` at `ϑ¹`, `ϑ²` and
     `weakNorm_sum_le_of_weak_bounds`.
  4. Glue: `trilinearOnSimple_expand_three_multiIndex` for `T f = ∑_k T(layer k)`;
     null layers are `0` a.e. (a vertex bound with a zero factor); `A_a = 0`
     gives `T f = 0` a.e.; normalisation `‖f_j‖_{p_j} = 1` by trilinearity;
     the budget `∑_k (2^k)^p m(k) ≤ ‖f‖_p^p`; and `lintegral ↔ lpNorm`.

From here the work is top-down: the final statement is written first and only
the lemmas it demands are proved.

### ext:interpolation — the fibre profile lemma

`layerSize`, `blockVec`, `fibre_profile_le` promoted; verified,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.  For
`Λ = K₀ ×ˢ (K₁ ×ˢ K₂)`, positive layer measures with unit budgets,
`∑ 1/p_j = 1/R`, `R ≥ 1`, and fibres `⌊ε N(k) + c₀⌋` with
`N(k) = ∑_j blockIndex(m_j(k_j))`, there is `C = C(δ, ε, p, R)` with
`∑_i (∑_{k ∈ Λ, fibre i} layerSize k)^R ≤ C` for every finite set of fibres.
Proof as planned: fibres are unions of blocks (`sum_fiberwise_of_maps_to`),
each block factorises (`sum_product_three`) and is bounded by
`blockSet_sum_le` and `exp_gain_le_block_decay`, the slices are merged with
`Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg` and `card_filter_floor_eq_le`,
and `discrete_core_le` with `sum_blockBudget_rpow_le` finishes.  Item 1 of the
remaining list is done; next is item 2, the balancing step.

### ext:interpolation — the balancing step

`balance_le` and `fibre_window` promoted; verified,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.  `balance_le`: two
bounds `x = D₁ G Q^ε`, `y = D₂ G Q^(-ε)` whose base-two log-ratio `L` lies in
`[i, i+1+η)` satisfy `2^(-i/2) x ≤ 2^((1+η)/2) √(D₁D₂) G` and
`2^(i/2) y ≤ √(D₁D₂) G`.  `fibre_window`: for a layer with measures
`m₀ m₁ m₂ > 0`, blocks `n_j`, `N = ∑ n_j` and fibre index `⌊2εN + c₀⌋`, the
log-ratio `c₀ + 2ε log₂(m₀m₁m₂)` lies in the window with `η = 6ε`.  Item 2 of
the remaining list is done; next are item 3 (weak bounds on fibre sums) and
the top-level assembly.

### ext:interpolation — assembly preparations

`exists_diagonal_weight_pair_le`, `lpNorm_le_of_lintegral_rpow_le`,
`sum_zpow_rpow_mul_toReal_le` promoted; verified,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.  The first shrinks the
diagonal shift below any prescribed `ε₀` (needed so that both perturbed output
exponents stay above one); the second converts the layer-cake bound
`∫ |g|^R ≤ C` into `lpNorm g R μ ≤ C^{1/R}` (trivial when `g` is not
a.e.-strongly measurable, since `lpNorm` is then `0`); the third is the layer
budget `∑_k (2^k)^p μ(level k) ≤ ‖f‖_p^p` in real form.

Two decisions for the assembly: the final theorem assumes `[SigmaFinite μ]`
(needed by `weakNorm_le_weakNormPrime`; the downstream use is Lebesgue measure
on `E3`, which is σ-finite), and it is first proved for inputs normalised to
`lpNorm ≤ 1`, the general case following by trilinearity — normalising the
measures instead is not available because the gain is not invariant under
rescaling a single slot.  Next: the assembly theorem itself.

### ext:interpolation — the fibre assembly (item 3 done)

`fibre_profile_le_uniform`, `layerProd`, `layerSize_pos`, `layerProd_pos`, and
the main `lintegral_rpow_sum_le_of_layer_weak_bounds` promoted; verified,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.  The uniform variant
of the fibre profile lemma pulls its constant in front of the data (the proof
was already data-free in the constant).  The main theorem is the
operator-free assembly: for exponents `p_j, R` with `∑ 1/p_j = 1/R`, `R > 1`,
straddling `ρ₁, ρ₂` with `1/ρ₁ = 1/R + 3ε`, `1/ρ₂ = 1/R - 3ε`, both above one,
and constants `D₁, D₂, δ`, there is `C` such that for every product set of
heights with positive layer measures and unit budgets, and every family of
measurable layer terms `u k` with

    ‖u k‖_{ρ₁,∞} ≤ D₁ · layerSize k · (m₀m₁m₂)^ε,
    ‖u k‖_{ρ₂,∞} ≤ D₂ · layerSize k · (m₀m₁m₂)^(-ε),

one has `∫ |∑_k u k|^R dμ ≤ C`.  Proof: pieces `v_i` are fibre sums with
fibre index `⌊2ε N(k) + c₀⌋`, `c₀ = log₂(D₁/D₂)`; weak bounds on the pieces
from `weakNorm_sum_le_of_weak_bounds` (tail pieces get explicit summable
bounds); `balance_le` with `fibre_window` turns the `J`-method profile into
the fibre profile; `fibre_profile_le_uniform` bounds it; and
`exists_lintegral_rpow_le_of_weak_pieces` finishes.  Remaining: the operator
part — the two gain bounds at `ϑ₁, ϑ₂` in exactly this form, the expansion
`T f = ∑_k T(layer k)`, null layers and `A_a = 0`, normalisation, `lpNorm`.

### ext:interpolation — the per-layer bounds in assembly form

`layerMeasure`, `layerTerm`, `exists_layer_weak_bound_gain_form` promoted;
verified, `[propext, Classical.choice, Quot.sound]`, zero `sorry`.  At an
interior weight `ϑ'` whose input reciprocals are `1/p_j + s`, the layer term
`T(layer k)` has weak norm at the output exponent bounded by
`8 · ∏ A_a^{ϑ'_a} · C_weights_shift A · layerSize k · (m₀m₁m₂)^s`, for every
gain parameter `δ'' ≤ δ'` — exactly the hypothesis shape of
`lintegral_rpow_sum_le_of_layer_weak_bounds`, with `s = ±ε` at `ϑ¹, ϑ²`.  The
proof is `exists_weakNorm_expansion_term_gain_le` plus the exponent algebra
`∏ 2^{k_j+1} m_j^{1/p_j+s} = 8 ∏ 2^{k_j} m_j^{1/p_j} · (∏ m_j)^s`.  Next: the
normalised main theorem.

### ext:interpolation — null layers and the a.e. expansion

`ae_eq_zero_of_weakNorm_eq_zero`, `lpNorm_dyadicLevelPiece_eq_zero`,
`layerTerm_ae_zero_of_null`, `positiveLayerIndices`, `ae_sum_eq_zero`,
`ae_eq_sum_layerTerm_positive` promoted; verified,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.  A layer whose level
set is null has a null layer piece, so any vertex bound forces the layer term
to vanish a.e.; hence `T f =ᵐ ∑_{k ∈ Λ} T(layer k)` with `Λ` the product of the
positive-measure heights — the set the fibre assembly works on.  Remaining:
the normalised main theorem (diagonal pair, two gain-form bounds, fibre
assembly, `lpNorm`), then the trilinearity wrapper and degenerate cases.  Note
for the wrapper: the fibre assembly needs the layer terms measurable, which the
recorded hypothesis does not supply; the main theorem will carry a
measurability hypothesis on `T` and this will be recorded.

### ext:interpolation — the normalised main theorem

`exists_lintegral_rpow_le_of_normalized` promoted; verified,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.  Under the blueprint
hypotheses with `0 < A a`, `[SigmaFinite μ]`, and measurable outputs
`T (simple triple)`, there is `C` such that every triple of simple functions
of finite measure support with `lpNorm ≤ 1` satisfies
`∫ |T f|^R dμ ≤ C`.  The proof: the diagonal pair with shift
`ε ≤ min((1-1/R)/6, 1/(6R))` gives `ρ₁, ρ₂ > 1` with `1/ρ₁ = 1/R + 3ε`,
`1/ρ₂ = 1/R - 3ε`; the two gain-form layer bounds at `ϑ ± εe` with the common
gain `min δ₁ δ₂`; the layer measures are cut off to `1` outside the positive
heights so the fibre assembly's positivity hypothesis holds; budgets from
`sum_zpow_rpow_mul_toReal_le` and `lpNorm ≤ 1`; `T f =ᵐ ∑_Λ T(layer)` from
`ae_eq_sum_layerTerm_positive`; and `lintegral_rpow_sum_le_of_layer_weak_bounds`
finishes.  Remaining: the wrapper to the recorded statement — `A_a = 0`
(then `T f = 0` a.e.), normalisation by trilinearity, and `lpNorm ≤ C^{1/R}`.

### ext:interpolation — the per-operator statement is proved

`finMeasSupp_smul`, `trilinearOnSimple_smul_three`,
`lpNorm_eq_zero_of_weakNorm_le_zero`, and `fourVertexMarcinkiewicz_of_measurable`
promoted; verified, `[propext, Classical.choice, Quot.sound]`, zero `sorry`.
The last of these proves `FourVertexMarcinkiewicz μ T` — the recorded
per-operator form of `ext:interpolation`, verbatim — for every σ-finite `μ` and
every `T` with measurable outputs on simple triples.  The wrapper handles the
degenerate case `A_a = 0` (the output vanishes a.e., so `lpNorm = 0`), inputs
with `lpNorm = 0` (likewise), and otherwise normalises the inputs to unit norm,
applies `exists_lintegral_rpow_le_of_normalized`, and undoes the scaling by
`trilinearOnSimple_smul_three`.

Status.md now records the item as partially proved.  What is still open is the
uniform form `FourVertexMarcinkiewiczUniform`, which `thm:main` consumes:
(a) uniformity in `T` — a quantifier reordering in
`exists_weakNorm_expansion_term_gain_le` and
`exists_layer_weak_bound_gain_form`, whose `δ` depends only on the exponent
data; (b) `MemLp (T f) R` — from measurability and the bound; (c) uniformity
in `A` — the substantive item, see ErrorReport for the plan: fold `log A` into
the deviation as a shift `ℓ_A` of the log-measures, run blocks and fibres on
`m_j e^{(ℓ_A)_j}`, and let the reciprocal constants at the two interpolation
points cancel in the geometric mean.  Order of work: (a), (b), then (c).

### ext:interpolation — uniformity in the operator

`exists_weakNorm_expansion_term_gain_le_uniform`,
`exists_layer_weak_bound_gain_form_uniform`, and
`exists_lintegral_rpow_le_of_normalized_uniform` promoted; verified,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.  These are the
promoted proofs with the operator quantified after the constant: the gain
`δ` comes from `exists_face_gain` and depends only on the exponent data, so
for fixed endpoint constants `A` a single `C` now serves every trilinear `T`
with measurable outputs and the four weak bounds.  Item (a) of the uniform
form is done.  Next: (b) `MemLp` of the output, then (c) uniformity in `A`.

### ext:interpolation — towards uniformity in the endpoint constants

`discrete_core_le_pair`, `memLp_of_lintegral_rpow_le`, `exists_face_gain_shift`,
`exp_shift_le_block_decay` promoted; verified,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.

The obstruction to uniformity in `A` is the factor `C_weights_shift A`, paid
when the interpolation weights move off `ϑ`.  The remedy is not to bound that
factor but to fold it into the *centre* of the decay, which the summation
lemmas already handle uniformly (`exists_sum_abs_tent_bound` takes an
arbitrary centre, and so does `card_filter_floor_eq_le`).

`exists_face_gain_shift` does this at the source.  For any vector `ã` of
endpoint logarithms it produces `δ > 0` and centres `c₁, c₂` — depending on
the vertices, the weights and `ã` — such that for every position `ℓ` some face
weight `ϑ'` satisfies

    ∑_a ϑ'_a (ã_a + ⟨ℓ, v_a - x⟩) ≤ ∑_a ϑ_a ã_a - δ(|ℓ₀-ℓ₁-c₁| + |ℓ₁-ℓ₂-c₂|).

The centres are `c_i = -∑_a (e_i)_a ã_a`, the pairing of `ã` with the two
tangent directions; no constant depending on `A` appears.  The statement is
also simpler than the norm-based `exists_face_gain` it replaces: the gain is
expressed directly in the two coordinate differences the block machinery
consumes, so `layerLogDeviation` and its norm drop out of the chain.

`exp_shift_le_block_decay` is the matching block comparison:
`exp(-δ|log m₀ - log m₁ - c|) ≤ 2^δ · 2^(-δ|n₀ - n₁ - c/log 2|)` with
`n_j = blockIndex m_j`, replacing `exp_gain_le_block_decay`.
`discrete_core_le_pair` is the discrete core with two independent decay
weights, needed because the two centres differ.  `memLp_of_lintegral_rpow_le`
discharges item (b) of the uniform form.

Next: re-derive the layer bound, `layerSize`, the fibre profile and the
assembly with the two centres carried through, then the uniform wrapper.

### ext:interpolation — canonical decay centres

`exists_face_gain_shift_of` and `exists_weakNorm_expansion_term_gain_shift_of`
promoted; verified, `[propext, Classical.choice, Quot.sound]`, zero `sorry`.

A subtlety surfaced while planning the assembly.  The two interpolation points
`ϑ₁, ϑ₂` each need a per-layer bound, and the fibre index is the log-ratio of
the two bounds; for that ratio to be a function of the layer measures alone,
the two bounds must carry the *same* decay factor, hence the same centres.
The centres produced by `exists_face_gain_shift` are
`c_i = -∑_a (e_i)_a log A_a`, which depend only on the vertex data and `A` —
not on the base weight — but the lemma obtains `e₁, e₂` internally, so two
applications yield formally unrelated centres.

The fix is to take the tangent directions as inputs.  `exists_face_gain_shift_of`
and `exists_weakNorm_expansion_term_gain_shift_of` are the same results with
`e₁, e₂` (and their defining properties `∑ e_i = 0`,
`∑_a (e_i)_a v_a = (1,-1,0)`, `(0,1,-1)`) as hypotheses, so the caller obtains
them once from `exists_zero_sum_combination` and passes them to both
applications, getting literally the same centres.  Only `δ` differs between
the two, and the minimum of the two serves both.

Next: `layerSizeC` with the two centres, the assembly-form layer bound, and
the centred fibre profile.

### ext:interpolation — the centred fibre profile

`layerSizeC` and `fibre_profile_le_centred` promoted; verified,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.  `layerSizeC` is the
layer size with the two-centre gain
`exp(-δ|log m₀ - log m₁ - c₁|) · exp(-δ|log m₁ - log m₂ - c₂|)`, and
`fibre_profile_le_centred` is the fibre profile bound for it, with a constant
depending only on `δ, ε, p, R` — not on the centres, because
`exists_sum_abs_tent_bound` is centre-uniform and
`discrete_core_le_pair` accepts the two different decays.  This is the step
where uniformity in `A` is actually secured: all dependence on the endpoint
constants sits in `c₁, c₂`, which the bound does not see.

### ext:interpolation — the centred chain reaches the assembly

`layerSizeC_pos`, `lintegral_rpow_sum_le_of_layer_weak_bounds_centred` and
`exists_layer_weak_bound_gain_shift_form` promoted; verified,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.  The centred chain is
now complete from the face gain to the fibre assembly: per-layer bound with
canonical centres, layer size with the two-centre gain, fibre profile whose
constant does not see the centres, and the assembly theorem taking the centres
as parameters.  All that remains is to re-run the normalised main theorem and
the wrapper on the centred chain, with `e₁, e₂` obtained once and shared
between the two interpolation points, and then to assemble
`FourVertexMarcinkiewiczUniform`.

### ext:interpolation — the endpoint constants leave the interpolation constant

`fibre_profile_le_centred_uniform` and
`lintegral_rpow_sum_le_of_layer_weak_bounds_uniform` promoted; verified,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.

Two quantifier moves finish the uniformity argument at the assembly level.
The fibre offset `c₀` moves inside the universal quantifier (the profile
constant never mentioned it).  The endpoint scales `D₁, D₂` do the same, and
the conclusion becomes

    ∫ |∑_k u k|^R dμ ≤ C · (D₁ D₂)^(R/2)

with `C` depending only on the exponents, `ε` and the gain.  Two places had to
change for that: the artificial values given to the tail fibres — those outside
the range of the fibre index, which only have to be positive and summable — are
now scaled by `κ = (D₁D₂)^(1/2)`, so that the whole profile bound is
homogeneous of degree one in `κ`; and the balancing constant `c₃` is split as
`c₃' · κ` with `c₃'` free of `D`.  Then `BwR = κ^R · B₀` exactly.

This is what makes the final constant uniform in `A`: at the call site
`D₁ D₂ = 64 ∏_a A_a^(ϑ₁+ϑ₂) = 64 (∏_a A_a^(ϑ_a))²`, so `(D₁D₂)^(R/2)` is
`8^R (∏_a A_a^(ϑ_a))^R` — the bound the blueprint asks for, with no other
dependence on the endpoint constants.

### ext:interpolation — the gain chain becomes uniform in the endpoint constants

`exists_face_gain_shift_unif`, `exists_weakNorm_expansion_term_gain_shift_unif`
and `exists_layer_weak_bound_gain_shift_unif` promoted; verified,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.  These are the three
gain lemmas with the endpoint data quantified after the gain: the gain `δ` is
`minWeight ϑ / (max(maxAbs e₁, maxAbs e₂) + 1) / 2`, which mentions only the
vertices and the weights, so `ã` (and hence `A`) can be moved inside the
universal quantifier.  The one real edit was in the face lemma, where the
perturbation identity had to be generalised over `ã` as well, since it is
proved before `ã` is introduced.

With this the whole chain — face gain, layer bound, layer bound in assembly
form, fibre profile, fibre assembly — has its constants free of `A`.  What
remains is to re-run the normalised theorem and the wrapper on it and to
assemble `FourVertexMarcinkiewiczUniform`.

### ext:interpolation — the normalised bound is fully uniform

`fibre_profile_le_full_uniform`, `lintegral_rpow_sum_le_of_layer_weak_bounds_full`
and `exists_lintegral_rpow_le_of_normalized_full` promoted; verified,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.

The first two move the decay centres inside the universal quantifier, the last
is the normalised theorem on the fully uniform chain.  Its statement: for the
exponent data alone there is `C` such that for *every* positive endpoint vector
`A`, every trilinear `T` with measurable outputs satisfying the four weak
bounds, and every triple of simple functions of unit norm,

    ∫ |T f|^R dμ ≤ C · (∏_a A_a^(ϑ_a))^R.

The `A`-dependence collapses exactly: the two interpolation points give
`D₁ D₂ = 64 ∏_a A_a^(ϑ₁+ϑ₂) = 64 (∏_a A_a^(ϑ_a))²` because `ϑ₁ + ϑ₂ = 2ϑ`, so
`(D₁D₂)^(R/2) = 8^R (∏_a A_a^(ϑ_a))^R`, and the centres `d₁, d₂` — the only
other place `A` enters — are invisible to the constant.

Next: the wrapper, and `FourVertexMarcinkiewiczUniform`.

### ext:interpolation — the uniform reading is proved

`exists_fourVertex_uniform_bound_of_measurable` promoted; verified,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`.  It is the body of
`FourVertexMarcinkiewiczUniform μ` with a measurability hypothesis on the
operator: for σ-finite `μ` and exponent data satisfying the blueprint's
conditions there is one constant `C₀^(1/R)` such that every vector of
endpoint constants `A ≥ 0`, every trilinear `T` with measurable values on
simple triples and the four weak bounds, and every triple of simple functions
of finite measure support satisfy

    MemLp (T f) R μ  and  ‖T f‖_R ≤ C · ∏_a A_a^(ϑ_a) · ∏_j ‖f_j‖_{p_j}.

The proof is the per-operator wrapper on the fully uniform chain: degenerate
`A_a = 0` and degenerate inputs give an a.e.-zero output, and otherwise the
inputs are normalised, `exists_lintegral_rpow_le_of_normalized_full` gives
`∫|T g|^R ≤ C₀ (∏ A^ϑ)^R`, `memLp_of_lintegral_rpow_le` gives membership,
`lpNorm_le_of_lintegral_rpow_le` gives the norm bound, and
`trilinearOnSimple_smul_three` undoes the normalisation.

Status.md and ErrorReport.md record the two hypotheses — σ-finiteness and
measurability — and why the second cannot be dropped: the `MemLp` conjunct is
false for an operator with non-measurable output, so the recorded statement
needs it.  Both hold for the intended application.

### ext:interpolation — closed

`FourVertexMarcinkiewiczUniformMeasurable`,
`fourVertexMarcinkiewiczUniformMeasurable_of_sigmaFinite` and
`fourVertexMarcinkiewicz_of_uniformMeasurable` promoted; verified,
`[propext, Classical.choice, Quot.sound]`, zero `sorry`, and `lake build`
completes.  The first packages the uniform reading as a named predicate, the
second proves it outright for every σ-finite measure — no hypothesis remains
beyond σ-finiteness and the operator's measurability — and the third recovers
the per-operator form.

Both external theorems of the task are now formalized: `ext:maximal` earlier,
and `ext:interpolation` here.  The corpus has no `sorry` and no axioms beyond
`propext`, `Classical.choice`, `Quot.sound`.

The one thing not done, and it is plumbing rather than mathematics: the
downstream theorems take `hU : FourVertexMarcinkiewiczUniform volume` as a
hypothesis, and that predicate is the one shown in ErrorReport to be false
without a measurability hypothesis.  Connecting them to the proved theorem
means changing those hypotheses to
`FourVertexMarcinkiewiczUniformMeasurable` and supplying, at each use, the
measurability of the concrete operator `U^{a,b}_{u,c}` — an edit to existing
statements, with one genuine obligation per use site.

### ext:interpolation — the hypothesis is discharged downstream, and thm:main is unconditional

The plumbing is done and the build is clean.  Three changes, all to statements
already in the corpus rather than to proofs:

The eleven hypotheses `hU : FourVertexMarcinkiewiczUniform ...` now read
`FourVertexMarcinkiewiczUniformMeasurable`, and the definition was moved to sit
beside the original so that it precedes its uses.  The one theorem that mirrors
the predicate's shape, `exists_strong_bound_at_simplex_interior_uniform`, gains
the same measurability arrow; everything else merely threads `hU`, so nothing
else in those statements changed.

The single place where the predicate is applied to a concrete operator is
`exists_ModelTruncatedOperator_extended_strong_bound`, and the obligation is
discharged outright by `measurable_ModelTruncatedOperator_of_measurable`, which
was already in the corpus — the truncated model operator is measurable, not
merely a.e.-measurable, for measurable inputs.  So the extra hypothesis costs
nothing downstream.

`fourVertexMarcinkiewiczUniformMeasurable_volume_E3` then discharges `hU` for
Lebesgue measure on `E3` (σ-finiteness is found by instance search), and

    anisotropicParaproduct_unconditional

is `thm:main` with no hypotheses beyond the exponent conditions:
`|Λ_m(f)| ≤ C_{α,p} M ∏_j ‖f_j‖_{p_j}`.  It was previously
`anisotropicParaproduct_of_interpolation`, conditional on `ext:interpolation`.

Final state of the task: both external theorems proved, `lake build` completes,
zero `sorry`, axioms `[propext, Classical.choice, Quot.sound]` throughout.
