

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
