

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
