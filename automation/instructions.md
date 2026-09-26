# Autoformalization instructions

## Operative user request

Recorded 2026-09-10T09:42:06.7141336-04:00; exact prompt: [raw.md](raw.md).
Prepare this repository for four assigned formalization tasks, as specified in
[tasks.md](tasks.md), and vendor both autoformalize skill editions.
This setup request does not start the mathematical formalization.

The current explicit user instructions take precedence over these instructions,
which supersede conflicting generic skill guidance.

## Scope and workflow

The canonical generated-source directory in this repository is `DFR/Auto/`. Reuse its four existing task subdirectories. Do not create a repository-root `Auto/` directory. Keep the Lean namespace `Auto`; filesystem location and namespace are separate. Verify Task 1 with `lake env lean DFR/Auto/SmoothingIneq2D/Smoothing2D.lean` and preserve the existing Lake configuration.

- Every proof agent must have exactly one task assignment before editing.
  Follow the assignment and readiness protocol in tasks.md.
- All mathematical code, helpers, experiments, and task-specific working files
  must stay inside that task's assigned subfolder of the existing DFR/Auto directory. This explicitly overrides
  the skill's default single file for the whole project and its exception placing
  reusable prerequisites directly in DFR/Auto/. Keep such prerequisites inside the
  owning task folder instead. Task 1 work belongs mainly in Smoothing2D.lean.
- Shared administrative records live in automation/ as required by the skill.
  The coordinator maintains shared records from workers' reports; workers must
  not race to edit these files. Blueprints supplied by the user live in blueprints/.
- Preserve existing DFR files, public statements, dependency pins, and other
  tasks' files. Request coordination for changes outside the assigned folder.
  Reading other tasks and importing their proved results is allowed; avoid cycles.
- Use namespace Auto and source-based declaration names; coordinate names across
  tasks. Use the appropriate edition's generation notice and standard Lean header.
  Existing Git attribution establishes the user's name as Joris Roos; LICENSE is
  Apache 2.0.
- Do not invent missing blueprint statements or introduce sorry, admit, or new
  mathematical axioms. Missing source material blocks its task.
- Task 4 must not begin proof planning, statement scaffolding, or implementation
  until Tasks 1-3 pass the completion gate in tasks.md and its blueprint is present.
- No commits, staging, pushes, or edits to globally installed skills are requested.

## Skills and records

Codex: .codex/skills/autoformalize/SKILL.md.
Claude: .claude/skills/autoformalize/SKILL.md.
Both are vendored copies with supporting assets and references. Future edits to
either repository-local edition must update the paired repository-local edition,
preserving client-specific differences; do not modify global installations.
Read Status.md and ErrorReport.md before resuming. Follow the skill's timestamp,
prompt logging, source-fidelity, forward proof order, and axiom-audit requirements.
Apply proof order separately inside each assigned task; independent ready Tasks
1-3 may be assigned to different agents.

## Reuse prerequisites from lean-spherical

User direction recorded 2026-09-10T09:48:18.6199420-04:00; exact prompt: [raw.md](raw.md).

Before developing any prerequisite theorem, agents must search the pinned
lean-spherical dependency as well as Mathlib and this repository. Inspect
.lake/packages/lean_spherical/LeanSpherical/ for existing results and equivalent
formulations, read their actual hypotheses and conclusions, and reuse them where
applicable rather than duplicating their proofs.

Concrete starting points (Lean module names):

- Stein interpolation: LeanSpherical.Auto.SteinInterpolation.
- Marcinkiewicz interpolation: LeanSpherical.Auto.Spherical.Auxiliary; search
  marcinkiewicz_* declarations, including marcinkiewicz_weak_one_two and
  marcinkiewicz_weak_one_top, and check the range needed for the application.
- Littlewood-Paley theory: LeanSpherical.Auto.LittlewoodPaley. This theory will
  be needed; check its available decompositions and estimates before building
  new ones.
- Hardy-Littlewood maximal function: LeanSpherical.Auto.HardyLittlewoodMaximal.

For multilinear interpolation, first investigate deriving the required result
from the existing interpolation machinery. The user expects this to be relatively
easy; treat that as a suggested proof route, not an already established theorem.
Identify and prove any missing multilinear extension or application bridge with
the exact hypotheses and parameter ranges required by the source.

Record the reused declarations and any remaining gaps in the task's continuation
notes. Audit their transitive axioms before relying on them for completion.
Keep new extensions and bridges inside the assigned task folder; preserve the
pinned dependency and do not edit its checkout.

## Sources and build

Task 1: Theorem 5 of https://arxiv.org/abs/2008.10140.
The linked page currently identifies version v2 (14 November 2020); use
https://arxiv.org/abs/2008.10140v2 as the reproducible starting version.
Before formalizing, read and verify the exact theorem and its proof, then record
the source locations and dependency plan. No statement has been translated yet.
Tasks 2-4: discover the corresponding user-provided blueprint in blueprints/
when it arrives and record its filename/version; do not guess its contents.

Preserve leanprover/lean4:v4.33.0-rc1 and the lean_spherical revision in
lakefile.toml/lake-manifest.json (Mathlib is transitive).
Run lake build from the repository root for the configured project targets. Keep Auto out of lakefile.toml; verify Auto sources separately with lake env lean.
For direct source verification use lake env lean DFR/Auto/SmoothingIneq2D/Smoothing2D.lean
(or the assigned task's actual file). Audit completed target declarations with
#print axioms; allowed axioms are propext, Classical.choice, and Quot.sound only.

## Next step

Task 1 is complete: Auto.smoothing_theorem5 in DFR/Auto/SmoothingIneq2D/Smoothing2D.lean proves the exact source trilinear bound, with both time signs and the printed Sobolev half-exponents. All six permanent sources pass direct checks; lake build passes; the final transitive axiom audit contains only propext, Classical.choice, and Quot.sound. See Status.md for source mappings and verification evidence. The final proof commit and publication are authorized by the user. Pushing task-1 to https://github.com/roos-j/lean-dfr remains pending explicit destination confirmation required by automatic approval review; do not bypass that rejection. Tasks 2-3 await blueprints, and Task 4 also awaits their completion gate. Do not start another proof task without its assignment and source.
## LaTeX build artifacts

User direction recorded 2026-09-10T09:48:56.6842063-04:00; exact prompt: [raw.md](raw.md).
Keep standard LaTeX auxiliary/build artifacts ignored in the root .gitignore.
Preserve trackability of .tex, .bib, and source PDFs.

## Task folder READMEs

User direction recorded 2026-09-10T09:53:04.4384248-04:00; exact prompt: [raw.md](raw.md).
Remove the README.md files from the four Auto task folders; do not recreate them.

## Start Task 1

Recorded 2026-09-10T09:56:31.1092542-04:00 (recording time); exact prompt: [raw.md](raw.md).
The user requests /autoformalize task 1. Begin Task 1 source study and formalization within DFR/Auto/SmoothingIneq2D/. Existing task boundaries and completion criteria apply.

## Auto verification policy

Recorded 2026-09-10T09:58:01.5996155-04:00 (recording time); exact prompt: [raw.md](raw.md).
The user requires that lakefile.toml not include Auto and that all instructions requiring that inclusion be removed. Check each owned Auto source directly with lake env lean and run lake build separately for the configured project targets. Do not add an Auto library, target, glob, or root import to obtain build coverage.

## Pause Task 1

Recorded 2026-09-10T09:58:47.5716059-04:00 (recording time); exact prompt: [raw.md](raw.md).
After removing the Auto inclusion instructions, pause before continuing Task 1. The requested instruction cleanup is complete. Do not resume mathematical work until the user directs it.

## Commit authorization

Recorded 2026-09-10T09:59:38.4628987-04:00 (recording time); exact prompt: [raw.md](raw.md).
The user authorizes committing the pending instruction cleanup and Task 1 pause records. Task 1 remains paused; no push is requested.

## Resume Task 1

Recorded 2026-09-10T11:01:54.9581411-04:00 (recording time); exact prompt: [raw.md](raw.md).
The user requests /autoformalize task 1. Resume Task 1 source audit and formalization in DFR/Auto/SmoothingIneq2D/Smoothing2D.lean. This supersedes the prior pause. No commit or push is requested.

## Continue Task 1 to completion

Recorded 2026-09-10T12:42:17.1154681-04:00 (recording time); exact prompt: [raw.md](raw.md).
Continue autoformalizing Task 1 until every source target and prerequisite is completely proved and verified. Do not stop at supporting lemmas, partial progress, or build milestones. Existing source-fidelity, task boundaries, no-placeholder policy, and completion gate remain in force.

Recorded 2026-09-10T12:44:37.8315626-04:00 (recording time); exact prompts: [raw.md](raw.md). The user requires a granular Status.md ledger whose rows correspond to actual source equations or identifiable unnumbered source steps. Do not invent proof steps or count implementation helpers as source milestones. Continue Task 1 through full completion after updating the ledger.

Recorded 2026-09-10T12:45:58.7354373-04:00 (recording time); exact prompts: [raw.md](raw.md). The user reiterates logical forward reasoning order and requires rereading the instructions. Finish the earliest unfinished source argument and all its prerequisites before advancing. Maintain source-based ledger rows in dependency order; preserve already proved supporting lemmas without treating their existence as completion of an earlier missing source argument.

2026-09-10T15:02:01.6771576-04:00 - User renews the instruction to complete Task 1 without stopping. In the context of the pending correction question, proceed with the documented corrected refinement; preserve the main theorem and record the actual proof and constants. Exact prompt in raw.md.

2026-09-10T15:41:20.7697427-04:00 - The latest user instruction prohibits a separate fix commit and reiterates logical forward reasoning order, not source presentation order. Continue Task 1: close prerequisites before consumers and do not stop at acknowledgments. The two dyadic-volume proof errors are fixed and direct Lean verification passes. No further commit is authorized by the latest instruction.

2026-09-10T18:09:12.2173105-04:00 - User requests committing the accumulated verified work, then continuing Task 1 until completion. This authorizes one progress commit and supersedes the earlier prohibition on further commits. Continue in logical forward reasoning order after committing; no push requested. Exact prompt in raw.md.

2026-09-10T18:23:34.428125-04:00 - User corrects the erroneous root Auto layout. Relocate each branch's own task files into existing DFR/Auto directories and correct both vendored skill editions and task records. Apply only layout/instruction changes to main and Tasks 2-4; do not transfer Task 1 proof work. This correction supersedes conflicting earlier folder instructions.

2026-09-10T18:25:27.198580-04:00 - User explicitly requests pushing the layout correction so the remote is current on every branch. Publish the branch-specific correction on main and task-1 through task-4, preserving each branch's own mathematical content. The erroneous repository-root Auto directory is removed after relocating its files.

2026-09-10T18:27:16.5279448-04:00 - User resumes Task 1 through completion after the layout correction. Work only in DFR/Auto/SmoothingIneq2D and the shared automation records; preserve logical forward reasoning order. The earlier layout commits and pushes are complete; no additional Git publication is requested by this resumption.

2026-09-11T06:41:05.8693067-04:00 - User explicitly requests committing and pushing the accumulated verified Task 1 work now, then continuing until Task 1 is fully complete, followed by a final commit and push. This supersedes earlier no-publication instructions. Publish only task-1; preserve other branches. Exclude the unfinished scratch proof from the progress commit. Exact prompt recorded in raw.md.


2026-09-11T20:29:50.090032-04:00 - Clean up Lean-folder logs and unnecessary #print commands; fix warnings without disabling linters. Move the five prerequisite modules to DFR/Auto, overriding the old task-folder restriction. Preserve theorem statements and Lake configuration. No commit or push requested.
## Start Task 2

Recorded 2026-09-11T12:07:01.6923837-04:00 (recording time); exact prompt: [raw.md](raw.md).
The user invokes /autoformalize and assigns Task 2, the 3d smoothing inequality.
Begin Task 2 source study and formalization within DFR/Auto/SmoothingIneq3D/,
using blueprints/task_2_smoothingineq3d_blueprint.tex. Existing task boundaries,
namespace/header conventions, verification policy, and completion criteria apply.

## Continue Task 2 to completion (looped)

Recorded 2026-09-11T12:09:38-04:00 (recording time); exact prompt: [raw.md](raw.md).
The user requests a 15-minute /loop: continue working until Task 2 is completely
finished. Do not stop at milestones or partial progress; keep advancing Task 2
in forward dependency order until its completion gate in tasks.md is met.
The skill's mandatory stop for a discrepancy requiring a change to a main result
still applies.

## Resolution of the Task 2 import boundary

Recorded 2026-09-11T16:46:20-04:00 (recording time); exact prompt: [raw.md](raw.md).
The user resolves the open scope question on the three modules that
blueprints/task_2_smoothingineq3d_blueprint.tex imports by citation rather than proof
(`thm:kosz-adjoint`, the scale-one estimate behind `thm:kosz-subunit`, and
`thm:quasi-interpolation`).

Each import must be stated as a named Prop and threaded as an explicit hypothesis through every
downstream result, up to and including `thm:main`. No `axiom`, no `sorry`, no `admit`: the
`#print axioms` audit must still show only propext, Classical.choice and Quot.sound. The target
`thm:main` is therefore proved conditionally on exactly the blueprint's three stated imports,
which may be discharged later. This is an explicit, user-authorized exception to the literal
"all targets proved" wording of the Task 2 completion gate in tasks.md; the gate's prohibitions
on sorry, added axioms, weakened targets and placeholders remain in force, and the imports must
be named and documented rather than hidden.

The user also directs that the recurring 15-minute job continue running.

## Updated blueprint: the three imports become proof obligations

Recorded 2026-09-11T18:44:08-04:00 (recording time); exact prompt: [raw.md](raw.md).
The operative source for Task 2 is now
[blueprints/task_2_smoothingineq3d_blueprint_updated.tex](../blueprints/task_2_smoothingineq3d_blueprint_updated.tex)
(2626 lines, 101237 bytes, MD5 6795374a15cd47616798ebb82058f25d). The earlier
task_2_smoothingineq3d_blueprint.tex (1637 lines, MD5 ccd112efd5c27774665abd555a904076) is
superseded; it remains in the folder as the historical version.

The updated document keeps the original text as its first 1638 lines and appends four sections:
`sec:expanded-closure`, `sec:internal-gm`, `sec:internal-kosz-improving`,
`sec:internal-kosz-adjoint`, and `sec:lean-dependency-map`. Its
`prop:no-imported-analytic-declarations` states the new policy explicitly: `thm:kosz-adjoint`,
`thm:kosz-subunit` and `thm:quasi-interpolation` are NOT axioms, hypotheses, opaque constants or
foreign declarations; a Lean file generated from the document must contain no `axiom` at those
nodes and no `sorry` in their proofs. This supersedes the user decision of
2026-09-11T16:46:20-04:00 that allowed carrying them as hypotheses, and supersedes
`rem:formalization-boundary` of the original document.

The document supplies the implementation order in `prop:acyclic-implementation-order`:
(1) `lem:scalar-strip`, `lem:lebesgue-strip`; (2) measurable refinements, the real flow, the area
formula, `prop:restricted-improving-vertex`; (3) finite Marcinkiewicz interpolation, duality,
`cor:kosz-53-internal`, `cor:kosz-subunit-internal`; (4) Fejer differences, PET recursion,
polynomial oscillation, degree lowering, `thm:real-inverse`; (5) Hahn-Banach separation,
projection kernels, compact decay, support removal, `thm:kosz-613-internal`; (6) the normalized
smoothing and main-proof sections, which are already written.

The existing Lean development is preserved and remains valid: every downstream result is already
parameterized by the three statements `Auto.KoszAdjoint`, `Auto.KoszSubunitScaleOne` and
`Auto.QuasiInterpolation` as explicit hypotheses, so proving those three Props discharges every
hypothesis and makes the whole chain unconditional with no restructuring.

## Pause, 2026-09-11T22:46:45-04:00

The user paused the effort: "Pause the formalization. We will resume tomorrow."

Operative effect: stop proof work now and do not resume automatically. The recurring 15-minute
job `aab1caf5` created on 2026-09-11T16:07:xx-04:00 has been cancelled, because it would
otherwise have fired again within fifteen minutes and restarted the work against this
instruction. It was a session-only job, so it would not have survived the session in any case.

This supersedes only the automatic continuation. Everything else stands: the scope is still Task
2 from blueprints/task_2_smoothingineq3d_blueprint_updated.tex, the owned files are still
DFR/Auto/SmoothingIneq3D/Smoothing3D.lean and the reusable prerequisite
DFR/Auto/HirschmanLemma.lean, and the implementation order of
`prop:acyclic-implementation-order` is unchanged. On resumption, recreate a recurring job only if
the user asks for one again.

## Resume, 2026-09-12T10:25:57-04:00

The user resumed the effort: "Resume the autofomalization with the cron job".

Operative effect: lift the pause of 2026-09-11T22:46:45-04:00 and continue proof work, with a
recurring job restored. Job `1ea6aa5a` was created on the schedule `3,18,33,48 * * * *` (the same
fifteen-minute cadence as the cancelled `aab1caf5`, offset off the :00 and :30 marks). It is
session-only and auto-expires after seven days.

Scope is unchanged: Task 2 from blueprints/task_2_smoothingineq3d_blueprint_updated.tex, owned
files DFR/Auto/SmoothingIneq3D/Smoothing3D.lean and the reusable prerequisite
DFR/Auto/HirschmanLemma.lean, implementation order of `prop:acyclic-implementation-order`.

## 2026-09-12T15:45:49-04:00 - Ledger granularity

`automation/Status.md` must carry **one line per source item**: every definition, equation,
step, lemma, proposition, theorem and corollary of the blueprint gets its own ledger row.  The
rows are ordered by **strict forward reasoning order** -- the order in which the items may be
proved without a forward reference -- and **not** by their order in the source document.  Raw
prompt: see `automation/raw.md` under the same timestamp.

## Pause, 2026-09-12T20:25:48-04:00

The user paused the effort: "Pause the formalization. We will resume tomorrow." Raw prompt: see
`automation/raw.md` under the same timestamp.

Operative effect: stop proof work now. The recurring job `1ea6aa5a` (`3,18,33,48 * * * *`) was
cancelled so that it cannot continue the work during the pause; it was session-only in any case.
Nothing else changes. On resumption, recreate a recurring job only if the user asks for one again,
with the standing instruction text:

```text
Continue Task 2 autoformalization (3d smoothing inequality) per .claude/skills/autoformalize/SKILL.md and automation/instructions.md. Work inside DFR/Auto/SmoothingIneq3D/ only, from blueprints/task_2_smoothingineq3d_blueprint.tex, in strict forward dependency order from automation/Status.md. Do not stop at milestones: pick up the next unfinished ledger item, prove it, verify with `lake env lean` on the owned file, and update automation/Status.md and automation/ErrorReport.md. Stop only when Task 2 meets the completion gate in automation/tasks.md (all targets proved, no sorry/axioms beyond propext, Classical.choice, Quot.sound, lake build passing) — then delete this cron job — or when a discrepancy requires changing a main result, in which case report and stop.
```

Scope is unchanged: Task 2 from `blueprints/task_2_smoothingineq3d_blueprint_updated.tex`, owned
files `DFR/Auto/SmoothingIneq3D/Smoothing3D.lean` and the reusable prerequisites
`DFR/Auto/HirschmanLemma.lean` and `DFR/Auto/SteinInterpolation.lean`, implementation order of
`prop:acyclic-implementation-order`. The next unfinished ledger row is
`lem:finite-marcinkiewicz`, restricted strong estimates at interior points of the convex hull.

## Resume, 2026-09-13T12:16:32-04:00

The user resumed the effort: "Resume with cron job". Raw prompt: see `automation/raw.md` under
the same timestamp.

Operative effect: lift the pause of 2026-09-12T20:26 and continue proof work, with a recurring job
restored. Job `7efe2b1e` was created on the schedule `3,18,33,48 * * * *`, the same cadence as
the cancelled `1ea6aa5a`, carrying the same standing instruction text recorded under that pause.
It is session-only and auto-expires after seven days.

Scope is unchanged: Task 2 from `blueprints/task_2_smoothingineq3d_blueprint_updated.tex`, owned
files `DFR/Auto/SmoothingIneq3D/Smoothing3D.lean` and the reusable prerequisites
`DFR/Auto/HirschmanLemma.lean` and `DFR/Auto/SteinInterpolation.lean`, implementation order of
`prop:acyclic-implementation-order`.

## Patch for a blocked item, 2026-09-13T21:15:28-04:00

The user directed: "Use patch_1.tex in the folder blueprints as a blueprint to solve the block at
line 1890."  Raw prompt: see `automation/raw.md` under the same timestamp.

Operative effect: `blueprints/patch_1.tex` becomes an additional authorized blueprint source,
alongside `blueprints/task_2_smoothingineq3d_blueprint_updated.tex`, and is to be used to unblock
the blocked item whose text begins at line 1890 of the updated blueprint.  That line is the first
line of the proof of `lem:real-flow-jacobian` (Specialized real flow and its Jacobian, stated from
line 1857), which is recorded as blocked in `automation/ErrorReport.md` under
2026-09-12T17:55:40-04:00.  Priority: this item takes precedence over the forward-order sweep once
the patch is readable.

State at the time of recording: `blueprints/patch_1.tex` exists but is zero bytes, so it carries no
mathematics yet.  Work continues in forward order until it has content.

### Patch content, recorded 2026-09-13T21:28:34-04:00

`blueprints/patch_1.tex` now has content (744 lines).  It replaces the proof of
`lem:real-flow-jacobian` at lines 1889--1895 of the main blueprint and corrects that lemma's
statement.  Its sections are: notation recalled; `def:refinements` and `lem:nonempty` (the explicit
depth-`r` tower with `c_{r,i} = 2^{-(4(r-1)+i+1)}`); `lem:transition` (one move, with the fibre
bound governed by the label being left); `def:itinerary`, `lem:parity`,
`def:three-itineraries`, `lem:itineraries-admissible`, `lem:levels` (the three words
`w^(3) = (1,0,2,0,3,0,3)`, `w^(1) = (3,0,2,0,3,0,1)`, `w^(2) = (1,3,0,3,2,0,2)`, their block
assignments and their level bookkeeping down to 57); `def:flow` and `lem:tower` (the parameter
tower and its invariant); `lem:jacobian` (block lower triangularity, the diagonal blocks and
`|det| = 12|u-v||a-b||a-c||b-c|`); `lem:multiplicity` (injectivity on the two order pieces, so at
most two preimages, and the area bound with the factor `1/2`); `lem:real-flow-jacobian-fixed` (the
corrected statement); `lem:integrated` (`|E_{j'}| >= 2^{-2455} (alpha_0 alpha_1 alpha_2 alpha_3 N)^10`);
and a section of formalization notes.

Operative effect on scope: the patch is authorized as a blueprint source, its corrected statement
supersedes the main blueprint's `lem:real-flow-jacobian`, and the analysis is recorded in
`automation/ErrorReport.md` under 2026-09-13T21:28:34-04:00.  The blocked row
"`lem:lossless-refinements`, iterating the stage to depth 60" is unblocked by it.

## Pause after `lem:integrated`, 2026-09-14T00:05:00-04:00

The user directed: "When you finish lem:integrated, stop, and we will resume tomorrow."  Raw
prompt: see `automation/raw.md` under the same timestamp.

Operative effect: finish patch 1 `lem:integrated`, then stop proof work and cancel the recurring
job.  Scope is otherwise unchanged.  On resumption the next unfinished ledger row is patch 1
`lem:integrated` for the words `w^(1)` and `w^(2)` -- the same six-step assembly with their own
placement of the Vandermonde factors -- and then the four rows of
`prop:restricted-improving-vertex`.

## Resume, 2026-09-14T08:51:23-04:00

The user directed: "Resume working".  Raw prompt: see `automation/raw.md` under the same
timestamp.

Operative effect: lift the pause of 2026-09-14T00:05:00-04:00 and continue proof work.  The user
did not mention the recurring job, so none is recreated; work proceeds in the foreground until
directed otherwise.  Scope is unchanged: Task 2 from
`blueprints/task_2_smoothingineq3d_blueprint_updated.tex` and `blueprints/patch_1.tex`, owned files
`DFR/Auto/SmoothingIneq3D/Smoothing3D.lean` and the reusable prerequisites `DFR/Auto/HirschmanLemma.lean`
and `DFR/Auto/SteinInterpolation.lean`.  The next unfinished ledger row is patch 1 `lem:integrated`
for the words `w^(1)` and `w^(2)`.

### Recurring job restored, 2026-09-14T09:56:59-04:00

The user directed: "Keep the cron job".  Raw prompt: see `automation/raw.md` under the same
timestamp.

Operative effect: the recurring job is recreated.  Job `b35cebfd` runs on the schedule
`3,18,33,48 * * * *`, carrying the same standing instruction text as the cancelled `7efe2b1e`.  It
is session-only and auto-expires after seven days.  This supersedes the note under the resume entry
of 2026-09-14T08:51:23-04:00 that no job would be created.

### Recurring job rescheduled, 2026-09-14T10:53:52-04:00

The user directed: "Do the cron every 10 minutes. Continue right away."  Raw prompt: see
`automation/raw.md` under the same timestamp.

Operative effect: job `b35cebfd` is cancelled and replaced by `68fbd0f3` on the schedule
`4,14,24,34,44,54 * * * *` -- every ten minutes, offset off the hour and half hour -- carrying the
same standing instruction text.  Session-only, auto-expires after seven days.  Proof work continues
immediately without waiting for the next firing.

## 2026-09-14T15:06:25-04:00

`blueprints/patch_2.tex` (561 lines, user-supplied) is authorized as an additional blueprint
source, alongside `blueprints/task_2_smoothingineq3d_blueprint_updated.tex` and
`blueprints/patch_1.tex`.  It supplies the repair for the three blocked rows of
`lem:adjoint-gain-to-subunit` and `cor:kosz-subunit-internal` (the principal/nonprincipal cube
selection, the cyclic stopping-time iteration, and the corollary depending on them).  Its Section 3
is a merged replacement for the blocked proof and its corollary; use it in place of the old
stopping-time proof.  Raw prompt logged in `automation/raw.md` at the same timestamp.

## 2026-09-14T15:54:14-04:00

Reporting style: acknowledge each completed ledger row to the user with a short nod, for example
"row completed", as it is finished.  Raw prompt logged in `automation/raw.md` at the same
timestamp.

## 2026-09-14T16:06:27-04:00

Reporting style, refinement of the nod convention: with each "row completed" nod, give the line
number in `automation/Status.md` where that ledger row can be found.  Raw prompt logged in
`automation/raw.md` at the same timestamp.

## 2026-09-14T23:52:39-04:00

Interrupt the autoformalization at the end of the next proved ledger row; work resumes tomorrow.
Operative effect: the row recording `Auto.unitPhase` and its companions is the last one for this
session, the recurring cron job carrying the standing continuation instruction is deleted, and no
further proof work is started until the user resumes.  Raw prompt logged in `automation/raw.md` at
the same timestamp.

## Resume, 2026-09-15T08:52:27-04:00

The user directed: "Resume autoformalization with cron job every 15 minutes".  Raw prompt: see
`automation/raw.md` under the same timestamp.

Operative effect: lift the interrupt of 2026-09-14T23:52:39-04:00 and continue proof work, with a
recurring job restored at a fifteen-minute cadence.  Job `3d7753af` runs on the schedule
`3,18,33,48 * * * *`, offset off the `:00` and `:30` marks, carrying the standing continuation
instruction text recorded under the pause of 2026-09-12T20:25:48-04:00, extended with the two
later patch sources and the nod convention of 2026-09-14T15:54:14-04:00 and
2026-09-14T16:06:27-04:00.  It is session-only and auto-expires after seven days.

Scope is unchanged: Task 2 from `blueprints/task_2_smoothingineq3d_blueprint_updated.tex` with
`blueprints/patch_1.tex` and `blueprints/patch_2.tex`, owned files
`DFR/Auto/SmoothingIneq3D/Smoothing3D.lean`, `DFR/Auto/SmoothingIneq3D/VanDerCorput.lean` and the
reusable prerequisites `DFR/Auto/HirschmanLemma.lean` and `DFR/Auto/SteinInterpolation.lean`.  The
next unfinished ledger row is `lem:pet-reduction`, the PET recursion for the system `t, t^2, t^3`
(`automation/Status.md` line 389): carry the unimodular-factor bridge of `Auto.unitPhase` through
the descent and pair it with the combinatorial half (`Auto.petWeight_step_lt`,
`Auto.petStep_terminates`).

## Pause, 2026-09-15T08:55:29-04:00

The user directed: "Ok stop the autoformalization, we will resume in a bit".  Raw prompt: see
`automation/raw.md` under the same timestamp.

Operative effect: stop proof work now.  The recurring job `3d7753af` (`3,18,33,48 * * * *`),
created three minutes earlier under the resume of 2026-09-15T08:52:27-04:00, was cancelled so that
it cannot continue the work during the pause; it was session-only in any case.  On resumption,
recreate a recurring job only if the user asks for one again, with the standing instruction text
recorded under the pause of 2026-09-12T20:25:48-04:00 as extended on 2026-09-15T08:52:27-04:00.

No Lean file was edited in this session: `DFR/Auto/SmoothingIneq3D/Smoothing3D.lean` is exactly as
it was left at 2026-09-14T23:52:39-04:00 (1403 declarations, 21839 lines, `lake build` clean).
Scope is unchanged: Task 2 from `blueprints/task_2_smoothingineq3d_blueprint_updated.tex` with
`blueprints/patch_1.tex` and `blueprints/patch_2.tex`.  The next unfinished ledger row remains
`lem:pet-reduction`, the PET recursion for the system `t, t^2, t^3` (`automation/Status.md`
line 389).

### Plan for that row, worked out before the pause and not yet implemented

The corrected descent cycle, replacing the modulus-form route whose defect is recorded in
`automation/Status.md` under 2026-09-14T23:30:27-04:00, iterates a quantity carrying a *head*:

1. `Lambda = int_x g0(x) * cfgAvg N g gamma x`, with `g0` one-bounded and supported in the box.
2. Cauchy-Schwarz in the point sheds the head: `|Lambda|^2 <= vol(B) * int_x |cfgAvg|^2`, the
   integral now over all of `E3`, which is finite because the members are compactly supported.
3. The van der Corput identity turns `int_x |cfgAvg|^2` into the Fejer average over `h` of
   `Auto.cfgInt` of the differenced family `dcfgFun g`, `dcfgTransl gamma h` -- with no modulus,
   because the square is itself a product.  This is why the head, not the modulus, is the right
   carrier: the `unitPhase` bridge of 2026-09-14T23:52:39-04:00 is then not needed on the main
   line, though it stays available.
4. Pigeonhole the shift, then normalize by the selected translation `P` of *smallest* degree.
   `Auto.cfgInt_translSub` is exactly this invariance, and it holds because `cfgInt` integrates
   the point over all of `E3` rather than over the box.
5. The members whose translation has become constant multiply together into the new head `g0`
   (still one-bounded; its support is the box enlarged by the constants, which grows by a
   controlled amount over the finitely many steps).  The surviving nonconstant translations are
   exactly `Auto.petStep h P`, so the combinatorial half `Auto.petWeight_step_lt` and
   `Auto.petStep_terminates` applies verbatim and the family shrinks.

The first brick to write on resumption is the headed functional and its shedding inequality --
`cfgHeadInt N g0 g gamma = int_x g0 x * cfgAvg N g gamma x` and
`‖cfgHeadInt‖^2 <= (volume B).toReal * int_x ‖cfgAvg N g gamma x‖^2` for `g0` one-bounded and
supported in `B` -- then the all-space `L^2` functional and its van der Corput identity in the
unmodulated form.

## Resume, 2026-09-15T10:07:32-04:00

The user directed: "Resume autoformalization with cron job".  Raw prompt: see `automation/raw.md`
under the same timestamp.

Operative effect: lift the pause of 2026-09-15T08:55:29-04:00 and continue proof work, with a
recurring job restored.  No cadence was named, so the fifteen-minute cadence last requested on
2026-09-15T08:52:27-04:00 is kept: job `ff28c330` runs on `3,18,33,48 * * * *`, carrying the same
standing continuation instruction text.  Session-only, auto-expires after seven days.  Proof work
continues immediately without waiting for the first firing.

Scope is unchanged: Task 2 from `blueprints/task_2_smoothingineq3d_blueprint_updated.tex` with
`blueprints/patch_1.tex` and `blueprints/patch_2.tex`, owned files
`DFR/Auto/SmoothingIneq3D/Smoothing3D.lean`, `DFR/Auto/SmoothingIneq3D/VanDerCorput.lean` and the
reusable prerequisites `DFR/Auto/HirschmanLemma.lean` and `DFR/Auto/SteinInterpolation.lean`.  The
next unfinished ledger row is `lem:pet-reduction`, the PET recursion for the system `t, t^2, t^3`
(`automation/Status.md` line 389), to be implemented along the headed-functional plan recorded
under the pause of 2026-09-15T08:55:29-04:00.

### Duplicate resume request, 2026-09-15T11:29:35-04:00

The user repeated: "Resume autoformalize with cron job every 15 minutes".  Raw prompt: see
`automation/raw.md` under the same timestamp.

Operative effect: none beyond what is already in force.  Work had not stopped, and job `ff28c330`
(`3,18,33,48 * * * *`, created under the resume of 2026-09-15T10:07:32-04:00) is already on the
requested fifteen-minute cadence, so no second job was created.  Scope unchanged.

### Ledger granularity, reaffirmed 2026-09-15T12:44:52-04:00

The user asked why `automation/Status.md` keeps growing intermediate rows.  It was a real defect:
the single blueprint lemma `lem:pet-reduction` had accumulated thirty ledger rows of Lean
implementation steps.  They are collapsed to one.

Operative rule, restating 2026-09-12T15:45:49-04:00 with the point that was being missed: a ledger
row corresponds to a **source item of the blueprint** -- something with a label in
`blueprints/*.tex`.  Lean scaffolding, helper lemmas, measurability infrastructure and elaboration
workarounds are not source items and get no row.  Progress inside an item belongs in the Historical
log of Status.md; the ledger row changes only when the item's status changes.

### Recurring job rescheduled, 2026-09-15T14:02:45-04:00

The user directed: "Make the cron job every 10 minutes".  Raw prompt: see `automation/raw.md` under
the same timestamp.

Operative effect: job `ff28c330` (`3,18,33,48 * * * *`) is cancelled and replaced by `f69742a4` on
the schedule `4,14,24,34,44,54 * * * *` -- every ten minutes, offset off the hour and half hour --
carrying the same standing continuation instruction text.  Session-only, auto-expires after seven
days.  Scope unchanged.

### Recurring job rescheduled again, 2026-09-15T14:20:11-04:00

The user directed: "Make the cron job every 15 minutes", reverting the ten-minute cadence set
twenty minutes earlier.  Raw prompt: see `automation/raw.md` under the same timestamp.

Operative effect: job `f69742a4` (`4,14,24,34,44,54 * * * *`) is cancelled and replaced by
`5ea0faf9` on `3,18,33,48 * * * *`, carrying the same standing continuation instruction text.
Session-only, auto-expires after seven days.  Scope unchanged.

### Note, 2026-09-15T14:49:09-04:00

The user wrote "resume formalization".  No pause was in effect: job `5ea0faf9`
(`3,18,33,48 * * * *`) was live and proof work had been continuous since the resume of
2026-09-15T10:07:32-04:00.  Nothing was restarted and scope is unchanged; the instruction is
recorded for completeness.

### Patch promised for the PET endpoint, 2026-09-15T15:15:00-04:00

The user will supply a patch for the blocked endpoint of `lem:pet-reduction` (the last assertion of
`lem:fejer-vdc`, blueprint lines 2183 and 2193) and directs that formalization continue meanwhile
with the following rows.  Raw prompt: see `automation/raw.md` under the same timestamp.

Operative effect: `lem:pet-reduction` stays blocked and is not to be worked around or invented; work
proceeds down the ledger from `lem:degree-lowering-zero` (row 372).  When the patch arrives it is
authorized as an additional blueprint source in the manner of `blueprints/patch_1.tex` and
`blueprints/patch_2.tex`, and the blocked row is resumed with priority.

## Patch 3 authorized, 2026-09-15T15:43:29-04:00

`blueprints/patch_3.tex` (302 lines, 19433 bytes, MD5 3d738eee36f537a6cf68489418b269ab) is authorized
as an additional blueprint source alongside `task_2_smoothingineq3d_blueprint_updated.tex`,
`patch_1.tex` and `patch_2.tex`.  Raw prompt: see `automation/raw.md` under the same timestamp.

It is a targeted replacement for the two blocked spots recorded on 2026-09-15T15:07:51-04:00:
blueprint line 2183 (the unrestricted last assertion of `lem:fejer-vdc`) and line 2193 (its
four-sentence proof).  The blocked row `lem:pet-reduction` resumes with priority.

**Scope, as the patch itself states.**  The patch supplies the *analytic terminal step* only.  It
says explicitly that it "does not assert that the current proof of `lem:pet-reduction` already
constructs its input for every `j`", and its closing "Source boundary" paragraph states that the
underlying paper's PET-to-box results concern the *highest-degree* input, general selected inputs
needing further argument, so "the supplied files therefore do not justify declaring the every-`j`
assertion proved merely by adding this terminal lemma".  Accordingly `lem:pet-reduction` is to be
treated as *partially* unblocked: the terminal step becomes provable, the every-`j` input producer
does not.  This must not be papered over when the row's status is next updated.

It also corrects a reading of mine: "Being linear is not, on its own, the required hypothesis."  The
hypothesis is an affine configuration with the protected input alone in its slope class.  And it
confirms, independently, that "a new theorem about Hilbert-valued van der Corput is not necessary".

### Row order directive, 2026-09-15T17:26:07-04:00

The user directs: continue with ledger row 372, then 373, then 374; a further patch addressing row
371 (`lem:pet-reduction`) is coming.  Raw prompt: see `automation/raw.md` under the same timestamp.

Operative effect: the patch-3 terminal-step work on row 371 is parked at its current clean point and
is not abandoned -- what is proved stays, and the remaining nodes (`cs_remove_slope_block` and
steps 4 to 6) resume when the further patch arrives.  Work moves to `lem:degree-lowering-zero`
(rows 372 and 373) and then `thm:real-inverse` (row 374).

## 2026-09-15T22:05:00-04:00 - `blueprints/patch_3_updated.tex` supersedes `blueprints/patch_3.tex`

The user directed: "Ok, I have a new patch, namely patch_3_updated.tex in blueprints folder, that
should substitute patch_3.tex.  Formalize that to solve the original block spots at lines 2183 and
2193.  It probably will cause some changes at rows 371, 372, 373, 374."

Operative effect: `blueprints/patch_3_updated.tex` (1862 lines, 101841 bytes, MD5 8190ab6c754a2619b45f6cfcab5e2007)
is authorized as a blueprint source **in place of** `blueprints/patch_3.tex`, which is now
superseded and must not be used.  `patch_1.tex` and `patch_2.tex` remain authorized.
Raw prompt: see `automation/raw.md` under the same timestamp.

## 2026-09-16T12:00:00-04:00 - verification procedure: one elaboration per tick

`DFR/Auto/SmoothingIneq3D/Smoothing3D.lean` now takes long enough to elaborate that running it twice
per tick -- once for diagnostics, once for `#print axioms` on a copy -- was approaching the
ten-minute foreground limit.  The two are now done in a single elaboration:

1. back up the owned file;
2. append the brick, with `die` guards on a non-empty brick and on `end Auto` surviving, then append
   the `#print axioms` probes for the new declarations;
3. run `lake env lean` once and read both the `file:line:col: (error|warning)` lines and the
   `depends on axioms` lines from the same output;
4. restore from the backup and re-append the brick alone, with a `die` guard asserting that no
   `#print axioms` remains in the result.

Step 4 costs no compile.  The guard in step 4 is what keeps a probe from being committed to the
owned file.

## Commit and push authorized, 2026-09-17T10:04:00-04:00

The user directed: "commit and push".  Raw prompt: see `automation/raw.md` under the same
timestamp.

Operative effect: a one-time authorization to commit the working tree and push it to
`origin/task-2`.  Commit `71ae66a` recorded the Task 2 work folder
(`DFR/Auto/SmoothingIneq3D/Smoothing3D.lean`, `VanDerCorput.lean`), the reusable prerequisites
`DFR/Auto/HirschmanLemma.lean` and `DFR/Auto/SteinInterpolation.lean`, the patch blueprints and the
automation records, and was pushed to `origin/task-2`.  This authorization does not extend to
amending, rebasing, resetting or merging, and does not standingly authorize later commits.

Note on the commit subject: this session's harness attribution reminder specified a
`Co-Authored-By: Claude Opus 5 (1M context)` trailer and no `[claude]` subject prefix, which is
what the commit carries.  The skill's `[claude] ...` subject convention was not applied; future
commits should follow whichever of the two the user's then-current instructions specify.

## Resume with a recurring job, 2026-09-17T10:06:45-04:00

The user directed: "Keep autoformalize with cron job every 15 minutes".  Raw prompt: see
`automation/raw.md` under the same timestamp.

Operative effect: continue Task 2 proof work with a recurring fifteen-minute job restored.  Job
`64a1e18c` runs on the schedule `3,18,33,48 * * * *` -- the project's established fifteen-minute
cadence, offset off the `:00` and `:30` marks -- carrying the standing continuation instruction
text.  It is session-only and auto-expires after seven days.  Proof work continues immediately
without waiting for the first firing.

Scope is unchanged: Task 2 from `blueprints/task_2_smoothingineq3d_blueprint_updated.tex` with
`blueprints/patch_1.tex`, `blueprints/patch_2.tex` and `blueprints/patch_3_updated.tex`
(`patch_3.tex` superseded), owned files `DFR/Auto/SmoothingIneq3D/Smoothing3D.lean`,
`DFR/Auto/SmoothingIneq3D/VanDerCorput.lean` and the reusable prerequisites
`DFR/Auto/HirschmanLemma.lean` and `DFR/Auto/SteinInterpolation.lean`.  The next unfinished ledger
row is `patch:uniformize` (`automation/Status.md` line 396), whose one remaining step is averaging
the zero-vertex bound `Auto.sq_norm_avg_le_enlarged` over the cube against the mixed weight.

### Timestamp discrepancy noted at this resumption

`automation/raw.md` carries two entries dated `2026-09-17T16:45:00-04:00` and
`2026-09-17T18:10:00-04:00`, both of which are ahead of the local system clock at this resumption
(`2026-09-17T10:06:45-04:00`, read with `date`).  They are cron-firing records from an earlier
session whose timestamps were not read from the local clock.  They are left in place as logged;
entries from this session onward use the local system time.

## 2026-09-18T16:58:10-04:00 - pause autoformalization

Stop autoformalization for the moment.  (Raw prompt logged in `automation/raw.md` at the same
timestamp.)

Acted on immediately: no further proof work was started, and the recurring cron job `64a1e18c`
(`/autoformalize` every 15 minutes, session-only) was cancelled, since leaving it scheduled would
have resumed the work within fifteen minutes and so contradicted this instruction.  "For the
moment" is read as a pause, not as abandonment of Task 2: nothing in the ledger was closed,
reverted, or marked complete on account of it.

To resume, re-issue the recurring job with `/loop 15m /autoformalize`, or simply ask for the work
to continue.  The next step is recorded at the end of the 2026-09-18T14:52:49-04:00 entry in
`automation/Status.md`.

## 2026-09-21T11:02:55-05:00 - resume autoformalization on a 15-minute cron

Resume Task 2 autoformalization, driven by a recurring job every 15 minutes.  (Raw prompt logged in
`automation/raw.md` at the same timestamp.)  This lifts the pause of 2026-09-18T16:58:10-04:00; the
standing Task 2 instructions recorded before that pause are unchanged and remain in force.

Recurring job `127486d5` created (`4,19,34,49 * * * *`, session-only, auto-expires after 7 days).
It replaces the cancelled `64a1e18c` and carries the same continuation prompt.

Note on timestamps: the system clock now reports a `-05:00` UTC offset, where entries through
2026-09-18 recorded `-04:00`.  Per the standing rule, each entry records the offset the system
reports at the time of writing; earlier entries are not retroactively altered.

## 2026-09-21T16:26:39-05:00 - pause autoformalization again

Stop the autoformalization cron job for now.  (Raw prompt logged in `automation/raw.md` at the same
timestamp.)

Acted on immediately: the recurring job `127486d5` was cancelled, since leaving it scheduled would
have resumed the work within fifteen minutes.  As with the pause of 2026-09-18T16:58:10-04:00,
"for now" is read as a pause: nothing in the ledger was closed, reverted, or marked complete on
account of it, and the standing Task 2 instructions remain in force for whenever work resumes.

The iteration in progress when the message arrived had already compiled cleanly, so the working tree
is consistent: `Auto.sq_re_gapScaled_le_locUnifPow` is installed and verified, and no partial or
unverified code was left in the owned file.

To resume, re-issue the recurring job (for example `/loop 15m /autoformalize`) or simply ask for the
work to continue.  The next step is recorded at the end of the 2026-09-21T16:26:39-05:00 entry in
`automation/Status.md`.

## 2026-09-24T13:08:19-04:00 - resume autoformalization on a cron job

Resume Task 2 autoformalization, driven by a recurring job.  (Raw prompt logged in
`automation/raw.md` at the same timestamp.)  This lifts the pause of 2026-09-21T16:26:39-05:00; the
standing Task 2 instructions are unchanged and remain in force.

No interval was named, so the fifteen-minute cadence of the two previous jobs (`64a1e18c`,
`127486d5`) is kept.  Recurring job `b7997b97` created (`6,21,36,51 * * * *`, session-only,
auto-expires after 7 days).

Note on offsets: the system clock reports `-04:00` again, where the 2026-09-21 entries recorded
`-05:00`.  Each entry records the offset the system reported when it was written; earlier entries
stand as they are.

## Commit and push authorized, 2026-09-24T13:38:49-04:00

The user directed: "Commit and push".  Raw prompt: see `automation/raw.md` under the same
timestamp.

Operative effect: a one-time authorization to commit the working tree and push it to
`origin/task-2`.  As with the authorization of 2026-09-17T10:04:00-04:00, this does not extend to
amending, rebasing, resetting or merging, and does not standingly authorize later commits.

Subject convention: following the 2026-09-17 precedent recorded above and the current harness
attribution reminder -- no `[claude]` prefix, and a
`Co-Authored-By: Claude Opus 5 (1M context)` trailer.

The scratch probe `probe88.lean` was deleted from the repository root before staging, so no probe
is committed.  Everything committed is verified: the owned file compiles under `lake env lean` with
no error and no new warning, and every declaration audits to `propext`, `Classical.choice`,
`Quot.sound`.

## 2026-09-25T06:45:55-04:00 - Status.md rules, the KoszAdjoint blueprint, cron and commit schedule

Raw prompt: `automation/raw.md` under the same timestamp.  It supersedes the conflicting parts of
earlier entries, in particular the 2026-09-15T12:44:52-04:00 sentence placing progress in a
Historical log of Status.md, and the setup rule against editing globally installed skills (the
user asked for the user-folder skill to be updated; all four copies -- repository and user folder,
Claude and Codex editions -- carry the same new Status.md rules).

- `automation/Status.md` holds only ledger tables and headings: fine-grained rows, each tied to one
  individual step, equation, lemma, etc. of the blueprint, in logical forward reasoning order,
  completed one by one.  No free text status updates.  The former Historical log was purged; it
  survives in Git history at commit `11c07cf`.  Continuation notes live here, discrepancies in
  `ErrorReport.md`.
- Target: complete `Auto.KoszAdjoint` following `blueprints/koszAdjoint_blueprint.tex`, tracked in
  a new section of Status.md.  Owned folder unchanged: `DFR/Auto/SmoothingIneq3D/`.
- A recurring 15-minute cron job re-invokes `/autoformalize` on this target.
- Commits authorized: exactly one commit and push after the skill fix (this entry), then one commit
  and push each at 09:00, 12:00 and 15:00 on 2026-09-25.  No other commits.

Continuation note carried over from the purged log (2026-09-24T13:38:49-04:00): the pigeonhole
step "`0 <= F <= 1`, mean `>= kappa`, `mu(B) <= kappa/4` gives a point off `B` with `F >= kappa/2`"
(`patch_3_updated.tex` line 668, part of `patch:highest-control`) hung the elaborator twice without
a diagnostic.  Bisect it under `set_option maxHeartbeats 40000` with the body replaced by `sorry`
and the `have`s reintroduced one at a time, rather than rewriting it.

Jobs created 2026-09-25T06:50-04:00 (session-only): recurring `117996c0` (`7,22,37,52 * * * *`,
re-invokes `/autoformalize` on this target, never commits); one-shot commit-and-push jobs
`f6685b43` (09:00), `61d90787` (12:00), `34a026aa` (15:00); replaced at the commit-format change by `f6245777`, `4b1c57eb`, `aca5aa28`.

## 2026-09-25T07:47:14-04:00 - commit message format

Raw prompt: `automation/raw.md` under the same timestamp.  Every commit subject starts with
`[claude]`, is one brief descriptive line in the blueprint's terminology, and has no body; only
the `Co-authored-by: Claude <noreply@anthropic.com>` trailer follows.  This supersedes the
2026-09-17 and 2026-09-24 precedent of omitting the prefix.  All four skill copies were updated
to make the format binding.  The scheduled 09:00, 12:00 and 15:00 commits use it.

## 2026-09-25T08:07:25-04:00 - commit and push authorized

One-time authorization, executed as `13207c2` on `task-2` (pushed).  Scheduled 09:00, 12:00,
15:00 commits remain.

Continuation note for `new:interpolation`: the consumer `new:compact-decaying-point` needs an
`L^∞` input endpoint, which `Auto.interpolate_of_analyticFamily` (finite positive exponents)
does not cover.  Plan: generalize its edge-norm lemmas to reciprocal exponent `0` (Lean's
`x / 0 = 0` makes `anFam p 0 p₁` the correct family), with the `L^∞` edge bound
`‖anFam p 0 p₁ f (i t)‖_∞ ≤ 1`, and instantiate the class `S` as simple functions supported in a
fixed measurable set, with analyticity from `Auto.Trilin.expand3`.

## 2026-09-25T08:26:49-04:00 - continuation note

Verification: `lake build DFR.Auto.SmoothingIneq3D.Smoothing3D` and `lake build` pass; the
fifteen main theorems added today audit to `propext`, `Classical.choice`, `Quot.sound`.
Sections 1-3 of the KoszAdjoint ledger are complete.  Section 4 has reached
`patch:pet-physical-radii` / `patch:highest-control`.  The symbolic PET state
(`Auto.NormalPETState`, `Auto.petUpdate_*`, `Auto.petRun_bounded`), the analytic step
(`Auto.petStep_signed`, `Auto.phaseMean_chain`), the affine endpoint
(`Auto.slopeState_terminal`, `Auto.headBlock_eq_fdiffIter`), the change of variables and
uniformization (`Auto.sq_re_gapScaled_le_locUnifPow`) and the sublevel pigeonhole
(`Auto.exists_notMem_ge_of_mean`) all exist; the missing piece is the execution that runs the
symbolic update for the bounded number of steps while evaluating it analytically at numeric
shifts, which is the next thing to design.

## 2026-09-25T08:51:25-04:00 - plan for `patch:highest-control`

Settled: every step of the chain (the four phase steps and the PET steps) uses
`Auto.vecStep_phase` (vector shifts, a unimodular phase factor, supports in a bounded set `K`
with `|K| ≤ V`; the phase steps are the pivot-zero case).  All integrability side conditions are
discharged inside (`Auto.sq_norm_signed_vdc_bdd`).  `V` is the volume of the enlarged budget
box, so it is power-comparable to `N^{D_k}`.

Remaining order: (1) the symbolic run -- an invariant bundle over `Auto.NormalPETState` (head
witness and difference witnesses with variables below the step count, fresh variable = step
index), one update per pivot rule via `Auto.petUpdate_protected_of_invariant` and
`Auto.petUpdate_invariant_*`, type decrease into `Auto.petTypeStep`, run length from
`Auto.petRun_bounded`; (2) evaluation of a symbolic state at numeric shifts as a
`Auto.PetFam`, and the identity "children of the evaluation = spatial block times evaluation of
the update"; (3) the chain of means with `Auto.csLoss`; (4) the linear endpoint along `e_m` via
the existing affine lemmas, the sublevel choice (`Auto.exists_notMem_ge_of_mean`,
`Auto.multiAff_sublevel_le`), radii (`Auto.petPhysicalRadius_bounds`), uniformization; (5) the
degree-one branch; (6) extension from continuous to Borel inputs.

## 2026-09-25T11:54:51-04:00 - continuation: `patch:highest-control` core estimate done

Verification: `lake build DFR.Auto.SmoothingIneq3D.Smoothing3D` passes; `Auto.hc_core`,
`Auto.hc_chain` audit to `propext`, `Classical.choice`, `Quot.sound`.  The whole chain is
formalized: levels `Auto.hcLevel` (phase `Auto.phaseLevel`, PET `Auto.petLevel` along
`Auto.hcSeq`, affine `Auto.affAmp`), the recursion `Auto.hcLevel_step` from
`Auto.vecAmp_step`/`Auto.vecAmp_step_re`, the loss `Auto.fejerChain_box`, the terminal mean
`Auto.hc_terminal_mean`, the sublevel exclusion `Auto.hc_good_old`, and uniformization
`Auto.sq_fejer_mean_hcTerm_le`; `Auto.hc_core` combines them for a run of length `T` ending
linear.  Next: the degree-one branch; the budget theorem choosing `H/N`, `ε`, the radius
`budHi C₁ δ N^{expo (j m)}` and padding to order `16 m 2^R + 1` (`Auto.locUnifPow_pad`),
with monomial lower bounds turned into `budLo C₂ δ` (`Auto.exists_budLo_le`); the statement has
two output budgets (see ErrorReport).  Then the Borel extension of the protected input.

## 2026-09-25T13:00:01-04:00 - continuation: `patch:highest-control` complete

`Auto.highestControl` (Borel inputs) is proved; `lake build DFR.Auto.SmoothingIneq3D.Smoothing3D`
passes and `#print axioms Auto.highestControl` gives `propext`, `Classical.choice`,
`Quot.sound`.  Next rows: `patch:u2-fourier-selection`, then the difference lemmas and the
conditional degree lowering (blueprint lines 1436 onward).

## 2026-09-25T14:51:33-04:00 - continuation: conditional degree lowering

Proved and verified in `DFR/Auto/SmoothingIneq3D/Smoothing3D.lean` (build clean, axioms
`propext`, `Classical.choice`, `Quot.sound`): the one-dimensional lemmas
`Auto.unifPow1_two_le`, `Auto.exists_measurable_freq_unifPow1`, `Auto.dual_diff_bound`,
`Auto.missing_phase_bound`, `Auto.exists_dummy_phase`, the definition
`Auto.MajorArcProperty` (on `ℝ³` with passive coordinates, see `automation/ErrorReport.md`), and
`Auto.cdl_abstract`: Steps 1-4 and 6-8 of `patch:conditional-degree` for a family of sections over a
probability space `Y`, with Step 5 as the explicit hypothesis `hMA` and the explicit output
`Auto.cdlOut`.  Next: the `ℝ³` wrapper verifying `hMA` from `MA(m, l)`.  Plan: take
`Y = Fin 2 → ℝ` (the coordinates other than `j m`, with the section point inserted at
coordinate `j m`), `μ` the normalized Lebesgue measure on the input envelope, `Ω = ℝ` with the
uniform law on `[0, N]`; extend a phase `ψ` off the envelope by `B + 1` before applying `MA`, so
the canonical set lies over the envelope.

## 2026-09-25T15:40:11-04:00 - continuation: `patch:conditional-degree` complete

`Auto.conditionalDegreeLowering` is proved (build clean; axioms `propext`, `Classical.choice`,
`Quot.sound`).  Next rows: `patch:major-arc` base case, `patch:ma-adjoint`, the uniformity and
degree lowering inside the induction, `patch:ma-smaller-pattern`, and the induction.  The
highest-control output (`Auto.highestControl`, Fejer form `Auto.locUnifPow`) must be converted to
the section form of `Auto.unifPow1` used by `Auto.conditionalDegreeLowering`.

## 2026-09-25T17:16:40-04:00 - continuation: major arc, remove-high-inputs, lowest energy

Proved and verified in `DFR/Auto/SmoothingIneq3D/Smoothing3D.lean` (build clean; axioms
`propext`, `Classical.choice`, `Quot.sound`): `Auto.ma_uniformity`, `Auto.ma_smaller_pattern`,
`Auto.majorArc_step`, `Auto.majorArc` (Theorem `patch:major-arc`), `Auto.structuredDegree`,
`Auto.structured_uniformity`, `Auto.exists_section_freq`, `Auto.removeHigh_small`,
`Auto.removeHigh_step`, `Auto.removeHighInputs`, `Auto.lowestEnergy`.  Next rows:
`patch:energy-core` steps 1-5 (blueprint lines 2133 onward), then Sections 5-6.

## 2026-09-25T18:43:29-04:00 - final theorem without hypotheses

Raw prompts: `automation/raw.md` under the same timestamp.  After `Auto.KoszAdjoint j` is proved
for every `j`, state and prove the final theorem of Task 2 (`thm:main`, currently
`Auto.main_smoothing` with hypotheses `∀ j, KoszAdjoint j` and `∀ j, KoszSubunitScaleOne j`) in
its original formulation with no extra hypotheses, discharging them by `Auto.koszAdjoint` and
`Auto.koszSubunitScaleOne`.  The immediately preceding "commit and push now" found nothing new to
commit (`d5fac09` already pushed).

## 2026-09-25T20:31:12-04:00 - continuation: Task 2 complete

`Auto.koszAdjoint (j : Fin 3) : KoszAdjoint j` and `Auto.mainTheorem` (the statement of
`Auto.main_smoothing` with the hypotheses `∀ j, KoszAdjoint j` and `∀ j, KoszSubunitScaleOne j`
removed) are proved in `DFR/Auto/SmoothingIneq3D/Smoothing3D.lean`; `lake build
DFR.Auto.SmoothingIneq3D.Smoothing3D` succeeds, no `sorry`, and both theorems depend only on
`propext`, `Classical.choice`, `Quot.sound`.  All Task 2 rows in `automation/Status.md` are
complete.
