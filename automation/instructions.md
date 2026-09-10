# Autoformalization instructions

## Operative user request

Recorded 2026-09-10T09:42:06.7141336-04:00; exact prompt: [raw.md](raw.md).
Prepare this repository for four assigned formalization tasks, as specified in
[tasks.md](tasks.md), and vendor both autoformalize skill editions.
This setup request does not start the mathematical formalization.

The current explicit user instructions take precedence over these instructions,
which supersede conflicting generic skill guidance.

## Scope and workflow

- Every proof agent must have exactly one task assignment before editing.
  Follow the assignment and readiness protocol in tasks.md.
- All mathematical code, helpers, experiments, and task-specific working files
  must stay inside that task's assigned Auto subfolder. This explicitly overrides
  the skill's default single file for the whole project and its exception placing
  reusable prerequisites directly in Auto/. Keep such prerequisites inside the
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
For direct source verification use lake env lean Auto/SmoothingIneq2D/Smoothing2D.lean
(or the assigned task's actual file). Audit completed target declarations with
#print axioms; allowed axioms are propext, Classical.choice, and Quot.sound only.

## Next step

Task 1 remains assigned and active. Lemmas 3.1-3.3 are verified. Equation (3.1) and its positive-time reduction are verified. Continue frequency and amplitude reductions (3.3)-(3.4), then the next ready source-ledger item in logical forward reasoning order. Preserve Lemma 3.3 and Theorem 5 and the documented corrections. The renewed instruction to proceed authorizes this correction; do not ask again or stop at intermediate milestones. Follow the remaining source ledger in forward order.
Tasks 2 and 3 await blueprints. Task 4 additionally awaits verified completion
of Tasks 1-3. Setup scaffolding is not theorem completion.

## LaTeX build artifacts

User direction recorded 2026-09-10T09:48:56.6842063-04:00; exact prompt: [raw.md](raw.md).
Keep standard LaTeX auxiliary/build artifacts ignored in the root .gitignore.
Preserve trackability of .tex, .bib, and source PDFs.

## Task folder READMEs

User direction recorded 2026-09-10T09:53:04.4384248-04:00; exact prompt: [raw.md](raw.md).
Remove the README.md files from the four Auto task folders; do not recreate them.

## Start Task 1

Recorded 2026-09-10T09:56:31.1092542-04:00 (recording time); exact prompt: [raw.md](raw.md).
The user requests /autoformalize task 1. Begin Task 1 source study and formalization within Auto/SmoothingIneq2D/. Existing task boundaries and completion criteria apply.

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
The user requests /autoformalize task 1. Resume Task 1 source audit and formalization in Auto/SmoothingIneq2D/Smoothing2D.lean. This supersedes the prior pause. No commit or push is requested.

## Continue Task 1 to completion

Recorded 2026-09-10T12:42:17.1154681-04:00 (recording time); exact prompt: [raw.md](raw.md).
Continue autoformalizing Task 1 until every source target and prerequisite is completely proved and verified. Do not stop at supporting lemmas, partial progress, or build milestones. Existing source-fidelity, task boundaries, no-placeholder policy, and completion gate remain in force.

Recorded 2026-09-10T12:44:37.8315626-04:00 (recording time); exact prompts: [raw.md](raw.md). The user requires a granular Status.md ledger whose rows correspond to actual source equations or identifiable unnumbered source steps. Do not invent proof steps or count implementation helpers as source milestones. Continue Task 1 through full completion after updating the ledger.

Recorded 2026-09-10T12:45:58.7354373-04:00 (recording time); exact prompts: [raw.md](raw.md). The user reiterates logical forward reasoning order and requires rereading the instructions. Finish the earliest unfinished source argument and all its prerequisites before advancing. Maintain source-based ledger rows in dependency order; preserve already proved supporting lemmas without treating their existence as completion of an earlier missing source argument.

2026-09-10T15:02:01.6771576-04:00 - User renews the instruction to complete Task 1 without stopping. In the context of the pending correction question, proceed with the documented corrected refinement; preserve the main theorem and record the actual proof and constants. Exact prompt in raw.md.

2026-09-10T15:41:20.7697427-04:00 - The latest user instruction prohibits a separate fix commit and reiterates logical forward reasoning order, not source presentation order. Continue Task 1: close prerequisites before consumers and do not stop at acknowledgments. The two dyadic-volume proof errors are fixed and direct Lean verification passes. No further commit is authorized by the latest instruction.

2026-09-10T18:09:12.2173105-04:00 - User requests committing the accumulated verified work, then continuing Task 1 until completion. This authorizes one progress commit and supersedes the earlier prohibition on further commits. Continue in logical forward reasoning order after committing; no push requested. Exact prompt in raw.md.
