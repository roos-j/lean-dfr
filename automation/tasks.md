# Autoformalization tasks

This is the authoritative task assignment and readiness registry.
Proof progress and verification evidence belong in the per-task ledgers
`Status-task1.md` ... `Status-task4.md`; discrepancies in `ErrorReport-task1.md` ... `ErrorReport-task4.md`.

| Task | Target/source | Exclusive work folder | Main file | Owner | Readiness |
| --- | --- | --- | --- | --- | --- |
| 1 | Trilinear smoothing inequality, Theorem 5, [arXiv:2008.10140](https://arxiv.org/abs/2008.10140) | DFR/Auto/SmoothingIneq2D/ | DFR/Auto/SmoothingIneq2D/Smoothing2D.lean | Codex root task1-20260910-0955 | Complete; Auto.smoothing_theorem5 verified with all prerequisites, full build, and allowed-axiom audit |
| 2 | 3d smoothing inequality, [blueprints/task_2_smoothingineq3d_blueprint.tex](../blueprints/task_2_smoothingineq3d_blueprint.tex) | DFR/Auto/SmoothingIneq3D/ | DFR/Auto/SmoothingIneq3D/Smoothing3D.lean | Claude session task2-20260911-1213 | Complete; Auto.mainTheorem (`thm:main`, no hypotheses) verified with Auto.koszAdjoint, lake build, and allowed-axiom audit |
| 3 | Twisted; `blueprints/task_3_twisted_blueprint.tex`, Theorem `thm:main` | DFR/Auto/Twisted/ | DFR/Auto/Twisted/Twisted.lean | Claude root task3-20260911-1842 | Complete; Auto.Twisted.thm_main verified (unconditional) |
| 4 | Reduction: `thm:main` of `blueprints/main.tex` (paper draft, kept out of git) from Tasks 1-3 | DFR/Auto/Reduction/ | DFR/Auto/Reduction/Reduction.lean | Claude session task4-20260925-2118 | Active (2026-09-25T21:17:51-04:00) |

## Assignment protocol

1. The coordinator reads current instructions, source availability, owners, and
   verification records before assigning work.
2. Assign each proof agent exactly one ready task by number and name. Record a
   unique owner/session identifier and local timestamp here before work starts.
   One active owner per task; different ready Tasks 1-3 may run independently.
3. Include the exact folder boundary, source, main file when specified, next
   unfinished proof step, and completion criteria in the assignment.
   Unassigned agents request assignment. Do not take an already owned task.
4. Workers keep code, scratch files, and mathematical notes in their assigned
   folder. Shared automation records are maintained serially by the coordinator
   using worker reports. Cross-task changes require reassignment/coordination;
   do not edit another task or place new prerequisites directly in DFR/Auto/.
5. On handoff, record the actual declarations, source mappings, checks, remaining
   obligations, and next step in the task's Status-taskN.md; update owner/readiness here.
   Never treat an absent or disconnected agent as evidence its task is complete.

## Completion gate

A task is complete only when all of its source targets and required prerequisites
are faithfully proved, owned sources pass direct lake env lean checks with the pinned toolchain, the configured project passes lake build,
and #print axioms on the exported results shows only a subset of propext,
Classical.choice, and Quot.sound. No sorryAx, additional axioms, unproved bridges,
weakened targets, or placeholders may underlie a completed task. Record the
exported module/declaration names, exact source/version, build result, axiom
output, and local verification timestamp in the task's Status-taskN.md.

Before assigning Task 4, the coordinator must verify all three prerequisite
tasks against this evidence and current source, mark each complete, confirm the
Reduction blueprint is present and read, and record that the gate passed.
Only then may a Reduction agent begin. Task 4 imports and uses the established
results of Tasks 1-3; it does not assume them as axioms or rewrite their proofs.

## Initial assignment state

No proof agents have been assigned by the setup operation. Empty folders and
the Task 1 starter module are infrastructure only; all four proofs are not started.

## Task 1 assignment

2026-09-10T09:56:31.1092542-04:00 — Coordinator assigns Codex root task1-20260910-0955 exactly Task 1, trilinear smoothing inequality. Scope: DFR/Auto/SmoothingIneq2D/; main file Smoothing2D.lean; source arXiv:2008.10140v2, Theorem 5. Next unfinished step: read the exact theorem and full dependency proof, then record forward proof order. Completion requires faithful source coverage, direct verification of owned Auto sources, lake build for configured targets, and the allowed-axiom audit. The root agent maintains shared records serially.


2026-09-10T11:01:54.9581411-04:00 - Coordinator resumes the existing Codex root task1-20260910-0955 assignment for exactly Task 1. Scope and completion gate above remain unchanged. Next: finish Theorem 5 and Section 3 source/dependency audit.

2026-09-11T16:04:16.7487146-04:00 - Task 1 completion gate passed. Owner Codex root task1-20260910-0955 completed Theorem 5 and its source proof; see Status.md for direct checks, full build, and transitive axiom evidence. Tasks 2-3 remain blocked on blueprints; Task 4 remains blocked on their completion and its blueprint.

2026-09-11T20:38:53.152569-04:00 - User-authorized Task 1 cleanup completed by Codex root. Shared prerequisites relocated to DFR/Auto/; the main file and all source targets are unchanged. Completion gate rechecked: direct source checks, configured build, and final theorem axiom audit pass.
## Task 2 assignment

2026-09-11T12:14:59-04:00 — Coordinator assigns Claude session task2-20260911-1213 exactly Task 2, the 3d trilinear Sobolev smoothing estimate. Scope: DFR/Auto/SmoothingIneq3D/; main file Smoothing3D.lean; source blueprints/task_2_smoothingineq3d_blueprint.tex, target `thm:main`. Next unfinished step: the elementary conventions of blueprint Section 2, in the forward order recorded in Status.md. Completion requires faithful coverage of the blueprint's proved steps, direct verification of the owned Auto source with `lake env lean`, `lake build` for configured targets, and the allowed-axiom audit.

Open scope question referred to the user (see Status.md and ErrorReport.md): the blueprint designates `thm:kosz-adjoint`, the scale-one input behind `thm:kosz-subunit`, and `thm:quasi-interpolation` as imported analytic modules carrying citations instead of proofs (Remark `rem:formalization-boundary`). The completion gate forbids unproved bridges, so these three imports must either be proved in Lean or explicitly carried as hypotheses of the main theorem.

## Task 2 completion gate: user-authorized exception for the blueprint's imports

2026-09-11T16:46:20-04:00 — The user resolves the scope question recorded above. The three
modules that blueprints/task_2_smoothingineq3d_blueprint.tex imports by citation rather than
proof (`thm:kosz-adjoint`, the scale-one estimate behind `thm:kosz-subunit`, and
`thm:quasi-interpolation`) are to be stated as named Props and threaded as explicit hypotheses
through every downstream result, including the target `thm:main`. Task 2 therefore completes with
`thm:main` proved conditionally on exactly those three named imports.

Everything else in the gate stands: no sorry, no admit, no added axioms, no weakened targets and
no placeholders; owned sources pass direct `lake env lean`; the configured project passes
`lake build`; and `#print axioms` on the exported results shows only a subset of propext,
Classical.choice and Quot.sound. The imports must be visible in the statement of `thm:main`
rather than hidden in a definition.

## Task 2 source change: the imports become proof obligations

2026-09-11T18:44:08-04:00 — The operative blueprint for Task 2 is now
blueprints/task_2_smoothingineq3d_blueprint_updated.tex. Its
`prop:no-imported-analytic-declarations` requires that `thm:kosz-adjoint`, `thm:kosz-subunit`
and `thm:quasi-interpolation` be proved internally rather than assumed. The gate exception
recorded on 2026-09-11T16:46:20-04:00, which permitted carrying them as hypotheses, is therefore
withdrawn by the source itself. The original completion gate applies in full: all targets proved,
no sorry, no added axioms, `#print axioms` showing only propext, Classical.choice and Quot.sound,
owned sources passing `lake env lean`, and the configured project passing `lake build`.
## Task 3 assignment

2026-09-10T18:55:25-07:00 — Coordinator assigns Codex root task3-20260910-1855 exactly Task 3, anisotropic twisted paraproduct. Scope: `DFR/Auto/Twisted/`; main file `DFR/Auto/Twisted/Twisted.lean`; source `blueprints/task_3_twisted_blueprint.tex`, Theorem `thm:main`. The task folder is absent on this branch and will be created only at that prescribed path. Next unfinished step: read the full blueprint and construct its strict forward dependency ledger, beginning with the analytic definitions and local telescoping prerequisites. Completion requires faithful source coverage, direct verification of every owned Auto source, `lake build` for configured targets, and the allowed-axiom audit.

## Task 3 reassignment

2026-09-11T18:42:00-07:00 — Coordinator reassigns Task 3, anisotropic twisted
paraproduct, to Claude root task3-20260911-1842 after the previous owner's
user-requested pause. Scope unchanged: `DFR/Auto/Twisted/`; main file
`DFR/Auto/Twisted/Twisted.lean`; source `blueprints/task_3_twisted_blueprint.tex`,
Theorem `thm:main`. The paused checkpoint's unverified selected-atom scale-tail
bridge was re-checked and audited before new work began. Next unfinished step:
finish Section 8's `lem:fiber_cz` good-part bounds and assemble the one-fiber
weak extension `lem:one_fiber`. Completion criteria are unchanged.

## Task 4 assignment

2026-09-25T21:17:51-04:00 — The user reports Tasks 1-3 complete and merges them into `main`;
the completion gate is rechecked on the merged tree (all three task modules build together,
exported theorems `Auto.smoothing_theorem5`, `Auto.mainTheorem`, `Auto.Twisted.thm_main`).
The user assigns Task 4 to Claude session task4-20260925-2118. Scope: `DFR/Auto/Reduction/`
(plus reusable prerequisites directly in `DFR/Auto/`); main file
`DFR/Auto/Reduction/Reduction.lean`; source `blueprints/main.tex`, target Theorem `thm:main`
(the first theorem). Ledger `Status-task4.md`, discrepancies `ErrorReport-task4.md`.
