# Autoformalization tasks

This is the authoritative task assignment and readiness registry.
Proof progress and verification evidence belong in [Status.md](Status.md).

| Task | Target/source | Exclusive work folder | Main file | Owner | Readiness |
| --- | --- | --- | --- | --- | --- |
| 1 | Trilinear smoothing inequality, Theorem 5, [arXiv:2008.10140](https://arxiv.org/abs/2008.10140) | Auto/SmoothingIneq2D/ | Auto/SmoothingIneq2D/Smoothing2D.lean | Codex root task1-20260910-0955 | Active; Lemmas 3.1-3.3 verified; (3.1) verified; frequency and amplitude reductions in progress |
| 2 | 3d smoothing inequality; user blueprint pending in blueprints/ | Auto/SmoothingIneq3D/ | Select from blueprint within folder | Unassigned | Blocked: blueprint missing |
| 3 | Twisted; user blueprint pending in blueprints/ | Auto/Twisted/ | Select from blueprint within folder | Unassigned | Blocked: blueprint missing |
| 4 | Reduction: use Tasks 1-3 to prove the main theorem; user blueprint pending in blueprints/ | Auto/Reduction/ | Select from blueprint within folder | Unassigned | Blocked: Tasks 1-3 incomplete and blueprint missing |

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
   do not edit another task or place new prerequisites directly in Auto/.
5. On handoff, record the actual declarations, source mappings, checks, remaining
   obligations, and next step in Status.md; update owner/readiness here.
   Never treat an absent or disconnected agent as evidence its task is complete.

## Completion gate

A task is complete only when all of its source targets and required prerequisites
are faithfully proved, owned sources pass direct lake env lean checks with the pinned toolchain, the configured project passes lake build,
and #print axioms on the exported results shows only a subset of propext,
Classical.choice, and Quot.sound. No sorryAx, additional axioms, unproved bridges,
weakened targets, or placeholders may underlie a completed task. Record the
exported module/declaration names, exact source/version, build result, axiom
output, and local verification timestamp in Status.md.

Before assigning Task 4, the coordinator must verify all three prerequisite
tasks against this evidence and current source, mark each complete, confirm the
Reduction blueprint is present and read, and record that the gate passed.
Only then may a Reduction agent begin. Task 4 imports and uses the established
results of Tasks 1-3; it does not assume them as axioms or rewrite their proofs.

## Initial assignment state

No proof agents have been assigned by the setup operation. Empty folders and
the Task 1 starter module are infrastructure only; all four proofs are not started.

## Task 1 assignment

2026-09-10T09:56:31.1092542-04:00 — Coordinator assigns Codex root task1-20260910-0955 exactly Task 1, trilinear smoothing inequality. Scope: Auto/SmoothingIneq2D/; main file Smoothing2D.lean; source arXiv:2008.10140v2, Theorem 5. Next unfinished step: read the exact theorem and full dependency proof, then record forward proof order. Completion requires faithful source coverage, direct verification of owned Auto sources, lake build for configured targets, and the allowed-axiom audit. The root agent maintains shared records serially.


2026-09-10T11:01:54.9581411-04:00 - Coordinator resumes the existing Codex root task1-20260910-0955 assignment for exactly Task 1. Scope and completion gate above remain unchanged. Next: finish Theorem 5 and Section 3 source/dependency audit.
