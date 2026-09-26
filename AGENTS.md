# Repository agent instructions

Read [automation/instructions.md](automation/instructions.md), then
[automation/tasks.md](automation/tasks.md), and the status ledger and error report of your task,
`automation/Status-taskN.md` and `automation/ErrorReport-taskN.md` (N = 1, 2, 3, 4), before working.

Read and follow [.codex/skills/autoformalize/SKILL.md](.codex/skills/autoformalize/SKILL.md)
for Codex. If absent, use ~/.codex/skills/autoformalize/SKILL.md (or
$CODEX_HOME/skills/autoformalize/SKILL.md when configured).
Claude agents use [.claude/skills/autoformalize/SKILL.md](.claude/skills/autoformalize/SKILL.md).

The user's current explicit instructions take precedence over all repository
guidance. Local automation instructions supersede conflicting skill guidance.

Every proof agent must be assigned exactly one of the four tasks in
automation/tasks.md. A coordinator assigns a ready unowned task and records the
owner before the worker edits. An unassigned worker must obtain an assignment,
not choose a folder silently. Keep all task work in its assigned folder and
report shared-record updates to the coordinator. Do not start Task 4 until
Tasks 1-3 meet the documented completion gate and its blueprint is available.

The canonical generated-source directory in this repository is `DFR/Auto/`. Reuse its four existing task subdirectories. Do not create a repository-root `Auto/` directory. Keep the Lean namespace `Auto`; filesystem location and namespace are separate. Verify Task 1 with `lake env lean DFR/Auto/SmoothingIneq2D/Smoothing2D.lean` and preserve the existing Lake configuration.
