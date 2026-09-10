# Repository agent instructions

Read [automation/instructions.md](automation/instructions.md), then
[automation/tasks.md](automation/tasks.md), [automation/Status.md](automation/Status.md),
and [automation/ErrorReport.md](automation/ErrorReport.md) before working.

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
