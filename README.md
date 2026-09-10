# Formalization of DFR

This is a Lean 4 project built on the [`lean-spherical`](https://github.com/roos-j/lean-spherical)
formalization. The dependency is declared in `lakefile.toml`; Mathlib is used only as a
transitive dependency of `lean-spherical`.

To fetch dependencies and build the project:

```text
lake exe cache get!
lake build
```

Autoformalization assignments and folder boundaries are in
[automation/tasks.md](automation/tasks.md). Start with [AGENTS.md](AGENTS.md).
Both Codex and Claude autoformalize skills are vendored locally.
The default build includes all Lean modules under Auto/.
