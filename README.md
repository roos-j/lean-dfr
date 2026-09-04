# Formalization of DFR

This is a Lean 4 project built on the [`lean-spherical`](https://github.com/roos-j/lean-spherical)
formalization. The dependency is declared in `lakefile.toml`; Mathlib is used only as a
transitive dependency of `lean-spherical`.

To fetch dependencies and build the project:

```text
lake exe cache get!
lake build
```
