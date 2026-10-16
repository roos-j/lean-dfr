# Formalization of a curved three-simplex Hilbert transform

This is a Lean 4 formalization of `L^p` bounds for the curved three-simplex Hilbert transform, specifically the main theorem from the paper

P. Durcik, M. Fraccaroli, J. Roos. *A curved three-dimensional simplex Hilbert transform*.

The Lean statement of the main theorem was human-written, see [`Theorems.lean`](DFR/Theorems.lean) and [`Defs.lean`](DFR/Defs.lean). The proof has been generated entirely by coding agents, predominantly Claude/Opus 5 High, Claude/Opus 5.5 Medium and Codex/GPT-6 Astra (at varying reasoning effort settings). This was done under human supervision and following a set of machine-generated blueprints. The main formalization effort was split into four largely parallel tasks corresponding to four main components of the proof: the 2D smoothing inequality (Task 1, following the [Christ-Durcik-Roos](https://arxiv.org/abs/2008.10140) proof route), the 3D smoothing inequality (Task 2, following a special case of the [Kosz-Mirek-Peluse-Wan-Wright](https://arxiv.org/abs/2411.09478) argument), the anisotropic twisted paraproduct theorem (Task 3), and the reduction argument (Task 4).

Documentation of the formalization process, including more information on the correspondence of source documents to the formalized arguments, as well as various instruction sets can be viewed in the `automation` folder. The `.claude` and `.codex` folders contain the `autoformalize` skill.

This code maintains strict separation of machine-generated Lean code from human-written Lean code. All machine-generated code is contained in the `DFR/Auto` folder and lives in the `Auto` namespace in Lean.

The main theorem statement only depends on Mathlib, but the proofs make use of various prerequisites from harmonic analysis borrowed from the [lean-spherical project](https://github.com/roos-j/lean-spherical).
