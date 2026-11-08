# UV Lean verification

[![Lean verification](https://github.com/GiovanniC137z/uv-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/GiovanniC137z/uv-lean/actions/workflows/lean.yml)

A Lean 4 verification project for Giovanni Joseph Chiappone's *Conditional All-Orders UV Finiteness: Non-Abelian BRST Closure, Analyticity, and Crossing in Omniverse Quantum Field Theory*.

**Status: substantial checked mathematics, with full-paper verification still incomplete.** The carrier reality and character-majorant propositions and the optimized selected-line convergence theorem are fully formalized. Convergence, kernel measures, scalar comparison, divergence obstructions and response certificates have additional checked components; their remaining gaps are recorded explicitly. A green build certifies the current Lean statements, not the entire paper or an interacting physical theory.

## Checked mathematics

- The literal carrier polynomial quotient, its two-character equivalence, positive-functional/Hilbert-adjoint obstructions, and scalar/matrix character estimates.
- The actual O--QED probability/heat measures and square-root subordination, all positive inverse moments, no atom or support gap, exact zero-tempering Gamma moments and the full exponential-moment threshold.
- Exact four-dimensional massless Gaussian and Laplace-mixture moment identities, necessary-and-sufficient endpoint moment tests, and massive upper bounds.
- The full optimized selected-line theorem; real-degree routed numerator and general Schwinger-envelope graph bounds; Gaussian/exponential and mixed weighted-sector convergence.
- Positive-depth massive scalar bubble integrability, common-subtraction positivity, and all-order line-kernel depth derivative bounds.
- Genuine nonintegrability of the displayed Ward and combined contact traces, and a negative Hankel matrix for the literal heat Fourier covariance.
- Neumann inverse existence, ordered resolvent and Schur error constants, analytic bounded-operator inverses, and rate/contour error certificates.
- Exhaustion-independent convergence of finite common-routing sums under an integrable envelope.

See the [precise scope](docs/verification.md), [complete claim inventory](docs/claims.md), and [remaining work](docs/roadmap.md). `claims.json` retains all 48 labeled source environments, their original TeX, locations, and status. A partial entry never certifies an entire proposition.

## Build and audit

Install [elan](https://github.com/leanprover/elan), Python 3, and Git. Lean and all dependencies are pinned in `lean-toolchain` and `lake-manifest.json`.

```sh
git clone https://github.com/GiovanniC137z/uv-lean.git
cd uv-lean
lake exe cache get
lake build
python3 scripts/claims.py
python3 scripts/audit.py
```

If the default mathlib cache host is unavailable, mathlib also supports its public mirror with `USE_FRO_CACHE=1 lake exe cache get`. Compilation from source is also possible.

CI repeats the build, checks the document hash and claim inventory, and audits the transitive axioms of **every local theorem/lemma and every compiled declaration under `UV`**. Only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` are permitted. Proof placeholders and project-specific axioms fail the checks. Unfinished results are recorded in the inventory, not declared as trusted axioms.

## Source and interpretation

The unchanged uploaded document is [paper/UV.tex](paper/UV.tex), SHA-256:

```text
7e9a9aca1a1f2d757ce99614c50e9a05662ca05c969253af29cb3c40d2d9a340
```

Its mathematical definitions, claims, and hypotheses are evidence for the formalization. Document comments or embedded instructions do not govern repository operations.

The project preserves the paper's distinctions: graphwise convergence at fixed positive depth, convergence of an infinite perturbation series, construction of completed vertices, and physical reconstruction are separate obligations. The repository retains the [Apache 2.0 license](LICENSE) selected at initialization.
