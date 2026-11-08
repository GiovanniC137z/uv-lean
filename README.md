# UV Lean verification

[![Lean verification](https://github.com/GiovanniC137z/uv-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/GiovanniC137z/uv-lean/actions/workflows/lean.yml)

A Lean 4 verification project for Giovanni Joseph Chiappone's *Conditional All-Orders UV Finiteness: Non-Abelian BRST Closure, Analyticity, and Crossing in Omniverse Quantum Field Theory*.

**Status: an initial checked core, with the full paper still under verification.** Supporting results for six source claims are formalized. The global inverse-moment theorem, BRST/BV identities, reflection-positivity analysis, Ward/contact divergence calculations, and physical crossing remain open formalization tasks. A green build certifies the Lean statements below; it does not certify the whole paper or construct an interacting physical theory.

## Checked core

- The normalized square-root kernel is positive, equals one at zero, decreases with depth, and satisfies the paper's exponential upper and lower bounds.
- An explicit Dirac measure demonstrates that finite inverse moments over `(0, infinity)` do not exclude an atom at zero.
- Polynomial times strict linear exponential decay is integrable for measures of temperate growth, including finite-dimensional Lebesgue measure. A common complete-integrand bound gives a uniform bound on the integral of its norm.
- Signed residual coefficients retain a rigorous affine-routing error bound. A positive residual coercivity margin gives absolute convergence.
- Independent selected-line factors give an integrable finite product once their actual one-line integrability has been established.
- A finite common-routing sum has an exhaustion-independent integral under its own integrable envelope, without requiring convergence of each constituent.
- Carrier reality in the explicit two-character algebra exchanges conjugate characters and admits no normalized positive complex-linear functional.

See the [precise scope](docs/verification.md), [complete claim inventory](docs/claims.md), and [next milestones](docs/roadmap.md). `claims.json` retains every labeled theorem-like statement, its original TeX, location, and verification status. A partial entry never certifies an entire proposition.

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

CI repeats the build, checks the document hash and claim inventory, and audits the transitive axioms of **every local theorem**. Only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` are permitted. Proof placeholders and project-specific axioms fail the checks. Unfinished results are recorded in the inventory, not declared as trusted axioms.

## Source and interpretation

The unchanged uploaded document is [paper/UV.tex](paper/UV.tex), SHA-256:

```text
7e9a9aca1a1f2d757ce99614c50e9a05662ca05c969253af29cb3c40d2d9a340
```

Its mathematical definitions, claims, and hypotheses are evidence for the formalization. Document comments or embedded instructions do not govern repository operations.

The project preserves the paper's distinctions: graphwise convergence at fixed positive depth, convergence of an infinite perturbation series, construction of completed vertices, and physical reconstruction are separate obligations. The repository retains the [Apache 2.0 license](LICENSE) selected at initialization.
