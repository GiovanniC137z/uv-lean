# UV Lean verification

[![Lean verification](https://github.com/GiovanniC137z/uv-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/GiovanniC137z/uv-lean/actions/workflows/lean.yml)

A Lean 4 verification project for Giovanni Joseph Chiappone's *Conditional All-Orders UV Finiteness: Non-Abelian BRST Closure, Analyticity, and Crossing in Omniverse Quantum Field Theory*.

**Status: 41 of 45 named mathematical results are verified; four remain partial. Full-paper verification remains incomplete.** The checked results include the original convergence theorems, exact kernel certificate, scalar analyticity and nonanalyticity results, Ward/contact obstructions, and finite-matrix pole certificates. The claim inventory distinguishes complete results from remaining components. A green build certifies the current Lean statements, not the entire paper or an interacting physical theory.

## Checked mathematics

- The literal carrier polynomial quotient, its two-character equivalence, positive-functional/Hilbert-adjoint obstructions, and scalar/matrix character estimates.
- The actual O--QED probability/heat measures and square-root subordination, all inverse moments with exact Bessel/Gamma formulas and polynomial cases, and the full exponential-moment threshold.
- Exact four-dimensional line moments, full-rank routing construction, global joint-parameter convergence, independent line multipliers, and quantitative selected-coordinate graph tails.
- Signed residual Gram/sphere coercivity, simultaneous weighted sectors, graphwise finite-order convergence, and summed-label amplitudes under summable derived majorants.
- Literal scalar bubble depth derivatives, complex-depth and external-momentum holomorphy, exact depth/crossover limits, positive proper-time Laplace representation, and signed Taylor enclosures.
- Actual common zero-depth subtraction with its uniform logarithmic limit/slope, and the universal unsubtracted Euler finite part with explicit error constants.
- The Gaussian loop’s unique normalized cut-plane continuation, actual upper-rim boundary, entire remainder, exact upper/lower bounds, and growth obstruction for both the remainder and normalized boundary after any finite polynomial addition.
- The literal stable-half bubble’s real C5 regularity and failure of C6 at zero, with exact Poisson/Green Fourier identities and coordinate-space tail.
- Actual joint external holomorphy, derivative/contour exchange and Cauchy estimate components from common graph majorants.
- Clifford-matrix derivation of zero/nonzero-transfer Ward and contact obstructions, the exact common-cutoff Ward identity, the general bare-QED one-loop integrability criterion including zero mass and its exact convolution-moment test, and smooth positive-time probes violating heat-covariance reflection positivity.
- Exact finite-mode field-redefinition/Jacobian cancellation, bounded spectral-cut source normalization by C*-functional calculus, and Hilbert-overlap residue positivity with a constructed invertible spectral normalization.
- Actual disk argument principle and zero-count homotopy, full finite-matrix pole enclosures, contour-constructed holomorphic root families and sharp Taylor/rate remainders, with Neumann/Schur inverse and actual matrix observable-residue formulas.
- Exhaustion-independent finite common-routing sums and the gapped positive-measure meromorphic counterexample.

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
