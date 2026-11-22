# Lean 4.32 companion verification

This independent companion closes `prop:OQED-observable-residue-error` for an arbitrary positively oriented rectifiable simple contour. It rebuilds the complete contour, matrix and operator proof chain under Lean 4.32.2. The root project retains Lean 4.24.0; compiled proofs are never imported across toolchain versions.

The expanded edition also uses this toolchain for the [critical Poisson opening limit](UV/FurtherOpeningCriticalLimit.lean) and the [boundary overlap Sobolev criterion](UV/NextOverlapCriterion.lean). The criterion constructs the weak spectral phase of the displacement PVM and proves the two-way density test with the exact normalized Bessel norm. Their hypotheses and coverage are recorded in the [expanded inventory](../docs/claims-expanded.md).

The main endpoint is [`observable_rectifiable_jordan_residue_error_compatible`](UV/CompatibleJordanObservableError.lean). It proves the exact original-length error constant and strict visibility consequence for actual inverse-observable residues, allowing different enclosed poles and vanishing readout residues. The retained space is finite-dimensional, the input is an arbitrary normed complex space, and the output may be any complex Banach space. Every bound remains in the original compatible operator norm. Coordinates are constructed from any finite basis and introduce no norm-equivalence constants.

[`JordanContourGeometry.lean`](UV/JordanContourGeometry.lean) derives the filling from the original simple closed path and the proved Jordan–Schoenflies theorem. It does not assume a filling or simply-connected neighbourhood. The removable regular part is analytic near the actual filled contour; scalar Cauchy integration and continuous dual separation handle Banach readouts. The arc-length construction preserves ordered traversal and original geometric length. No contour/residue identity or nonzero readout overlap is an input.

The exact dependencies are:

- Lean `leanprover/lean4:v4.32.2`.
- [mathlib](https://github.com/leanprover-community/mathlib4/tree/905b95818eb32af7874a58b427f50c1711a5e96c), revision `905b95818eb32af7874a58b427f50c1711a5e96c`.
- [schoenflies-lean](https://github.com/alonamaloh/schoenflies-lean/tree/05a43d29cde026618777db3d4e4316204ccca237), revision `05a43d29cde026618777db3d4e4316204ccca237`, under Apache 2.0. Its actual square-extension theorem supplies the topology proof. The upstream Comparator challenge library is not imported.

`uv-port-manifest.json` records the original root source revision and the hashes of the 31 independently rechecked contour modules, together with their compatibility changes. Copyright notices are retained; the former Poincare backport now invokes the pinned mathlib's identical native theorem.

From this directory, with elan and Python 3.11 or newer:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
python3 scripts/fetch_cache.py
lake build
python3 scripts/audit.py
```

The cache step is optional. The audit checks every local theorem and declaration, every imported Schoenflies declaration and the mandatory square-extension anchor. The permitted transitive axioms are `propext`, `Classical.choice` and `Quot.sound`.
