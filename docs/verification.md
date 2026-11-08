# Verified scope and remaining gaps

The project checks its Lean statements without project-specific axioms. A source result is marked **verified** only when all of its mathematical conclusions are represented. **Partial** means that the specified component is proved, while the original result still has missing steps. The full manuscript is not yet verified.

## Carrier structure

`UV/CarrierStructure.lean` constructs the actual complex polynomial quotient `C[X]/(X^2-1)` and proves its complex-algebra equivalence with the two character coordinates `C x C`. The project transports the declared reality, norm, and integration structure through that equivalence. It proves character interchange, the absence of normalized positive complex-linear functionals, and the impossibility of identifying this reality with the adjoint in a unital representation on a nonzero positive Hilbert space.

The character estimates include submultiplicativity, absolute integrability under the two majorants, the integral norm bound, the explicit projectors `(1+e)/2` and `(1-e)/2`, and reconstruction of the integral. A generic complete normed-ring pair theorem covers uniform external parameters and matrix coefficients with a chosen submultiplicative norm. These results close `prop:carrier-reality-adjoint` and `prop:character-majorants`. They do not establish positivity of physical states.

## Kernel measures and the exact selected-line moment

`UV/Kernel.lean` uses the literal normalized square-root kernel. Its elementary exponential bounds, positivity, normalization at zero and depth monotonicity are proved.

`UV/KernelMeasure.lean` constructs the actual source density as a `withDensity` measure on the positive real half-line. It proves absence of atoms, absence of a positive support gap, finiteness of all positive inverse moments, and a quantitative Gamma bound at every tempering parameter. At zero tempering it proves the exact Gamma formula, probability normalization, and the first three integer moments `2`, `12`, and `120`.

The same module proves the exact extended inverse-moment/no-atom equivalence and lower-moment implication. Divergence remains extended-valued rather than being assigned the Bochner integral's default zero.

`UV/GlobalConvergence.lean` proves the exact four-dimensional Gaussian radial moment and exchanges its nonnegative Laplace integrations by Tonelli. The massless weighted one-line integral equals

```text
pi^2 Gamma(1+d/2) a^(-2-d) M_(1+d/2).
```

This equality is extended-valued. With a finite representing measure, its finiteness is equivalent to the endpoint inverse moment; massive denominators obey the corresponding upper bound. The full Laplace transform is identified with the positive-half-line transform under explicit nonnegative-support and no-zero-atom hypotheses. Values at zero momentum are handled only through null-set equalities. An independent review of these modules checked the support assumptions, integrability premises and infinity conversions.

`UV/SubordinationChange.lean`, `UV/SubordinationTilt.lean` and `UV/Subordination.lean` now prove the missing general-tempering normalization and transform. The reciprocal-Gaussian integral follows from an actual bijective `x-b/x` change of variables and reciprocal inversion, not from an assumed transform identity. The density's exact Laplace transform is `exp(mu-sqrt(mu^2+z))` on its full admitted real domain. Exact exponential moments below/at the threshold and divergence above it are proved. `UV/HeatMeasure.lean` then constructs the dimensionful heat pushforward, proves its probability and inverse-moment scaling, and identifies its transform with the literal kernel.

The remaining kernel-certificate gap is the Bessel/general-tempering inverse-moment formula and its displayed polynomial specializations. The zero-tempering moments are already exact.

## Graph and sector convergence

`UV/Convergence.lean` checks independent products and common-integrand domination. `UV/RealDegree.lean` proves linear exponential and quadratic Gaussian integrability for arbitrary nonnegative real numerator degree, including the actual `4L`-dimensional Euclidean loop space. Both residual analytic convergence implications are checked.

`UV/Routing.lean` proves the signed affine-shift bound. `UV/Forest.lean` proves the strict scale-power integral `-1/omega`, mixed Gaussian/power scale integrability with finite angular measures, and transfer through finitely many parametrized sectors. Its general weighted variant retains a scale-dependent nonnegative Jacobian in both the pushed-forward measure and the transformed integrand, including ordinary radial factors such as `R^(n-1)`. The measure domination condition makes the covering obligation explicit. Applying it to a graph requires proving that condition for that graph.

The optimized selected-line theorem is complete: `optimized_selected_lines` derives the actual Fourier-normalized bound. An invertible selected matrix constructs its continuous linear equivalence; canonical coordinates recover the routing formula, and `C tensor I4` gives precisely `abs(det C)^(-4)`.

`UV/PolynomialRouting.lean` derives the routed numerator envelope from the original real-degree bound. `UV/SchwingerEnvelope.lean` derives `C_E(z) <= K/z + I_E exp(-alpha0 z)` from the stated proper-time assumptions. Its `global_schwinger_graph` proves actual selected/nonselected line convergence and an explicit uniform external-parameter bound, using exactly the endpoint moment `1+D/2`. `UV/Gap.lean` proves that a positive depth gap supplies all these moments. `UV/JointMajorant.lean` factors the absolute line-parameter integrals and derives actual joint parameter/loop integrability from the established graph majorant; joint integrability is not assumed.

This direct proof avoids needing the manuscript's Gaussian determinant/weighted-shift proof. The remaining gap for marking the original global theorem fully verified is the bare rectangular full-column-rank routing to selected-row construction and exact source-statement assembly. No analytic theorem presumes bounds for unspecified completed vertices.

## Scalar comparison and divergence tests

`UV/AnalyticScalar.lean` defines the actual massive scalar covariance and Fourier-normalized bubble. It proves absolute bubble integrability at positive depth, depth monotonicity, the positive common-subtraction difference-square identity, and the bound by the zero-transfer bubble. It also proves all-order line-kernel depth derivatives and their compact-parameter envelope. For the actual bubble, all-order differentiation under the integral, strict complete monotonicity, and a factorial derivative budget are checked; the source's sharper constant, auxiliary-mass uniformization and complex-depth half-plane remain. The zero-depth logarithmic subtraction limit, finite-part constants, crossovers, external-momentum holomorphy and their uniform estimates remain separate obligations.

`UV/Obstructions.lean` proves that the explicitly displayed zero-transfer Ward trace has limit `-4 e^2 a^2` and is not integrable on four-dimensional loop momentum. The displayed combined constant-background bubble/contact trace has a positive inverse-linear lower bound and is also not integrable. These are genuine integral obstructions. Deriving the displayed traces from Clifford matrices and action-generated vertices, the exact radial exhaustion formulas, nonzero-transfer angular tests, the general radial-damper obstruction and OS positivity counterexample are not yet formalized.

`UV/ReflectionPositivity.lean` proves the literal complex heat Fourier covariance equals its real cosine representation and its actual complex positive-time Hankel matrix fails positive semidefiniteness at all sufficiently small positive spacings. All Gaussian frequency moments, two dominated derivatives and determinant negativity are derived. The passage to smooth positive-time probes/spatial wave packets remains open.

`UV/Grouped.lean` proves convergence of real finite common-routing sums under their own integrable envelope and independence of measurable exhaustion. The holomorphic grouped-integral extension remains open.

## Response certificates

`UV/Response.lean` proves actual Neumann inverse existence, the ordered resolvent identity, the source's exact inverse and Schur norm bounds, the first-order pole-functional error bound and strict positive-rate certificate. It also proves holomorphic inverse/Schur statements for bounded Banach operator families and normalized contour-integral error bounds.

The root-family and residue identification, contour root counts, finite shifted-pole remainder, physical branch interpretation and graph-domain realization remain. A bound on an operator inverse does not establish those claims.

## BRST, reconstruction and crossing

The manuscript explicitly treats the completed BRST/BV functional, invariant anomaly-free integration domain, physical OS completion and cut matching as hypotheses. The project has not constructed those objects or formalized the entire conditional pipeline. A conditional theorem may quantify over a rigorously defined such structure; that differs from declaring its desired conclusion as a new trusted axiom. A graded functional/Legendre framework and formal versions of the cited external reconstruction/crossing theorems are still needed.

No physical interacting completion, convergence of the infinite perturbation series, or unconditional scattering result follows from the checked estimates.

## Trust and reproduction

Lean and mathlib are pinned. The compiler treats warnings as errors. `scripts/audit.py` checks both every named local theorem/lemma and every declaration under the compiled `UV` namespace, transitively allowing only `propext`, `Classical.choice` and `Quot.sound`. The namespace check was also tested against an unlisted custom axiom and rejected it. `scripts/claims.py` checks the unchanged upload hash and regenerates all 48 source environments with their status.

The logical axiom audit and the mathematical source-to-formal-statement review are complementary checks. A green build establishes precisely the formal statements in the current modules.
