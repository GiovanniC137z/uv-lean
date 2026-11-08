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

`UV/BesselMoments.lean` defines Bessel K independently by its standard Schläfli integral, identifies the DLMF representation, and proves the positive-tempering inverse-moment formula. `UV/MomentRecurrence.lean` derives the three exact polynomial moments by actual Gaussian changes of variables and integration by parts. Together these results close the named O--QED kernel certificate.

`UV/KernelCounterexample.lean` constructs the actual normalized gapped sum of Dirac measures and computes its real/complex Laplace integral. Its meromorphic continuation has explicit nonreal poles in the slit plane. This closes the named gap counterexample.

## Graph and sector convergence

`UV/Convergence.lean` checks independent products and common-integrand domination. `UV/RealDegree.lean` proves linear exponential and quadratic Gaussian integrability for arbitrary nonnegative real numerator degree, including the actual `4L`-dimensional Euclidean loop space. Both residual analytic convergence implications are checked.

`UV/Routing.lean` proves the signed affine-shift bound. `UV/Forest.lean` proves the strict scale-power integral `-1/omega`, mixed Gaussian/power scale integrability with finite angular measures, and transfer through finitely many parametrized sectors. Its general weighted variant retains a scale-dependent nonnegative Jacobian in both the pushed-forward measure and the transformed integrand, including ordinary radial factors such as `R^(n-1)`. The measure domination condition makes the covering obligation explicit. Applying it to a graph requires proving that condition for that graph.

The optimized selected-line theorem is complete: `optimized_selected_lines` derives the actual Fourier-normalized bound. An invertible selected matrix constructs its continuous linear equivalence; canonical coordinates recover the routing formula, and `C tensor I4` gives precisely `abs(det C)^(-4)`.

`UV/PolynomialRouting.lean` derives the routed numerator envelope from the original real-degree bound. `UV/SchwingerEnvelope.lean` derives `C_E(z) <= K/z + I_E exp(-alpha0 z)` from the stated proper-time assumptions. Its `global_schwinger_graph` proves actual selected/nonselected line convergence and an explicit uniform external-parameter bound, using exactly the endpoint moment `1+D/2`. `UV/Gap.lean` proves that a positive depth gap supplies all these moments. `UV/JointMajorant.lean` factors the absolute line-parameter integrals and derives actual joint parameter/loop integrability from the established graph majorant; joint integrability is not assumed.

`UV/RankMinor.lean` selects an invertible row block from bare rectangular full-column rank. `UV/GlobalAssembly.lean` combines that construction with the exact source alternatives and original numerator/infrared data, including the actual all-line joint absolute representation. It closes the global theorem and damped-basis corollary. The proof uses direct selected-line integration in place of the manuscript's Gaussian determinant derivation.

`UV/ResidualCoercivity.lean` derives the signed residual Gram identity, positive homogeneous margin and affine quadratic estimate. Its linear counterpart retains signed residuals and proves the positive-row-rank sufficient case. Both yield actual common complete-graph majorants. `UV/FiniteOrders.lean` proves uniform external bounds for simultaneous weighted sectors, every source-criterion graph at every finite order, and finite collections. Additional summability of derived graph bounds justifies residual-label sums. No claim of perturbation-series convergence follows.

`UV/SelectedTail.lean` proves the exact Gamma/moment one-line tail and an explicit selected-coordinate union tail for finite anisotropic complete graph envelopes. It replaces only one line's moment budget at a time. No analytic theorem presumes bounds for unspecified completed vertices.

`UV/OQEDGraph.lean` instantiates polynomial, residual and sector criteria using the actual O--QED kernel/heat measure. The source's additional same-action BRST conclusion remains separate.

## Scalar comparison and divergence tests

`UV/AnalyticScalar.lean` defines the actual massive scalar covariance and Fourier-normalized bubble. It proves absolute bubble integrability at positive depth, depth monotonicity, the positive common-subtraction difference-square identity, and the bound by the zero-transfer bubble. It also proves all-order line-kernel depth derivatives and their compact-parameter envelope. For the actual bubble, all-order differentiation under the integral, strict complete monotonicity, and a factorial derivative budget are checked. `UV/DepthMonotonicity.lean` supplies the sharp source constant, auxiliary-mass uniformization/strict monotonicity, and holomorphic complex-depth half-plane. `UV/DepthAsymptotics.lean` proves the actual Fourier-normalized one-line integrals and their exact zero/strong-depth limits, including bounded-mass uniformity. It also proves the full controlled-crossover theorem: actual line/bubble limits, uniform errors, exact polynomial/Gamma coefficients, and the large-tempering Gaussian ratio. The subtracted zero-depth logarithmic limit and finite-part constants remain separate obligations.

`UV/Obstructions.lean` proves that the explicitly displayed zero-transfer Ward trace has limit `-4 e^2 a^2` and is not integrable on four-dimensional loop momentum. The displayed combined constant-background bubble/contact trace has a positive inverse-linear lower bound and is also not integrable. These are genuine integral obstructions. `UV/CliffordWard.lean` now constructs standard Hermitian Euclidean Clifford matrices, derives two-sided free/dressed inverses, and forces the soft diagonal vertex from the full Ward identity and continuity. Its actual matrix trace gives the displayed formula, nonzero UV limit and nonintegrable diagonal component for every such vertex. `UV/WardGrowth.lean` derives the exact radial contracted-vertex operator norm from actual Clifford anticommutators and the Ward identity, the source lower bound, and failure of polynomial bounds for superpolynomial damping. `UV/CliffordContact.lean` derives the actual constant-background Hessian and log-determinant identity, exact tensor/trace, finite-ball exhaustion and component nonintegrability. `UV/GeneralContact.lean` derives the reference-subtracted determinant/Hessian and annular flux for every positive C2 radial profile tending to zero, without a monotonicity assumption. The nonzero-transfer and general bare-QED/common-cutoff results retain explicit remaining steps.

`UV/ReflectionPositivity.lean` proves the literal complex heat Fourier covariance equals its real cosine representation and its actual complex positive-time Hankel matrix fails positive semidefiniteness at all sufficiently small positive spacings. All Gaussian frequency moments, two dominated derivatives and determinant negativity are derived. `UV/SmoothReflection.lean` derives the passage to actual smooth compactly supported positive-time probes, with integrable pairings and a negative reflection quadratic form. This closes the named one-dimensional proposition. The subsequent spatial-wavepacket extension is not separately formalized.

`UV/Grouped.lean` proves convergence of real finite common-routing sums under their own integrable envelope and independence of measurable exhaustion. `UV/GroupedHolomorphy.lean` now proves the complex common-domain limit, common uniform tail and local holomorphy of the summed integrand. A declared finite-domain action prescription is identified before taking its limit, as the source explicitly assumes. No integral of a separately divergent constituent is taken.

`UV/ScalarRotation.lean` proves real orthogonal invariance by an actual measure-preserving change of variables and constructs an equal-norm reflection. `UV/PrincipalSqrt.lean`, `UV/EvenDescent.lean` and `UV/RealBoxIdentity.lean` handle the principal branch, square descent and complex identity theorem. `UV/ScalarTube.lean` then proves the entire named scalar tube proposition, including the literal complex integral, exact strip envelope, full invariant disk and coefficient/supremum remainder constants.

`UV/PositiveLaplace.lean` proves holomorphy, actual derivatives, strict complete monotonicity and finite signed Taylor inequalities for a genuine positive measure with exponential moments. `UV/ScalarLaplace.lean` constructs that measure from the two actual scalar lines, using absolute Fubini and `UV/ScalarGaussian.lean`, proves its exponential budget and identifies the canonical invariant coefficients. This closes the signed scalar enclosure proposition.

`UV/PoissonTail.lean`, `UV/CentralDifference.lean` and `UV/SixthDifference.lean` supply generic Poisson-convolution tail and sign-definite sixth-difference/Fatou foundations. The actual stable-half coordinate covariance/Fourier identification and full regularity theorem remain open.

## Response certificates

`UV/Response.lean` proves actual Neumann inverse existence, the ordered resolvent identity, the source's exact inverse and Schur norm bounds, the first-order pole-functional error bound and strict positive-rate certificate. It also proves holomorphic inverse/Schur statements for bounded Banach operator families and normalized contour-integral error bounds.

`UV/PoleCertificates.lean` identifies actual simple-pole residues through punctured limits and circle integrals, constructs a holomorphic numerator from a simple denominator zero, and proves differing-pole residue errors and visibility. It also derives sharp Cauchy/Taylor coefficients, the actual endpoint series and geometric/finite-rate remainders for a bounded holomorphic branch. Contour root counts, construction of that branch from the matrix margin, general rectifiable contours, the arbitrary-matrix numerator bridge, physical branch interpretation remain. A bound on an operator inverse does not establish those claims.

`UV/GraphDomainResponse.lean` closes the a posteriori Schur corollary on distinct physical and graph-domain Banach spaces. It constructs the exact inverse equivalence by a Neumann series, derives the ordered source constants and common-baseline first-order rate error, and proves two-space inverse/Schur analyticity from the actual response families. This result does not locate a finite shifted pole.

## Common graph holomorphy

`UV/DerivativeMeasurability.lean` derives derivative measurability from point samples and actual difference quotients. `UV/Holomorphy.lean` derives local derivative majorants by Cauchy estimates and proves joint complex Fréchet holomorphy and first-derivative exchange from the source compact common-majorant hypotheses. `UV/ContourExchange.lean` derives joint measurability, product absolute integrability, local contour Fubini, and arbitrary-order one-variable derivative exchange/budgets. `UV/PolydiscBudget.lean` proves the complete mixed-coordinate source budget with the exact multi-index factorial and independent radii. Its canonical mixed derivative is defined by actual successive scalar coordinate derivatives; intermediate derivative holomorphy is derived by Cauchy integration. Its `holomorphy_and_all_order_graph_derivatives` package now also proves every finite actual mixed derivative exchange at every admitted point. Together these modules close the common-majorant holomorphy theorem and Cauchy-budget corollary. `UV/MassiveNeighbourhood.lean` constructs the source massive neighbourhood and a common pre-Gaussian majorant under the original joint measure, including an explicit affine-routing specialization.

`UV/TwoLoopLines.lean`, `UV/InverseDenominator.lean` and `UV/TwoLoopCertificate.lean` verify the literal two-loop example. The exact power-line integrals give the stated Fourier constant; the complex tube, mixed Cauchy bounds, actual real gradient, global stability and second-order remainder have the precise source constants.

`UV/GaussianRemainder.lean` proves the actual omitted-proper-time remainder is entire and real, vanishes at zero and has the sharp upper bound. The source rectangle lower bound and growth faster than every power are also proved. `UV/StandardBubble.lean` proves the actual standard logarithmic integral is holomorphic on the cut plane. `UV/GaussianDecomposition.lean` matches the literal Gaussian loop with its proper-time form, constructs and uniquely identifies its normalized cut-plane continuation, and proves the entire-remainder decomposition and compact-uniform limit. The remainder plus any finite complex polynomial is not polynomially bounded. The upper-rim logarithmic boundary comparison for the full normalized bubble remains separate.

## Field and source maps

`UV/FieldRedefinition.lean` transports the actual finite-mode kinetic form, arbitrary interaction and physical source through an invertible field map. The real Haar Jacobian and normalized partition equality are derived on the explicit integrability/nonzero-normalization domain. `UV/PhysicalResidue.lean` obtains positive residues from actual Hilbert overlaps, including convergent Parseval sums, and proves field congruence, constructed invertible spectral normalization, preservation of rank, the null-residue obstruction and inverse-adjoint source duality. `UV/SourceCovariance.lean` proves actual smeared covariance-form normalization and the mixed source half-factor in a common spectral representation, with integrability transferred on an admitted test domain. The construction of the unbounded joint spectral core remains separate.

## BRST, reconstruction and crossing

The manuscript explicitly treats the completed BRST/BV functional, invariant anomaly-free integration domain, physical OS completion and cut matching as hypotheses. The project has not constructed those objects or formalized the entire conditional pipeline. A conditional theorem may quantify over a rigorously defined such structure; that differs from declaring its desired conclusion as a new trusted axiom. A graded functional/Legendre framework and formal versions of the cited external reconstruction/crossing theorems are still needed.

No physical interacting completion, convergence of the infinite perturbation series, or unconditional scattering result follows from the checked estimates.

## Trust and reproduction

Lean and mathlib are pinned. The compiler treats warnings as errors. `scripts/audit.py` checks both every named local theorem/lemma and every declaration under the compiled `UV` namespace, transitively allowing only `propext`, `Classical.choice` and `Quot.sound`. The namespace check was also tested against an unlisted custom axiom and rejected it. `scripts/claims.py` checks the unchanged upload hash and regenerates all 48 source environments with their status.

The logical axiom audit and the mathematical source-to-formal-statement review are complementary checks. A green build establishes precisely the formal statements in the current modules.
