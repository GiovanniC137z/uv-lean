# What the current Lean build establishes

The statements in `UV/` are proved without project-specific axioms. The source mapping in `verification.json` deliberately marks every touched named source result as **partial**. Hypotheses about an actual action, completed vertices, routing, and physical observables must still be justified for any proposed application.

## Kernel

`UV/Kernel.lean` defines the source functions literally:

```text
h_M(u) = sqrt(u + M^2) - M
F(a,M,u) = exp(-a h_M(u)).
```

For nonnegative kinetic variable, scale, and depth, the proofs establish normalization, positivity, the bound by one, both exponential envelopes, and monotonicity in depth. The envelopes use the independent auxiliary scale `M`; it is not identified with the electron mass.

`UV.inverseMoment` is an **extended-valued** nonnegative integral on the positive half-line. This avoids the convention that a nonintegrable Bochner integral is assigned zero. The separate `laplace` definition is only used for a Dirac-measure example, where integrability is automatic. `UV.inverseMoment_does_not_exclude_atom` and `UV.laplace_dirac_zero` verify the warning immediately preceding `thm:global-uv`: the measure concentrated at zero has excluded-zero inverse moment zero and constant Laplace transform one.

The measure is represented on the real line and the moment integrates over its positive half-line. A future general Laplace-kernel theorem must explicitly impose support on the nonnegative half-line, finite positive mass, and absence of an atom at zero. The current definitions alone impose none of these assumptions.

The density/subordination identity, its normalization as a probability measure, the Bessel formulas, and finiteness of all of that density's inverse moments are not yet proved.

## Convergence

`UV.integrable_norm_pow_exp` proves, for any natural degree `n` and `a > 0`,

```text
x ↦ norm(x)^n exp(-a norm(x)) is integrable.
```

Its domain is any normed space with a Borel measure of temperate growth. Mathlib supplies that property for Haar measures on finite-dimensional real normed spaces. No finite-dimensional graph integral is assumed integrable as a premise. The proof uses a factorial/exponential estimate and mathlib's integrable inverse-power majorant.

`UV.graph_integrable_of_common_bound` and `UV.uniform_integral_norm_bound` apply this result when the *complete* measurable integrand, uniformly in its external parameter, obeys a supplied polynomial/exponential bound. This includes all numerator, vertex, contact, denominator, and source factors in the function being bounded. An exponential bound on an isolated propagator does not discharge this hypothesis.

`UV.residual_linear_convergence` proves convergence from a supplied inequality

```text
psi(p,k) >= a norm(k) - B,  a > 0.
```

`UV.signed_affine_coercivity` derives the affine version from a homogeneous coercivity certificate and uniform shift bounds, including negative line residuals. The current formalization does not derive coercivity from matrix rank or a smallest singular value. It also does not formalize the quadratic case or arbitrary real numerator degrees.

`UV.oqed_complete_integrand_convergence` combines the literal normalized kernel envelope with the analytic theorem for a stronger sufficient subclass, where the kernel bounds the full loop norm. Deriving that bound from selected routed line factors remains a task. It is not assumed to hold for the paper's Ward or contact tests.

`UV.selected_product_integrable` checks the finite product integration step under supplied one-line integrability. It does not prove the four-dimensional massless radial/Gamma identity, establish the inverse-moment criterion, or perform the affine routing change of variables.

## Grouping and carrier reality

`UV/Grouped.lean` proves absolute convergence and the limit along a measurable exhaustion for a real-valued finite pointwise sum dominated by an integrable envelope. The result applies to any exhaustion with eventual membership almost everywhere, so each such exhaustion has the same limiting integral. Individual terms need not be integrable. Holomorphy of a grouped integral remains open.

`UV/Carrier.lean` works in the explicit character model `Complex x Complex`, with componentwise multiplication and reality `(z+,z-) ↦ (conj(z-),conj(z+))`. It proves character interchange, involutivity, and the no-positive-functional obstruction using the generator `(1,-1)`. The quotient presentation `Complex[e]/(e^2-1)` has not yet been formally identified with this model, and the Hilbert-representation consequence has not been separately proved.

## Trust and reproducibility

`scripts/audit.py` regenerates a list of every local theorem from source and checks its transitive axiom dependencies with Lean's `#print axioms`. Missing entries and axioms beyond `propext`, `Classical.choice`, and `Quot.sound` fail the check. The compiler treats warnings as errors. `scripts/claims.py` verifies the unchanged upload hash and regenerates the entire source inventory, preventing a status table from silently dropping unproved claims.

The audit establishes logical dependence of the formal statements. Checking that their definitions and hypotheses faithfully represent the manuscript is a separate mathematical review, aided by the explicit source mapping and limitations above.
