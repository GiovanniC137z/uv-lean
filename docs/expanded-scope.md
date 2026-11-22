# Expanded manuscript verification

The expanded upload is [paper/expanded/UV.tex](../paper/expanded/UV.tex). Its title is *Geo-Phase Suppression and Ultraviolet Finiteness in PE-CGG-HOUQFT: The Curvature Action, Raw O-QED, and the Induced Electromagnetic Sector*. The upload identifies this version as DOI `10.5281/zenodo.24407735`. The [archived manuscript](../paper/UV.tex), its [45-result inventory](claims.md), and its preferred citation refer to the earlier edition.

The [expanded inventory](claims-expanded.md) covers 203 labeled environments, including 199 mathematical results, three assumptions, and one definition. Of the mathematical results, 154 have new labels. The 48 retained environments include revisions to both statements and referenced definitions. Each checked result in this edition has a separate scope note. Source provenance is checked against both upload hashes.

The [machine-readable expanded inventory](../claims-expanded.json) indexes the front matter and each of the 701 section, subsection, and paragraph headings by line range. The index locates independent derivations, comparisons, characterizations, and counterexamples. The [equation checks](equations-expanded.md) separately record the equations with cited Lean proof evidence. Coverage of a numbered result does not extend to nearby material.

The fixed sector-plane model retains the diamond `(s, b_s)` and its assigned geometric-time carrier as a vector of norm one. The branch, positive boundary height, fixed pole unit, and running unit occupy separate slots. The scalar pole inverse is checked in the literal carrier quotient and both characters keep their prescribed denominator sides. The real clock, cut, and spatial variables use the manuscript’s intrinsic formulas.

The regular positive-shell coarea proof derives the scalar state weight `1/(2κ)` and the branch-routed measure as a pushforward of the full covector. It includes the limit against bounded continuous integrable axial tests. The [boundary product proof](../UV/FurtherCoincidentShell.lean) checks the opposite-side pair at common positive height in the real invariant shell coordinate `D`. Its mass is exactly `π/h`, and subtraction against a bounded test with a quadratic even increment gives the finite part. For a uniform first-order height expansion, the zeroth shell coefficient determines whether the tested limit can be finite, and the first height coefficient contributes the contact term. This covers the opposite-side part of the [coincident-shell calculation](../paper/expanded/UV.tex#L16640). The full-shell principal-value extensions, running-multiplier domains, same-side higher boundary products, and source-level matching for complete graphs still require their respective analytic premises and proofs.

Use `verified` when the Lean statement and its premises cover the complete named result. Use `partial` when a specific clause, supporting estimate, or restricted case has a checked proof. A `pending` entry has no cited proof of the revised claim. The unified quantum source postulate, physical Osterwalder–Schrader completion, and cut–discontinuity matching remain source assumptions. They are not added as trusted Lean axioms.

The main work remaining is organized around the mathematical dependencies in the expanded source:

| Source region | Remaining formalization |
| --- | --- |
| [Path-enriched source and induced actions](../paper/expanded/UV.tex#L811) | Operator-valued history and boundary laws, action pushforwards, and identification of the resulting complete charged and photon vertices. |
| [History phases and curvature determinant](../paper/expanded/UV.tex#L3150) | Joint marked incidence and minor estimates, simultaneous-degeneration criteria, lattice tails, and graph identification from the literal curvature and Wilson actions. |
| [Positive charged comparisons and coupled depths](../paper/expanded/UV.tex#L5143) | Normal Friedrichs generators, Green and heat estimates, operator ideal bounds, full Fredholm determinants, arbitrary hopping and source derivatives. |
| [Gauge identities and reconstruction](../paper/expanded/UV.tex#L14257) | Tie the expanded graph constructors to the same completed action. Check the enlarged source and spectral classifications, physical comparison limits and reconstruction under their stated premises. |
| [Physical sector and two-band constructions](../paper/expanded/UV.tex#L17058) | Complete Maxwell sewing, charge and pair thresholds, interacting transfer and continuum limits, with the actual contact terms and common measures. |
| [Unnumbered native-source analysis](../paper/expanded/UV.tex#L28138) | Extract and formalize individual estimates and counterexamples, including pole and cut tests, normalized vacuum constructions, and explicit benchmarks. |
| [Kernel examples and raw O-QED](../paper/expanded/UV.tex#L44443) | Recheck retained results whose definitions or conclusions changed, including the refined asymptotic terms and the elastic benchmark. |

To review either edition, run `python3 scripts/claims.py` from the root. To check the theorems and their axiom dependencies use the [build and audit commands](../README.md#build-and-audit). The inventory validator checks provenance, status, and theorem references. Mathematical correspondence is reviewed in the mapping notes rather than inferred from the presence of a Lean declaration.
