import UV.ExtendTransverseJump
import UV.ScalarLineSide

/-! Analytic coefficient extraction and directed reconstruction on a compact
regular shell chart. The normal coordinate is D, and the chart density and
test are included in each regulated numerator. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory UV.Carrier
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

/-- Extract the first character of the actual directed product at positive
height, with the sign prescribed by the fixed plane and evolution label. -/
theorem Plane.cut_directed_product_coefficient (diamond : Plane E) (ε : Evolution)
    (h : Height) (D : ℝ) (f : QuotientCarrier) :
    (quotientCharacterEquiv (f * diamond.poleInverse ε h D)).1 =
      (quotientCharacterEquiv f).1 /
        ((D : ℂ) + Complex.I * ((diamond.eta ε * (h : ℝ) : ℝ) : ℂ)) := by
  simp [diamond.pole_inverse_complex, directed, div_eq_mul_inv]

/-- The full carrier product of a tested directed numerator and the literal
vectorial inverse on the same positive-height chart. -/
def Plane.cutDirectedChartPairing (diamond : Plane E) (ε : Evolution)
    (ν : Measure Spatial) (n : ShellChartNumerator) (h : Height) : QuotientCarrier :=
  ∫ x : ℝ × Spatial, directed (n.base x + n.error (h : ℝ) x) *
    diamond.poleInverse ε h x.1 ∂(volume.prod ν)

private theorem Plane.cut_chart_integrable (diamond : Plane E) (ε : Evolution)
    (ν : Measure Spatial) [IsFiniteMeasure ν] (n : ShellChartNumerator) (h : Height) :
    Integrable (fun x : ℝ × Spatial => diamond.poleCoefficient ε h x.1 *
      (n.base x + n.error (h : ℝ) x)) (volume.prod ν) :=
  chart_integrable_mul ν (n.base_continuous.add (n.error_continuous h h.property))
    (A := n.baseBound + n.errorBound h) (r := n.radius)
    (fun x => (norm_add_le _ _).trans (add_le_add (n.base_norm x) (n.error_norm h h.property x)))
    (fun D p hr => by simp only [n.base_support D p hr, n.error_support h h.property D p hr, add_zero])
    (diamond.pole_coefficient_continuous ε h)

theorem Plane.cut_directed_chart_pairing_eq (diamond : Plane E) (ε : Evolution)
    (ν : Measure Spatial) [IsFiniteMeasure ν] (n : ShellChartNumerator) (h : Height) :
    diamond.cutDirectedChartPairing ε ν n h = directed (diamond.transversePoleTest ε ν n h) := by
  rw [Plane.cutDirectedChartPairing, Plane.transversePoleTest, dif_pos h.property,
    ← directed_integral (diamond.cut_chart_integrable ε ν n h)]
  apply integral_congr_ae
  refine Eventually.of_forall fun x => ?_
  dsimp only
  rw [diamond.pole_inverse_complex, ← directed_mul, mul_comm]
  simp [Plane.poleCoefficient, diamond.pole_inverse_complex, directed]

/-- The individual character boundary in `eq:cut-directed-coefficient-extraction`.
The ± side is the sign of η on this plane. -/
theorem Plane.cut_directed_coefficient_extraction (diamond : Plane E) (ε : Evolution)
    (ν : Measure Spatial) [IsFiniteMeasure ν] (n : ShellChartNumerator) :
    Tendsto (fun h : Height => (quotientCharacterEquiv
      (diamond.cutDirectedChartPairing ε ν n h)).1) poleBoundaryHeights
      (𝓝 (complexShellPV (transverseTest ν n.base) -
        Complex.I * (diamond.eta ε : ℂ) * ((Real.pi : ℂ) * transverseTest ν n.base 0))) := by
  have hc := (diamond.transverse_pole_test_limit ε ν n).comp
    (tendsto_comap : Tendsto (fun h : Height => (h : ℝ)) poleBoundaryHeights (𝓝[>] (0 : ℝ)))
  apply hc.congr
  intro h
  simp [diamond.cut_directed_chart_pairing_eq, directed]

/-- The individual directed boundary is the embedding of the extracted
coefficient, with the entire complex coefficient retained. -/
theorem Plane.cut_directed_boundary_reconstruction (diamond : Plane E) (ε : Evolution)
    (ν : Measure Spatial) [IsFiniteMeasure ν] (n : ShellChartNumerator) :
    Tendsto (diamond.cutDirectedChartPairing ε ν n) poleBoundaryHeights
      (𝓝 (directed (complexShellPV (transverseTest ν n.base) -
        Complex.I * (diamond.eta ε : ℂ) * ((Real.pi : ℂ) * transverseTest ν n.base 0)))) := by
  have hc := directed_shell_readout_continuous.continuousAt.tendsto.comp
    (diamond.cut_directed_coefficient_extraction ε ν n)
  apply hc.congr
  intro h
  simp [diamond.cut_directed_chart_pairing_eq, directed]

theorem directed_sub (z w : ℂ) : directed (z - w) = directed z - directed w := by
  apply quotientCharacterEquiv.injective
  simp [directed]

/-- `eq:directed-discontinuity-reconstruction` on a regular chart. The
difference of the actual directed branch pairings converges to the
embedding of the full scalar jump, including the numerator PV term. -/
theorem Plane.directed_discontinuity_reconstruction (diamond : Plane E) (εPos εNeg : Evolution)
    (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    (ν : Measure Spatial) [IsFiniteMeasure ν] (pos neg : ShellChartNumerator) :
    Tendsto (fun h : Height => diamond.cutDirectedChartPairing εPos ν pos h -
      diamond.cutDirectedChartPairing εNeg ν neg h) poleBoundaryHeights
      (𝓝 (directed (complexShellPV
        (fun D => transverseTest ν pos.base D - transverseTest ν neg.base D) -
        Complex.I * (Real.pi : ℂ) * (∫ p, (pos.base (0, p) + neg.base (0, p)) ∂ν)))) := by
  have hc := (diamond.transverse_directed_pole_jump εPos εNeg hPos hNeg ν pos neg).comp
    (tendsto_comap : Tendsto (fun h : Height => (h : ℝ)) poleBoundaryHeights (𝓝[>] (0 : ℝ)))
  exact hc.congr fun h => by simp [diamond.cut_directed_chart_pairing_eq, directed_sub]

end UV.SectorPlane
