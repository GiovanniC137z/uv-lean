import UV.NextOverlapNormalization
import UV.NextOverlapSpectral
import UV.NextOverlapConverse

/-! The complete weighted moment criterion for the paired boundary maps
and the actual displacement PVM. All momentum variables are the
independent real coordinates on one fixed Euclidean sector plane. -/

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace SchwartzMap

namespace UV.ContinuationBoundary

variable {E H I O ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup I] [InnerProductSpace ℂ I]
  [NormedAddCommGroup O] [InnerProductSpace ℂ O] [CompleteSpace O]

private def displacementPhaseFunction (k : E) (x : E) : ℂ :=
  Complex.exp ((⟪x, k⟫_ℝ : ℂ) * Complex.I)

omit [FiniteDimensional ℝ E] in
private theorem measurable_displacement_phase_function (k : E) :
    Measurable (displacementPhaseFunction k) := by
  unfold displacementPhaseFunction
  fun_prop

/-- The weak spectral integral of the positive physical phase from the
supplied normalized orthogonal displacement PVM. -/
def physicalDisplacementPhase (P : DisplacementPVM E H) (k : E) : H →L[ℂ] H :=
  weakDisplacementIntegral P (displacementPhaseFunction k)
    (measurable_displacement_phase_function k) zero_le_one
    (fun x => (Complex.norm_exp_ofReal_mul_I ⟪x, k⟫_ℝ).le)

omit [FiniteDimensional ℝ E] in
theorem physical_displacement_phase_norm (P : DisplacementPVM E H) (k : E) :
    ‖physicalDisplacementPhase P k‖ ≤ 1 :=
  weak_displacement_integral_norm P _ _ _ _

omit [FiniteDimensional ℝ E] in
theorem physical_displacement_phase_readout (P : DisplacementPVM E H) (k : E) (y x : H) :
    ⟪y, physicalDisplacementPhase P k x⟫_ℂ = physicalOverlapPhase (overlapMeasure P y x) k := by
  rw [physicalDisplacementPhase, weak_displacement_integral_readout]
  simp only [physicalOverlapPhase, charFun_apply, overlapIntegral, displacementPhaseFunction]

def boundaryOverlapMeasure (P : DisplacementPVM E H)
    (u : HilbertBasis ι ℂ I) (v : HilbertBasis κ ℂ O)
    (W : I →L[ℂ] H) (L : H →L[ℂ] O) (a : ι) (b : κ) : ComplexMeasure E :=
  overlapMeasure P (L.adjoint (v b)) (W (u a))

/-- The positive, weighted Hilbert–Schmidt moment in the physical
momentum variable. The normalization is (d^Dk/(2π)^D). -/
def pairedBoundaryMoment (P : DisplacementPVM E H)
    (u : HilbertBasis ι ℂ I) (W : I →L[ℂ] H) (L : H →L[ℂ] O) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ k, ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ N) *
    pairedCoefficient u W L (physicalDisplacementPhase P) k ∂physicalMomentumMeasure

theorem paired_boundary_moment_eq_entry_energy (P : DisplacementPVM E H)
    (u : HilbertBasis ι ℂ I) (v : HilbertBasis κ ℂ O)
    (W : I →L[ℂ] H) (L : H →L[ℂ] O) (N : ℕ) (hW : hilbertSchmidtSquare u W ≠ ∞) :
    pairedBoundaryMoment P u W L N = ∑' a, ∑' b, overlapEnergy N (boundaryOverlapMeasure P u v W L a b) := by
  have hphase (a : ι) (b : κ) (k : E) :
      pairedEntry u v W L (physicalDisplacementPhase P) k a b =
        physicalOverlapPhase (boundaryOverlapMeasure P u v W L a b) k :=
    physical_displacement_phase_readout P k _ _
  have hc (a : ι) (b : κ) :
      Continuous (fun k => pairedEntry u v W L (physicalDisplacementPhase P) k a b) := by
    simp_rw [hphase]
    exact continuous_physical_overlap_phase _
  have hw : Measurable (fun k : E => ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ N)) :=
    (ENNReal.continuous_ofReal.comp ((continuous_const.add (continuous_norm.pow 2)).pow N)).measurable
  unfold pairedBoundaryMoment
  rw [paired_coefficient_weighted_moment_arbitrary_bases u v W L _ hc hW
    (physical_displacement_phase_norm P) _ _ hw]
  apply tsum_congr
  intro a
  apply tsum_congr
  intro b
  rw [overlap_energy_eq_physical_momentum]
  apply lintegral_congr
  intro k
  simp only [hphase, ENNReal.ofReal_mul (by positivity : 0 ≤ (1 + ‖k‖ ^ 2) ^ N)]

/-- Exact weighted moment identity for all supplied Sobolev density
witnesses of the paired entries. -/
theorem paired_boundary_moment_eq_bessel_sum (P : DisplacementPVM E H)
    (u : HilbertBasis ι ℂ I) (v : HilbertBasis κ ℂ O)
    (W : I →L[ℂ] H) (L : H →L[ℂ] O) (N : ℕ) (hW : hilbertSchmidtSquare u W ≠ ∞)
    (h g : ι → κ → Lp (α := E) ℂ 2 volume)
    (hh : ∀ a b, IsOverlapDensity (boundaryOverlapMeasure P u v W L a b) (h a b))
    (hg : ∀ a b, overlapBesselPotential N (h a b : 𝓢'(E, ℂ)) = (g a b : 𝓢'(E, ℂ))) :
    pairedBoundaryMoment P u W L N = ∑' a, ∑' b, ENNReal.ofReal (‖g a b‖ ^ 2) := by
  rw [paired_boundary_moment_eq_entry_energy P u v W L N hW]
  apply tsum_congr
  intro a
  apply tsum_congr
  intro b
  exact overlap_energy_eq_density_bessel_norm _ N _ _ (hh a b) (hg a b)

/-- The full boundary criterion. Finite moment is equivalent to a genuine
Sobolev density for every matrix entry with a finite sum of squared Bessel
norms. The bases are arbitrary Hilbert bases. -/
theorem paired_boundary_moment_finite_iff_sobolev_density (P : DisplacementPVM E H)
    (u : HilbertBasis ι ℂ I) (v : HilbertBasis κ ℂ O)
    (W : I →L[ℂ] H) (L : H →L[ℂ] O) (N : ℕ) (hW : hilbertSchmidtSquare u W ≠ ∞) :
    pairedBoundaryMoment P u W L N ≠ ∞ ↔
      ∃ h g : ι → κ → Lp (α := E) ℂ 2 volume,
        (∀ a b, IsOverlapDensity (boundaryOverlapMeasure P u v W L a b) (h a b)) ∧
        (∀ a b, overlapBesselPotential N (h a b : 𝓢'(E, ℂ)) = (g a b : 𝓢'(E, ℂ))) ∧
        (∑' a, ∑' b, ENNReal.ofReal (‖g a b‖ ^ 2)) ≠ ∞ := by
  constructor
  · intro hfin
    have hm := paired_boundary_moment_eq_entry_energy P u v W L N hW
    rw [hm] at hfin
    have he (a : ι) (b : κ) : overlapEnergy N (boundaryOverlapMeasure P u v W L a b) ≠ ∞ :=
      ENNReal.ne_top_of_tsum_ne_top (ENNReal.ne_top_of_tsum_ne_top hfin a) b
    have hh (a : ι) (b : κ) := (overlap_finite_iff_density (boundaryOverlapMeasure P u v W L a b) N).mp (he a b)
    choose h g hg using hh
    refine ⟨h, g, fun a b => (hg a b).1, fun a b => (hg a b).2, ?_⟩
    rw [← paired_boundary_moment_eq_bessel_sum P u v W L N hW h g
      (fun a b => (hg a b).1) (fun a b => (hg a b).2), hm]
    exact hfin
  · rintro ⟨h, g, hh, hg, hfin⟩
    rw [paired_boundary_moment_eq_bessel_sum P u v W L N hW h g hh hg]
    exact hfin

end UV.ContinuationBoundary
