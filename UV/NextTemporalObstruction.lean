import UV.NextTemporalBasis
import UV.NextTemporalScaling
import UV.FurtherTemporalAbsolute

/-! The equal-energy obstruction for the original coefficient, in original
frequency and spatial momentum variables on a fixed sector plane. -/

noncomputable section
open Complex Filter Matrix MeasureTheory Set
open scoped ENNReal Topology Matrix Matrix.Norms.Elementwise

namespace UV

variable {d : ℕ} {Sector : Type*}

/-- A strictly positive lower bound for the rescaled frequency band of the
actual coefficient. The limit Hamiltonian need not be diagonal in the chosen
slot coordinates. A single fixed orthonormal spectral chart is used on the ray. -/
theorem temporal_contact_ray_band_lower (b : Bool) (plane : ChargePlane Sector)
    (A B : ℝ → TemporalHermitian d) (C Q : ℝ → TemporalMatrix d)
    (scale : ℝ → ℝ) (hs : ∀ᶠ t in (atTop : Filter ℝ), 0 < scale t)
    (H Q₀ : ChargePlane Sector → TemporalMatrix d) (hH : (H plane).IsHermitian)
    (hA : Tendsto (fun t => (((scale t)⁻¹ : ℝ) : ℂ) • (A t).1) atTop (𝓝 (H plane)))
    (hB : Tendsto (fun t => (((scale t)⁻¹ : ℝ) : ℂ) • (B t).1) atTop (𝓝 (H plane)))
    (hQ : Tendsto Q atTop (𝓝 (Q₀ plane)))
    (hC : ∃ M : ℝ, ∀ᶠ t in (atTop : Filter ℝ), scale t * ‖C t‖ ≤ M)
    (E : ℝ) (hq : furtherTemporalEnergyProjection hH E * Q₀ plane *
      furtherTemporalEnergyProjection hH E ≠ 0) :
    ∃ c > (0 : ℝ), ∀ᶠ t in (atTop : Filter ℝ),
      c ≤ scale t * ∫ ω in Icc (scale t) (2 * scale t),
        ‖furtherTemporalCoefficient (A t).1 (B t).1 (C t) (Q t) (furtherTemporalFrequency b ω)‖ := by
  let U : TemporalUnitary d := hH.eigenvectorUnitary
  let D := temporalBasis U
  let A' := fun t => (((scale t)⁻¹ : ℝ) : ℂ) • (A t).1
  let B' := fun t => (((scale t)⁻¹ : ℝ) : ℂ) • (B t).1
  let C' := fun t => (scale t : ℂ) • C t
  let ε : ChargePlane Sector → Fin d → ℝ := fun _ => hH.eigenvalues
  let Ah : ℝ → TemporalHermitian d := fun t =>
    ⟨D (A' t), temporalBasis_hermitian U (temporal_hermitian_real_smul (A t).2 _)⟩
  let Bh : ℝ → TemporalHermitian d := fun t =>
    ⟨D (B' t), temporalBasis_hermitian U (temporal_hermitian_real_smul (B t).2 _)⟩
  have hD : Continuous D := continuous_temporalBasis U
  have hdiag : D (H plane) = Matrix.diagonal (fun i => (ε plane i : ℂ)) :=
    hH.star_mul_self_mul_eq_diagonal
  have hAh : Tendsto (fun t => (Ah t).1) atTop
      (𝓝 (Matrix.diagonal fun i => (ε plane i : ℂ))) := by
    rw [← hdiag]
    exact hD.continuousAt.tendsto.comp hA
  have hBh : Tendsto (fun t => (Bh t).1) atTop
      (𝓝 (Matrix.diagonal fun i => (ε plane i : ℂ))) := by
    rw [← hdiag]
    exact hD.continuousAt.tendsto.comp hB
  have hCh : ∃ M : ℝ, ∀ᶠ t in (atTop : Filter ℝ), ‖D (C' t)‖ ≤ M := by
    apply temporalBasis_bounded U
    obtain ⟨M, hM⟩ := hC
    refine ⟨M, (hs.and hM).mono fun t ht => ?_⟩
    simpa [C', norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1] using ht.2
  obtain ⟨c, hc, hc'⟩ := temporal_contact_rescaled_ray_bound b ε plane Ah Bh (D ∘ C') (D ∘ Q)
    hAh hBh (D ∘ Q₀) (hD.continuousAt.tendsto.comp hQ) hCh E
    (temporalBasis_nonzero_energy_block hH E (Q₀ plane) hq)
  refine ⟨c, hc, (hs.and hc').mono fun t ht => ?_⟩
  have he : furtherTemporalBand b (Ah t) (Bh t) (D (C' t)) (D (Q t)) =
      furtherTemporalBand b ⟨A' t, temporal_hermitian_real_smul (A t).2 _⟩
        ⟨B' t, temporal_hermitian_real_smul (B t).2 _⟩ (C' t) (Q t) := by
    unfold furtherTemporalBand
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    exact congrArg norm (temporalBasis_coefficient U
      (temporal_hermitian_real_smul (A t).2 ((scale t)⁻¹))
      (temporal_hermitian_real_smul (B t).2 ((scale t)⁻¹)) (C' t) (Q t)
      (furtherTemporalFrequency_im_ne_zero b (zero_lt_one.trans_le hu.1))).symm
  have ht' := ht.2
  change c ≤ furtherTemporalBand b (Ah t) (Bh t) (D (C' t)) (D (Q t)) at ht'
  rw [he] at ht'
  exact (temporalBand_scale b (A t).2 (B t).2 (C t) (Q t) ht.1) ▸ ht'

/-- The actual band coefficient is integrable on every compact positive
frequency interval because the two Hermitian pencils are invertible there. -/
theorem temporal_coefficient_integrable_band (b : Bool) (A B : TemporalHermitian d)
    (C Q : TemporalMatrix d) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun ω => furtherTemporalCoefficient A.1 B.1 C Q (furtherTemporalFrequency b ω))
      (Icc a (2 * a)) volume := by
  have hR (H : TemporalHermitian d) : ContinuousOn
      (fun ω => furtherTemporalResolvent H.1 (furtherTemporalFrequency b ω)) (Icc a (2 * a)) := by
    intro ω hω
    apply ContinuousAt.continuousWithinAt
    apply (continuousAt_matrix_inv _ ?_).comp
      (((furtherTemporalFrequency_continuous b).smul continuous_const).add continuous_const).continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (furtherTemporalPencil_isUnit_of_im_ne_zero H.2
        (furtherTemporalFrequency_im_ne_zero b (ha.trans_le hω.1)))))
  have htrace : Continuous (Matrix.trace : TemporalMatrix d → ℂ) :=
    continuous_finset_sum _ fun i _ => (continuous_apply i).comp (continuous_apply i)
  have hc : ContinuousOn
      (fun ω => furtherTemporalCoefficient A.1 B.1 C Q (furtherTemporalFrequency b ω))
      (Icc a (2 * a)) :=
    (htrace.comp_continuousOn ((hR A).mul continuousOn_const)).sub
      (htrace.comp_continuousOn ((((hR A).mul continuousOn_const).mul (hR B)).mul continuousOn_const))
  exact hc.integrableOn_compact isCompact_Icc

/-- The complete coefficient in the original shared four-momentum routing.
Both Hermitian slots carry the fixed sector-plane label. -/
def temporalMomentumCoefficient (b : Bool) (A B : ChargePlane Sector →
    ChargeSpatialMomentum → TemporalHermitian d) (C Q : ChargePlane Sector →
    ChargeSpatialMomentum → TemporalMatrix d) (plane : ChargePlane Sector)
    (kw : ChargeSpatialMomentum × ℝ) : ℂ :=
  furtherTemporalCoefficient (A plane kw.1).1 (B plane kw.1).1 (C plane kw.1) (Q plane kw.1)
    (furtherTemporalFrequency b kw.2)

/-- The limiting equal-energy charge obstruction forces nonintegrability of
the actual four-momentum coefficient on a positive-solid-angle ray family.
The two momentum slots may be distinct and need not commute. -/
theorem temporal_contact_scaling_obstruction (b : Bool) (plane : ChargePlane Sector)
    (A B : ChargePlane Sector → ChargeSpatialMomentum → TemporalHermitian d)
    (C Q : ChargePlane Sector → ChargeSpatialMomentum → TemporalMatrix d)
    (hK : Measurable (temporalMomentumCoefficient b A B C Q plane))
    (s : Set TemporalRayDirection) (hm : MeasurableSet s)
    (hsolid : (volume : Measure ChargeSpatialMomentum).toSphere s ≠ 0)
    (scale : TemporalRayDirection → ℝ → ℝ)
    (hscale : ∀ n ∈ s, ∀ t > 0, 0 < scale n t)
    (H : TemporalRayDirection → TemporalHermitian d) (Q₀ : TemporalRayDirection → TemporalMatrix d)
    (hA : ∀ n ∈ s, Tendsto (fun t => (((scale n t)⁻¹ : ℝ) : ℂ) • (A plane (t • n.1)).1)
      atTop (𝓝 (H n).1))
    (hB : ∀ n ∈ s, Tendsto (fun t => (((scale n t)⁻¹ : ℝ) : ℂ) • (B plane (t • n.1)).1)
      atTop (𝓝 (H n).1))
    (hQ : ∀ n ∈ s, Tendsto (fun t : ℝ => Q plane (t • n.1)) atTop (𝓝 (Q₀ n)))
    (hC : ∀ n ∈ s, ∃ M : ℝ, ∀ᶠ t in (atTop : Filter ℝ), scale n t * ‖C plane (t • n.1)‖ ≤ M)
    (hcharge : ∀ n ∈ s, ∃ E : ℝ, furtherTemporalEnergyProjection (H n).2 E * Q₀ n *
      furtherTemporalEnergyProjection (H n).2 E ≠ 0)
    (hrad : ∀ n ∈ s, ∀ R > 0, (∫⁻ t in Ioi R, ENNReal.ofReal (t ^ 2 / scale n t)) = ∞) :
    ¬ Integrable (temporalMomentumCoefficient b A B C Q plane)
      ((volume : Measure ChargeSpatialMomentum).prod volume) := by
  apply temporal_contact_four_momentum_divergence plane (temporalMomentumCoefficient b A B C Q)
    hK s hm hsolid scale hscale _ _ hrad
  · intro n hn t ht
    exact temporal_coefficient_integrable_band b (A plane (t • n.1)) (B plane (t • n.1))
      (C plane (t • n.1)) (Q plane (t • n.1)) (hscale n hn t ht)
  · intro n hn
    obtain ⟨E, hE⟩ := hcharge n hn
    have hs : ∀ᶠ t in (atTop : Filter ℝ), 0 < scale n t :=
      (eventually_gt_atTop 0).mono (fun t ht => hscale n hn t ht)
    exact temporal_contact_ray_band_lower b plane (fun t => A plane (t • n.1))
      (fun t => B plane (t • n.1)) (fun t => C plane (t • n.1)) (fun t => Q plane (t • n.1))
      (scale n) hs (fun _ => (H n).1) (fun _ => Q₀ n) (H n).2 (hA n hn) (hB n hn)
      (hQ n hn) (hC n hn) E hE

end UV
