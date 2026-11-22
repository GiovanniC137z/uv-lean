import UV.NextTemporalSum

/-! Ray-to-four-momentum transfer for a common-scale finite sum of ordinary
fermion log-determinant coefficients. -/

noncomputable section
open Complex Filter MeasureTheory Set
open scoped ENNReal Topology Matrix Matrix.Norms.Elementwise

namespace UV

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Sector : Type*}

/-- Integrability fails for a finite sum at a common ray scale as soon as
one equal-energy charge survives on each ray in the positive-angle set. -/
theorem temporal_contact_finite_sum_scaling_obstruction (b : Bool) (plane : ChargePlane Sector)
    (d : ι → ℕ)
    (A B : ∀ i, ChargePlane Sector → ChargeSpatialMomentum → TemporalHermitian (d i))
    (C Q : ∀ i, ChargePlane Sector → ChargeSpatialMomentum → TemporalMatrix (d i))
    (hK : Measurable (fun kw => ∑ i, temporalMomentumCoefficient b (A i) (B i) (C i) (Q i) plane kw))
    (s : Set TemporalRayDirection) (hm : MeasurableSet s)
    (hsolid : (volume : Measure ChargeSpatialMomentum).toSphere s ≠ 0)
    (scale : TemporalRayDirection → ℝ → ℝ)
    (hscale : ∀ n ∈ s, ∀ t > 0, 0 < scale n t)
    (H : TemporalRayDirection → (i : ι) → TemporalHermitian (d i))
    (Q₀ : TemporalRayDirection → (i : ι) → TemporalMatrix (d i))
    (hA : ∀ n ∈ s, ∀ i, Tendsto (fun t => (((scale n t)⁻¹ : ℝ) : ℂ) • (A i plane (t • n.1)).1)
      atTop (𝓝 (H n i).1))
    (hB : ∀ n ∈ s, ∀ i, Tendsto (fun t => (((scale n t)⁻¹ : ℝ) : ℂ) • (B i plane (t • n.1)).1)
      atTop (𝓝 (H n i).1))
    (hQ : ∀ n ∈ s, ∀ i, Tendsto (fun t : ℝ => Q i plane (t • n.1)) atTop (𝓝 (Q₀ n i)))
    (hC : ∀ n ∈ s, ∀ i, ∃ M : ℝ, ∀ᶠ t in (atTop : Filter ℝ),
      scale n t * ‖C i plane (t • n.1)‖ ≤ M)
    (hcharge : ∀ n ∈ s, ∃ j E, furtherTemporalEnergyProjection (H n j).2 E * Q₀ n j *
      furtherTemporalEnergyProjection (H n j).2 E ≠ 0)
    (hrad : ∀ n ∈ s, ∀ R > 0, (∫⁻ t in Ioi R, ENNReal.ofReal (t ^ 2 / scale n t)) = ∞) :
    ¬ Integrable (fun kw => ∑ i, temporalMomentumCoefficient b (A i) (B i) (C i) (Q i) plane kw)
      ((volume : Measure ChargeSpatialMomentum).prod volume) := by
  let K (p : ChargePlane Sector) (kw : ChargeSpatialMomentum × ℝ) : ℂ :=
    ∑ i, temporalMomentumCoefficient b (A i) (B i) (C i) (Q i) p kw
  apply temporal_contact_four_momentum_divergence plane K hK s hm hsolid scale hscale _ _ hrad
  · intro n hn t ht
    unfold IntegrableOn
    unfold K
    apply integrable_finset_sum
    intro i _
    exact temporal_coefficient_integrable_band b (A i plane (t • n.1)) (B i plane (t • n.1))
      (C i plane (t • n.1)) (Q i plane (t • n.1)) (hscale n hn t ht)
  · intro n hn
    obtain ⟨j, E, hE⟩ := hcharge n hn
    have hs : ∀ᶠ t in (atTop : Filter ℝ), 0 < scale n t :=
      (eventually_gt_atTop (0 : ℝ)).mono (fun t ht => hscale n hn t ht)
    exact temporal_contact_finite_sum_ray_band_lower b plane d (fun i t => A i plane (t • n.1))
      (fun i t => B i plane (t • n.1)) (fun i t => C i plane (t • n.1))
      (fun i t => Q i plane (t • n.1)) (scale n) hs (H n) (Q₀ n)
      (hA n hn) (hB n hn) (hQ n hn) (hC n hn) j E hE

end UV
