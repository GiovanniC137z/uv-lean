import UV.FurtherTemporalPolar

/-! The equal-energy obstruction for the original coefficient, in original
frequency and spatial momentum variables on a fixed sector plane. -/

noncomputable section
open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace UV

variable {Sector : Type*}

/-- Tonelli directly on the absolute value of the complete coefficient. The
joint measurability premise records that the spacetime integral is defined. -/
theorem temporal_contact_four_momentum_divergence (plane : ChargePlane Sector)
    (K : ChargePlane Sector → ChargeSpatialMomentum × ℝ → ℂ) (hK : Measurable (K plane))
    (s : Set TemporalRayDirection) (hm : MeasurableSet s)
    (hsolid : (volume : Measure ChargeSpatialMomentum).toSphere s ≠ 0)
    (scale : TemporalRayDirection → ℝ → ℝ)
    (hscale : ∀ n ∈ s, ∀ t > 0, 0 < scale n t)
    (hband : ∀ n ∈ s, ∀ t > 0, IntegrableOn (fun ω => K plane (t • n.1, ω))
      (Icc (scale n t) (2 * scale n t)) volume)
    (hbound : ∀ n ∈ s, ∃ c > (0 : ℝ), ∀ᶠ t in (atTop : Filter ℝ),
      c ≤ scale n t * ∫ ω in Icc (scale n t) (2 * scale n t), ‖K plane (t • n.1, ω)‖)
    (hrad : ∀ n ∈ s, ∀ R > 0, (∫⁻ t in Ioi R, ENNReal.ofReal (t ^ 2 / scale n t)) = ∞) :
    ¬ Integrable (K plane) ((volume : Measure ChargeSpatialMomentum).prod volume) := by
  have htop := temporal_contact_polar_divergence plane (fun p k => ‖K p k‖ₑ) hK.enorm s hm hsolid scale
    (fun n hn => ?_) hrad
  · intro h
    exact (hasFiniteIntegral_iff_enorm.mp h.hasFiniteIntegral).ne htop
  · obtain ⟨c, hc, hcb⟩ := hbound n hn
    obtain ⟨R, hR⟩ := eventually_atTop.mp hcb
    refine ⟨c, hc, max R 1, zero_lt_one.trans_le (le_max_right _ _), fun t ht => ?_⟩
    have ht₀ : 0 < t := (zero_lt_one.trans_le (le_max_right R 1)).trans ht
    have hle := hR t ((le_max_left R 1).trans ht.le)
    calc
      _ ≤ ENNReal.ofReal (∫ ω in Icc (scale n t) (2 * scale n t), ‖K plane (t • n.1, ω)‖) :=
        ENNReal.ofReal_le_ofReal ((div_le_iff₀ (hscale n hn t ht₀)).mpr (by simpa only [mul_comm] using hle))
      _ = ∫⁻ ω in Icc (scale n t) (2 * scale n t), ‖K plane (t • n.1, ω)‖ₑ :=
        ofReal_integral_norm_eq_lintegral_enorm (hband n hn t ht₀)
      _ ≤ _ := setLIntegral_le_lintegral _ _

end UV
