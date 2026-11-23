import UV.ContinueSeamAngularCharacter
import UV.ContinueVisitNormalPolar

/-! Radial moment consequences of the two angular metrics.
The charged-sector state and the electromagnetic variance still have to
be obtained from the one-hop Hamiltonian. -/

noncomputable section

namespace UV.SeamAngular

open Real MeasureTheory Set Filter
open scoped ENNReal

/-- A constant neutral-pair potential reweights each insertion time by the
exact propagation factor on the time remaining after the hop. -/
theorem seam_constant_potential_bounds {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℤ) {T : ℝ} (s : Ω → ℝ) (hs : ∀ᵐ z ∂μ, s z ∈ Icc 0 T) (F : Ω → ℝ≥0∞) :
    let m := ENNReal.ofReal (exp (-(2*(q:ℝ)^2)*T))
    let A := ∫⁻ z, ENNReal.ofReal (exp (-(2*(q:ℝ)^2)*(T-s z)))*F z ∂μ
    m*(∫⁻ z, F z ∂μ) ≤ A ∧ A ≤ ∫⁻ z, F z ∂μ := by
  intro m A
  have hq : 0 ≤ 2*(q:ℝ)^2 := by positivity
  constructor
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [hs] with z hz
    apply mul_le_mul_right'
    apply ENNReal.ofReal_le_ofReal
    apply exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (sub_le_self T hz.1) (neg_nonpos.mpr hq)
  · apply lintegral_mono_ae
    filter_upwards [hs] with z hz
    have hw : ENNReal.ofReal (exp (-(2*(q:ℝ)^2)*(T-s z))) ≤ 1 :=
      ENNReal.ofReal_le_one.mpr (exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) (sub_nonneg.mpr hz.2)))
    exact (mul_le_mul_right' hw (F z)).trans_eq (one_mul _)

theorem seam_constant_potential_finite_iff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℤ) {T : ℝ} (s : Ω → ℝ) (hs : ∀ᵐ z ∂μ, s z ∈ Icc 0 T) (F : Ω → ℝ≥0∞) :
    (∫⁻ z, ENNReal.ofReal (exp (-(2*(q:ℝ)^2)*(T-s z)))*F z ∂μ) < ⊤ ↔ (∫⁻ z, F z ∂μ) < ⊤ := by
  obtain ⟨hl,hu⟩ := seam_constant_potential_bounds μ q s hs F
  constructor
  · intro h
    by_contra! hh
    rw [top_le_iff.mp hh,ENNReal.mul_top (ENNReal.ofReal_pos.mpr (exp_pos _)).ne'] at hl
    exact (not_le_of_gt h) hl
  · exact fun h => hu.trans_lt h

/-- The neutral quartic radial power of the n-th variance moment changes
integrability precisely at n=10, the coefficient of e^20. -/
theorem seam_quartic_tip_moment (n : ℕ) :
    IntegrableOn (fun r : ℝ => r^4*r^(-(n:ℝ)/2)) (Ioo 0 1) ↔ n < 10 := by
  have he : EqOn (fun r : ℝ => r^4*r^(-(n:ℝ)/2)) (fun r : ℝ => r^((4:ℝ)-(n:ℝ)/2)) (Ioo 0 1) := by
    intro r hr
    dsimp only
    rw [show ((4:ℝ)-(n:ℝ)/2) = 4+(-(n:ℝ)/2) by ring,Real.rpow_add hr.1,Real.rpow_ofNat]
  rw [integrableOn_congr_fun he measurableSet_Ioo,intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
  constructor
  · intro h
    exact_mod_cast (show (n:ℝ) < 10 by linarith)
  · intro h
    have h' : (n:ℝ) < 10 := by exact_mod_cast h
    linarith

/-- A square-integrable neutral state and the charged state's corresponding
inverse radial moment pay the actual mixed r⁴ v₀ vq readout cost. -/
theorem seam_mixed_radial_moment (n : ℕ) (v₀ vq : ℝ → ℝ)
    (h0 : MemLp (fun r : ℝ => r^2*v₀ r) 2 (volume.restrict (Ioo (0:ℝ) 1)))
    (hq : MemLp (fun r : ℝ => r^2*r^(-(n:ℝ)/2)*vq r) 2 (volume.restrict (Ioo (0:ℝ) 1))) :
    IntegrableOn (fun r : ℝ => r^4*r^(-(n:ℝ)/2)*|v₀ r*vq r|) (Ioo 0 1) := by
  apply (h0.norm.integrable_mul hq.norm).congr
  filter_upwards [ae_restrict_mem (μ := volume) (s := Ioo (0:ℝ) 1) measurableSet_Ioo] with r hr
  change ‖r^2*v₀ r‖ * ‖r^2*r^(-(n:ℝ)/2)*vq r‖ = _
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg r),
    abs_of_nonneg (Real.rpow_nonneg hr.1.le (-(n:ℝ)/2))]
  ring

end UV.SeamAngular
