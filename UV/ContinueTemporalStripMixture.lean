import UV.ContinueTemporalStripDecay

/-! Depth mixtures keep the actual optical attenuation, including
samples arbitrarily close to the boundary. -/

noncomputable section

namespace UV.TemporalRay

open MeasureTheory Set Real
open scoped Interval Nat

/-- If the positive strip extends from zero to a sampled depth, the
depth moment of order j+N bounds the j-th derivative of the mixture
at inverse-frequency order N. The depth measure can approach zero. -/
theorem normal_transfer_optical_strip_mixture_decay (D : NormalChannel) {ω : ℝ} (hω : ω ≠ 0)
    (u : NormalTransfer D.a (D.potential (ω ^ 2))) {d : ℝ} (hd : 0 < d)
    (ν : Measure ℝ) (j N : ℕ)
    (hstrip : ∀ᵐ r ∂ν.restrict (Ioi (0 : ℝ)), ∀ s ∈ Icc 0 r, d ≤ D.a s * D.temporal s)
    (hmom : IntegrableOn (fun r : ℝ => (r ^ (j + N))⁻¹) (Ioi (0 : ℝ)) ν) :
    let f (r : ℝ) := (Complex.I * (ω : ℂ)) ^ j * (u.amplitude r : ℂ)
    let c := Real.sqrt d / D.aMax
    IntegrableOn f (Ioi (0 : ℝ)) ν ∧
      ‖∫ r in Ioi (0 : ℝ), f r ∂ν‖ ≤
        (2 * ((j + N)! : ℝ) / c ^ (j + N) / |ω| ^ N) *
          ∫ r in Ioi (0 : ℝ), (r ^ (j + N))⁻¹ ∂ν := by
  intro f c
  have hmax : 0 < D.aMax := D.aMin_pos.trans_le ((D.a_bound 0 le_rfl).1.trans (D.a_bound 0 le_rfl).2)
  have hc : 0 < c := div_pos (Real.sqrt_pos.2 hd) hmax
  have hrate (r : ℝ) (hr : 0 < r) : c * r ≤ D.opticalStripRate d 0 r := by
    have H := mul_le_mul_of_nonneg_left (D.optical_length_lower le_rfl hr.le) (Real.sqrt_nonneg d)
    have hzero : D.opticalCoordinate 0 = 0 := by simp [NormalChannel.opticalCoordinate]
    unfold NormalChannel.opticalStripRate
    rw [hzero]
    dsimp only [c]
    simpa only [hzero, sub_zero, div_eq_mul_inv, mul_assoc, mul_comm r] using H
  let K := 2 * ((j + N)! : ℝ) / c ^ (j + N) / |ω| ^ N
  let M (r : ℝ) := K * (r ^ (j + N))⁻¹
  have hM : Integrable M (ν.restrict (Ioi (0 : ℝ))) := hmom.const_mul K
  have hMA : ∀ᵐ r ∂ν.restrict (Ioi (0 : ℝ)), ‖f r‖ ≤ M r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, hstrip] with r hr hs
    have hpos : 0 < r := hr
    have hp := pow_le_pow_left₀ (mul_nonneg hc.le hpos.le) (hrate r hpos) (j + N)
    calc
      ‖f r‖ ≤ (2 * ((j + N)! : ℝ) / (D.opticalStripRate d 0 r) ^ (j + N)) / |ω| ^ N :=
        normal_transfer_optical_strip_time_symbol_decay D hω u le_rfl hpos le_rfl hd hs j N
      _ ≤ (2 * ((j + N)! : ℝ) / (c * r) ^ (j + N)) / |ω| ^ N :=
        div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_left (by positivity) (pow_pos (mul_pos hc hpos) _) hp) (by positivity)
      _ = M r := by
        dsimp only [M, K]
        rw [mul_pow]
        simp only [div_eq_mul_inv, mul_inv]
        ring
  have hcont : ContinuousOn f (Ioi (0 : ℝ)) :=
    continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
      (fun r hr => (u.has_gradient r hr.le).continuousAt.continuousWithinAt))
  refine ⟨hM.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) hMA, ?_⟩
  have H := norm_integral_le_of_norm_le hM hMA
  rw [show (∫ r in Ioi (0 : ℝ), M r ∂ν) = K * ∫ r in Ioi (0 : ℝ), (r ^ (j + N))⁻¹ ∂ν from
    integral_const_mul K _] at H
  exact H

end UV.TemporalRay
