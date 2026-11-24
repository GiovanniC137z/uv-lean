import UV.Convergence
import UV.ContinueTwoBandResolvent

/-! Photon lines after two marks of a complete ordered path. The sector's
Euclidean carrier frequency and three spatial components share the harmonic
readout at both ends of the line. -/

noncomputable section

open MeasureTheory

namespace UV.SectorPlane

/-- The two transverse marks each supply one power of the soft four-momentum. -/
def orderedTransverseEnvelope (a : ℝ) (p : ℝ × Spatial) : ℝ :=
  Real.exp (-(2*a*‖p.2‖)) *
    (min 1 (Real.sqrt (p.1^2 + ‖p.2‖^2)))^2 / (p.1^2 + ‖p.2‖^2)

/-- The two temporal marks each supply a soft spatial factor and carrier decay. -/
def orderedCoulombEnvelope (a : ℝ) (p : ℝ × Spatial) : ℝ :=
  Real.exp (-(2*a*‖p.2‖)) * (min 1 ‖p.2‖)^2 / (‖p.2‖^2 * (1+|p.1|)^2)

theorem measurable_orderedTransverseEnvelope (a : ℝ) : Measurable (orderedTransverseEnvelope a) := by
  unfold orderedTransverseEnvelope
  fun_prop

theorem measurable_orderedCoulombEnvelope (a : ℝ) : Measurable (orderedCoulombEnvelope a) := by
  unfold orderedCoulombEnvelope
  fun_prop

/-- Squaring the two soft factors cancels their common massless denominator.
The original quotient takes the Lebesgue representative zero at its singularity. -/
private theorem ordered_soft_ratio (r : ℝ) (hr : 0 ≤ r) :
    (min 1 r)^2 / r^2 = if r = 0 then 0 else (max 1 (r^2))⁻¹ := by
  by_cases hz : r = 0
  · simp [hz]
  rw [if_neg hz]
  by_cases h : r ≤ 1
  · have hs : r^2 ≤ 1 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr h)]
    rw [min_eq_right h, max_eq_left hs, div_self (pow_ne_zero _ hz), inv_one]
  · have h' : 1 ≤ r := le_of_not_ge h
    have hs : 1 ≤ r^2 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr h')]
    rw [min_eq_left h', max_eq_right hs, one_pow, one_div]

theorem ordered_transverse_envelope_eq (a : ℝ) (p : ℝ × Spatial) :
    orderedTransverseEnvelope a p = if p.1^2+‖p.2‖^2 = 0 then 0 else
      Real.exp (-(2*a*‖p.2‖)) / max 1 (p.1^2+‖p.2‖^2) := by
  have hs : 0 ≤ p.1^2+‖p.2‖^2 := by positivity
  unfold orderedTransverseEnvelope
  have h := ordered_soft_ratio _ (Real.sqrt_nonneg (p.1^2+‖p.2‖^2))
  simp only [Real.sq_sqrt hs, Real.sqrt_eq_zero hs] at h
  rw [mul_div_assoc, h]
  split_ifs <;> simp [div_eq_mul_inv]

theorem ordered_coulomb_envelope_eq (a : ℝ) (p : ℝ × Spatial) :
    orderedCoulombEnvelope a p = if p.2 = 0 then 0 else
      Real.exp (-(2*a*‖p.2‖)) / max 1 (‖p.2‖^2) / (1+|p.1|)^2 := by
  unfold orderedCoulombEnvelope
  rw [←div_div, mul_div_assoc, ordered_soft_ratio _ (norm_nonneg _)]
  simp only [norm_eq_zero]
  split_ifs <;> simp [div_eq_mul_inv]

theorem ordered_envelopes_nonneg (a : ℝ) (p : ℝ × Spatial) :
    0 ≤ orderedTransverseEnvelope a p ∧ 0 ≤ orderedCoulombEnvelope a p := by
  unfold orderedTransverseEnvelope orderedCoulombEnvelope
  constructor <;> positivity

theorem ordered_envelopes_le_one {a : ℝ} (ha : 0 ≤ a) (p : ℝ × Spatial) :
    orderedTransverseEnvelope a p ≤ 1 ∧ orderedCoulombEnvelope a p ≤ 1 := by
  have hE : Real.exp (-(2*a*‖p.2‖)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hm (r : ℝ) : 0 < max 1 r := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hω : (1:ℝ) ≤ (1+|p.1|)^2 := by nlinarith [abs_nonneg p.1, sq_nonneg |p.1|]
  rw [ordered_transverse_envelope_eq, ordered_coulomb_envelope_eq]
  constructor
  · split_ifs
    · exact zero_le_one
    · exact (div_le_one (hm _)).mpr (hE.trans (le_max_left _ _))
  · split_ifs
    · exact zero_le_one
    · exact (div_le_one (zero_lt_one.trans_le hω)).mpr
        (((div_le_one (hm _)).mpr (hE.trans (le_max_left _ _))).trans hω)

/-- A common separable majorant for the internal transverse and Coulomb
lines. It controls the full carrier axis, including arbitrarily large frequency. -/
theorem ordered_envelopes_product_bound (a : ℝ) (p : ℝ × Spatial) :
    let H := 2*(1+p.1^2)⁻¹ * Real.exp (-(2*a*‖p.2‖))
    orderedTransverseEnvelope a p ≤ H ∧ orderedCoulombEnvelope a p ≤ H := by
  dsimp only
  have hω : 0 < 1+p.1^2 := by positivity
  have hE := Real.exp_nonneg (-(2*a*‖p.2‖))
  have hm (r : ℝ) : 0 < max 1 r := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hT : (1+p.1^2) ≤ 2 * max 1 (p.1^2+‖p.2‖^2) := by
    linarith [le_max_left (1:ℝ) (p.1^2+‖p.2‖^2), le_max_right (1:ℝ) (p.1^2+‖p.2‖^2),sq_nonneg ‖p.2‖]
  have hC : 1+p.1^2 ≤ (1+|p.1|)^2 := by nlinarith [abs_nonneg p.1,sq_abs p.1]
  have hb : 0 ≤ 2*(1+p.1^2)⁻¹ * Real.exp (-(2*a*‖p.2‖)) := by positivity
  rw [ordered_transverse_envelope_eq, ordered_coulomb_envelope_eq]
  constructor
  · split_ifs
    · exact hb
    · rw [div_eq_mul_inv, mul_comm (Real.exp _)]
      apply mul_le_mul_of_nonneg_right _ hE
      rw [←div_eq_mul_inv, ←one_div, div_le_div_iff₀ (hm _) hω, one_mul]
      exact hT
  · split_ifs
    · exact hb
    · have h₁ : Real.exp (-(2*a*‖p.2‖)) / max 1 (‖p.2‖^2) ≤ Real.exp (-(2*a*‖p.2‖)) :=
        div_le_self hE (le_max_left _ _)
      have h₂ : ((1+|p.1|)^2)⁻¹ ≤ (1+p.1^2)⁻¹ := inv_anti₀ hω hC
      rw [div_eq_mul_inv]
      calc
        _ ≤ Real.exp (-(2*a*‖p.2‖)) * (1+p.1^2)⁻¹ := mul_le_mul h₁ h₂
          (inv_nonneg.mpr (sq_nonneg _)) hE
        _ ≤ _ := by nlinarith [mul_nonneg hE (inv_nonneg.mpr hω.le)]

theorem ordered_envelopes_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (orderedTransverseEnvelope a) ∧ Integrable (orderedCoulombEnvelope a) := by
  have hS : Integrable (fun k : Spatial => Real.exp (-(2*a*‖k‖))) := by
    simpa only [pow_zero,one_mul] using
      (UV.integrable_norm_pow_exp (E := Spatial) (μ := volume) (show 0 < 2*a by positivity) 0)
  have h := (integrable_inv_one_add_sq.const_mul 2).mul_prod hS
  constructor
  · refine h.mono' (measurable_orderedTransverseEnvelope a).aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [Real.norm_of_nonneg (ordered_envelopes_nonneg a p).1]
    exact (ordered_envelopes_product_bound a p).1
  · refine h.mono' (measurable_orderedCoulombEnvelope a).aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [Real.norm_of_nonneg (ordered_envelopes_nonneg a p).2]
    exact (ordered_envelopes_product_bound a p).2

end UV.SectorPlane
