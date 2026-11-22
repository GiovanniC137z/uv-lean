import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import UV.FurtherBoundaryCollar

/-! The stated logarithmic determinant envelope is absorbed by the normal heat barrier. -/

noncomputable section

open Filter Set MeasureTheory
open scoped Topology

namespace UV.FurtherBoundaryEnvelope

/-- The decreasing logarithmic upper envelope from the short-collar estimate. -/
def logEnvelope (C N r : ℝ) : ℝ :=
  C * (1 + (1 + |Real.log r|) ^ (3 : ℕ) / r ^ (2 : ℕ)) + N * |Real.log r|

/-- On the collar, the absolute logarithm equals the logarithm of the reciprocal radius. -/
theorem logEnvelope_eq_source (C N : ℝ) {r : ℝ} (hr : r ∈ Ioc 0 1) :
    logEnvelope C N r =
      C * (1 + (r ^ (2 : ℕ))⁻¹ * (1 + Real.log (1 / r)) ^ (3 : ℕ)) +
        N * Real.log (1 / r) := by
  rw [logEnvelope, one_div, Real.log_inv, abs_of_nonpos (Real.log_nonpos hr.1.le hr.2)]
  ring

/-- The logarithmic determinant bound is of strictly lower order than the radial barrier. -/
theorem logarithmic_envelope_lower_order (C N : ℝ) :
    Tendsto (fun r : ℝ => r ^ (3 : ℕ) * logEnvelope C N r) (𝓝[>] 0) (𝓝 0) := by
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hlog (j : ℕ) :
      Tendsto (fun r : ℝ => r * |Real.log r| ^ j) (𝓝[>] 0) (𝓝 0) := by
    convert (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (j : ℝ)
      (show (-1 : ℝ) < 0 by norm_num)).tendsto_div_nhds_zero using 1
    ext r
    rw [Real.rpow_neg_one, div_inv_eq_mul, Real.rpow_natCast, mul_comm]
  have hL : Tendsto (fun r : ℝ => r * (1 + |Real.log r|) ^ (3 : ℕ)) (𝓝[>] 0) (𝓝 0) := by
    convert (((hr.add ((hlog 1).const_mul 3)).add ((hlog 2).const_mul 3)).add (hlog 3)) using 1
    · ext r
      ring
    · norm_num
  have hscaled := (((hr.pow 3).add hL).const_mul C).add
    (((hr.pow 2).mul (hlog 1)).const_mul N)
  change Tendsto _ (𝓝[>] 0) (𝓝 (C * (0 ^ (3 : ℕ) + 0) + N * (0 ^ (2 : ℕ) * 0))) at hscaled
  simp only [zero_pow (show (3 : ℕ) ≠ 0 by decide), mul_zero, add_zero] at hscaled
  apply hscaled.congr'
  filter_upwards [self_mem_nhdsWithin] with r hrpos
  have hr0 : r ≠ 0 := ne_of_gt (show 0 < r from hrpos)
  unfold logEnvelope
  field_simp

/-- The exact source envelope yields a uniform exponential majorant for every positive rate. -/
theorem determinant_envelope_absorbed (C N : ℝ) {F : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hF : ∀ r ∈ Ioc 0 1, F r ≤ Real.exp (logEnvelope C N r)) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ r ∈ Ioc 0 1, F r ≤ M * Real.exp (ε / r ^ (3 : ℕ)) := by
  have he : ∀ᶠ r : ℝ in 𝓝[>] 0, r ^ (3 : ℕ) * logEnvelope C N r < ε :=
    (tendsto_order.mp (logarithmic_envelope_lower_order C N)).2 ε hε
  obtain ⟨d, hd, hdsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp he
  have hcont : ContinuousOn (logEnvelope C N) (Icc d 1) := by
    unfold logEnvelope
    have hlog : ContinuousOn Real.log (Icc d 1) := fun r hr =>
      (Real.continuousAt_log (ne_of_gt (hd.trans_le hr.1))).continuousWithinAt
    have hdiv : ∀ r ∈ Icc d 1, r ^ (2 : ℕ) ≠ 0 := fun r hr =>
      pow_ne_zero _ (ne_of_gt (hd.trans_le hr.1))
    exact (continuousOn_const.mul
      (continuousOn_const.add ((continuousOn_const.add hlog.abs).pow 3 |>.div
        (continuousOn_id.pow 2) hdiv))).add (continuousOn_const.mul hlog.abs)
  obtain ⟨B, hB⟩ := (isCompact_Icc.image_of_continuousOn hcont).bddAbove
  refine ⟨Real.exp (max 0 B), Real.one_le_exp_iff.mpr (le_max_left _ _), fun r hr => ?_⟩
  apply (hF r hr).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hpos : 0 ≤ ε / r ^ (3 : ℕ) := by exact div_nonneg hε.le (pow_nonneg hr.1.le _)
  by_cases hdr : r ≤ d
  · have hlt : r ^ (3 : ℕ) * logEnvelope C N r < ε := hdsub ⟨hr.1, hdr⟩
    have hle : logEnvelope C N r ≤ ε / r ^ (3 : ℕ) :=
      (le_div_iff₀ (pow_pos hr.1 _)).mpr (by simpa only [mul_comm] using hlt.le)
    linarith [le_max_left (0 : ℝ) B]
  · have hle : logEnvelope C N r ≤ B := hB ⟨r, ⟨le_of_not_ge hdr, hr.2⟩, rfl⟩
    linarith [le_max_right (0 : ℝ) B]

/-- The stated determinant bound and the scalar heat comparison give the joint trace. -/
theorem logarithmic_envelope_joint_collar_trace {F : ℝ → ℝ} {K : ℝ → ℝ → ℝ}
    {C A N k T : ℝ} (hC : 0 ≤ C) (hk : 0 < k)
    (hFmeas : Measurable F) (hKmeas : Measurable (Function.uncurry K))
    (hF0 : ∀ r ∈ Ioc 0 1, 0 ≤ F r)
    (hF : ∀ r ∈ Ioc 0 1, F r ≤ Real.exp (logEnvelope A N r))
    (hK0 : ∀ t ∈ Ioc 0 T, ∀ r ∈ Ioc 0 1, 0 ≤ K t r)
    (hK₀ : ∀ t ∈ Ioc 0 T, ∀ r ∈ Ioc 0 1, K t r ≤ C * t ^ (-1 / 2 : ℝ))
    (hK₁ : ∀ t ∈ Ioc 0 T, ∀ r ∈ Ioc 0 1, r < 1 / 4 → r ^ (5 : ℕ) ≤ t →
      K t r ≤ C * t ^ (-1 / 2 : ℝ) * Real.exp (-k / r ^ (3 : ℕ))) :
    IntegrableOn (fun t : ℝ =>
      UV.FurtherBoundaryCollar.collarReadout F K t / (2 * Real.pi * t)) (Ioc 0 T) := by
  have hε : 0 < min (k / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
  obtain ⟨M, hM, hbound⟩ := determinant_envelope_absorbed A N hε hF
  exact UV.FurtherBoundaryCollar.joint_collar_trace_integrableOn
    hC (zero_le_one.trans hM) hk hFmeas hKmeas hF0 hbound hK0 hK₀ hK₁

end UV.FurtherBoundaryEnvelope
