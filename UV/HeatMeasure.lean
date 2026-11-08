import UV.Subordination

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal

namespace UV

/-- Heat-depth measure for the dimensional square-root kernel. -/
def oqedHeatMeasure (a M : ℝ) : Measure ℝ :=
  Measure.map (fun τ : ℝ => a ^ 2 * τ) (oqedMeasure (a * M))

instance oqedHeatMeasure_isFinite (a M : ℝ) : IsFiniteMeasure (oqedHeatMeasure a M) := by
  unfold oqedHeatMeasure
  infer_instance

theorem oqedHeatMeasure_probability {a M : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M) :
    IsProbabilityMeasure (oqedHeatMeasure a M) := by
  haveI := oqedMeasure_probability (mul_nonneg ha hM)
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem oqedHeatMeasure_inverseMoment {a : ℝ} (ha : 0 < a) (M r : ℝ) :
    inverseMoment (oqedHeatMeasure a M) r =
      ENNReal.ofReal (a ^ (-2 * r)) * inverseMoment (oqedMeasure (a * M)) r := by
  have hscale : Measurable (fun τ : ℝ => a ^ 2 * τ) := by fun_prop
  have hpower : Measurable (fun τ : ℝ => ENNReal.ofReal (τ ^ (-r))) := by fun_prop
  have hpre : (fun τ : ℝ => a ^ 2 * τ) ⁻¹' Ioi (0 : ℝ) = Ioi 0 := by
    ext τ
    simp only [mem_preimage, mem_Ioi]
    exact mul_pos_iff_of_pos_left (sq_pos_of_pos ha)
  unfold inverseMoment oqedHeatMeasure
  rw [setLIntegral_map measurableSet_Ioi hpower hscale, hpre]
  calc
    _ = ∫⁻ τ : ℝ in Ioi 0,
        ENNReal.ofReal (a ^ (-2 * r)) * ENNReal.ofReal (τ ^ (-r)) ∂oqedMeasure (a * M) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro τ hτ
      dsimp only
      rw [Real.mul_rpow (sq_nonneg a) hτ.le,
        ENNReal.ofReal_mul (Real.rpow_nonneg (sq_nonneg a) (-r))]
      congr 2
      rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le]
      congr 1
      ring
    _ = _ := lintegral_const_mul _ hpower

theorem oqedHeatMeasure_inverseMoment_finite {a : ℝ} (ha : 0 < a) (M : ℝ)
    {r : ℝ} (hr : -(1 / 2 : ℝ) < r) :
    inverseMoment (oqedHeatMeasure a M) r < ⊤ := by
  rw [oqedHeatMeasure_inverseMoment ha]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (oqedInverseMoment_finite (a * M) hr)

theorem oqedHeatMeasure_no_atom_zero {a : ℝ} (ha : 0 < a) (M : ℝ) :
    oqedHeatMeasure a M {0} = 0 := by
  unfold oqedHeatMeasure
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton 0)]
  have hpre : (fun τ : ℝ => a ^ 2 * τ) ⁻¹' ({0} : Set ℝ) = {0} := by
    ext τ
    simp only [mem_preimage, mem_singleton_iff, mul_eq_zero,
      ne_of_gt (sq_pos_of_pos ha), false_or]
  rw [hpre, oqedMeasure_no_atom]

theorem oqedHeatMeasure_nonnegative_support {a : ℝ} (ha : 0 < a) (M : ℝ) :
    oqedHeatMeasure a M (Iic 0) = 0 := by
  unfold oqedHeatMeasure
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
  have hpre : (fun τ : ℝ => a ^ 2 * τ) ⁻¹' Iic (0 : ℝ) = Iic 0 := by
    ext τ
    simp only [mem_preimage, mem_Iic]
    simpa only [mul_zero] using
      (mul_le_mul_iff_right₀ (sq_pos_of_pos ha) : a ^ 2 * τ ≤ a ^ 2 * 0 ↔ τ ≤ 0)
  rw [hpre, oqedMeasure_nonnegative_support]

/-- The scaled manuscript density represents the actual dimensional kernel. -/
theorem oqedHeatMeasure_laplace {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) (M : ℝ) :
    laplace (oqedHeatMeasure a M) u = kernel a M u := by
  unfold laplace oqedHeatMeasure
  rw [integral_map (by fun_prop) (by fun_prop)]
  have hfun : (fun τ : ℝ => Real.exp (-(a ^ 2 * τ) * u)) =
      (fun τ : ℝ => Real.exp (-τ * (a ^ 2 * u))) := by
    funext τ
    congr 1
    ring
  rw [hfun]
  change laplace (oqedMeasure (a * M)) (a ^ 2 * u) = kernel a M u
  rw [oqedLaplace_nonnegative (a * M) (a ^ 2 * u) (by positivity)]
  have hs : Real.sqrt ((a * M) ^ 2 + a ^ 2 * u) = a * Real.sqrt (u + M ^ 2) := by
    rw [show (a * M) ^ 2 + a ^ 2 * u = a ^ 2 * (u + M ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
  rw [hs]
  unfold kernel depthProfile
  congr 1
  ring

end UV
