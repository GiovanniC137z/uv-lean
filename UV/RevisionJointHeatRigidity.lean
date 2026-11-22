import UV.RevisionJointHeatSelector

/-! Rigidity of an exact fixed-depth multiplier. -/

noncomputable section
open MeasureTheory Set Real

namespace UV.RevisionJointHeat

private theorem depthProfile_at_target (M : ℝ) {t : ℝ} (h : 0 ≤ t + M) :
    depthProfile M ((t + M) ^ 2 - M ^ 2) = t := by
  unfold depthProfile
  rw [sub_add_cancel, sqrt_sq h]
  ring

/-- Matching the fixed-depth transfer on its entire nonnegative domain forces
an atomic depth. In fact it suffices to match at profile values 1 and 2 for
an already normalized probability law. Their variance identity gives the
measure equality without an axiomatized uniqueness theorem. -/
theorem fixedDepthLaw_eq_dirac (w : Measure ℝ) [IsProbabilityMeasure w]
    (hw : ∀ᵐ r ∂w, 0 ≤ r) {a M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x ≥ 0, (∫ r, kernel (2 * r) M x ∂w) = kernel a M x) :
    w = Measure.dirac (a / 2) := by
  let f := fun r : ℝ => exp (-2 * r)
  let c := exp (-a)
  have ht (n : ℝ) (hn : 0 ≤ n) : (∫ r, exp (-(2 * r) * n) ∂w) = exp (-a * n) := by
    have ht' := h ((n + M) ^ 2 - M ^ 2) (by nlinarith [mul_nonneg hn hM])
    unfold kernel at ht'
    rwa [depthProfile_at_target M (add_nonneg hn hM)] at ht'
  have hf : (∫ r, f r ∂w) = c := by simpa only [f, c, mul_one, neg_mul] using ht 1 (by norm_num)
  have hf2 : (∫ r, f r ^ 2 ∂w) = c ^ 2 := by
    have hh (t : ℝ) : exp t ^ 2 = exp (t * 2) := by rw [← exp_nat_mul]; congr 1; norm_num; ring
    simp only [f, c, hh, neg_mul] at *
    exact ht 2 (by norm_num)
  have hfi : Integrable f w := by
    apply (integrable_const (1 : ℝ)).mono' (by unfold f; fun_prop)
    filter_upwards [hw] with r hr
    change ‖exp (-2 * r)‖ ≤ 1
    rw [Real.norm_of_nonneg (exp_nonneg _)]
    exact exp_le_one_iff.mpr (by linarith)
  have hf2i : Integrable (fun r => f r ^ 2) w := by
    apply (integrable_const (1 : ℝ)).mono' (by unfold f; fun_prop)
    filter_upwards [hw] with r hr
    change ‖exp (-2 * r) ^ 2‖ ≤ 1
    rw [Real.norm_of_nonneg (sq_nonneg _), ← exp_nat_mul]
    exact exp_le_one_iff.mpr (by norm_num; linarith)
  have he (r : ℝ) : (f r - c) ^ 2 = f r ^ 2 - (2 * c) * f r + c ^ 2 := by ring
  have hei : Integrable (fun r => (f r - c) ^ 2) w := by
    simp_rw [he]
    exact (hf2i.sub (hfi.const_mul _)).add (integrable_const _)
  have hzero : (∫ r, (f r - c) ^ 2 ∂w) = 0 := by
    calc
      _ = (∫ r, f r ^ 2 - (2 * c) * f r ∂w) + ∫ _ : ℝ, c ^ 2 ∂w := by
        simp_rw [he]
        exact integral_add (hf2i.sub (hfi.const_mul (2 * c))) (integrable_const (c ^ 2))
      _ = (∫ r, f r ^ 2 ∂w) - (2 * c) * (∫ r, f r ∂w) + c ^ 2 := by
        have hh := integral_sub hf2i (hfi.const_mul (2 * c))
        change (∫ r, f r ^ 2 - (2 * c) * f r ∂w) =
          (∫ r, f r ^ 2 ∂w) - (∫ r, (2 * c) * f r ∂w) at hh
        rw [hh, integral_const_mul]
        simp
      _ = 0 := by rw [hf, hf2]; ring
  have hae : ∀ᵐ r ∂w, r = a / 2 := by
    filter_upwards [(integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hei).mp hzero] with r hr
    have hf' : f r = c := sub_eq_zero.mp (sq_eq_zero_iff.mp hr)
    change exp (-2 * r) = exp (-a) at hf'
    linarith [exp_injective hf']
  ext s hs
  have hm : w {a / 2}ᶜ = 0 := by
    change w {r : ℝ | ¬ r = a / 2} = 0
    exact ae_iff.mp hae
  rw [Measure.dirac_apply' _ hs]
  by_cases hmem : a / 2 ∈ s
  · rw [Set.indicator_of_mem hmem]
    have hsz : w sᶜ = 0 := measure_mono_null (by
      intro r hr
      show r ≠ a / 2
      intro heq
      subst r
      exact hr hmem) hm
    have heq := measure_add_measure_compl (μ := w) hs
    rw [hsz, add_zero, measure_univ] at heq
    exact heq
  · rw [Set.indicator_of_notMem hmem]
    exact measure_mono_null (by
      intro r hr
      show r ≠ a / 2
      intro heq
      subst r
      exact hmem hr) hm

end UV.RevisionJointHeat
