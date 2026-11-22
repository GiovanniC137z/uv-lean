import UV.NextCurvatureLaw

/-! Weighted absolute Fourier coefficients at positive normal separation
on the same fixed sector-plane torus and common Gaussian preparation. -/

noncomputable section

open MeasureTheory Real Filter
open scoped BigOperators ENNReal NNReal

namespace UV.NextCurvatureFourierSummability

open UV.NextCurvatureLaw UV.FurtherCurvatureLine UV.FurtherCurvatureShell
open UV.RevisionCurvatureDeterminant (latticeFrequency)

def derivativeWeight (q : ℕ) (ℓ : ℝ) (k : MeanZeroMode) : ℝ :=
  (1 + latticeFrequency k)^q * exp (-ℓ * latticeFrequency k) *
    sqrt (2 * curvatureCovariance ℓ k)

theorem derivativeWeight_nonneg (q : ℕ) (ℓ : ℝ) (k : MeanZeroMode) :
    0 ≤ derivativeWeight q ℓ k := by
  unfold derivativeWeight latticeFrequency
  positivity

theorem derivativeWeight_summable (q : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Summable (derivativeWeight q ℓ) := by
  obtain ⟨_, _, hline⟩ := full_weighted_line_bound
    (s := ((q+1 : ℕ) : ℝ)) (by positivity)
  have h : Summable fun k : MeanZeroMode => 4 * weightedLine ((q+1 : ℕ) : ℝ) (ℓ/2) k :=
    ((hline (half_pos hℓ)).1.comp_injective Subtype.val_injective).mul_left 4
  apply h.of_nonneg_of_le (derivativeWeight_nonneg q ℓ)
  intro k
  let r := latticeFrequency k
  let e := exp (-ℓ*r)
  have hr : 0 < r := (Nat.cast_pos.mpr
    (Nat.pos_of_ne_zero (latticeHeight_ne_zero k.2))).trans_le
    (latticeHeight_le_latticeFrequency k)
  have he : e ≤ 1 := exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hℓ.le) hr.le)
  have hs : sqrt (2 * curvatureCovariance ℓ k) ≤ 2/r := by
    apply (sqrt_le_left (by positivity)).2
    calc
      _ ≤ 2 * (r^2)⁻¹ := mul_le_mul_of_nonneg_left (mode_covariance_le_boundary ℓ k) zero_le_two
      _ ≤ (2 / r)^2 := by
        rw [div_pow]
        norm_num
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hd : 2/r ≤ 4*(1+r)/(r^2*(1+e)) := by
    apply (div_le_div_iff₀ hr (by dsimp [e]; positivity)).2
    calc
      _ ≤ 2 * (r^2 * 2) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) zero_le_two
      _ ≤ _ := by nlinarith
  have hg := mul_le_mul_of_nonneg_left (hs.trans hd)
    (show 0 ≤ (1+r)^q * e by dsimp [e]; positivity)
  unfold derivativeWeight weightedLine curvatureLine curvatureCovariance
  rw [Real.rpow_natCast, pow_succ]
  change (1+r)^q * e * sqrt (2 * curvatureCovariance ℓ k) ≤
    4 * ((1+r)^q * (1+r) *
      (exp (-2 * (ℓ/2) * r) * (r^2 * (1+exp (-2 * (ℓ/2) * r)))⁻¹))
  rw [show -2*(ℓ/2)*r = -ℓ*r by ring]
  simpa only [div_eq_mul_inv, ← mul_assoc, mul_left_comm, mul_comm, e] using hg

private theorem base_power_integrable (q : ℕ) : Integrable (fun x : ℝ => x ^ q) sourceGaussianBase := by
  have h := sourceGaussian_power_integrable (1/2 : ℝ) q
  have he : sourceGaussian (1/2 : ℝ) = sourceGaussianBase := by
    unfold sourceGaussian
    norm_num
  simpa only [he] using h

private theorem eval_integral_abs (n : ℕ) (i : ModeSlot n) :
    (∫ X, |X i| ∂commonGaussian n) = ∫ x : ℝ, |x| ∂sourceGaussianBase := by
  have h := measurePreserving_eval_infinitePi (μ := fun _ : ModeSlot n => sourceGaussianBase) i
  rw [← h.map_eq, integral_map h.measurable.aemeasurable
    (by fun_prop : Measurable (fun x : ℝ => |x|)).aestronglyMeasurable]
  rfl

/-- The positive-depth transferred coordinate sum is absolutely summable
almost surely for every derivative order in the same Gaussian preparation. -/
theorem ae_weighted_transfer_summable (n : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᵐ X ∂commonGaussian n, ∀ q : ℕ,
      Summable fun i : ModeSlot n => derivativeWeight q ℓ i.1 * |X i| := by
  rw [eventually_countable_forall]
  intro q
  let w (i : ModeSlot n) := derivativeWeight q ℓ i.1
  let f (i : ModeSlot n) (X : ModeSlot n → ℝ) := w i * |X i|
  have hw (i : ModeSlot n) : 0 ≤ w i := derivativeWeight_nonneg q ℓ i.1
  have hs : Summable w := by
    apply (summable_prod_of_nonneg hw).2
    refine ⟨fun _ => summable_of_finite_support (Set.toFinite _), ?_⟩
    simp only [w, tsum_fintype, Finset.sum_const, nsmul_eq_mul]
    exact (derivativeWeight_summable q hℓ).mul_left _
  have hfi (i : ModeSlot n) : Integrable (f i) (commonGaussian n) := by
    have he := measurePreserving_eval_infinitePi (μ := fun _ : ModeSlot n => sourceGaussianBase) i
    have hi : Integrable (fun x : ℝ => |x|) sourceGaussianBase := by
      simpa only [pow_one, Real.norm_eq_abs] using (base_power_integrable 1).norm
    have hj : Integrable (fun X : ModeSlot n → ℝ => |X i|) (commonGaussian n) := by
      unfold commonGaussian
      simpa only [Function.comp_apply, Function.eval] using he.integrable_comp_of_integrable hi
    exact hj.const_mul (w i)
  have hn (i : ModeSlot n) (X : ModeSlot n → ℝ) : 0 ≤ f i X :=
    mul_nonneg (hw i) (abs_nonneg _)
  have hg (i : ModeSlot n) : AEMeasurable (fun X => ENNReal.ofReal (f i X)) (commonGaussian n) :=
    (hfi i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  let m := ∫ x : ℝ, |x| ∂sourceGaussianBase
  have hm : 0 ≤ m := integral_nonneg abs_nonneg
  have hintegral (i : ModeSlot n) :
      (∫⁻ X, ENNReal.ofReal (f i X) ∂commonGaussian n) = ENNReal.ofReal (w i * m) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi i) (Eventually.of_forall (hn i))]
    dsimp only [f, m]
    rw [integral_const_mul, eval_integral_abs]
  have hfinite : (∫⁻ X, (∑' i, ENNReal.ofReal (f i X)) ∂commonGaussian n) ≠ ∞ := by
    rw [lintegral_tsum hg]
    simp_rw [hintegral]
    let a (i : ModeSlot n) : ℝ≥0 := ⟨w i * m, mul_nonneg (hw i) hm⟩
    have he (i : ModeSlot n) : ENNReal.ofReal (w i * m) = (a i : ℝ≥0∞) :=
      ENNReal.ofReal_eq_coe_nnreal (mul_nonneg (hw i) hm)
    simp_rw [he]
    exact ENNReal.tsum_coe_ne_top_iff_summable_coe.2 (hs.mul_right m)
  filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum hg) hfinite] with X hX
  let a (i : ModeSlot n) : ℝ≥0 := ⟨f i X, hn i X⟩
  have he (i : ModeSlot n) : ENNReal.ofReal (f i X) = (a i : ℝ≥0∞) :=
    ENNReal.ofReal_eq_coe_nnreal (hn i X)
  simp_rw [he] at hX
  change Summable fun i => (a i : ℝ)
  exact ENNReal.tsum_coe_ne_top_iff_summable_coe.1 hX.ne

end UV.NextCurvatureFourierSummability
