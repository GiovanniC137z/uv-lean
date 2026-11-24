import UV.ContinueTwoBandDensityTrace
import UV.ContinueRelativeSpectralTest

/-! Products of the signed-energy Euclidean carrier propagators on one sector plane.
The frequency integral is an ordinary absolutely convergent Bochner integral.
The difference of the single-line propagators is integrated before any splitting
of its imaginary part. -/

noncomputable section
open MeasureTheory Filter Complex
open scoped Topology

namespace UV.SectorPlane

open UV.RelativeSoft (carrierCauchyKernel carrierCauchyKernel_re carrierCauchyKernel_im)

private theorem band_denom_ne {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    I * (x : ℂ) + a ≠ 0 := by
  intro h
  apply ha
  simpa [mul_re] using congrArg Complex.re h

private theorem band_denom_pos {a : ℝ} (ha : a ≠ 0) (x : ℝ) : 0 < x^2+a^2 :=
  add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero ha)

private theorem band_norm_sq (a x : ℝ) : ‖carrierCauchyKernel x a‖^2 = (x^2+a^2)⁻¹ := by
  rw [Complex.sq_norm,carrierCauchyKernel,Complex.normSq_inv]
  congr 1
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

private theorem band_lorentzian {a : ℝ} (ha : a ≠ 0) (s : ℝ) :
    Integrable (fun x : ℝ => ((x+s)^2+a^2)⁻¹) ∧
      (∫ x : ℝ, ((x+s)^2+a^2)⁻¹) = Real.pi/|a| := by
  let M := measurePreserving_add_right (volume : Measure ℝ) s
  have h := twoBand_frequency_integral (abs_pos.mpr ha)
  simp_rw [twoBand_frequency_bound_sq, sq_abs] at h
  exact ⟨M.integrable_comp_of_integrable h.1,
    (M.integral_comp (Homeomorph.addRight s).measurableEmbedding _).trans h.2⟩

theorem twoBand_signed_line_product_integrable {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (ν : ℝ) :
    Integrable (fun x : ℝ => carrierCauchyKernel x a * carrierCauchyKernel (x+ν) b) := by
  have h₁ := (band_lorentzian ha 0).1
  simp only [add_zero] at h₁
  have h₂ := (band_lorentzian hb ν).1
  apply ((h₁.add h₂).div_const 2).mono'
  · exact (by unfold carrierCauchyKernel; fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards with x
    change ‖_ * _‖ ≤ ((x^2+a^2)⁻¹ + ((x+ν)^2+b^2)⁻¹)/2
    rw [norm_mul, ← band_norm_sq, ← band_norm_sq]
    nlinarith [sq_nonneg (‖carrierCauchyKernel x a‖-‖carrierCauchyKernel (x+ν) b‖)]

private def bandLogRatio (a b ν x : ℝ) : ℝ :=
  (Real.log ((x+ν)^2+b^2) - Real.log (x^2+a^2))/2

private theorem band_log_limit (a b ν : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    {l : Filter ℝ} (hl : Tendsto (fun x : ℝ => x⁻¹) l (𝓝 0)) (hne : ∀ᶠ x in l, x ≠ 0) :
    Tendsto (bandLogRatio a b ν) l (𝓝 0) := by
  let r := fun y : ℝ => ((1+ν*y)^2+(b*y)^2)/(1+(a*y)^2)
  have hr : ContinuousAt r 0 := by unfold r; fun_prop (disch := norm_num)
  have hr0 : r 0 = 1 := by simp [r]
  have h := (((Real.continuousAt_log (by rw [hr0]; norm_num)).comp hr).tendsto.comp hl).div_const 2
  simp only [Function.comp_apply,hr0,Real.log_one,zero_div] at h
  apply h.congr'
  filter_upwards [hne] with x hx
  unfold bandLogRatio
  rw [← Real.log_div (band_denom_pos hb _).ne' (band_denom_pos ha _).ne']
  congr 2
  dsimp [r]
  have hq : 1 + (a*x⁻¹)^2 ≠ 0 := by positivity
  field_simp [hx, hq,(band_denom_pos ha _).ne']

private theorem band_diff {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (ν x : ℝ) :
    carrierCauchyKernel x a - carrierCauchyKernel (x+ν) b =
      ((b:ℂ)-a+I*ν) * (carrierCauchyKernel x a * carrierCauchyKernel (x+ν) b) := by
  unfold carrierCauchyKernel
  rw [show ((b:ℂ)-a+I*ν) = (I*((x+ν:ℝ):ℂ)+b) - (I*x+a) by push_cast; ring]
  generalize hd₁ : (I*(x:ℂ)+a) = d₁
  generalize hd₂ : (I*((x+ν:ℝ):ℂ)+b) = d₂
  have h₁ := hd₁ ▸ band_denom_ne ha x
  have h₂ := hd₂ ▸ band_denom_ne hb (x+ν)
  field_simp

private theorem band_diff_integral {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (ν : ℝ) :
    (∫ x : ℝ, carrierCauchyKernel x a - carrierCauchyKernel (x+ν) b) =
      ((a*(Real.pi/|a|)-b*(Real.pi/|b|) : ℝ) : ℂ) := by
  let f := fun x : ℝ => carrierCauchyKernel x a - carrierCauchyKernel (x+ν) b
  have hi : Integrable f :=
    ((twoBand_signed_line_product_integrable ha hb ν).const_mul ((b:ℂ)-a+I*ν)).congr
      (ae_of_all _ (fun x => (band_diff ha hb ν x).symm))
  apply Complex.ext
  · change RCLike.re (∫ x, f x) = _
    rw [← integral_re hi]
    simp only [f, RCLike.re_to_complex, Complex.sub_re,carrierCauchyKernel_re,Complex.ofReal_re]
    have h₁ := band_lorentzian ha 0
    simp only [add_zero] at h₁
    have h₂ := band_lorentzian hb ν
    simp_rw [div_eq_mul_inv]
    rw [integral_sub (h₁.1.const_mul _) (h₂.1.const_mul _),integral_const_mul,integral_const_mul,h₁.2,h₂.2]
    rfl
  · change RCLike.im (∫ x, f x) = 0
    rw [← integral_im hi]
    have hd (x : ℝ) : HasDerivAt (bandLogRatio a b ν) (f x).im x := by
      have hd₁ := ((((hasDerivAt_id x).add_const ν).pow 2).add_const (b^2)).log (band_denom_pos hb _).ne'
      have hd₂ := (((hasDerivAt_id x).pow 2).add_const (a^2)).log (band_denom_pos ha _).ne'
      convert (hd₁.sub hd₂).div_const 2 using 1
      simp [f,Complex.sub_im,carrierCauchyKernel_im]
      ring
    have h := integral_of_hasDerivAt_of_tendsto hd hi.im
      (band_log_limit a b ν ha hb tendsto_inv_atBot_zero ((eventually_lt_atBot (0:ℝ)).mono fun _ h => h.ne))
      (band_log_limit a b ν ha hb tendsto_inv_atTop_zero ((eventually_gt_atTop (0:ℝ)).mono fun _ h => h.ne'))
    simpa using h

/-- The integral of the product of two distinct shifted poles including both energy signs. -/
theorem twoBand_signed_line_integral_distinct {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (ν : ℝ)
    (hne : (b:ℂ)-a+I*ν ≠ 0) :
    (∫ x : ℝ, carrierCauchyKernel x a * carrierCauchyKernel (x+ν) b) =
      ((a*(Real.pi/|a|)-b*(Real.pi/|b|) : ℝ) : ℂ) / ((b:ℂ)-a+I*ν) := by
  apply (eq_div_iff hne).2
  rw [mul_comm, ← integral_const_mul, ← band_diff_integral ha hb ν]
  exact integral_congr_ae (ae_of_all _ (fun x => (band_diff ha hb ν x).symm))

private theorem band_line_tendsto_zero (a : ℝ) {l : Filter ℝ}
    (hl : Tendsto (fun x : ℝ => x⁻¹) l (𝓝 0)) (hne : ∀ᶠ x in l, x ≠ 0) :
    Tendsto (fun x : ℝ => carrierCauchyKernel x a) l (𝓝 0) := by
  let U := fun y : ℝ => (y:ℂ)/(I+a*(y:ℂ))
  have hU : ContinuousAt U 0 := by unfold U; fun_prop (disch := simp)
  have hU₀ : U 0 = 0 := by simp [U]
  rw [← hU₀]
  apply (hU.tendsto.comp hl).congr'
  filter_upwards [hne] with x hx
  simp only [Function.comp_apply,U,carrierCauchyKernel,Complex.ofReal_inv]
  have hx' : (x:ℂ) ≠ 0 := by exact_mod_cast hx
  rw [show I+(a:ℂ)*(x:ℂ)⁻¹ = (I*x+a)*(x:ℂ)⁻¹ by field_simp]
  simp [div_eq_mul_inv, hx']

/-- Coincident poles give the derivative of a single propagator and have zero integral. -/
theorem twoBand_signed_line_integral_coincident {a : ℝ} (ha : a ≠ 0) :
    (∫ x : ℝ, carrierCauchyKernel x a * carrierCauchyKernel x a) = 0 := by
  have hd (x : ℝ) : HasDerivAt (fun y => I*carrierCauchyKernel y a)
      (carrierCauchyKernel x a * carrierCauchyKernel x a) x := by
    have h := (((((hasDerivAt_id (x : ℂ)).const_mul I).add_const (a:ℂ)).fun_inv
      (band_denom_ne ha x)).const_mul I).comp_ofReal
    convert h using 1
    simp [carrierCauchyKernel,div_eq_mul_inv,pow_two,← mul_assoc]
  have hi := twoBand_signed_line_product_integrable ha ha 0
  simp only [add_zero] at hi
  have h := integral_of_hasDerivAt_of_tendsto hd hi
    ((band_line_tendsto_zero a tendsto_inv_atBot_zero ((eventually_lt_atBot (0:ℝ)).mono fun _ h => h.ne)).const_mul I)
    ((band_line_tendsto_zero a tendsto_inv_atTop_zero ((eventually_gt_atTop (0:ℝ)).mono fun _ h => h.ne')).const_mul I)
  simpa using h

end UV.SectorPlane
