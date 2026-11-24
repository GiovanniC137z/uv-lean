import UV.ContinueSewnFlagLogMoments
import UV.ContinueNetworkSchwinger
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! A smooth depth readout can give a non-atomic sewn law with infinite
logarithmic energy. The inverse-time divergence is obtained on the
triangle `0 < s < r < 1` in the original two-history preparation. -/

noncomputable section
open MeasureTheory Real Filter Set
open scoped ENNReal ContDiff
namespace UV.SewnFlags

def flatDepth (r : ℝ) : ℝ := expNegInvGlue (r^2)

theorem flatDepth_smooth : ContDiff ℝ ∞ flatDepth :=
  expNegInvGlue.contDiff.comp (contDiff_id.pow 2)

theorem flatDepth_formula {r : ℝ} (hr : 0 < r) : flatDepth r = exp (-(r^2)⁻¹) := by
  unfold flatDepth expNegInvGlue
  rw [if_neg (not_le.mpr (pow_pos hr 2))]

theorem flatDepth_strictMono : StrictMonoOn flatDepth (Ioi 0) := by
  intro s hs r hr hsr
  rw [flatDepth_formula hs, flatDepth_formula hr]
  apply exp_lt_exp.mpr
  apply neg_lt_neg
  apply (inv_lt_inv₀ (pow_pos hr 2) (pow_pos hs 2)).mpr
  nlinarith [mul_pos (show 0 < r-s from sub_pos.mpr hsr) (show 0 < r+s from add_pos hr hs)]

private theorem flatDepth_difference_bounds {r s : ℝ} (hs : s ∈ Ioo 0 r) :
    0 < |flatDepth r - flatDepth s| ∧ |flatDepth r - flatDepth s| ≤ flatDepth r := by
  have hr : 0 < r := hs.1.trans hs.2
  have h := sub_pos.mpr (flatDepth_strictMono hs.1 hr hs.2)
  rw [abs_of_pos h]
  exact ⟨h, sub_le_self _ (expNegInvGlue.nonneg _)⟩

private def flatDepthVolume : Measure ℝ := volume.restrict (Ioo 0 1)

private instance : IsFiniteMeasure flatDepthVolume := by
  unfold flatDepthVolume
  infer_instance

def flatDepthLaw (u : SectorPlane.UnitVector ScalarMomentum) : Measure (PUnit → ScalarMomentum) :=
  coherentProfileLaw flatDepthVolume flatDepth (fun _ => u)

instance (u : SectorPlane.UnitVector ScalarMomentum) : IsFiniteMeasure (flatDepthLaw u) := by
  unfold flatDepthLaw
  infer_instance

theorem flat_depth_no_atom (u : SectorPlane.UnitVector ScalarMomentum) (d : PUnit → ScalarMomentum) :
    flatDepthLaw u {d} = 0 := by
  let F := coherentProfileDisplacement flatDepth (fun _ : PUnit => u)
  have hF : Measurable F := coherentProfileDisplacement_measurable flatDepth_smooth.continuous.measurable _
  unfold flatDepthLaw coherentProfileLaw
  rw [Measure.map_apply hF (measurableSet_singleton d)]
  apply Measure.measure_prod_null_of_ae_null (hF (measurableSet_singleton d))
  apply ae_of_all
  intro r
  dsimp only [Pi.zero_apply]
  rw [flatDepthVolume, Measure.restrict_apply (measurable_prodMk_left (hF (measurableSet_singleton d)))]
  refine Set.Subsingleton.measure_zero ?_ volume
  intro s hs t ht
  have he : F (r,s) PUnit.unit = F (r,t) PUnit.unit :=
    (congrFun (mem_singleton_iff.mp hs.1) PUnit.unit).trans
      (congrFun (mem_singleton_iff.mp ht.1) PUnit.unit).symm
  have hz : (flatDepth t - flatDepth s) • u.val = 0 := by
    change (flatDepth r-flatDepth s) • u.val = (flatDepth r-flatDepth t) • u.val at he
    rw [← sub_eq_zero,← sub_smul] at he
    convert he using 2
    ring
  have hn : u.val ≠ 0 := by
    intro h
    have hu := u.property
    rw [h, norm_zero] at hu
    norm_num at hu
  exact flatDepth_strictMono.injOn hs.2.1 ht.2.1
    (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hn)).symm

private theorem flat_depth_triangle_diverges (F : ℝ → ℝ≥0∞) {c : ℝ} (hc : 0 < c)
    (hF : ∀ r ∈ Ioo (0:ℝ) 1, ∀ s ∈ Ioo (0:ℝ) r,
      ENNReal.ofReal (c*(r^2)⁻¹) ≤ F |flatDepth r-flatDepth s|) :
    (∫⁻ r in Ioo (0:ℝ) 1, ∫⁻ s in Ioo (0:ℝ) 1, F |flatDepth r-flatDepth s|) = ⊤ := by
  have hl (r : ℝ) (hr : r ∈ Ioo (0:ℝ) 1) :
      ENNReal.ofReal (c*r⁻¹) ≤ ∫⁻ s in Ioo (0:ℝ) 1, F |flatDepth r-flatDepth s| := by
    calc
      _ = ∫⁻ _ in Ioo (0:ℝ) r, ENNReal.ofReal (c*(r^2)⁻¹) := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
          ← ENNReal.ofReal_mul (mul_nonneg hc.le (inv_nonneg.mpr (sq_nonneg _)))]
        congr 1
        field_simp [hr.1.ne']
      _ ≤ ∫⁻ s in Ioo (0:ℝ) r, F |flatDepth r-flatDepth s| :=
        lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioo).mono (hF r hr))
      _ ≤ _ := lintegral_mono_set (Ioo_subset_Ioo_right hr.2.le)
  have hb : (∫⁻ r in Ioo (0:ℝ) 1, ENNReal.ofReal (c*r⁻¹)) = ⊤ := by
    have he := directionalEndpointMass_eq (a := 0) zero_lt_one
    have hinv : (∫⁻ r in Ioo (0:ℝ) 1, ENNReal.ofReal r⁻¹) = ⊤ := by
      simpa [directionalEndpointMass, rpow_neg_one] using he
    simp_rw [ENNReal.ofReal_mul hc.le]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hinv,
      ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hc)]
  apply top_le_iff.mp
  rw [← hb]
  exact lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioo).mono hl)

theorem flat_depth_log_diverges :
    (∫⁻ r in Ioo (0:ℝ) 1, ∫⁻ s in Ioo (0:ℝ) 1,
      ENNReal.ofReal (-log |flatDepth r-flatDepth s|)) = ⊤ := by
  apply flat_depth_triangle_diverges (c := 1) (fun x => ENNReal.ofReal (-log x)) zero_lt_one
  intro r hr s hs
  have h := flatDepth_difference_bounds hs
  have hlog : log |flatDepth r - flatDepth s| ≤ -(r^2)⁻¹ :=
    (log_le_log h.1 h.2).trans_eq (by rw [flatDepth_formula hr.1, log_exp])
  exact ENNReal.ofReal_le_ofReal (by simpa only [one_mul, neg_neg] using neg_le_neg hlog)

private theorem flat_depth_kernel_lower (m : ℝ) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal ((exp (-(m^2+1/4))/(4*π)^2)*(r^2)⁻¹) ≤ logKernel m (flatDepth r) := by
  let u := flatDepth r
  let c := exp (-(m^2+1/4))/(4*π)^2
  have hπ : 0 < (4*π)^2 := by positivity
  have hc : 0 < c := div_pos (exp_pos _) hπ
  have hu : 0 < u := expNegInvGlue.pos_of_pos (pow_pos hr 2)
  have hu₁ : u < 1 := by
    unfold u
    rw [flatDepth_formula hr]
    exact exp_lt_one_iff.mpr (neg_neg_of_pos (inv_pos.mpr (pow_pos hr 2)))
  have hI : IntegrableOn (fun t : ℝ => c/t) (Icc u 1) :=
    (continuousOn_const.div continuousOn_id (fun t ht => (hu.trans_le ht.1).ne')).integrableOn_compact isCompact_Icc
  have h0 : 0 ≤ᵐ[volume.restrict (Icc u 1)] fun t => c/t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact div_nonneg hc.le (hu.trans_le ht.1).le
  have hlog : (∫ t in Icc u 1, c/t) = c*(r^2)⁻¹ := by
    simp_rw [div_eq_mul_inv]
    rw [integral_const_mul,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hu₁.le]
    have h := integral_one_div_of_pos hu zero_lt_one
    simp only [one_div,log_inv] at h
    rw [h]
    unfold u
    rw [flatDepth_formula hr,log_exp,neg_neg]
  rw [← hlog, ofReal_integral_eq_lintegral_ofReal hI h0,logKernel_proper_time]
  calc
    _ ≤ ∫⁻ t in Icc u 1, ENNReal.ofReal (exp (-(m^2*t+u^2/(4*t)))/((4*π)^2*t)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have ht₀ : 0 < t := hu.trans_le ht.1
      have hphase : m^2*t + u^2/(4*t) ≤ m^2+1/4 := by
        apply add_le_add ((mul_le_mul_of_nonneg_left ht.2 (sq_nonneg m)).trans_eq (mul_one _))
        apply (div_le_iff₀ (by positivity : 0 < 4*t)).mpr
        have h := mul_le_mul_of_nonneg_left hu₁.le hu.le
        nlinarith [ht.1]
      apply ENNReal.ofReal_le_ofReal
      unfold c
      rw [div_div]
      exact div_le_div_of_nonneg_right (exp_le_exp.mpr (neg_le_neg hphase)) (mul_nonneg hπ.le ht₀.le)
    _ ≤ _ := lintegral_mono_set (fun _ ht => hu.trans_le ht.1)

/-- The original positive one-loop momentum integral diverges for
the smooth flat readout, even though the complete displacement law has no atoms. -/
theorem flat_depth_bare_energy_diverges {m : ℝ} (hm : 0 < m)
    (u : SectorPlane.UnitVector ScalarMomentum) :
    (∫⁻ q : PUnit → ScalarMomentum, ENNReal.ofReal (marginalCharacteristic (flatDepthLaw u) q) *
      ∏ i, ENNReal.ofReal (((m^2+‖q i‖^2)^2)⁻¹/(2*π)^4)) = ⊤ := by
  have hM := flatDepth_smooth.continuous.measurable
  have hC (q : PUnit → ScalarMomentum) : 0 ≤ marginalCharacteristic (flatDepthLaw u) q := by
    unfold flatDepthLaw
    rw [coherent_profile_characteristic _ _ hM]
    exact Complex.normSq_nonneg _
  rw [joint_marginal_log_energy _ hm hC]
  let H := fun d : PUnit → ScalarMomentum => ∏ i, logKernel m ‖d i‖
  have hH : Measurable H := Finset.measurable_prod _ fun i _ =>
    (logKernel_measurable m).comp (measurable_pi_apply i).norm
  let F := coherentProfileDisplacement flatDepth (fun _ : PUnit => u)
  have hF : Measurable F := coherentProfileDisplacement_measurable hM _
  change (∫⁻ d, H d ∂Measure.map F (flatDepthVolume.prod flatDepthVolume)) = ⊤
  rw [lintegral_map hH hF,lintegral_prod (fun p => H (F p)) (hH.comp hF).aemeasurable]
  have he (r s : ℝ) : H (F (r,s)) = logKernel m |flatDepth r-flatDepth s| := by
    simp only [H, F, Fintype.prod_unique, coherentProfileDisplacement, norm_smul,
      u.property, mul_one, Real.norm_eq_abs]
  simp_rw [he]
  apply flat_depth_triangle_diverges (c := exp (-(m^2+1/4))/(4*π)^2) (logKernel m) (by positivity)
  intro r hr s hs
  have h := flatDepth_difference_bounds hs
  exact (flat_depth_kernel_lower m hr.1).trans
    (logKernel_antitone m h.1.le (expNegInvGlue.nonneg _) h.2)

end UV.SewnFlags
