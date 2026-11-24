import UV.ContinueSewnFlagLogBounds
import UV.ContinueSewnFlagLogPairing
import UV.ContinuationSectorPlane
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! A single shared depth coordinate controls every finite logarithmic
moment of its difference on the closed unit square. -/

noncomputable section
open MeasureTheory Real Filter Set
open scoped ENNReal BigOperators RealInnerProductSpace ComplexConjugate
namespace UV.SewnFlags

theorem unit_log_power_integral (n : ℕ) :
    (∫⁻ r in Ioo (0:ℝ) 1, ENNReal.ofReal ((-log r)^n)) = ENNReal.ofReal (n.factorial:ℝ) := by
  let e := fun t : ℝ => exp (-t)
  have hImage : e '' Ioi (0:ℝ) = Ioo 0 1 := by
    ext r
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨exp_pos _, exp_lt_one_iff.mpr (neg_neg_of_pos ht)⟩
    · intro hr
      refine ⟨-log r, neg_pos.mpr (log_neg hr.1 hr.2),?_⟩
      simp only [e,neg_neg,exp_log hr.1]
  have hD (t : ℝ) (_ht : t ∈ Ioi (0:ℝ)) : HasDerivWithinAt e (-exp (-t)) (Ioi 0) t := by
    simpa [e] using ((hasDerivAt_id t).neg.exp).hasDerivWithinAt (s := Ioi 0)
  have hInj : InjOn e (Ioi (0:ℝ)) :=
    (exp_injective.comp (fun _ _ h => neg_injective h)).injOn
  rw [← hImage, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hD hInj]
  let f := fun t : ℝ => exp (-t) * t ^ n
  have hI : IntegrableOn f (Ioi 0) := by
    have h := GammaIntegral_convergent (by positivity : 0 < (n:ℝ)+1)
    simpa only [add_sub_cancel_right,rpow_natCast] using h
  have hN : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (exp_pos _).le (pow_nonneg ht.le _)
  calc
    _ = ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (f t) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t _
      change ENNReal.ofReal |-exp (-t)| * ENNReal.ofReal ((-log (exp (-t)))^n) = _
      rw [abs_neg,abs_of_pos (exp_pos _),log_exp,neg_neg,← ENNReal.ofReal_mul (exp_pos _).le]
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hI hN]
      congr 1
      have h := Gamma_eq_integral (by positivity : 0 < (n:ℝ)+1)
      rw [Gamma_nat_eq_factorial] at h
      simpa only [add_sub_cancel_right,rpow_natCast,f] using h.symm

private def depthLogPower (n : ℕ) (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (abs (log |x|)^n)

private theorem depthLogPower_posInterval (n : ℕ) :
    (∫⁻ r in Icc (0:ℝ) 1, depthLogPower n r) = ENNReal.ofReal (n.factorial : ℝ) := by
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc.symm,← unit_log_power_integral n]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro r hr
  rw [depthLogPower,abs_of_pos hr.1,abs_of_neg (log_neg hr.1 hr.2)]

private theorem depthLogPower_symmetric (n : ℕ) :
    (∫⁻ r in Icc (-1:ℝ) 1, depthLogPower n r) ≤ 2 * ENNReal.ofReal (n.factorial:ℝ) := by
  have hImage : (fun r : ℝ => -r) '' Icc 0 1 = Icc (-1:ℝ) 0 := by
    ext r; constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨neg_le_neg ht.2,neg_nonpos.mpr ht.1⟩
    · intro hr
      exact ⟨-r,⟨neg_nonneg.mpr hr.2,neg_le_of_neg_le hr.1⟩,neg_neg r⟩
  have hD (t : ℝ) (_ht : t ∈ Icc (0:ℝ) 1) : HasDerivWithinAt (fun t => -t) (-1) (Icc 0 1) t :=
    ((hasDerivAt_id t).neg).hasDerivWithinAt
  have hneg : (∫⁻ r in Icc (-1:ℝ) 0, depthLogPower n r) = ENNReal.ofReal (n.factorial : ℝ) := by
    rw [← hImage,lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc hD neg_injective.injOn]
    simpa only [abs_neg,abs_one,ENNReal.ofReal_one,one_mul,depthLogPower] using depthLogPower_posInterval n
  have hS : Icc (-1:ℝ) 1 = Icc (-1) 0 ∪ Icc 0 1 := by
    ext r; simp only [mem_Icc,mem_union]; constructor
    · intro h
      exact (le_or_gt r 0).elim (fun hh => Or.inl ⟨h.1,hh⟩) (fun hh => Or.inr ⟨hh.le,h.2⟩)
    · rintro (h|h)
      · exact ⟨h.1,h.2.trans zero_le_one⟩
      · exact ⟨(by norm_num : (-1:ℝ) ≤ 0).trans h.1,h.2⟩
  rw [hS]
  calc
    _ ≤ (∫⁻ r in Icc (-1:ℝ) 0, depthLogPower n r) + (∫⁻ r in Icc (0:ℝ) 1, depthLogPower n r) :=
      lintegral_union_le _ _ _
    _ = _ := by rw [hneg,depthLogPower_posInterval,two_mul]

/-- All powers of the logarithm of the depth difference have a finite
joint integral over the literal unit square. The bound controls the
fully correlated displacement coordinates of the coherent example. -/
theorem coherent_depth_log_moment (n : ℕ) :
    (∫⁻ r in Icc (0:ℝ) 1, ∫⁻ s in Icc (0:ℝ) 1,
      ENNReal.ofReal (abs (log |r-s|)^n)) ≤ 2 * ENNReal.ofReal (n.factorial : ℝ) := by
  have hb (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
      (∫⁻ s in Icc (0:ℝ) 1, depthLogPower n (r-s)) ≤ 2 * ENNReal.ofReal (n.factorial:ℝ) := by
    let e := fun u : ℝ => r-u
    have hImage : e '' Icc (r-1) r = Icc (0:ℝ) 1 := by
      ext x; constructor
      · rintro ⟨u,hu,rfl⟩
        exact ⟨sub_nonneg.mpr hu.2,(sub_le_comm.mp hu.1)⟩
      · intro hx
        refine ⟨r-x,⟨sub_le_sub_left hx.2 _,sub_le_self _ hx.1⟩,?_⟩
        dsimp [e]
        ring
    have hD (u : ℝ) (_hu : u ∈ Icc (r-1) r) :
        HasDerivWithinAt e (-1) (Icc (r-1) r) u := by
      simpa [e] using ((hasDerivAt_const u r).sub (hasDerivAt_id u)).hasDerivWithinAt (s := Icc (r-1) r)
    have hInj : InjOn e (Icc (r-1) r) := by
      intro x _ y _ h
      change r-x = r-y at h
      linarith
    have hEq := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc hD hInj
      (fun s => depthLogPower n (r-s))
    rw [hImage] at hEq
    rw [hEq]
    have hN (u : ℝ) : ENNReal.ofReal |(-1:ℝ)| * depthLogPower n (r-e u) = depthLogPower n u := by
      simp only [abs_neg,abs_one,ENNReal.ofReal_one,one_mul,e,sub_sub_cancel]
    simp_rw [hN]
    apply (lintegral_mono_set (s := Icc (r-1) r) (t := Icc (-1:ℝ) 1) ?_).trans (depthLogPower_symmetric n)
    exact fun _ hu => ⟨(by linarith [hr.1] : -1 ≤ r-1).trans hu.1, hu.2.trans hr.2⟩
  change (∫⁻ r in Icc (0:ℝ) 1, ∫⁻ s in Icc (0:ℝ) 1, depthLogPower n (r-s)) ≤ _
  calc
    _ ≤ ∫⁻ _ in Icc (0:ℝ) 1, 2 * ENNReal.ofReal (n.factorial : ℝ) :=
      lintegral_mono_ae ((ae_restrict_mem measurableSet_Icc).mono hb)
    _ = _ := by simp [lintegral_const,Real.volume_Icc]

private theorem logKernel_scaled_majorant {m ell : ℝ} (hm : 0 < m) (hell : 0 < ell) :
    ∃ A : ℝ, 0 < A ∧ ∀ x ∈ Ioc (0:ℝ) 1,
      logKernel m (ell*x) ≤ ENNReal.ofReal (A*(1+|log x|)) := by
  let c := min 1 (m*ell)
  let B := 8*π^2
  let R := (2+log 4)/(16*π^2)
  let A := R+(|log c|+1)/B
  have hc : 0 < c := lt_min zero_lt_one (mul_pos hm hell)
  have hB : 0 < B := by unfold B; positivity
  have hR : 0 < R := by
    unfold R
    apply div_pos
    · linarith [log_nonneg (show (1:ℝ) ≤ 4 by norm_num)]
    · positivity
  have hAB : B⁻¹ ≤ A := by
    unfold A
    rw [← one_div]
    linarith [div_le_div_of_nonneg_right (show (1:ℝ) ≤ |log c|+1 by linarith [abs_nonneg (log c)]) hB.le]
  refine ⟨A,lt_of_lt_of_le (inv_pos.mpr hB) hAB,?_⟩
  intro x hx
  have hx₀ := hx.1
  have hx₁ := hx.2
  have hcx : 0 < c*x := mul_pos hc hx₀
  have hcx₁ : 1*(c*x) ≤ 2 := by
    rw [one_mul]
    exact (mul_le_one₀ (min_le_left _ _) hx₀.le hx₁).trans (by norm_num)
  have hl : logKernel m (ell*x) = logKernel 1 (m*ell*x) := by
    rw [logKernel_bessel hm (mul_pos hell hx₀),
      logKernel_bessel zero_lt_one (mul_pos (mul_pos hm hell) hx₀),one_mul,mul_assoc]
  have hcmp : logKernel 1 (m*ell*x) ≤ logKernel 1 (c*x) := logKernel_antitone 1
    hcx.le (mul_nonneg (mul_pos hm hell).le hx₀.le) (mul_le_mul_of_nonneg_right (min_le_right _ _) hx₀.le)
  rw [hl]
  apply hcmp.trans
  have hfin : logKernel 1 (c*x) ≠ ⊤ := by
    rw [logKernel_bessel zero_lt_one hcx]
    exact ENNReal.ofReal_ne_top
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  have hbound := (abs_le.mp (logKernel_log_remainder zero_lt_one hcx hcx₁)).2
  rw [one_mul,one_div,log_inv,log_mul hc.ne' hx₀.ne'] at hbound
  change (logKernel 1 (c*x)).toReal - (-(log c+log x))/B ≤ R at hbound
  have hlog : -(log c+log x) ≤ |log c|+|log x| := by
    linarith [neg_abs_le (log c),neg_abs_le (log x)]
  calc
    _ ≤ R+(|log c|+|log x|)/B := by
      linarith [div_le_div_of_nonneg_right hlog hB.le]
    _ ≤ A*(1+|log x|) := by
      have hA' : R+|log c|/B ≤ A := by
        unfold A
        have h : |log c| ≤ |log c|+1 := le_add_of_nonneg_right zero_le_one
        exact add_le_add_left (div_le_div_of_nonneg_right h hB.le) R
      rw [show R+(|log c|+|log x|)/B = (R+|log c|/B)+B⁻¹*|log x| by ring,mul_add,mul_one]
      exact add_le_add hA' (mul_le_mul_of_nonneg_right hAB (abs_nonneg _))

/-- The actual retained displacements on each marked line can all
use the same depth difference. Unit readout directions preserve its
size, and the complete product of marginal kernels is integrable. -/
theorem coherent_depth_log_kernel_finite {ι : Type*} [Fintype ι]
    {m ell : ℝ} (hm : 0 < m) (hell : 0 < ell)
    (u : ι → SectorPlane.UnitVector ScalarMomentum) :
    (∫⁻ r in Icc (0:ℝ) 1, ∫⁻ s in Icc (0:ℝ) 1,
      ∏ i, logKernel m ‖(ell*(r-s)) • (u i).val‖) < ⊤ := by
  obtain ⟨A,hA,hBound⟩ := logKernel_scaled_majorant hm hell
  let n := Fintype.card ι
  let C := ENNReal.ofReal (A^n*2^n)
  let ν : Measure ℝ := volume.restrict (Icc 0 1)
  let g := fun r s : ℝ => depthLogPower n (r-s)
  have hν : ν univ = 1 := by simp [ν,Measure.restrict_apply,Real.volume_Icc]
  have hcomp (r s : ℝ) (hr : r ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1) (hne : s≠r) :
      (∏ i, logKernel m ‖(ell*(r-s)) • (u i).val‖) ≤ C*(1+g r s) := by
    have hNorm (i : ι) : ‖(ell*(r-s)) • (u i).val‖ = ell*|r-s| := by
      rw [norm_smul,(u i).property,mul_one,Real.norm_eq_abs,abs_mul,abs_of_pos hell]
    have hx : |r-s| ∈ Ioc (0:ℝ) 1 := by
      refine ⟨abs_pos.mpr (sub_ne_zero.mpr hne.symm),abs_le.mpr ⟨?_,?_⟩⟩
      · linarith [hr.1,hs.2]
      · linarith [hr.2,hs.1]
    let y := abs (log |r-s|)
    have hy : 0 ≤ y := abs_nonneg _
    have hp : (1+y)^n ≤ 2^n*(1+y^n) := by
      rcases le_or_gt y 1 with hh | hh
      · exact (pow_le_pow_left₀ (by linarith) (by linarith : 1+y ≤ 2) n).trans
          (le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg hy n]))
      · have h := pow_le_pow_left₀ (by linarith) (by linarith : 1+y ≤ 2*y) n
        rw [mul_pow] at h
        exact h.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity))
    simp only [hNorm,Finset.prod_const]
    change logKernel m (ell*|r-s|)^n ≤ ENNReal.ofReal (A^n*2^n)*(1+ENNReal.ofReal (y^n))
    apply (pow_le_pow_left' (hBound |r-s| hx) n).trans
    rw [← ENNReal.ofReal_one,← ENNReal.ofReal_add zero_le_one (pow_nonneg hy n),
      ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_pow (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [mul_pow,mul_assoc]
    exact mul_le_mul_of_nonneg_left hp (pow_nonneg hA.le n)
  have hlt : (∫⁻ r, (∫⁻ s, g r s ∂ν) ∂ν) < ⊤ := by
    apply (coherent_depth_log_moment n).trans_lt
    exact ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top
  refine lt_of_le_of_lt (lintegral_mono_ae (g := fun r => ∫⁻ s, C*(1+g r s) ∂ν) ?_) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    apply lintegral_mono_ae
    have hd : ∀ᵐ s ∂ν, s ≠ r := by
      rw [ae_iff,show {s : ℝ | ¬s≠r} = {r} by ext s; simp]
      exact measure_singleton r
    filter_upwards [ae_restrict_mem measurableSet_Icc,hd] with s hs hd'
    exact hcomp r s hr hs hd'
  · have hC : C ≠ ⊤ := ENNReal.ofReal_ne_top
    have hOne : Measurable (fun _ : ℝ => (1:ℝ≥0∞)) := measurable_const
    have hInner (r : ℝ) : (∫⁻ s, C*(1+g r s) ∂ν) = C*(1+∫⁻ s, g r s ∂ν) := by
      rw [lintegral_const_mul' C _ hC,lintegral_add_left hOne,lintegral_const,hν,mul_one]
    simp_rw [hInner]
    rw [lintegral_const_mul' C _ hC,lintegral_add_left hOne,lintegral_const,hν,mul_one]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨by simp,hlt⟩)

private def coherentDepthVolume : Measure ℝ := volume.restrict (Icc 0 1)

private instance : IsFiniteMeasure coherentDepthVolume := by
  unfold coherentDepthVolume
  infer_instance

private def coherentDisplacement {ι : Type*} (ell : ℝ)
    (u : ι → SectorPlane.UnitVector ScalarMomentum) (p : ℝ × ℝ) (i : ι) :=
  (ell*(p.1-p.2)) • (u i).val

private theorem coherentDisplacement_measurable {ι : Type*} (ell : ℝ)
    (u : ι → SectorPlane.UnitVector ScalarMomentum) :
    Measurable (coherentDisplacement ell u) := by
  apply measurable_pi_iff.mpr
  intro i
  have h : Continuous (fun p : ℝ × ℝ => ell*(p.1-p.2)) := by fun_prop
  change Measurable (fun p : ℝ × ℝ => (ell*(p.1-p.2)) • (u i).val)
  exact (h.smul continuous_const).measurable

def coherentDepthLaw {ι : Type*} (ell : ℝ) (u : ι → SectorPlane.UnitVector ScalarMomentum) :
    Measure (ι → ScalarMomentum) :=
  Measure.map (coherentDisplacement ell u) (coherentDepthVolume.prod coherentDepthVolume)

instance {ι : Type*} (ell : ℝ) (u : ι → SectorPlane.UnitVector ScalarMomentum) :
    IsFiniteMeasure (coherentDepthLaw ell u) := by unfold coherentDepthLaw; infer_instance

private def coherentReadout {ι : Type*} [Fintype ι] (ell : ℝ)
    (u : ι → SectorPlane.UnitVector ScalarMomentum) (q : ι → ScalarMomentum) :=
  ell * ∑ i, ⟪(u i).val,q i⟫

/-- The characteristic of the joint pushforward is the squared
coherent amplitude, with the same single depth at every readout. -/
theorem coherent_depth_characteristic {ι : Type*} [Fintype ι] (ell : ℝ)
    (u : ι → SectorPlane.UnitVector ScalarMomentum) (q : ι → ScalarMomentum) :
    marginalCharacteristic (coherentDepthLaw ell u) q =
      Complex.normSq (∫ r in Icc (0:ℝ) 1, Complex.exp (Complex.I*(r*coherentReadout ell u q:ℝ))) := by
  let B := coherentReadout ell u q
  let F := fun r : ℝ => Complex.exp (Complex.I*(r*B:ℝ))
  have hΦ : Measurable (marginalPhase q) := by
    let f := fun d : ι → ScalarMomentum => (q,d)
    have hf : Measurable f := measurable_prodMk_left
    change Measurable ((fun p : (ι → ScalarMomentum) × (ι → ScalarMomentum) => marginalPhase p.1 p.2) ∘ f)
    exact marginalPhase_measurable.comp hf
  unfold marginalCharacteristic coherentDepthLaw
  rw [integral_map (coherentDisplacement_measurable ell u).aemeasurable hΦ.aestronglyMeasurable]
  have he (p : ℝ × ℝ) : marginalPhase q (coherentDisplacement ell u p) = F p.1 * conj (F p.2) := by
    unfold marginalPhase coherentDisplacement stableFourierPhase F B coherentReadout
    rw [← Complex.exp_sum,← Complex.exp_conj,← Complex.exp_add]
    congr 1
    simp_rw [real_inner_smul_left]
    rw [← Finset.mul_sum,← Complex.ofReal_sum,← Finset.mul_sum]
    simp only [map_mul,Complex.conj_I,Complex.conj_ofReal]
    push_cast
    ring
  simp_rw [he]
  rw [integral_prod_mul F (fun r => conj (F r)),integral_conj,Complex.mul_conj,Complex.ofReal_re]
  rfl

/-- The genuine coherent unit-square law supplies a finite bare
energy for every finite list of marginal loop directions. -/
theorem coherent_depth_marginal_energy_finite {ι : Type*} [Fintype ι]
    {m ell : ℝ} (hm : 0 < m) (hell : 0 < ell) (u : ι → SectorPlane.UnitVector ScalarMomentum) :
    (∫⁻ q : ι → ScalarMomentum, ENNReal.ofReal (marginalCharacteristic (coherentDepthLaw ell u) q) *
      ∏ i, ENNReal.ofReal (((m^2+‖q i‖^2)^2)⁻¹/(2*π)^4)) < ⊤ := by
  have hC (q : ι → ScalarMomentum) : 0 ≤ marginalCharacteristic (coherentDepthLaw ell u) q := by
    rw [coherent_depth_characteristic]
    exact Complex.normSq_nonneg _
  rw [joint_marginal_log_energy _ hm hC]
  unfold coherentDepthLaw
  let H := fun d : ι → ScalarMomentum => ∏ i, logKernel m ‖d i‖
  have hH : Measurable H := Finset.measurable_prod _ fun i _ =>
    (logKernel_measurable m).comp (measurable_pi_apply i).norm
  rw [lintegral_map hH (coherentDisplacement_measurable ell u)]
  let f := fun p : ℝ × ℝ => H (coherentDisplacement ell u p)
  change (∫⁻ p, f p ∂coherentDepthVolume.prod coherentDepthVolume) < ⊤
  rw [lintegral_prod f (hH.comp (coherentDisplacement_measurable ell u)).aemeasurable]
  exact coherent_depth_log_kernel_finite hm hell u

end UV.SewnFlags
