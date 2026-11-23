import UV.ContinueCollarEigenmode

/-! From the singular radial eigenvalue equation to an integrable
determinant-weighted eigenmode. An L² normalization selects a point in
a short interior annulus for the comparison boundary. -/

noncomputable section

open Real Set Filter MeasureTheory
open scoped Topology

namespace UV.CollarEigenmode

private theorem annular_sample {u : ℝ → ℝ} {h : ℝ} (hh : 0 < h) (h₁ : h ≤ 1)
    (hi : IntegrableOn (fun r => u r^2) (Ioc 0 1)) (hn : (∫ r in Ioc (0:ℝ) 1,u r^2) = 1) :
    ∃ s ∈ Ioc (h/2) h, u s^2 ≤ 4/h := by
  classical
  by_contra hc
  have hle (s : ℝ) (hs : s ∈ Ioc (h/2) h) : 4/h ≤ u s^2 := le_of_not_ge fun hu => hc ⟨s,hs,hu⟩
  have hin : Ioc (h/2) h ⊆ Ioc (0:ℝ) 1 := fun _ hx => ⟨(by linarith : 0 < h/2).trans hx.1,hx.2.trans h₁⟩
  have hconst : IntegrableOn (fun _ : ℝ => 4/h) (Ioc (h/2) h) := integrableOn_const (measure_Ioc_lt_top (μ := (volume : Measure ℝ)) (a := h/2) (b := h)).ne
  have hl : (∫ _ in Ioc (h/2) h,(4:ℝ)/h) ≤ (∫ r in Ioc (h/2) h,u r^2) := setIntegral_mono_on hconst (hi.mono_set hin) measurableSet_Ioc hle
  have hr : (∫ r in Ioc (h/2) h,u r^2) ≤ (∫ r in Ioc (0:ℝ) 1,u r^2) := setIntegral_mono_set hi (Eventually.of_forall fun r => sq_nonneg (u r)) (Eventually.of_forall fun _ hy => hin hy)
  rw [hn] at hr
  rw [setIntegral_const,Real.volume_real_Ioc_of_le (by linarith : h/2 ≤ h),smul_eq_mul] at hl
  have heq : (h-h/2)*(4/h)=2 := by field_simp; ring
  exact (by norm_num : ¬(2:ℝ) ≤ 1) (heq ▸ hl.trans hr)


def logWeight (C r : ℝ) := C/r^2*(1-log r)^3

theorem logWeight_anti {A x y : ℝ} (hA : 0 ≤ A) (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1) :
    logWeight A y ≤ logWeight A x := by
  have hlog := log_le_log hx hxy
  have hp := log_nonpos (hx.trans_le hxy).le hy
  apply mul_le_mul (div_le_div_of_nonneg_left hA (sq_pos_of_pos hx) (pow_le_pow_left₀ hx.le hxy 2)) _
    (pow_nonneg (by linarith) 3) (div_nonneg hA (sq_nonneg x))
  exact pow_le_pow_left₀ (by linarith) (by linarith) 3

theorem logWeight_tame {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    ∃ β : ℝ,0 < β ∧ β ≤ 1 ∧ ∀ r,0 < r → r ≤ β → logWeight A r ≤ c/r^3 := by
  have hlim := (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (3:ℝ) (s := -1) (by norm_num)).tendsto_div_nhds_zero
  have hexp : ∀ᶠ r : ℝ in 𝓝[>] 0, r*|log r|^3 < c/(8*A) := by
    filter_upwards [hlim.eventually_lt_const (show 0 < c/(8*A) by positivity),self_mem_nhdsWithin] with r hr hr₀
    norm_num [show (3:ℝ) = (3:ℕ) by norm_num,Real.rpow_neg_one,div_inv_eq_mul,mul_comm] at hr ⊢
    exact hr
  have ht : ∀ᶠ r : ℝ in 𝓝[>] 0, logWeight A r ≤ c/r^3 := by
    filter_upwards [hexp,self_mem_nhdsWithin,Ioo_mem_nhdsGT (exp_pos (-1))] with r hr hr₀ hr₁
    have hlog : log r < -1 := by simpa only [log_exp] using log_lt_log hr₀ hr₁.2
    rw [abs_of_neg (by linarith : log r < 0)] at hr
    have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1-log r) (by linarith : 1-log r ≤ 2*(-log r)) 3
    unfold logWeight
    rw [le_div_iff₀ (pow_pos hr₀ 3)]
    have hmul := (lt_div_iff₀ (by positivity : 0 < 8*A)).mp hr
    have hcalc : A/r^2*(1-log r)^3*r^3 = (A*r)*(1-log r)^3 := by field_simp
    rw [hcalc]
    nlinarith only [mul_le_mul_of_nonneg_left hp (mul_nonneg hA.le hr₀.le),hmul]
  obtain ⟨b,hb,hs⟩ := (mem_nhdsGT_iff_exists_Ioc_subset.mp ht)
  exact ⟨min 1 b,lt_min zero_lt_one hb,min_le_left ..,fun r hr h => hs ⟨hr,h.trans (min_le_right ..)⟩⟩

theorem weighted_mode_at_scale {j E c A h : ℝ} (hc : 0 < c) (hA : 0 < A) (hE : 0 ≤ E)
    (hh : 0 < h) (h₁ : h ≤ 1) (hgap : E*h^8 ≤ j^2-(3*c)^2)
    (hl : ∀ r, 0 < r → r ≤ h → logWeight A r ≤ c/r^3)
    {u g : ℝ → ℝ} (hU : ContinuousOn u (Icc 0 1)) (hz : u 0 = 0)
    (hu : ∀ x ∈ Ioo 0 1,HasDerivAt u (g x) x) (hg : ∀ x ∈ Ioo 0 1,HasDerivAt g ((potential j x-E)*u x) x)
    (hn : (∫ r in Ioc (0:ℝ) 1, u r^2) = 1) (F : ℝ → ℝ) (hF : Measurable F) (hF₀ : ∀ r,0 ≤ F r)
    (hFb : ∀ r ∈ Ioc (0:ℝ) 1,F r ≤ exp (logWeight A r)) :
    IntegrableOn (fun r => F r*u r^2) (Ioc 0 1) ∧ (∫ r in Ioc (0:ℝ) 1,F r*u r^2) ≤ 4+exp (logWeight A (h/4)) := by
  have huss : IntegrableOn (fun r => u r^2) (Ioc 0 1) := ((hU.pow 2).integrableOn_Icc (μ := volume)).mono_set (Ioc_subset_Icc_self : Ioc (0:ℝ) 1 ⊆ _)
  obtain ⟨s,hs,hsv⟩ := annular_sample hh h₁ huss hn
  have hs0 : 0 < s := by linarith [hs.1]
  have hs1 := hs.2.trans h₁
  have hgap' := (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0.le hs.2 8) hE).trans hgap
  have hmode := dirichlet_mode_bound hc hs0 hE (hU.mono (Icc_subset_Icc_right hs1)) hz (fun x hx => hu x ⟨hx.1,hx.2.trans_le hs1⟩)
    (fun x hx => hg x ⟨hx.1,hx.2.trans_le hs1⟩) hgap'
  let Y := (Ioc (0:ℝ) h).indicator (fun _ : ℝ => 4/h)
  let C := exp (logWeight A (h/4))
  have hY : Integrable Y := (integrableOn_const (measure_Ioc_lt_top (μ := volume)).ne).integrable_indicator measurableSet_Ioc
  have hI := hY.integrableOn.add (huss.const_mul C)
  have hb (r : ℝ) (hr : r ∈ Ioc (0:ℝ) 1) : F r*u r^2 ≤ Y r+C*u r^2 := by
    by_cases hh' : r ≤ h/4
    · have hrs : r ≤ s := by linarith [hs.1]
      have hrh := hrs.trans hs.2
      have hu' := hmode r ⟨hr.1.le,hrs⟩
      have hratio : (r^2/s^2) ≤ 1 := (div_le_one (sq_pos_of_pos hs0)).mpr (pow_le_pow_left₀ hr.1.le hrs 2)
      have hre : |u s|/barrier c s*barrier c r = |u s| *(r^2/s^2)* exp (-c/r^3+c/s^3) := by
        rw [barrier,barrier,exp_add,show c/s^3 = -(-c/s^3) by ring,exp_neg]
        field_simp [exp_ne_zero]
      rw [hre] at hu'
      have hx := hu'.trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg _) hratio) (exp_pos _).le)
      have hx2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
      rw [sq_abs,mul_pow,←Real.exp_nat_mul,sq_abs] at hx2
      norm_num only [Nat.cast_ofNat] at hx2
      have hPow : 2*r^3 ≤ s^3 := by nlinarith only [pow_le_pow_left₀ (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hr.1.le) (show 2*r ≤ s by linarith [hs.1]) 3, pow_nonneg hr.1.le 3]
      have hxc : c/r^3 + 2*(-c/r^3 + c/s^3) ≤ 0 := by
        have hd : (2*c)/s^3 ≤ c/r^3 := (div_le_div_iff₀ (pow_pos hs0 3) (pow_pos hr.1 3)).mpr (show (2*c)*r^3 ≤ c*s^3 by nlinarith only [mul_le_mul_of_nonneg_left hPow hc.le])
        rw [mul_div_assoc] at hd
        rw [neg_div]
        linarith only [hd]
      have hbF := (hFb r hr).trans (exp_le_exp.mpr (hl r hr.1 hrh))
      have heq : exp (c/r^3)*(u s^2*exp (2*(-c/r^3+c/s^3))) = u s^2*exp (c/r^3+2*(-c/r^3+c/s^3)) := by rw [exp_add]; ring
      apply (mul_le_mul hbF hx2 (sq_nonneg _) (exp_pos _).le).trans
      rw [heq]
      have hsum := (mul_le_of_le_one_right (sq_nonneg (u s)) (exp_le_one_iff.mpr hxc)).trans hsv
      rw [show Y r = 4/h by exact Set.indicator_of_mem (show r ∈ Ioc 0 h from ⟨hr.1,hrh⟩) _]
      exact hsum.trans (le_add_of_nonneg_right (mul_nonneg (exp_pos _).le (sq_nonneg _)))
    · have hyy : 0 ≤ Y r := indicator_nonneg (fun _ _ => div_nonneg (by norm_num) hh.le) _
      exact (mul_le_mul_of_nonneg_right ((hFb r hr).trans (exp_le_exp.mpr
        (logWeight_anti hA.le (by positivity) (le_of_not_ge hh') hr.2))) (sq_nonneg _)).trans (le_add_of_nonneg_left hyy)
  have hmf := hF.aestronglyMeasurable.mul huss.aestronglyMeasurable
  have hi := hI.mono' hmf ((ae_restrict_mem measurableSet_Ioc).mono fun r hr => by
    change ‖F r*u r^2‖ ≤ Y r+C*u r^2
    rw [Real.norm_of_nonneg (mul_nonneg (hF₀ r) (sq_nonneg _))]; exact hb r hr)
  refine ⟨hi,(setIntegral_mono_on hi hI measurableSet_Ioc hb).trans_eq ?_⟩
  change (∫ r in Ioc (0:ℝ) 1,Y r+C*u r^2) = _
  rw [integral_add hY.integrableOn (huss.const_mul C),integral_const_mul,hn,mul_one]
  congr 1
  have hsub : Ioc (0:ℝ) h ⊆ Ioc 0 1 := Ioc_subset_Ioc_right h₁
  rw [show ∫ r in Ioc (0:ℝ) 1,Y r = ∫ r,Y r from setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr => Set.indicator_of_notMem (fun ha => hr (hsub ha)) _]
  dsimp [Y]; rw [integral_indicator measurableSet_Ioc,setIntegral_const,Real.volume_real_Ioc_of_le hh.le,smul_eq_mul]
  field_simp
  exact sub_zero h

end UV.CollarEigenmode
