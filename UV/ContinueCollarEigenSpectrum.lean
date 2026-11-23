import UV.ContinueCollarEigenWeight

/-! Sharp determinant weight per normalized radial eigenfunction at
energy E, and the corresponding sum over collar durations. -/

noncomputable section

open Real Set Filter MeasureTheory
open scoped Topology

namespace UV.CollarEigenmode

theorem weighted_mode_spectral_bound {j A : ℝ} (hj : j ≠ 0) (hA : 0 < A) :
    ∃ B : ℝ,0 < B ∧ ∀ E : ℝ,0 ≤ E → ∀ u g : ℝ → ℝ,ContinuousOn u (Icc 0 1) → u 0 = 0 →
      (∀ x ∈ Ioo 0 1,HasDerivAt u (g x) x) → (∀ x ∈ Ioo 0 1,HasDerivAt g ((potential j x-E)*u x) x) →
      (∫ r in Ioc (0:ℝ) 1,u r^2) = 1 → ∀ F : ℝ → ℝ,Measurable F → (∀ r,0 ≤ F r) →
      (∀ r ∈ Ioc (0:ℝ) 1,F r ≤ exp (logWeight A r)) →
      IntegrableOn (fun r => F r*u r^2) (Ioc 0 1) ∧
        (∫ r in Ioc (0:ℝ) 1,F r*u r^2) ≤ B*(1+E)*exp (B*(1+E)^(1/4:ℝ)*(1+log (2+E))^3) := by
  let c := |j|/6
  have hc : 0 < c := div_pos (abs_pos.mpr hj) (by norm_num)
  have hd : 0 < j^2-(3*c)^2 := by
    dsimp [c]; rw [mul_div_assoc',div_pow,mul_pow,sq_abs]; nlinarith [sq_pos_of_ne_zero hj]
  obtain ⟨β,hβ,hβ1,ht⟩ := logWeight_tame hA hc
  let D := j^2-(3*c)^2
  let K := min β (D^(1/8:ℝ))
  have hK : 0 < K := lt_min hβ (rpow_pos_of_pos hd _)
  have hK1 : K ≤ 1 := (min_le_left ..).trans hβ1
  have hKD : K^8 ≤ D := by
    have hh := pow_le_pow_left₀ hK.le (min_le_right β (D^(1/8:ℝ))) 8
    rw [←Real.rpow_mul_natCast hd.le] at hh
    norm_num at hh
    exact hh
  let J := 1+log (4/K)
  have hJ : 1 ≤ J := by dsimp [J]; have h := log_nonneg (show 1 ≤ 4/K from (le_div_iff₀ hK).mpr (by linarith)); linarith
  let B := max 5 ((16*A/K^2)*J^3)
  have hB : 5 ≤ B := le_max_left ..
  refine ⟨B,by linarith,fun E hE u g hu0 hz hu hg hn F hm hF hFb => ?_⟩
  let x := 1+E
  let p := x^(1/8:ℝ)
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hp : 1 ≤ p := one_le_rpow hx (by norm_num)
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hp8 : p^8=x := by rw [←Real.rpow_mul_natCast hx0.le]; norm_num
  have hp2 : p^2=x^(1/4:ℝ) := by rw [←Real.rpow_mul_natCast hx0.le]; norm_num
  let h := K/p
  have hh : 0 < h := div_pos hK hp0
  have hhk : h ≤ K := div_le_self hK.le hp
  have hh1 := hhk.trans hK1
  have hgap : E*h^8 ≤ D := by
    dsimp only [h]; rw [div_pow,hp8]
    calc E*(K^8/x) ≤ x*(K^8/x) := mul_le_mul_of_nonneg_right (by dsimp [x]; linarith) (by positivity)
         _ = K^8 := by field_simp
         _ ≤ D := hKD
  obtain ⟨hi,hval⟩ := weighted_mode_at_scale hc hA hE hh hh1 hgap (fun r hr hrh => ht r hr (hrh.trans (hhk.trans (min_le_left ..))))
    hu0 hz hu hg hn F hm hF hFb
  refine ⟨hi,hval.trans ?_⟩
  have hlog : log (h/4) = -log (4/K) -(1/8:ℝ)*log x := by
    change log (K/p/4) = -log (4/K) -(1/8:ℝ)*log x
    rw [log_div (div_ne_zero hK.ne' hp0.ne') (by norm_num : (4:ℝ) ≠ 0),
      log_div hK.ne' hp0.ne',log_div (by norm_num : (4:ℝ) ≠ 0) hK.ne',show log p = (1/8:ℝ)*log x from log_rpow hx0 _]
    ring
  let Lg := 1+log (2+E)
  have hl : 0 ≤ log x := log_nonneg hx
  have hL : 1 ≤ Lg := by dsimp [Lg]; have h := log_nonneg (show 1 ≤ 2+E by linarith); linarith
  have hden : A/(h/4)^2 = (16*A/K^2)*x^(1/4:ℝ) := by
    dsimp only [h]; rw [←hp2]; field_simp; ring
  have hlogu : 1-log (h/4) ≤ J*Lg := by
    have hx' : x ≤ 2+E := by dsimp [x]; linarith
    have hlogx := log_le_log hx0 hx'
    rw [hlog]; dsimp [J,Lg] at *
    nlinarith [mul_nonneg (show 0 ≤ log (4/K) by linarith) (log_nonneg (show 1 ≤ 2+E by linarith))]
  have hlow : 0 ≤ 1-log (h/4) := by have hrel := log_nonpos (by positivity : 0 ≤ h/4) (by linarith : h/4 ≤ 1); linarith
  have hW : logWeight A (h/4) ≤ B*x^(1/4:ℝ)*Lg^3 := by
    rw [logWeight,hden]
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlow hlogu 3) (by positivity : 0 ≤ (16*A/K^2)*x^(1/4:ℝ))).trans
    rw [mul_pow]
    have hb := le_max_right (5:ℝ) ((16*A/K^2)*J^3)
    calc _ = (((16*A/K^2)*J^3)*x^(1/4:ℝ))*Lg^3 := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (rpow_nonneg hx0.le _)) (pow_nonneg (by linarith) 3)
  have hb0 : 0 ≤ B*x^(1/4:ℝ)*Lg^3 := by positivity
  have hbexp := one_le_exp hb0
  have hBx : 5 ≤ B*x := hB.trans (le_mul_of_one_le_right (by linarith) hx)
  change 4+_ ≤ B*x*exp (B*x^(1/4:ℝ)*Lg^3)
  exact (add_le_add_left (exp_le_exp.mpr hW) 4).trans (by nlinarith [mul_le_mul_of_nonneg_right hBx (exp_pos (B*x^(1/4:ℝ)*Lg^3)).le])

end UV.CollarEigenmode
