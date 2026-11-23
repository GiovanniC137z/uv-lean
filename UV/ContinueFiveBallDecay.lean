import UV.ContinueNormalShellDecay

/-! The five-ball has quartic transverse sections along its Fourier axis.
Their double endpoint zero gives cubic Fourier decay, uniform in the
slice radius. This power controls the two charged-leg compressions. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set Metric
open scoped RealInnerProductSpace ENNReal

namespace UV

def normalFiveBallAxis : (d : ℕ) → Fin (d+5)
  | 0 => 0
  | d+1 => (normalFiveBallAxis d).succ

theorem normal_five_ball_integral {R : ℝ} (hR : 0 ≤ R) (a : ℝ) :
    (∫ y in ball (0 : NormalBall 5) R, normalBallWave 0 a y) =
      ((Real.pi^2/2:ℝ):ℂ) * ∫ t in Ioo (-R) R, (((R:ℂ)^2-(t:ℂ)^2)^2*Complex.exp ((Complex.I*(a:ℂ))*(t:ℂ))) := by
  rw [normal_ball_slice hR _ (normal_ball_wave_continuous _ a),←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have hsq : 0 ≤ R^2-t^2 := by nlinarith [mul_pos (sub_pos.mpr ht.2) (by linarith [ht.1] : 0 < R+t)]
  change (∫ _ : NormalBall 4 in ball 0 (Real.sqrt (R^2-t^2)), Complex.exp ((Complex.I*(a:ℂ))*(t:ℂ))) = _
  have hv (r : ℝ) : volume (ball (0:NormalBall 4) r) = ENNReal.ofReal r^4*ENNReal.ofReal (Real.pi^2/2) := by
    norm_num [InnerProductSpace.volume_ball_of_dim_even (k := 2) (by simp) (0:NormalBall 4)]
  rw [setIntegral_const]
  simp only [measureReal_def,hv,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _),ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi^2/2),Complex.real_smul]
  rw [show Real.sqrt (R^2-t^2)^4 = (R^2-t^2)^2 by nlinarith [Real.sq_sqrt hsq,congrArg (fun z:ℝ => z^2) (Real.sq_sqrt hsq)]]
  push_cast
  ring

/-- Fourier transform of the actual quartic cross-section, controlled at
both endpoints by the third and higher inverse powers of frequency. -/
theorem normal_quartic_fourier_bound {R a : ℝ} (hR : 0 ≤ R) (hR' : R ≤ 1) (ha : 1 ≤ a) :
    ‖∫ t in Ioo (-R) R, (((R:ℂ)^2-(t:ℂ)^2)^2*Complex.exp ((Complex.I*(a:ℂ))*(t:ℂ)))‖ ≤ 112/(a^3) := by
  let c := Complex.I*(a:ℂ)
  have ha' : 0 < a := by linarith
  have hc : c ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ha'.ne')
  let q := fun z : ℂ => (R:ℂ)^2-z^2
  let H := fun z : ℂ => q z^2*c⁻¹+4*z*q z*c⁻¹^2+(12*z^2-4*(R:ℂ)^2)*c⁻¹^3-24*z*c⁻¹^4+24*c⁻¹^5
  let F := fun z : ℂ => H z*Complex.exp (c*z)
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => F s) ((q t)^2*Complex.exp (c*t)) t := by
    have hz := hasDerivAt_id (t:ℂ)
    have hq := (hasDerivAt_const (t:ℂ) ((R:ℂ)^2)).sub (hz.pow 2)
    have hp := (((((hq.pow 2).mul_const c⁻¹).add ((((hz.const_mul 4).mul hq).mul_const (c⁻¹^2)))).add
      ((((hz.pow 2).const_mul 12).sub_const (4*(R:ℂ)^2)).mul_const (c⁻¹^3))).sub
      ((hz.const_mul 24).mul_const (c⁻¹^4))).add_const (24*c⁻¹^5)
    have h := (hp.mul (hz.const_mul c).cexp).comp_ofReal
    convert h using 1
    dsimp [H,q,id]
    field_simp [hc]
    ring
  rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le (by linarith : -R ≤ R),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (by apply Continuous.intervalIntegrable; fun_prop)]
  have hcabs : ‖c‖ = a := by simp [c,abs_of_pos ha']
  have hp (t : ℝ) (ht : |t| = R) : ‖F t‖ ≤ 56/(a^3) := by
    have ht2 : (R:ℂ)^2=(t:ℂ)^2 := by exact_mod_cast (show R^2=t^2 by rw [←ht,sq_abs])
    have hexp : ‖Complex.exp (c*(t:ℂ))‖ = 1 := by simp [c,Complex.norm_exp,Complex.mul_re]
    have hzero : q t = 0 := sub_eq_zero.mpr ht2
    have hH : H t = 8*(t:ℂ)^2*c⁻¹^3-24*(t:ℂ)*c⁻¹^4+24*c⁻¹^5 := by dsimp only [H]; rw [hzero,ht2]; ring
    rw [show F t = H t*Complex.exp (c*t) from rfl,norm_mul,hexp,mul_one,hH]
    apply (norm_add_le _ _).trans ((add_le_add_right (norm_sub_le _ _) _).trans ?_)
    simp only [norm_mul,norm_pow,norm_inv,Complex.norm_real,Real.norm_eq_abs,ht,hcabs,Complex.norm_ofNat]
    have h1 : 0 ≤ a⁻¹ := inv_nonneg.mpr ha'.le
    have h2 : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha
    have h4 : a⁻¹^4 ≤ a⁻¹^3 := by simpa only [pow_succ] using mul_le_of_le_one_right (pow_nonneg h1 3) h2
    have h5 : a⁻¹^5 ≤ a⁻¹^4 := by simpa only [pow_succ] using mul_le_of_le_one_right (pow_nonneg h1 4) h2
    have hR2 : R^2 ≤ 1 := by nlinarith [mul_nonneg hR (sub_nonneg.mpr hR')]
    rw [div_eq_mul_inv,←inv_pow]
    nlinarith [mul_le_mul_of_nonneg_right hR' (pow_nonneg h1 4),mul_le_mul_of_nonneg_right hR2 (pow_nonneg h1 3)]
  exact (norm_sub_le _ _).trans ((add_le_add (hp R (abs_of_nonneg hR)) (hp (-R) (by simp [abs_of_nonneg hR]))).trans_eq (by ring))

/-- Extra normal directions can be integrated one at a time. The
estimate is uniform in every slice radius between zero and one. -/
theorem normal_five_ball_axis_decay (d : ℕ) {R a : ℝ} (hR : 0 ≤ R) (hR' : R ≤ 1) (ha : 1 ≤ a) :
    ‖∫ y in ball (0 : NormalBall (d+5)) R, normalBallWave (normalFiveBallAxis d) a y‖ ≤
      ((2:ℝ)^d * (112*(Real.pi^2/2)))/(a^3) := by
  induction d generalizing R with
  | zero =>
    rw [normalFiveBallAxis,normal_five_ball_integral hR,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ Real.pi^2/2)]
    apply (mul_le_mul_of_nonneg_left (normal_quartic_fourier_bound hR hR' ha) (by positivity : 0 ≤ Real.pi^2/2)).trans_eq
    ring
  | succ d ih =>
    rw [normal_ball_slice hR _ (normal_ball_wave_continuous _ a)]
    let F := fun t : ℝ => ∫ y in ball (0 : NormalBall (d+5)) (Real.sqrt (R^2-t^2)), normalBallWave (normalFiveBallAxis d) a y
    let B := ((2:ℝ)^d*(112*(Real.pi^2/2)))/(a^3)
    change ‖∫ t in Ioo (-R) R, F t‖ ≤ _
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hb (t : ℝ) : ‖F t‖ ≤ B := ih (Real.sqrt_nonneg _) ((Real.sqrt_le_iff).mpr
      ⟨zero_le_one,by nlinarith [sq_nonneg t]⟩)
    have hfin : volume (Ioo (-R) R) < ⊤ := measure_Ioo_lt_top
    have h := norm_setIntegral_le_of_norm_le_const hfin (fun t _ => hb t)
    apply h.trans
    rw [Real.volume_real_Ioo_of_le (by linarith : -R ≤ R)]
    calc B*(R- -R) ≤ B*2 := mul_le_mul_of_nonneg_left (by linarith) hB
         _ = _ := by dsimp [B]; rw [pow_succ]; ring

theorem normal_shell_characteristic_cubic (ι : Type*) [Fintype ι] (hn : 5 ≤ Fintype.card ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : WilsonBallSpace ι, ‖normalShellCharacteristic p‖ ≤ C / (1+‖p‖)^3 := by
  let d := Fintype.card ι-5
  have hdim : Fintype.card ι = d+5 := by dsimp [d]; omega
  let e : WilsonBallSpace ι ≃ₗᵢ[ℝ] NormalBall (d+5) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hdim))
  let j := normalFiveBallAxis d
  let A := (volume (ball (0:NormalBall (d+5)) 1)).toReal⁻¹ * ((2:ℝ)^d*(112*(Real.pi^2/2)))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨8*(1+A),by positivity,fun p => ?_⟩
  let a := ‖p‖
  have ha : 0 ≤ a := norm_nonneg p
  by_cases h : 1 ≤ a
  · let q := EuclideanSpace.single j a
    have he : ‖e p‖ = ‖q‖ := by simp [q,a,EuclideanSpace.norm_single]
    have hw (x : NormalBall (d+5)) : Complex.exp (Complex.I*(⟪q,x⟫:ℝ)) = normalBallWave j a x := by
      simp [q,EuclideanSpace.inner_single_left,normalBallWave,mul_assoc]
    have hbound : ‖normalShellCharacteristic q‖ ≤ A/a^3 := by
      unfold normalShellCharacteristic wilsonBallMeasure ProbabilityTheory.cond
      simp_rw [hw]
      rw [integral_smul_measure,norm_smul,ENNReal.toReal_inv,Real.norm_of_nonneg (by positivity)]
      apply (mul_le_mul_of_nonneg_left (normal_five_ball_axis_decay d (R := 1) zero_le_one le_rfl h) (by positivity)).trans_eq
      dsimp [A]; ring
    rw [←normal_shell_characteristic_isometry e p,normal_shell_characteristic_radial he]
    apply hbound.trans
    change A/a^3 ≤ 8*(1+A)/(1+a)^3
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h8 : (1+a)^3 ≤ (2*a)^3 := pow_le_pow_left₀ (by positivity) (by linarith) _
    rw [mul_pow] at h8
    nlinarith [mul_le_mul_of_nonneg_left h8 hA,show 0 ≤ a^3 by positivity]
  · apply (normal_shell_characteristic_le_one p).trans
    change 1 ≤ 8*(1+A)/(1+a)^3
    rw [le_div_iff₀ (by positivity)]
    have h8 : (1+a)^3 ≤ (2:ℝ)^3 := pow_le_pow_left₀ (by positivity) (by linarith) _
    linarith

end UV
