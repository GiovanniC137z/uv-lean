import UV.ContinueFiveBallBessel
import UV.ContinueNormalLegProfile

/-! Dimension-dependent decay of the normalized A4 characteristic. The
Haar slice measure gives exactly the weight (1−t²)^((n−1)/2).
Combined with the radial Fourier equation this yields the exponent
(n+1)/2 for a single mark, and n+1 for two independent marks. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Metric
open scoped RealInnerProductSpace ENNReal

namespace UV

private theorem normal_ball_cosine_slice_real {n : ℕ} (a : ℝ) :
    (∫ y in ball (0:NormalBall (n+1)) 1, Real.cos (a*y 0)) =
      ∫ t in Ioo (-1:ℝ) 1, ∫ _ : NormalBall n in ball 0 (Real.sqrt (1-t^2)), Real.cos (a*t) := by
  let f := fun y : NormalBall (n+1) => (Real.cos (a*y 0):ℂ)
  have hc : Continuous f := by dsimp [f]; fun_prop
  have h := normal_ball_slice zero_le_one f hc
  change (∫ y in ball (0:NormalBall (n+1)) 1, (Real.cos (a*y 0):ℂ)) =
    ∫ t in Ioo (-1:ℝ) 1, ∫ _ : NormalBall n in ball 0 (Real.sqrt (1^2-t^2)), (Real.cos (a*t):ℂ) at h
  simp only [integral_complex_ofReal,one_pow] at h
  exact_mod_cast h

theorem normal_ball_axis_cosine_formula (d : ℕ) (a : ℝ) :
    (∫ y in ball (0:NormalBall (d+1+1)) 1, Real.cos (a*y 0)) =
      (volume.real (ball (0:NormalBall (d+1)) 1))*normalBallCosine (((d+1:ℕ):ℝ)/2) a := by
  rw [normal_ball_cosine_slice_real,normalBallCosine,intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1),
    integral_Ioc_eq_integral_Ioo,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have hq : 0 ≤ 1-t^2 := by nlinarith [mul_pos (sub_pos.mpr ht.2) (by linarith [ht.1] : 0 < 1+t)]
  let R := Real.sqrt (1-t^2)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hr : R^(d+1) = normalBallSectionWeight (((d+1:ℕ):ℝ)/2) t := by
    simp only [R,Real.sqrt_eq_rpow,normalBallSectionWeight,←Real.rpow_mul_natCast hq]
    congr 1; ring
  rw [setIntegral_const,measureReal_def,Measure.addHaar_ball volume 0 hR,ENNReal.toReal_mul,
    finrank_euclideanSpace_fin,ENNReal.toReal_ofReal (pow_nonneg hR _),hr]
  dsimp only [measureReal_def,smul_eq_mul]
  ring

theorem normal_ball_axis_characteristic (d : ℕ) (a : ℝ) :
    let V := (volume (ball (0:NormalBall (d+1+1)) 1)).toReal⁻¹ * (volume.real (ball (0:NormalBall (d+1)) 1))
    (normalShellCharacteristic (EuclideanSpace.single (0:Fin (d+1+1)) a)).re = V*normalBallCosine (((d+1:ℕ):ℝ)/2) a := by
  dsimp only
  rw [normal_shell_axis_cosine]
  unfold wilsonBallMeasure ProbabilityTheory.cond
  rw [integral_smul_measure,ENNReal.toReal_inv,normal_ball_axis_cosine_formula,smul_eq_mul,mul_assoc]

/-- The full dimension-dependent mark estimate from the manuscript.
It applies also to even shell dimensions, with a half-integral
decay exponent. No readout direction is privileged. -/
theorem normal_shell_characteristic_sharp (ι : Type*) [Fintype ι] (hn : 2 ≤ Fintype.card ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : WilsonBallSpace ι, ‖normalShellCharacteristic p‖ ≤ C / (1+‖p‖)^(((Fintype.card ι:ℝ)+1)/2) := by
  let d := Fintype.card ι-2
  have hdim : Fintype.card ι = d+1+1 := by dsimp [d]; omega
  let e : WilsonBallSpace ι ≃ₗᵢ[ℝ] NormalBall (d+1+1) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hdim))
  let α := ((d+1:ℕ):ℝ)/2
  let β := α+1
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have hdim' : ((Fintype.card ι:ℝ)+1)/2 = β := by
    rw [hdim]; dsimp [β,α]; push_cast; ring
  obtain ⟨C,hC,hdec⟩ := normal_ball_cosine_decay hα
  let V := (volume (ball (0:NormalBall (d+1+1)) 1)).toReal⁻¹ * (volume.real (ball (0:NormalBall (d+1)) 1))
  have hV : 0 ≤ V := by dsimp [V]; positivity
  let A := V*C
  have hA : 0 ≤ A := mul_nonneg hV hC.le
  have hTwo : 0 < (2:ℝ)^β := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨(2:ℝ)^β*(1+A),by positivity,fun p => ?_⟩
  rw [hdim']
  let a := ‖p‖
  have ha : 0 ≤ a := norm_nonneg _
  have h1 : 0 < (1+a)^β := Real.rpow_pos_of_pos (by positivity) _
  by_cases h : 1 ≤ a
  · let q := EuclideanSpace.single (0:Fin (d+1+1)) a
    have he : ‖e p‖ = ‖q‖ := by simp [q,a,EuclideanSpace.norm_single]
    rw [←normal_shell_characteristic_isometry e p,normal_shell_characteristic_radial he]
    have hval : ‖normalShellCharacteristic q‖ ≤ A/a^β := by
      rw [←normal_shell_characteristic_real q,Complex.norm_real,Real.norm_eq_abs,normal_ball_axis_characteristic,abs_mul,abs_of_nonneg hV]
      exact (mul_le_mul_of_nonneg_left (hdec a h) hV).trans_eq (by dsimp only [β,A]; ring)
    apply hval.trans
    change A/a^β ≤ 2^β*(1+A)/(1+a)^β
    rw [div_le_div_iff₀ (Real.rpow_pos_of_pos (by linarith) _) h1]
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ 1+a) (show 1+a ≤ 2*a by linarith) hβ
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) ha] at hpow
    calc A*(1+a)^β ≤ A*(2^β*a^β) := mul_le_mul_of_nonneg_left hpow hA
         _ ≤ 2^β*(1+A)*a^β := by nlinarith [mul_pos hTwo (Real.rpow_pos_of_pos (by linarith : 0<a) β)]
  · apply (normal_shell_characteristic_le_one p).trans
    change 1 ≤ 2^β*(1+A)/(1+a)^β
    rw [le_div_iff₀ h1,one_mul]
    exact (Real.rpow_le_rpow (by positivity) (by linarith : 1+a ≤ 2) hβ).trans
      (le_mul_of_one_le_right hTwo.le (by linarith))

theorem normal_shell_pair_sharp (ι : Type*) [Fintype ι] (hn : 2 ≤ Fintype.card ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : WilsonBallSpace ι, ‖normalShellCharacteristic p‖^2 ≤ C / (1+‖p‖)^(Fintype.card ι+1) := by
  obtain ⟨C,hC,h⟩ := normal_shell_characteristic_sharp ι hn
  refine ⟨C^2,sq_pos_of_pos hC,fun p => (pow_le_pow_left₀ (norm_nonneg _) (h p) 2).trans_eq ?_⟩
  rw [div_pow,←Real.rpow_mul_natCast (by positivity)]
  congr 1
  rw [show (((Fintype.card ι:ℝ)+1)/2)*(2:ℕ)=(Fintype.card ι+1:ℕ) by push_cast; ring, Real.rpow_natCast]

end UV
