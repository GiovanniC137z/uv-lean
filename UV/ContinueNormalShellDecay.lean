import UV.ContinueNormalBallSlice

/-! Decay of the normalized A4 ball characteristic in every shell
dimension at least three. Slicing down to a two-dimensional disk gives
inverse-square decay of the amplitude, sufficient for rank-three sewing. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set Metric
open scoped RealInnerProductSpace ENNReal

namespace UV

def normalBallAxis : (d : ℕ) → Fin (d+3)
  | 0 => 0
  | d+1 => (normalBallAxis d).succ

def normalBallWave {n : ℕ} (j : Fin n) (a : ℝ) (y : NormalBall n) : ℂ :=
  Complex.exp ((Complex.I*(a:ℂ))*(y j:ℂ))

theorem normal_ball_wave_continuous {n : ℕ} (j : Fin n) (a : ℝ) : Continuous (normalBallWave j a) := by
  change Continuous (fun x : NormalBall n => Complex.exp ((Complex.I*(a:ℂ))*(x j:ℂ)))
  fun_prop

/-- The unnormalized three-ball integral, including the actual disk
volume π(R²−t²) at each slice. -/
theorem normal_three_ball_integral {R : ℝ} (hR : 0 ≤ R) (a : ℝ) :
    (∫ y in ball (0 : NormalBall 3) R, normalBallWave 0 a y) =
      (Real.pi:ℂ) * ∫ t in Ioo (-R) R, (((R:ℂ)^2-(t:ℂ)^2)*Complex.exp ((Complex.I*(a:ℂ))*(t:ℂ))) := by
  rw [normal_ball_slice hR _ (normal_ball_wave_continuous _ a),←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have hsq : 0 ≤ R^2-t^2 := by nlinarith [mul_pos (sub_pos.mpr ht.2) (by linarith [ht.1] : 0 < R+t)]
  change (∫ _ : NormalBall 2 in ball 0 (Real.sqrt (R^2-t^2)), Complex.exp ((Complex.I*(a:ℂ))*(t:ℂ))) = _
  rw [setIntegral_const]
  simp only [measureReal_def,EuclideanSpace.volume_ball_fin_two,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _),ENNReal.toReal_ofReal Real.pi_nonneg,Real.sq_sqrt hsq,Complex.real_smul]
  push_cast
  ring

/-- Extra normal directions can be integrated one at a time. The
estimate is uniform in every slice radius between zero and one. -/
theorem normal_ball_axis_decay (d : ℕ) {R a : ℝ} (hR : 0 ≤ R) (hR' : R ≤ 1) (ha : 1 ≤ a) :
    ‖∫ y in ball (0 : NormalBall (d+3)) R, normalBallWave (normalBallAxis d) a y‖ ≤
      ((2:ℝ)^d * (8*Real.pi))/(a^2) := by
  induction d generalizing R with
  | zero =>
    rw [normalBallAxis,normal_three_ball_integral hR,norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_nonneg]
    apply (mul_le_mul_of_nonneg_left (normal_parabolic_fourier_bound hR hR' ha) Real.pi_nonneg).trans_eq
    ring
  | succ d ih =>
    rw [normal_ball_slice hR _ (normal_ball_wave_continuous _ a)]
    let F := fun t : ℝ => ∫ y in ball (0 : NormalBall (d+3)) (Real.sqrt (R^2-t^2)), normalBallWave (normalBallAxis d) a y
    let B := ((2:ℝ)^d*(8*Real.pi))/(a^2)
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

def normalShellCharacteristic {ι : Type*} [Fintype ι] (p : WilsonBallSpace ι) : ℂ :=
  ∫ y, Complex.exp (Complex.I*(⟪p,y⟫:ℝ)) ∂wilsonBallMeasure ι

theorem normal_shell_characteristic_le_one {ι : Type*} [Fintype ι] (p : WilsonBallSpace ι) :
    ‖normalShellCharacteristic p‖ ≤ 1 := by
  apply (norm_integral_le_integral_norm _).trans_eq
  simp [Complex.norm_exp,Complex.mul_re]

/-- All finite-dimensional shell coordinates of the same norm give the
same characteristic function, including after changing orthonormal frame. -/
theorem normal_shell_characteristic_isometry {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : WilsonBallSpace ι ≃ₗᵢ[ℝ] WilsonBallSpace κ) (p : WilsonBallSpace ι) :
    normalShellCharacteristic (e p) = normalShellCharacteristic p := by
  have hp : e ⁻¹' (ball 0 1 : Set (WilsonBallSpace κ)) = ball 0 1 := by ext; simp
  have hm := e.measurePreserving.restrict_preimage (s := ball 0 1) measurableSet_ball
  rw [hp] at hm
  have hv : volume (ball (0:WilsonBallSpace ι) 1) = volume (ball (0:WilsonBallSpace κ) 1) := by
    rw [←hp,e.measurePreserving.measure_preimage measurableSet_ball.nullMeasurableSet]
  unfold normalShellCharacteristic wilsonBallMeasure ProbabilityTheory.cond
  rw [integral_smul_measure,integral_smul_measure,hv,←hm.integral_comp e.toHomeomorph.measurableEmbedding]
  simp only [e.inner_map_map]

theorem normal_shell_characteristic_radial {ι : Type*} [Fintype ι] {p q : WilsonBallSpace ι} (h : ‖p‖=‖q‖) :
    normalShellCharacteristic p = normalShellCharacteristic q := by
  let e := (ℝ ∙ (p-q))ᗮ.reflection
  have he : e p = q := Submodule.reflection_sub h
  simpa only [he] using (normal_shell_characteristic_isometry e p).symm

/-- Actual squared-amplitude damping is at least fourth order in the
shell argument. This weaker power than the optimal Bessel asymptotic
already suffices when three carrier directions are observed. -/
theorem normal_shell_characteristic_decay (ι : Type*) [Fintype ι] (hn : 3 ≤ Fintype.card ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : WilsonBallSpace ι, ‖normalShellCharacteristic p‖ ≤ C / (1+‖p‖)^2 := by
  let d := Fintype.card ι-3
  have hdim : Fintype.card ι = d+3 := by dsimp [d]; omega
  let e : WilsonBallSpace ι ≃ₗᵢ[ℝ] NormalBall (d+3) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hdim))
  let j := normalBallAxis d
  let A := (volume (ball (0:NormalBall (d+3)) 1)).toReal⁻¹ * ((2:ℝ)^d*(8*Real.pi))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨4*(1+A),by positivity,fun p => ?_⟩
  let a := ‖p‖
  have ha : 0 ≤ a := norm_nonneg p
  by_cases h : 1 ≤ a
  · let q := EuclideanSpace.single j a
    have he : ‖e p‖ = ‖q‖ := by simp [q,a,EuclideanSpace.norm_single]
    have hw (x : NormalBall (d+3)) : Complex.exp (Complex.I*(⟪q,x⟫:ℝ)) = normalBallWave j a x := by
      simp [q,EuclideanSpace.inner_single_left,normalBallWave,mul_assoc]
    have hbound : ‖normalShellCharacteristic q‖ ≤ A/a^2 := by
      unfold normalShellCharacteristic wilsonBallMeasure ProbabilityTheory.cond
      simp_rw [hw]
      rw [integral_smul_measure,norm_smul,ENNReal.toReal_inv,Real.norm_of_nonneg (by positivity)]
      apply (mul_le_mul_of_nonneg_left (normal_ball_axis_decay d (R := 1) zero_le_one le_rfl h) (by positivity)).trans_eq
      dsimp [A]; ring
    rw [←normal_shell_characteristic_isometry e p,normal_shell_characteristic_radial he]
    apply hbound.trans
    change A/a^2 ≤ 4*(1+A)/(1+a)^2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h4 : (1+a)^2 ≤ 4*a^2 := by nlinarith [sq_nonneg (a-1)]
    nlinarith [mul_le_mul_of_nonneg_left h4 hA,sq_nonneg a]
  · apply (normal_shell_characteristic_le_one p).trans
    change 1 ≤ 4*(1+A)/(1+a)^2
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg a,mul_nonneg ha (by linarith : 0 ≤ 1-a)]

end UV
