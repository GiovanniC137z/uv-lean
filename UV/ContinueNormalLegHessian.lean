import UV.ContinueNormalLegMoments

/-! The zero-transfer transverse loop with the specified three shell
compressions, including all shifted circle modes. The readout is an
isometry of the five-dimensional carrier-plus-normal momentum. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set UV.SectorPlane
open scoped RealInnerProductSpace

namespace UV

variable {ι : Type*} [Fintype ι]

def normalLegWeight (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ s : ℝ) : ℝ :=
  normalLegForm L T ξ (EuclideanSpace.single (0 : Fin 4) (Real.sqrt s))^4 / (m^2+max s 0+ξ^2)^2

theorem normal_leg_weight_continuous {m : ℝ} (hm : 0 < m) (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ) :
    Continuous (normalLegWeight m L T ξ) := by
  unfold normalLegWeight
  apply Continuous.div₀
  · apply Continuous.pow
    apply (normal_leg_form_continuous L T ξ).comp
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).comp
    apply continuous_pi
    intro j
    by_cases hj : j = 0
    · subst j; simpa only [Pi.single_eq_same] using Real.continuous_sqrt
    · simpa only [Pi.single_eq_of_ne hj] using (continuous_const : Continuous (fun _ : ℝ => (0:ℝ)))
  · fun_prop
  · intro s
    positivity

theorem normal_leg_weight_value (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ) (p : OSFourSpace) :
    normalLegWeight m L T ξ (‖p‖^2) = normalLegForm L T ξ p^4 / normalFiveDenom m p ξ^2 := by
  have he : ‖EuclideanSpace.single (0 : Fin 4) (Real.sqrt (‖p‖^2))‖ = ‖p‖ := by
    simp [EuclideanSpace.norm_single]
  simp only [normalLegWeight,normal_leg_form_radial L T ξ he,max_eq_left (sq_nonneg _),normalFiveDenom]

def normalLegHessian (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ) (i : Fin 4) (p : OSFourSpace) : ℝ :=
  let S := normalDiracFrequency m p ξ
  let V := (Complex.I*((normalLegForm L T ξ p:ℝ):ℂ)^2) • diracSlash (osAxis i).val
  ((S*V)*(S*V)).trace.re

theorem normal_leg_hessian_value (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ) (i : Fin 4) (p : OSFourSpace) :
    normalLegHessian m L T ξ i p = -(4*(normalFiveDenom m p ξ-2*(p i)^2)*normalLegWeight m L T ξ (‖p‖^2)) := by
  rw [normalLegHessian,normal_zero_transfer_hessian,normal_leg_weight_value]
  simp only [osAxis,EuclideanSpace.inner_single_left,map_one,one_mul]
  ring

theorem normal_leg_form_modes {L : ℝ} (hL : 0 < L) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (θ : ℝ) :
    let F := fun j : ℤ => fun p => normalLegForm L T (normalLegFrequency L θ j) p^4
    (∀ j, Integrable (F j)) ∧ Summable (fun j => ∫ p, F j p) := by
  let F := fun j : ℤ => fun p => normalLegForm L T (normalLegFrequency L θ j) p^4
  let W := normalPhotonWeight (E := OSFourSpace) 6
  have hi : Integrable W := normal_photon_weight_integrable volume (by rw [finrank_euclideanSpace_fin]; decide)
  obtain ⟨C,hC,hb⟩ := normal_leg_fourth_power hL T
  let b := fun j => normalPhotonWeight 2 (normalLegFrequency L θ j)
  have hle (j p) : F j p ≤ (C*b j)*W p := by
    simpa only [F,b,W,mul_right_comm] using hb (normalLegFrequency L θ j) p
  have hf j : Integrable (F j) := (hi.const_mul (C*b j)).mono' ((normal_leg_form_continuous L T _).pow 4).aestronglyMeasurable
    (Eventually.of_forall fun p => by rw [Real.norm_of_nonneg (by dsimp [F]; positivity)]; exact hle j p)
  refine ⟨hf,?_⟩
  change Summable (fun j => ∫ p, F j p)
  apply Summable.of_nonneg_of_le (fun j => integral_nonneg fun p => by dsimp [F]; positivity) _ ((normal_shifted_frequency_summable hL θ).mul_left (C*∫ p, W p))
  intro j
  have h := integral_mono (hf j) (hi.const_mul (C*b j)) (hle j)
  rw [integral_const_mul] at h
  exact h.trans_eq (by dsimp only [b]; ring)

theorem normal_leg_weight_estimates {m : ℝ} (hm : 0 < m) (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (p : OSFourSpace) (i : Fin 4) :
    let f := normalLegForm L T ξ p^4
    let g := normalLegWeight m L T ξ (‖p‖^2)
    0 ≤ g ∧ g ≤ f/(m^2)^2 ∧ ‖p‖^2*g ≤ f/m^2 ∧ |normalLegHessian m L T ξ i p| ≤ (4/m^2)*f := by
  let D := normalFiveDenom m p ξ
  let f := normalLegForm L T ξ p^4
  have hD : 0 < D := by dsimp [D,normalFiveDenom]; positivity
  have hmD : m^2 ≤ D := by dsimp [D,normalFiveDenom]; nlinarith [sq_nonneg ‖p‖,sq_nonneg ξ]
  have hpD : ‖p‖^2 ≤ D := by dsimp [D,normalFiveDenom]; nlinarith [sq_nonneg m,sq_nonneg ξ]
  have hiD : (p i)^2 ≤ D := by
    have hh := PiLp.norm_apply_le p i
    rw [Real.norm_eq_abs] at hh
    exact (by nlinarith [sq_abs (p i),abs_nonneg (p i),norm_nonneg p] : (p i)^2 ≤ ‖p‖^2).trans hpD
  have hf : 0 ≤ f := by dsimp [f]; positivity
  have he : |D-2*(p i)^2| ≤ D := abs_le.mpr ⟨by linarith,by nlinarith [sq_nonneg (p i)]⟩
  simp only [normal_leg_hessian_value,normal_leg_weight_value,abs_neg,abs_mul]
  change 0 ≤ f/D^2 ∧ f/D^2 ≤ f/(m^2)^2 ∧ ‖p‖^2*(f/D^2) ≤ f/m^2 ∧ |4| * |D-2*(p i)^2| * |f/D^2| ≤ (4/m^2)*f
  have hg : 0 ≤ f/D^2 := by positivity
  have hmid : D*(f/D^2) ≤ f/m^2 := by
    have h : D*(f/D^2) = f/D := by field_simp
    rw [h]; exact div_le_div_of_nonneg_left hf (sq_pos_of_pos hm) hmD
  refine ⟨hg,div_le_div_of_nonneg_left hf (by positivity) (pow_le_pow_left₀ (sq_nonneg m) hmD 2),
    (mul_le_mul_of_nonneg_right hpD hg).trans hmid,?_⟩
  rw [abs_of_nonneg hg,abs_of_pos (by norm_num : (0:ℝ)<4),mul_assoc]
  exact (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right he hg).trans hmid) (by norm_num : (0:ℝ)≤4)).trans_eq (by ring)

theorem normal_leg_radial_integrability {m : ℝ} (hm : 0 < m) (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (hf : Integrable (fun p => normalLegForm L T ξ p^4)) :
    let g := normalLegWeight m L T ξ
    Integrable (fun p : OSFourSpace => g (‖p‖^2)) ∧ Integrable (fun p : OSFourSpace => ‖p‖^2*g (‖p‖^2)) := by
  let g := normalLegWeight m L T ξ
  have hc : Continuous (fun p : OSFourSpace => g (‖p‖^2)) := (normal_leg_weight_continuous hm L T ξ).comp (continuous_norm.pow 2)
  have he (p : OSFourSpace) := normal_leg_weight_estimates hm L T ξ p 0
  constructor
  · refine (hf.div_const ((m^2)^2)).mono' hc.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [Real.norm_of_nonneg (he p).1]; exact (he p).2.1
  · refine (hf.div_const (m^2)).mono' (((continuous_norm.pow 2).mul hc).aestronglyMeasurable) (Eventually.of_forall fun p => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (he p).1)]; exact (he p).2.2.1

theorem normal_leg_hessian_mode_integral {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (θ : ℝ) (j : ℤ) (i : Fin 4) :
    let ξ := normalLegFrequency L θ j
    (∫ p, normalLegHessian m L T ξ i p) =
      -(∫ p : OSFourSpace, 4*normalLegForm L T ξ p^4*(m^2+ξ^2+‖p‖^2/2)/(normalFiveDenom m p ξ)^2) := by
  let ξ := normalLegFrequency L θ j
  obtain ⟨h0,h2⟩ := normal_leg_radial_integrability hm L T ξ ((normal_leg_form_modes hL T θ).1 j)
  dsimp only
  simp_rw [normal_leg_hessian_value]
  rw [normal_zero_transfer_radial m ξ i (normal_leg_weight_continuous hm L T ξ).measurable h0 h2]
  congr 1
  apply integral_congr_ae (Eventually.of_forall fun p => ?_)
  rw [normal_leg_weight_value]; ring

/-- Every mode is included in the absolute integral at zero transfer.
The radial real Hessian is strictly negative after the mode sum. -/
theorem normal_leg_hessian_zero {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (θ : ℝ) (i : Fin 4) :
    let H := fun j : ℤ => normalLegHessian m L T (normalLegFrequency L θ j) i
    (∀ j, Integrable (H j)) ∧ Summable (fun j => ∫ p, ‖H j p‖) ∧ (∑' j, ∫ p, H j p) < 0 := by
  let ξ := normalLegFrequency L θ
  let H := fun j => normalLegHessian m L T (ξ j) i
  let g := fun j => normalLegWeight m L T (ξ j)
  have hc (j) : Continuous (fun p : OSFourSpace => g j (‖p‖^2)) := (normal_leg_weight_continuous hm L T _).comp (continuous_norm.pow 2)
  have hHc (j) : Continuous (H j) := by
    change Continuous (fun p => normalLegHessian m L T (ξ j) i p)
    simp_rw [normal_leg_hessian_value]
    apply Continuous.neg
    apply Continuous.mul _ (hc j)
    unfold normalFiveDenom
    fun_prop
  obtain ⟨hf,hfS⟩ := normal_leg_form_modes hL T θ
  have est (j p) := normal_leg_weight_estimates hm L T (ξ j) p i
  have hi (j) : Integrable (H j) := ((hf j).const_mul (4/m^2)).mono' (hHc j).aestronglyMeasurable
    (Eventually.of_forall fun p => (est j p).2.2.2)
  have hs : Summable (fun j => ∫ p, ‖H j p‖) := by
    apply Summable.of_nonneg_of_le (fun j => integral_nonneg fun _ => norm_nonneg _) _ (hfS.mul_left (4/m^2))
    intro j
    exact (integral_mono (hi j).norm ((hf j).const_mul (4/m^2)) (fun p => (est j p).2.2.2)).trans_eq (integral_const_mul ..)
  have hr (j) := normal_leg_radial_integrability hm L T (ξ j) (hf j)
  have h0 (j) := (hr j).1
  have h2 (j) := (hr j).2
  have hsgn (j) : (∫ p, H j p) ≤ 0 := by
    simp_rw [H,normal_leg_hessian_value]
    rw [normal_zero_transfer_radial m (ξ j) i (normal_leg_weight_continuous hm L T _).measurable (h0 j) (h2 j),neg_nonpos]
    exact integral_nonneg fun p => mul_nonneg (by positivity) (est j p).1
  obtain ⟨j,hpos⟩ := normal_leg_nearest_positive hL T θ
  have hsup : 0 < volume (Function.support (fun p : OSFourSpace => g j (‖p‖^2))) := by
    apply (hc j).isOpen_support.measure_pos volume
    refine ⟨0,?_⟩
    change normalLegWeight m L T (ξ j) (‖(0:OSFourSpace)‖^2) ≠ 0
    rw [normal_leg_weight_value]
    apply ne_of_gt
    have hd : 0 < normalFiveDenom m 0 (ξ j) := by dsimp [normalFiveDenom]; positivity
    exact div_pos (pow_pos hpos _) (sq_pos_of_pos hd)
  have hj : (∫ p, H j p) < 0 := by
    simp_rw [H,normal_leg_hessian_value]
    exact normal_zero_transfer_negative hm (ξ j) i (normal_leg_weight_continuous hm L T _).measurable (h0 j) (h2 j) (fun p => (est j p).1) hsup
  have hsum : Summable (fun j => ∫ p, H j p) := hs.of_norm_bounded (fun _ => norm_integral_le_integral_norm _)
  refine ⟨hi,hs,?_⟩
  have hn := hsum.neg
  have hstrict := hn.tsum_pos (fun k => neg_nonneg.mpr (hsgn k)) j (neg_pos.mpr hj)
  rwa [tsum_neg,neg_pos] at hstrict

end UV
