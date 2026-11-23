import UV.ContinueNormalLegProfile
import UV.ContinueNormalAllLegsSpin
import Mathlib.Analysis.PSeries

/-! Summable majorants for the actual four form factors in the
zero-transfer transverse Hessian. The normal modes are discrete and the
four-dimensional carrier momentum is integrated over the entire plane. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter UV.SectorPlane
open scoped RealInnerProductSpace

namespace UV

variable {ι : Type*} [Fintype ι]

def normalLegFrequency (L θ : ℝ) (j : ℤ) := (2*Real.pi*(j:ℝ)+θ)/L

def normalLegForm (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ) (p : OSFourSpace) : ℝ :=
  (normalShellCharacteristic (L • T (normalBallJoin ξ p))).re

theorem normal_leg_form_continuous (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ) :
    Continuous (normalLegForm L T ξ) := by
  unfold normalLegForm
  apply Complex.continuous_re.comp (normal_shell_characteristic_continuous.comp ?_)
  apply Continuous.const_smul
  apply T.continuous.comp
  unfold normalBallJoin
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_const
  · exact (continuous_apply j).comp (PiLp.continuous_ofLp 2 (fun _ : Fin 4 => ℝ))

theorem normal_leg_form_radial (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    {p q : OSFourSpace} (h : ‖p‖=‖q‖) : normalLegForm L T ξ p = normalLegForm L T ξ q := by
  apply congrArg Complex.re (normal_shell_characteristic_radial ?_)
  simp only [norm_smul,T.norm_map]
  congr 1
  have he := normal_ball_join_norm ξ p
  rw [h] at he
  nlinarith [normal_ball_join_norm ξ q,norm_nonneg (normalBallJoin ξ q),norm_nonneg (normalBallJoin ξ p)]

theorem normal_leg_nearest_positive {L : ℝ} (hL : 0 < L) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (θ : ℝ) :
    ∃ j : ℤ, 0 < normalLegForm L T (normalLegFrequency L θ j) 0 := by
  obtain ⟨j,hj⟩ := normal_nearest_holonomy θ
  have hd := T.toLinearMap.finrank_le_finrank_of_injective T.injective
  rw [finrank_euclideanSpace_fin,finrank_euclideanSpace] at hd
  refine ⟨j,normal_shell_positive_pi hd ?_⟩
  have he := normal_ball_join_norm (normalLegFrequency L θ j) (0 : OSFourSpace)
  have ht : ‖normalBallJoin (normalLegFrequency L θ j) (0 : OSFourSpace)‖ = |normalLegFrequency L θ j| := by
    simp only [norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,add_zero] at he
    nlinarith [sq_abs (normalLegFrequency L θ j),abs_nonneg (normalLegFrequency L θ j),norm_nonneg (normalBallJoin (normalLegFrequency L θ j) (0:OSFourSpace))]
  rw [norm_smul,T.norm_map,Real.norm_of_nonneg hL.le,ht,normalLegFrequency,abs_div,abs_of_pos hL]
  calc L*(|2*Real.pi*(j:ℝ)+θ|/L) = |2*Real.pi*(j:ℝ)+θ| := by field_simp
       _ ≤ _ := hj

theorem normal_shifted_frequency_summable {L : ℝ} (hL : 0 < L) (θ : ℝ) :
    Summable (fun j : ℤ => normalPhotonWeight 2 (normalLegFrequency L θ j)) := by
  have hs : Summable (fun j : ℤ => ((1+|(j:ℝ)|)^2)⁻¹) := by
    have hn := (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
    have hh := (summable_nat_add_iff 1).mpr hn
    apply summable_int_iff_summable_nat_and_neg.mpr
    constructor <;> simpa [Nat.cast_add,abs_of_nonneg,one_div,add_comm] using hh
  let A := L/(2*Real.pi)
  let B := |θ|/(2*Real.pi)
  let C := 1+A+B
  have ha : 0 < A := by dsimp [A]; positivity
  have hb : 0 ≤ B := by dsimp [B]; positivity
  have hc : 0 < C := by dsimp [C]; positivity
  apply Summable.of_nonneg_of_le (fun j => by dsimp [normalPhotonWeight]; positivity) _ (hs.mul_left (C^2))
  intro j
  let ξ := normalLegFrequency L θ j
  have he : (j:ℝ) = A*ξ-θ/(2*Real.pi) := by dsimp [A,ξ,normalLegFrequency]; field_simp; ring
  have hj : |(j:ℝ)| ≤ A*|ξ|+B := by
    calc |(j:ℝ)| = |A*ξ-θ/(2*Real.pi)| := congrArg abs he
         _ ≤ |A*ξ|+|θ/(2*Real.pi)| := abs_sub _ _
         _ = _ := by simp [abs_mul,abs_div,abs_of_pos ha,abs_of_pos Real.pi_pos,B]
  have hle : 1+|(j:ℝ)| ≤ C*(1+|ξ|) := by dsimp [C]; nlinarith [abs_nonneg ξ,mul_nonneg hb (abs_nonneg ξ)]
  change ((1+|ξ|)^2)⁻¹ ≤ C^2*((1+|(j:ℝ)|)^2)⁻¹
  rw [←one_div,←div_eq_mul_inv,div_le_div_iff₀ (by positivity) (by positivity),one_mul,←mul_pow]
  exact pow_le_pow_left₀ (by positivity) hle 2

/-- The four vertex form factors yield six powers in carrier momentum
and two summable powers in the independently shifted normal frequency. -/
theorem normal_leg_fourth_power {L : ℝ} (hL : 0 < L) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ξ : ℝ) (p : OSFourSpace), normalLegForm L T ξ p ^ 4 ≤
      C * normalPhotonWeight 6 p * normalPhotonWeight 2 ξ := by
  have hd := T.toLinearMap.finrank_le_finrank_of_injective T.injective
  rw [finrank_euclideanSpace_fin,finrank_euclideanSpace] at hd
  obtain ⟨B,hB,hh⟩ := normal_shell_characteristic_decay ι (by omega)
  let D := 1+L⁻¹
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨B^4*D^8,by positivity,fun ξ p => ?_⟩
  let P := normalBallJoin ξ p
  let X := 1+L*‖P‖
  have hX : 0 < X := by dsimp [X]; positivity
  have hs := normal_ball_join_norm ξ p
  have hp : ‖p‖ ≤ ‖P‖ := by dsimp [P]; nlinarith [norm_nonneg p,norm_nonneg (normalBallJoin ξ p),sq_nonneg ξ]
  have hξ : |ξ| ≤ ‖P‖ := by dsimp [P]; nlinarith [sq_abs ξ,abs_nonneg ξ,norm_nonneg (normalBallJoin ξ p),sq_nonneg ‖p‖]
  have hscale : 1+‖P‖ ≤ D*X := by
    dsimp [D,X]
    have he : L⁻¹*(L*‖P‖) = ‖P‖ := by rw [←mul_assoc,inv_mul_cancel₀ hL.ne',one_mul]
    nlinarith [inv_nonneg.mpr hL.le,mul_nonneg hL.le (norm_nonneg P)]
  have h1 := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖p‖) ((add_le_add_left hp 1).trans hscale) 6
  have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|ξ|) ((add_le_add_left hξ 1).trans hscale) 2
  have hc := hh (L • T P)
  rw [norm_smul,T.norm_map,Real.norm_of_nonneg hL.le] at hc
  have hval : |normalLegForm L T ξ p| ≤ B/X^2 := (Complex.abs_re_le_norm _).trans hc
  have hp4 := pow_le_pow_left₀ (abs_nonneg _) hval 4
  rw [show |normalLegForm L T ξ p|^4 = normalLegForm L T ξ p^4 by rw [show 4=2*2 by decide,pow_mul,pow_mul,sq_abs],div_pow,←pow_mul] at hp4
  let S := (1+‖p‖)^6*(1+|ξ|)^2
  have hS : 0 < S := by dsimp [S]; positivity
  have hw : S ≤ D^8*X^8 := by
    refine (mul_le_mul h1 h2 (by positivity) (by positivity)).trans_eq ?_
    ring
  have hbound : B^4/X^8 ≤ B^4*D^8/S := by
    rw [div_le_div_iff₀ (by positivity) hS]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ B^4)
  apply hp4.trans (hbound.trans_eq ?_)
  simp only [S,normalPhotonWeight,Real.norm_eq_abs,div_eq_mul_inv,mul_inv_rev]
  ring

end UV
