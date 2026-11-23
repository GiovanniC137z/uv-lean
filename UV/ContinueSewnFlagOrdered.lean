import UV.ContinueNetworkOrdered
import UV.ContinueSewnFlagMoments
import UV.ContinueSewnFlagProjection

/-! Joint moment control on the literal ordered Schwinger simplex.
The phase enters through projections of the same displacement in the
four intrinsic sector-plane coordinates. -/

noncomputable section
open MeasureTheory Filter Real Set Matrix
open scoped ENNReal BigOperators Matrix
namespace UV.SewnFlags

theorem ordered_joint_flag_moments {n : ℕ} {D : Type*} [MeasurableSpace D]
    (μ : Measure D) (a c : Fin n → ℝ) (x : Fin n → D → ℝ)
    (hc : ∀ i, 0 < c i) (hx : ∀ i d, 0 ≤ x i d) (hxm : ∀ i, Measurable (x i))
    (hJoint : (∫⁻ d, ∏ i, displacementCost (directionalOrderedPrefix a i) (x i d) ∂μ) < ⊤) :
    (∫⁻ d, directionalWeightedSector a
      (fun i r => ENNReal.ofReal (exp (-(c i*(x i d)^2)/r))) ∂μ) < ⊤ := by
  have h := joint_displacement_ratios μ (directionalOrderedPrefix a) c x hc hx hxm hJoint
  refine (lt_of_eq_of_lt ?_ h)
  apply lintegral_congr
  intro d
  rw [directionalWeightedSector_eq_prefix_product _ _ (fun _ => by fun_prop)]
  rw [UV.network_lintegral_fintype_prod _ (fun i r =>
    ENNReal.ofReal (ratioHeat (directionalOrderedPrefix a i) (c i*(x i d)^2) r))
    (fun _ => by unfold ratioHeat; fun_prop)]
  apply Finset.prod_congr rfl
  intro i _
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro r hr
  change ENNReal.ofReal (r^(directionalOrderedPrefix a i-1)) *
      ENNReal.ofReal (exp (-(c i*(x i d)^2)/r)) =
    ENNReal.ofReal (ratioHeat (directionalOrderedPrefix a i) (c i*(x i d)^2) r)
  rw [← ENNReal.ofReal_mul (rpow_nonneg hr.1.le _)]
  rfl

def projectedDisplacement {E : Type*} [Fintype E] {L : ℕ}
    (C : Matrix E (Fin L) ℝ) (S : Finset E) (d : EuclideanSpace ℝ (Fin L × Fin 4)) :=
  sqrt (∑ ν : Fin 4, ‖(routingFace C S).starProjection (WithLp.toLp 2 (fun j => d (j,ν)))‖^2)

theorem projectedDisplacement_nonneg {E : Type*} [Fintype E] {L : ℕ}
    (C : Matrix E (Fin L) ℝ) (S : Finset E) (d : EuclideanSpace ℝ (Fin L × Fin 4)) :
    0 ≤ projectedDisplacement C S d := sqrt_nonneg _

theorem projectedDisplacement_measurable {E : Type*} [Fintype E] {L : ℕ}
    (C : Matrix E (Fin L) ℝ) (S : Finset E) :
    Measurable (projectedDisplacement C S) := by
  apply Continuous.measurable
  unfold projectedDisplacement
  apply Continuous.sqrt
  apply continuous_finset_sum _ (fun ν _ => Continuous.pow (Continuous.norm ?_) 2)
  apply ((routingFace C S).starProjection.continuous).comp
  exact PiLp.continuous_toLp 2 _ |>.comp (continuous_pi fun j => PiLp.continuous_apply 2 _ (j,ν))

def routedInverseWeight {E : Type*} [Fintype E] {L : ℕ}
    (C : Matrix E (Fin L) ℝ) (t : E → ℝ) (d : EuclideanSpace ℝ (Fin L × Fin 4)) :=
  ∑ ν : Fin 4, (fun j => d (j,ν)) ⬝ᵥ ((residualGram C t)⁻¹ *ᵥ (fun j => d (j,ν)))

def flagRatioCoefficient {E : Type*} [Fintype E] {L : ℕ}
    (C : Matrix E (Fin L) ℝ) (S : Finset E) (n : ℕ) :=
  (4*((n:ℝ)+1)*routingFaceConstant C S)⁻¹

theorem flagRatioCoefficient_pos {E : Type*} [Fintype E] {L : ℕ}
    (C : Matrix E (Fin L) ℝ) (S : Finset E) (n : ℕ) :
    0 < flagRatioCoefficient C S n := by
  have := routingFaceConstant_pos C S
  unfold flagRatioCoefficient
  positivity

/-- Allocate the Gaussian inverse form over the finite set of prefixes
without introducing independent copies of the displacement. -/
theorem ordered_routed_inverse_weight {n : ℕ} {E : Type*} [Fintype E] {L : ℕ}
    (C : Matrix E (Fin L) ℝ) (S : Fin n → Finset E) (t : E → ℝ) (u : Fin n → ℝ)
    (hu : u ∈ directionalOrderedSet n) (ht : ∀ e, 0 ≤ t e)
    (hS : ∀ i e, e ∈ S i → t e ≤ u i)
    (hM : (residualGram C t).PosDef) (d : EuclideanSpace ℝ (Fin L × Fin 4)) :
    exp (-(routedInverseWeight C t d)/4) ≤
      ∏ i, exp (-(flagRatioCoefficient C (S i) n * projectedDisplacement C (S i) d ^ 2)
        / directionalOrderedRatios u i) := by
  let q := routedInverseWeight C t d
  let r := directionalOrderedRatios u
  have hq : 0 ≤ q := by
    unfold q routedInverseWeight
    apply Finset.sum_nonneg
    intro ν _
    let D := fun j => d (j,ν)
    let z := (residualGram C t)⁻¹ *ᵥ D
    have hz : residualGram C t *ᵥ z = D := by
      dsimp [z]
      rw [mulVec_mulVec,mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM.det_pos.ne'),one_mulVec]
    calc 0 ≤ z ⬝ᵥ (residualGram C t *ᵥ z) := by
          rw [residualGram_scalar_identity]
          exact Finset.sum_nonneg fun e _ => mul_nonneg (ht e) (sq_nonneg _)
    _ = D ⬝ᵥ z := by rw [hz,dotProduct_comm]
  have hscale (i : Fin n) :
      flagRatioCoefficient C (S i) n * projectedDisplacement C (S i) d ^ 2 / r i ≤ q/(4*((n:ℝ)+1)) := by
    have hUi : 0 < u i := ((directionalOrderedSet_mem_iff u).1 hu).2 i |>.1
    let A := routingFaceConstant C (S i)
    let x := projectedDisplacement C (S i) d
    have hA : 0 < A := routingFaceConstant_pos C (S i)
    have h := routing_face_four_coordinate_bound C (S i) t hUi ht (hS i) hM d
    have hx : x^2 = _ := sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hn : x^2 / (r i*A) ≤ q := by
      calc
        _ ≤ x^2/(u i*A) := div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hUi hA)
          (mul_le_mul_of_nonneg_right (directionalOrderedRatios_ge_time hu i) hA.le)
        _ ≤ _ := by rw [hx]; exact h
    change (4*((n:ℝ)+1)*A)⁻¹*x^2/r i ≤ _
    rw [show (4*((n:ℝ)+1)*A)⁻¹*x^2/r i = (x^2/(r i*A))/(4*((n:ℝ)+1)) by
      simp only [div_eq_mul_inv,mul_inv]
      ring]
    exact div_le_div_of_nonneg_right hn (by positivity)
  rw [← exp_sum,exp_le_exp]
  simp only [neg_div,Finset.sum_neg_distrib]
  apply neg_le_neg
  calc
    _ ≤ ∑ _ : Fin n, q/(4*((n:ℝ)+1)) := by
      exact Finset.sum_le_sum (fun i _ => hscale i)
    _ ≤ q/4 := by
      simp [div_mul_eq_div_div,nsmul_eq_mul]
      have hn : 0 < (n:ℝ)+1 := by positivity
      field_simp [hn.ne']
      nlinarith

end UV.SewnFlags
