import UV.ResidualCoercivity
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The inverse routed precision sees precisely the projection
onto the loop directions orthogonal to all lines outside a face. -/

noncomputable section
open Matrix
open scoped RealInnerProductSpace BigOperators Matrix
namespace UV.SewnFlags

def routingFace {E : Type*} [Fintype E] {L : ℕ} (C : Matrix E (Fin L) ℝ) (S : Finset E) :
    Submodule ℝ (EuclideanSpace ℝ (Fin L)) where
  carrier := {x | ∀ e ∉ S, (C *ᵥ x.ofLp) e = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy e he
    change (C *ᵥ (x.ofLp+y.ofLp)) e = 0
    rw [Matrix.mulVec_add,Pi.add_apply,hx e he,hy e he,add_zero]
  smul_mem' := by
    intro r x hx e he
    change (C *ᵥ (r • x.ofLp)) e = 0
    rw [Matrix.mulVec_smul,Pi.smul_apply,hx e he,smul_zero]

def routingFaceConstant {E : Type*} [Fintype E] {L : ℕ} (C : Matrix E (Fin L) ℝ) (S : Finset E) :=
  1 + ∑ e ∈ S, ‖WithLp.toLp 2 (C e)‖^2

theorem routingFaceConstant_pos {E : Type*} [Fintype E] {L : ℕ}
    (C : Matrix E (Fin L) ℝ) (S : Finset E) : 0 < routingFaceConstant C S :=
  add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun _ _ => sq_nonneg _)

private theorem residualGram_bilinear {E : Type*} [Fintype E] {L : ℕ}
    (C : Matrix E (Fin L) ℝ) (t : E → ℝ) (x y : Fin L → ℝ) :
    x ⬝ᵥ (residualGram C t *ᵥ y) = ∑ e, t e * (C *ᵥ x) e * (C *ᵥ y) e := by
  classical
  unfold residualGram
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro e _
  ring

private theorem routingFace_scale {E : Type*} [Fintype E] {L : ℕ}
    (C : Matrix E (Fin L) ℝ) (S : Finset E) (t : E → ℝ) {T : ℝ} (hT : 0 < T)
    (hS : ∀ e ∈ S, t e ≤ T)
    {w : EuclideanSpace ℝ (Fin L)} (hw : w ∈ routingFace C S) :
    w.ofLp ⬝ᵥ (residualGram C t *ᵥ w.ofLp) ≤ T * routingFaceConstant C S * ‖w‖^2 := by
  classical
  rw [residualGram_scalar_identity, ← Finset.sum_subset (Finset.subset_univ S) (fun e _ he => by
    have hz : (C *ᵥ w.ofLp) e = 0 := hw e he
    simp [hz])]
  calc
    _ ≤ ∑ e ∈ S, T * (‖WithLp.toLp 2 (C e)‖^2 * ‖w‖^2) := by
      apply Finset.sum_le_sum
      intro e he
      have hd : (C *ᵥ w.ofLp) e = ⟪WithLp.toLp 2 (C e),w⟫ := by
        rw [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct_comm]
        rfl
      have ha := abs_real_inner_le_norm (WithLp.toLp 2 (C e)) w
      rw [← hd] at ha
      have h := sq_le_sq₀ (abs_nonneg ((C *ᵥ w.ofLp) e)) (by positivity :
        0 ≤ ‖WithLp.toLp 2 (C e)‖ * ‖w‖) |>.2 ha
      rw [sq_abs,mul_pow] at h
      exact mul_le_mul (hS e he) h (sq_nonneg _) hT.le
    _ ≤ _ := by
      rw [routingFaceConstant,mul_add,mul_one,add_mul,Finset.mul_sum,Finset.sum_mul]
      simp_rw [mul_assoc]
      exact le_add_of_nonneg_left (mul_nonneg hT.le (sq_nonneg _))

private theorem routingGram_cauchy {E : Type*} [Fintype E] {L : ℕ}
    (C : Matrix E (Fin L) ℝ) (t : E → ℝ) (ht : ∀ e, 0 ≤ t e) (x y : Fin L → ℝ) :
    (x ⬝ᵥ (residualGram C t *ᵥ y))^2 ≤ (x ⬝ᵥ (residualGram C t *ᵥ x)) *
      (y ⬝ᵥ (residualGram C t *ᵥ y)) := by
  let a := fun e => Real.sqrt (t e) * (C *ᵥ x) e
  let b := fun e => Real.sqrt (t e) * (C *ᵥ y) e
  have hab (e : E) : a e*b e = t e*(C *ᵥ x) e*(C *ᵥ y) e := by
    calc a e*b e = (Real.sqrt (t e))^2*(C *ᵥ x) e*(C *ᵥ y) e := by dsimp [a,b]; ring
    _ = _ := by rw [Real.sq_sqrt (ht e)]
  rw [residualGram_bilinear C t x y,residualGram_scalar_identity,residualGram_scalar_identity]
  simpa only [hab,a,b,mul_pow,Real.sq_sqrt (ht _)] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b

theorem routing_face_inverse_bound {E : Type*} [Fintype E] {L : ℕ}
    (C : Matrix E (Fin L) ℝ) (S : Finset E) (t : E → ℝ) {T : ℝ} (hT : 0 < T)
    (ht : ∀ e, 0 ≤ t e) (hS : ∀ e ∈ S, t e ≤ T)
    (hM : (residualGram C t).PosDef) (d : EuclideanSpace ℝ (Fin L)) :
    ‖(routingFace C S).starProjection d‖^2 / (T*routingFaceConstant C S) ≤
      d.ofLp ⬝ᵥ ((residualGram C t)⁻¹ *ᵥ d.ofLp) := by
  let K := routingFace C S
  let w := K.starProjection d
  let M := residualGram C t
  let z := M⁻¹ *ᵥ d.ofLp
  have hMw : w ∈ K := K.starProjection_apply_mem d
  have hz : M *ᵥ z = d.ofLp := by
    dsimp only [z]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM.det_pos.ne'), Matrix.one_mulVec]
  have hw : w.ofLp ⬝ᵥ d.ofLp = ‖w‖^2 := by
    have h : ⟪w,d⟫ = ⟪w,w⟫ := by
      calc ⟪w,d⟫ = ⟪K.starProjection w,d⟫ := by rw [(K.starProjection_eq_self_iff).mpr hMw]
      _ = ⟪w,w⟫ := K.inner_starProjection_left_eq_right w d
    rw [real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      dotProduct_comm] at h
    exact h
  have hcoef : 0 < T*routingFaceConstant C S := mul_pos hT (routingFaceConstant_pos C S)
  have hCs := routingGram_cauchy C t ht w.ofLp z
  change (w.ofLp ⬝ᵥ (M *ᵥ z))^2 ≤ (w.ofLp ⬝ᵥ (M *ᵥ w.ofLp))*(z ⬝ᵥ (M *ᵥ z)) at hCs
  rw [hz,hw,dotProduct_comm z] at hCs
  have hnonneg : 0 ≤ d.ofLp ⬝ᵥ z := by
    calc 0 ≤ z ⬝ᵥ (M *ᵥ z) := by
          exact (residualGram_scalar_identity C t z).symm ▸
            Finset.sum_nonneg (fun e _ => mul_nonneg (ht e) (sq_nonneg _))
    _ = d.ofLp ⬝ᵥ z := by rw [hz,dotProduct_comm]
  change ‖w‖^2/(T*routingFaceConstant C S) ≤ d.ofLp ⬝ᵥ z
  apply (div_le_iff₀ hcoef).2
  by_cases hn : ‖w‖^2=0
  · rw [hn]
    exact mul_nonneg hnonneg hcoef.le
  have hscale := routingFace_scale C S t hT hS hMw
  have h := hCs.trans (mul_le_mul_of_nonneg_right hscale hnonneg)
  have hh : ‖w‖^2 * ‖w‖^2 ≤ ‖w‖^2 * (d.ofLp ⬝ᵥ z * (T*routingFaceConstant C S)) := by
    convert h using 1 <;> ring
  exact le_of_mul_le_mul_left hh (lt_of_le_of_ne (sq_nonneg _) (Ne.symm hn))

/-- The same bound in all four intrinsic sector-plane coordinates,
with one common cutoff for the given routed face. -/
theorem routing_face_four_coordinate_bound {E : Type*} [Fintype E] {L : ℕ}
    (C : Matrix E (Fin L) ℝ) (S : Finset E) (t : E → ℝ) {T : ℝ} (hT : 0 < T)
    (ht : ∀ e, 0 ≤ t e) (hS : ∀ e ∈ S, t e ≤ T)
    (hM : (residualGram C t).PosDef) (d : EuclideanSpace ℝ (Fin L × Fin 4)) :
    (∑ ν : Fin 4, ‖(routingFace C S).starProjection (WithLp.toLp 2 (fun j => d (j,ν)))‖^2) /
        (T*routingFaceConstant C S) ≤
      ∑ ν : Fin 4, (fun j => d (j,ν)) ⬝ᵥ ((residualGram C t)⁻¹ *ᵥ (fun j => d (j,ν))) := by
  rw [Finset.sum_div]
  exact Finset.sum_le_sum (fun ν _ => routing_face_inverse_bound C S t hT ht hS hM _)

end UV.SewnFlags
