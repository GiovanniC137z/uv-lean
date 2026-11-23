import UV.ContinueNetworkDirectionalObstructions
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Algebra.MvPolynomial.Monad

/-! Completing the real square in the literal directional model. The
translation acts on the original polynomial and every affine route. -/

noncomputable section

namespace UV

open MeasureTheory Set
open scoped InnerProductSpace BigOperators

variable {E : Type*} [Fintype E] {d : ℕ}
variable {V : E → Type*} [∀ e, NormedAddCommGroup (V e)] [∀ e, NormedSpace ℝ (V e)]

def translateDirectionalPolynomial (v : DirectionalMomentum d) (P : MvPolynomial (Fin d) ℂ) :
    MvPolynomial (Fin d) ℂ :=
  MvPolynomial.bind₁ (fun i => MvPolynomial.X i + MvPolynomial.C (v i : ℂ)) P

theorem translate_directional_polynomial_eval (P : MvPolynomial (Fin d) ℂ)
    (v : DirectionalMomentum d) (z : Fin d → ℂ) :
    MvPolynomial.eval z (translateDirectionalPolynomial v P) =
      MvPolynomial.eval (fun i => z i + (v i : ℂ)) P := by
  unfold translateDirectionalPolynomial MvPolynomial.eval
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) z
    (MvPolynomial.bind₁ (fun i => MvPolynomial.X i + MvPolynomial.C (v i : ℂ)) P) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  have he : (fun i => MvPolynomial.eval₂Hom (RingHom.id ℂ) z
        (MvPolynomial.X i + MvPolynomial.C (v i : ℂ))) = fun i => z i + (v i : ℂ) := by
    funext i
    simp only [map_add,MvPolynomial.eval₂Hom_X',MvPolynomial.eval₂Hom_C,RingHom.id_apply]
  rw [he]

theorem directional_numerator_translate (P : MvPolynomial (Fin d) ℂ) (v k : DirectionalMomentum d) :
    directionalNumerator (translateDirectionalPolynomial v P) k = directionalNumerator P (k+v) := by
  unfold directionalNumerator
  rw [translate_directional_polynomial_eval]
  have he : (fun i => (k i : ℂ) + (v i : ℂ)) = fun i => ((k+v) i : ℂ) :=
    funext fun i => (Complex.ofReal_add (k i) (v i)).symm
  rw [he]

theorem translate_directional_polynomial_nonzero {P : MvPolynomial (Fin d) ℂ} (hP : P ≠ 0)
    (v : DirectionalMomentum d) : translateDirectionalPolynomial v P ≠ 0 := by
  obtain ⟨x,hx⟩ := directionalNumerator_exists_ne_zero hP
  intro h
  have he := directional_numerator_translate P v (x-v)
  rw [h,sub_add_cancel] at he
  have hz : directionalNumerator (0 : MvPolynomial (Fin d) ℂ) (x-v) = 0 :=
    map_zero (MvPolynomial.eval (fun i => ((x-v) i : ℂ)))
  exact hx (he ▸ hz)

theorem directional_kernel_drift_center
    (Q : DirectionalMomentum d →L[ℝ] DirectionalMomentum d) (h : DirectionalMomentum d)
    (hSym : ∀ k k', inner ℝ k (Q k') = inner ℝ k' (Q k))
    (hker : ∀ w, Q w = 0 → inner ℝ h w = 0) :
    ∃ v : DirectionalMomentum d, h = (2 : ℝ) • Q v := by
  have hs : Q.toLinearMap.IsSymmetric := by
    intro x y
    change inner ℝ (Q x) y = inner ℝ x (Q y)
    exact (real_inner_comm y (Q x)).trans (hSym y x)
  let K := LinearMap.ker Q.toLinearMap
  have hm : h ∈ Kᗮ := (K.mem_orthogonal' h).mpr fun w hw => hker w (LinearMap.mem_ker.mp hw)
  have hRange : Kᗮ = LinearMap.range Q.toLinearMap := by
    rw [show K = LinearMap.ker Q.toLinearMap from rfl,← hs.orthogonal_range,
      Submodule.orthogonal_orthogonal]
  rw [hRange] at hm
  obtain ⟨v,hv⟩ := hm
  change Q v = h at hv
  refine ⟨(1/2 : ℝ) • v,?_⟩
  rw [map_smul,hv,smul_smul,show (2:ℝ)*(1/2)=1 by norm_num,one_smul]

theorem directional_model_complete_square
    (Q : DirectionalMomentum d →L[ℝ] DirectionalMomentum d)
    (v : DirectionalMomentum d)
    (C : ∀ e, DirectionalMomentum d →L[ℝ] V e) (p : ∀ e, V e)
    (ν : E → ℝ) (P : MvPolynomial (Fin d) ℂ)
    (hSym : ∀ k k', inner ℝ k (Q k') = inner ℝ k' (Q k)) (k : DirectionalMomentum d) :
    directionalAbsoluteModel Q ((2:ℝ) • Q v) C p ν P (k+v) =
      Real.exp (inner ℝ v (Q v)) *
        directionalAbsoluteModel Q 0 C (fun e => C e v + p e) ν (translateDirectionalPolynomial v P) k := by
  have hquad :
      -inner ℝ (k+v) (Q (k+v)) + inner ℝ ((2:ℝ) • Q v) (k+v) =
        -inner ℝ k (Q k) + inner ℝ v (Q v) := by
    simp only [map_add,inner_add_left,inner_add_right,real_inner_smul_left]
    rw [hSym v k,real_inner_comm (Q v) k,real_inner_comm (Q v) v]
    ring
  have hroute (e : E) : C e (k+v) + p e = C e k + (C e v + p e) := by
    rw [map_add,add_assoc]
  simp only [directionalAbsoluteModel,hquad,hroute,directional_numerator_translate,
    inner_zero_left,add_zero,Real.exp_add]
  ring

theorem directional_model_integrable_iff_centered
    (Q : DirectionalMomentum d →L[ℝ] DirectionalMomentum d)
    (v : DirectionalMomentum d)
    (C : ∀ e, DirectionalMomentum d →L[ℝ] V e) (p : ∀ e, V e)
    (ν : E → ℝ) (P : MvPolynomial (Fin d) ℂ)
    (hSym : ∀ k k', inner ℝ k (Q k') = inner ℝ k' (Q k)) :
    Integrable (directionalAbsoluteModel Q ((2:ℝ) • Q v) C p ν P) ↔
      Integrable (directionalAbsoluteModel Q 0 C (fun e => C e v + p e) ν (translateDirectionalPolynomial v P)) := by
  let G := directionalAbsoluteModel Q 0 C (fun e => C e v + p e) ν (translateDirectionalPolynomial v P)
  let H := directionalAbsoluteModel Q ((2:ℝ) • Q v) C p ν P
  let a := Real.exp (inner ℝ v (Q v))
  have ha : 0 < a := Real.exp_pos _
  let e := Homeomorph.addRight v
  have hm : MeasurePreserving e (volume : Measure (DirectionalMomentum d)) volume :=
    measurePreserving_add_right volume v
  have h := hm.integrable_comp_emb e.measurableEmbedding (g := H)
  have he : H ∘ e = fun k => a * G k := funext (directional_model_complete_square Q v C p ν P hSym)
  rw [he] at h
  refine h.symm.trans ⟨?_,fun hG => hG.const_mul a⟩
  intro hG
  refine (hG.const_mul a⁻¹).congr (Filter.Eventually.of_forall fun k => ?_)
  change a⁻¹ * (a * G k) = G k
  rw [← mul_assoc,inv_mul_cancel₀ ha.ne',one_mul]

/-- Shifting every route can be removed after centering because the
finite product of shifted massive factors has two height- and
momentum-independent comparison constants. -/
theorem directional_model_integrable_iff_unshifted
    (Q : DirectionalMomentum d →L[ℝ] DirectionalMomentum d) (h : DirectionalMomentum d)
    (C : ∀ e, DirectionalMomentum d →L[ℝ] V e) (p : ∀ e, V e)
    (ν : E → ℝ) (hν : ∀ e, 0 ≤ ν e) (P : MvPolynomial (Fin d) ℂ) :
    Integrable (directionalAbsoluteModel Q h C p ν P) ↔
      Integrable (directionalAbsoluteModel Q h C (fun _ => 0) ν P) := by
  let W (e : E) := 2 * (1 + ‖p e‖^2)
  let a := ∏ e, W e ^ (-ν e)
  let b := ∏ e, W e ^ ν e
  have ha : 0 < a := Finset.prod_pos fun e _ => by dsimp [W]; positivity
  have hb : 0 < b := Finset.prod_pos fun e _ => by dsimp [W]; positivity
  let F := directionalAbsoluteModel Q h C p ν P
  let G := directionalAbsoluteModel Q h C (fun _ => 0) ν P
  have hcF : Continuous F := directionalAbsoluteModel_continuous Q h C p ν P
  have hcG : Continuous G := directionalAbsoluteModel_continuous Q h C _ ν P
  have hF (k : DirectionalMomentum d) : 0 ≤ F k := by
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
      (Finset.prod_nonneg fun e _ => (directionalMassiveFactor_pos (ν e) _).le)
  have hG (k : DirectionalMomentum d) : 0 ≤ G k := by
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
      (Finset.prod_nonneg fun e _ => (directionalMassiveFactor_pos (ν e) _).le)
  have hh (k : DirectionalMomentum d) : a * G k ≤ F k ∧ F k ≤ b * G k := by
    let c := ‖directionalNumerator P k‖ * Real.exp (-inner ℝ k (Q k) + inner ℝ h k)
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hlow : a * (∏ e, directionalMassiveFactor (ν e) (C e k)) ≤
        (∏ e, directionalMassiveFactor (ν e) (C e k + p e)) := by
      unfold a
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod (fun e _ => mul_nonneg
        (Real.rpow_nonneg (by dsimp [W]; positivity) _) (directionalMassiveFactor_pos (ν e) _).le)
        (fun e _ => (directionalMassiveFactor_shift_compare (hν e) (C e k) (p e)).1)
    have hupp : (∏ e, directionalMassiveFactor (ν e) (C e k + p e)) ≤
        b * (∏ e, directionalMassiveFactor (ν e) (C e k)) := by
      unfold b
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod (fun e _ => (directionalMassiveFactor_pos (ν e) _).le)
        (fun e _ => (directionalMassiveFactor_shift_compare (hν e) (C e k) (p e)).2)
    change a * (c * (∏ e, directionalMassiveFactor (ν e) (C e k + 0))) ≤
      c * (∏ e, directionalMassiveFactor (ν e) (C e k + p e)) ∧
      c * (∏ e, directionalMassiveFactor (ν e) (C e k + p e)) ≤
        b * (c * (∏ e, directionalMassiveFactor (ν e) (C e k + 0)))
    simp only [add_zero]
    rw [mul_left_comm a c,mul_left_comm b c]
    exact ⟨mul_le_mul_of_nonneg_left hlow hc,mul_le_mul_of_nonneg_left hupp hc⟩
  constructor
  · intro hi
    apply (hi.const_mul a⁻¹).mono' hcG.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro k
    rw [Real.norm_of_nonneg (hG k),← div_eq_inv_mul,le_div_iff₀ ha,mul_comm (G k)]
    exact (hh k).1
  · intro hi
    apply (hi.const_mul b).mono' hcF.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun k => by rw [Real.norm_of_nonneg (hF k)]; exact (hh k).2

end UV
