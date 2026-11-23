import UV.ContinueNetworkSchwinger
import UV.ContinueNetworkTonelli

/-! The Gaussian Schwinger integral with the same affine route on every
line and with the numerator kept inside the common momentum integral. -/

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal InnerProductSpace

namespace UV

variable {E : Type*} [Fintype E] {d : ℕ}
variable {V : E → Type*} [∀ e, NormedAddCommGroup (V e)] [∀ e, NormedSpace ℝ (V e)]

def directionalSchwingerMeasure (E : Type*) [Fintype E] : Measure (E → ℝ) :=
  Measure.pi fun _ : E => volume.restrict (Ioo (0 : ℝ) 1)

/-- Real Gaussian exponential and polynomial on the literal affine routes. -/
def directionalSchwingerGaussian
    (Q : DirectionalMomentum d →L[ℝ] DirectionalMomentum d) (h : DirectionalMomentum d)
    (C : ∀ e, DirectionalMomentum d →L[ℝ] V e) (p : ∀ e, V e)
    (P : MvPolynomial (Fin d) ℂ) (t : E → ℝ) (k : DirectionalMomentum d) : ℝ :=
  ‖directionalNumerator P k‖ *
    Real.exp (-inner ℝ k (Q k) + inner ℝ h k - ∑ e, t e * ‖C e k + p e‖ ^ 2)

def directionalSchwingerCost
    (Q : DirectionalMomentum d →L[ℝ] DirectionalMomentum d) (h : DirectionalMomentum d)
    (C : ∀ e, DirectionalMomentum d →L[ℝ] V e) (p : ∀ e, V e) (ν : E → ℝ)
    (P : MvPolynomial (Fin d) ℂ) : ℝ≥0∞ :=
  ∫⁻ t : E → ℝ, (∏ e, ENNReal.ofReal (t e ^ (ν e - 1))) *
    (∫⁻ k : DirectionalMomentum d, ENNReal.ofReal (directionalSchwingerGaussian Q h C p P t k))
    ∂directionalSchwingerMeasure E

private theorem directionalSchwinger_apply_bounds
    (C : ∀ e, DirectionalMomentum d →L[ℝ] V e) (p : ∀ e, V e) (ν : E → ℝ)
    (hν : ∀ e, 0 < ν e) (k : DirectionalMomentum d) :
    (∏ e, directionalSchwingerLower (ν e)) *
        (∏ e, ENNReal.ofReal (directionalMassiveFactor (ν e) (C e k + p e))) ≤
      (∏ e, directionalSchwingerLine (ν e) (‖C e k + p e‖ ^ 2)) ∧
    (∏ e, directionalSchwingerLine (ν e) (‖C e k + p e‖ ^ 2)) ≤
      (∏ e, directionalSchwingerUpper (ν e)) *
        (∏ e, ENNReal.ofReal (directionalMassiveFactor (ν e) (C e k + p e))) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact ⟨Finset.prod_le_prod' fun e _ =>
      (directionalSchwingerLine_compare (hν e) (sq_nonneg ‖C e k + p e‖)).1,
    Finset.prod_le_prod' fun e _ =>
      (directionalSchwingerLine_compare (hν e) (sq_nonneg ‖C e k + p e‖)).2⟩

/-- Tonelli preserves the actual affine shifts and all loop coordinates. -/
theorem directionalSchwingerCost_eq_line_product
    (Q : DirectionalMomentum d →L[ℝ] DirectionalMomentum d) (h : DirectionalMomentum d)
    (C : ∀ e, DirectionalMomentum d →L[ℝ] V e) (p : ∀ e, V e) (ν : E → ℝ)
    (P : MvPolynomial (Fin d) ℂ) :
    directionalSchwingerCost Q h C p ν P =
      ∫⁻ k : DirectionalMomentum d,
        ENNReal.ofReal (‖directionalNumerator P k‖ * Real.exp (-inner ℝ k (Q k) + inner ℝ h k)) *
          ∏ e, directionalSchwingerLine (ν e) (‖C e k + p e‖ ^ 2) := by
  let z (k : DirectionalMomentum d) (e : E) := ‖C e k + p e‖ ^ 2
  let A (k : DirectionalMomentum d) :=
    ENNReal.ofReal (‖directionalNumerator P k‖ * Real.exp (-inner ℝ k (Q k) + inner ℝ h k))
  let F (t : E → ℝ) (k : DirectionalMomentum d) :=
    A k * ∏ e, directionalSchwingerWeight (ν e) (z k e) (t e)
  letI : SigmaFinite (directionalSchwingerMeasure E) := by
    unfold directionalSchwingerMeasure
    infer_instance
  have hA : Measurable A := ENNReal.measurable_ofReal.comp
    ((directionalNumerator_continuous P).norm.mul (by fun_prop)).measurable
  have hF : Measurable (Function.uncurry F) := by
    apply (hA.comp measurable_snd).mul
    apply Finset.measurable_prod
    intro e _
    unfold directionalSchwingerWeight z
    have hs : Measurable (fun q : (E → ℝ) × DirectionalMomentum d => q.1 e) :=
      (measurable_pi_apply e).comp measurable_fst
    have hz : Measurable (fun k : DirectionalMomentum d => ‖C e k + p e‖ ^ 2) :=
      (((C e).continuous.add continuous_const).norm.pow 2).measurable
    exact ENNReal.measurable_ofReal.comp ((hs.pow_const _).mul
      (Real.measurable_exp.comp (hs.mul (hz.comp measurable_snd)).neg))
  have htz : ∀ᵐ t : E → ℝ ∂directionalSchwingerMeasure E, ∀ e, 0 < t e := by
    apply ae_all_iff.mpr
    intro e
    exact (Measure.quasiMeasurePreserving_eval _ e).ae
      ((ae_restrict_mem measurableSet_Ioo).mono fun _ ht => ht.1)
  calc
    directionalSchwingerCost Q h C p ν P =
        ∫⁻ t : E → ℝ, ∫⁻ k : DirectionalMomentum d, F t k
          ∂volume ∂directionalSchwingerMeasure E := by
      unfold directionalSchwingerCost
      apply lintegral_congr_ae
      filter_upwards [htz] with t ht
      have hfin : (∏ e, ENNReal.ofReal (t e ^ (ν e - 1))) ≠ ⊤ :=
        (ENNReal.prod_lt_top fun e _ => ENNReal.ofReal_lt_top).ne
      rw [← lintegral_const_mul' _ _ hfin]
      apply lintegral_congr
      intro k
      have ht' : ∀ e, 0 ≤ t e ^ (ν e - 1) := fun e => Real.rpow_nonneg (ht e).le _
      have he (e : E) :
          ENNReal.ofReal (t e ^ (ν e - 1) * Real.exp (-(t e * z k e))) =
            ENNReal.ofReal (t e ^ (ν e - 1)) * ENNReal.ofReal (Real.exp (-(t e * z k e))) :=
        ENNReal.ofReal_mul (ht' e)
      simp only [F, directionalSchwingerWeight]
      simp_rw [he, Finset.prod_mul_distrib]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun e _ => Real.exp_nonneg _),
        ← Real.exp_sum, Finset.sum_neg_distrib]
      have heq : ENNReal.ofReal (directionalSchwingerGaussian Q h C p P t k) =
          A k * ENNReal.ofReal (Real.exp (-(∑ e, t e * z k e))) := by
        rw [directionalSchwingerGaussian, sub_eq_add_neg, Real.exp_add, ← mul_assoc]
        exact ENNReal.ofReal_mul (by positivity)
      rw [heq]
      ac_rfl
    _ = ∫⁻ k : DirectionalMomentum d, ∫⁻ t : E → ℝ, F t k
          ∂directionalSchwingerMeasure E := lintegral_lintegral_swap hF.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro k
      change (∫⁻ t : E → ℝ, A k * ∏ e, directionalSchwingerWeight (ν e) (z k e) (t e)
        ∂directionalSchwingerMeasure E) = _
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hm (e : E) : Measurable (directionalSchwingerWeight (ν e) (z k e)) :=
        ENNReal.measurable_ofReal.comp ((measurable_id.pow_const _).mul
          (Real.measurable_exp.comp ((measurable_id.mul_const _).neg)))
      rw [directionalSchwingerMeasure, network_lintegral_fintype_prod _ _ hm]
      rfl

/-- The shifted massive absolute integral is finite exactly when its
literal joint momentum and Schwinger-parameter integral is finite. -/
theorem directionalAbsoluteModel_integrable_iff_schwinger
    (Q : DirectionalMomentum d →L[ℝ] DirectionalMomentum d) (h : DirectionalMomentum d)
    (C : ∀ e, DirectionalMomentum d →L[ℝ] V e) (p : ∀ e, V e) (ν : E → ℝ)
    (hν : ∀ e, 0 < ν e) (P : MvPolynomial (Fin d) ℂ) :
    Integrable (directionalAbsoluteModel Q h C p ν P) ↔
      directionalSchwingerCost Q h C p ν P < ⊤ := by
  let L := ∏ e, directionalSchwingerLower (ν e)
  let U := ∏ e, directionalSchwingerUpper (ν e)
  let f := directionalAbsoluteModel Q h C p ν P
  let I : ℝ≥0∞ := ∫⁻ k, ENNReal.ofReal (f k)
  have hL : L ≠ 0 := Finset.prod_ne_zero_iff.mpr fun e _ => directionalSchwingerLower_ne_zero (hν e)
  have hU : U < ⊤ := ENNReal.prod_lt_top fun e _ => ENNReal.ofReal_lt_top
  have hLf : L ≠ ⊤ := (ENNReal.prod_lt_top fun e _ => ENNReal.ofReal_lt_top).ne
  have hfn (k : DirectionalMomentum d) : 0 ≤ f k := by
    unfold f directionalAbsoluteModel
    exact mul_nonneg (by positivity)
      (Finset.prod_nonneg fun e _ => (directionalMassiveFactor_pos _ _).le)
  have hI : Integrable f ↔ I < ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable
      (directionalAbsoluteModel_continuous Q h C p ν P).aestronglyMeasurable
      (Eventually.of_forall hfn)).symm.trans lt_top_iff_ne_top.symm
  let A (k : DirectionalMomentum d) :=
    ENNReal.ofReal (‖directionalNumerator P k‖ * Real.exp (-inner ℝ k (Q k) + inner ℝ h k))
  let W (k : DirectionalMomentum d) :=
    ∏ e, directionalSchwingerLine (ν e) (‖C e k + p e‖ ^ 2)
  let M (k : DirectionalMomentum d) :=
    ∏ e, ENNReal.ofReal (directionalMassiveFactor (ν e) (C e k + p e))
  have he (k : DirectionalMomentum d) : ENNReal.ofReal (f k) = A k * M k := by
    unfold f directionalAbsoluteModel
    rw [ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_prod_of_nonneg (fun e _ => (directionalMassiveFactor_pos _ _).le)]
  have hcost : L * I ≤ directionalSchwingerCost Q h C p ν P ∧
      directionalSchwingerCost Q h C p ν P ≤ U * I := by
    rw [directionalSchwingerCost_eq_line_product]
    unfold I
    rw [← lintegral_const_mul' _ _ hLf, ← lintegral_const_mul' _ _ hU.ne]
    constructor <;> apply lintegral_mono <;> intro k
    · change L * ENNReal.ofReal (f k) ≤ A k * W k
      rw [he k, mul_left_comm]
      exact mul_le_mul_left' (directionalSchwinger_apply_bounds C p ν hν k).1 _
    · change A k * W k ≤ U * ENNReal.ofReal (f k)
      rw [he k, mul_left_comm U]
      exact mul_le_mul_left' (directionalSchwinger_apply_bounds C p ν hν k).2 _
  rw [hI]
  constructor
  · intro h
    exact hcost.2.trans_lt (ENNReal.mul_lt_top hU h)
  · intro h
    by_contra! hnot
    have he : I = ⊤ := top_le_iff.mp hnot
    have h' := hcost.1.trans_lt h
    rw [he, ENNReal.mul_top hL] at h'
    exact (lt_irrefl _ h')

end UV
