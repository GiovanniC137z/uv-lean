import UV.ContinueSewnFlagResolutionHilbert
import UV.ResidualCoercivity
import Mathlib.Data.Real.StarOrdered

/-! Exact independent Gaussian readouts on routed marks and absolute
integrability against any fixed polynomial growth bound. -/

noncomputable section
open MeasureTheory Matrix Real Filter
open scoped BigOperators Matrix
namespace UV.SewnFlags

def oneScaleIndependentProfile {N : ℕ} (ℓ : ℝ) (q x : Fin N → ScalarMomentum) : ℂ :=
  ∏ i, oneScaleMarkedAmplitude ℓ (q i) (x i)

def oneScaleIndependentWeight {N : ℕ} (ℓ : ℝ) (q : Fin N → ScalarMomentum) : ℝ :=
  (((2/3:ℝ)^2)^N)⁻¹ * ∫ x, ‖oneScaleIndependentProfile ℓ q x‖^2

theorem oneScaleIndependentWeight_eq {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (q : Fin N → ScalarMomentum) :
    Integrable (fun x => ‖oneScaleIndependentProfile ℓ q x‖^2) ∧
      oneScaleIndependentWeight ℓ q = exp (-(2*ℓ^2/3)*∑ i, ‖q i‖^2) := by
  let f := fun i (x : ScalarMomentum) => ‖oneScaleMarkedAmplitude ℓ (q i) x‖^2
  have he (x : Fin N → ScalarMomentum) : ‖oneScaleIndependentProfile ℓ q x‖^2 = ∏ i, f i (x i) := by
    unfold f oneScaleIndependentProfile
    rw [norm_prod,Finset.prod_pow]
  constructor
  · simp_rw [he]
    rw [volume_pi]
    exact Integrable.fintype_prod (fun i => (oneScaleMarkedAmplitude_inclusive hℓ (q i)).1)
  · unfold oneScaleIndependentWeight
    simp_rw [he]
    rw [integral_fintype_prod_volume_eq_prod f]
    unfold f
    simp_rw [(oneScaleMarkedAmplitude_inclusive hℓ _).2]
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,← Real.exp_sum,
      ← Finset.mul_sum,← mul_assoc,inv_mul_cancel₀ (by positivity),one_mul]

/-- If the routing sees every independent loop direction, the literal
normalized inclusive readout weight makes every polynomially bounded
measurable numerator absolutely integrable. -/
theorem oneScaleIndependent_routed_integrable {N L : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ℓ : ℝ} (hℓ : 0 < ℓ) (C : Matrix (Fin N) (Fin L) ℝ) (hC : Function.Injective C.mulVec)
    (p : Fin N → ScalarMomentum) (f : EuclideanSpace ℝ (Fin L × Fin 4) → F)
    (hf : AEStronglyMeasurable f volume) {K D : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hPoly : ∀ᵐ k, ‖f k‖ ≤ K*(1+‖k‖^D)) :
    Integrable (fun k : EuclideanSpace ℝ (Fin L × Fin 4) =>
      oneScaleIndependentWeight ℓ (fun i => residualRouting C i k + p i) • f k) := by
  let V := EuclideanSpace ℝ (Fin L × Fin 4)
  let a := 2*ℓ^2/3
  let W := fun k : V => oneScaleIndependentWeight ℓ (fun i => residualRouting C i k + p i)
  have ha : 0 < a := by unfold a; positivity
  have hW (k : V) : W k = exp (-a * ∑ i, ‖residualRouting C i k + p i‖^2) :=
    (oneScaleIndependentWeight_eq hℓ _).2
  have hm : Continuous W := by
    rw [funext hW]
    fun_prop
  have hG : (residualGram C (fun _ => a)).PosDef := by
    have he : residualGram C (fun _ => a) = Cᴴ * diagonal (fun _ => a) * C := by
      unfold residualGram
      rw [conjTranspose_eq_transpose_of_trivial]
      congr!
    rw [he]
    exact (Matrix.PosDef.diagonal (fun _ => ha)).conjTranspose_mul_mul_same hC
  obtain ⟨c,B,hc,_,hb⟩ := matrix_residual_affine_coercivity C (fun _ => a) hG
    (fun i (_ : Unit) => p i) (fun i => ‖p i‖) (fun i => norm_nonneg (p i)) (fun _ _ => le_rfl)
  have hF : Integrable (fun k : V => (1+‖k‖^D)*exp (-((c/2)*‖k‖^2))) :=
    integrable_real_degree_gaussian (by positivity) hD
  apply (hF.const_mul (K*exp B)).mono' (hm.measurable.aestronglyMeasurable.smul hf)
  filter_upwards [hPoly] with k hk
  change ‖W k • f k‖ ≤ (K*exp B)*((1+‖k‖^D)*exp (-((c/2)*‖k‖^2)))
  rw [norm_smul,hW,Real.norm_of_nonneg (exp_pos _).le]
  have hd : (c/2)*‖k‖^2-B ≤ a*∑ i, ‖residualRouting C i k + p i‖^2 := by
    rw [Finset.mul_sum]
    exact hb () k
  have hk₀ : 0 ≤ K*(1+‖k‖^D) := mul_nonneg hK (by positivity)
  calc
    _ ≤ exp (-a*∑ i, ‖residualRouting C i k + p i‖^2)*(K*(1+‖k‖^D)) :=
      mul_le_mul_of_nonneg_left hk (exp_pos _).le
    _ ≤ exp (B-(c/2)*‖k‖^2)*(K*(1+‖k‖^D)) :=
      mul_le_mul_of_nonneg_right (exp_le_exp.mpr (by linarith [hd])) hk₀
    _ = _ := by rw [sub_eq_add_neg,exp_add]; ring

end UV.SewnFlags
