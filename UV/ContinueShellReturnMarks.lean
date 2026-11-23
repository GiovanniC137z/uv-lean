import UV.ContinueNormalHolonomyProperTime
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The two-state transition on the transported Neumann shell and the
inclusive sum over all intermediate internal slots. The positive time
power test below uses separately established upper and lower trace bounds. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace UV

/-- Matrix elements between the unit vectors (1,±1)/√2 and the transported
initial (1,1)/√2 in the diagonal connection. -/
def shellMarkAmplitude (δ : ℝ) (flip : Bool) : ℂ :=
  (1 + (if flip then -1 else 1) * Complex.exp (δ * Complex.I))/2

theorem shell_mark_flip_sq (δ : ℝ) :
    ‖shellMarkAmplitude δ true‖^2 = Real.sin (δ/2)^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp [shellMarkAmplitude,Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin]
  have h := Real.cos_two_mul (δ/2)
  rw [show 2*(δ/2) = δ by ring] at h
  nlinarith [Real.sin_sq_add_cos_sq δ,Real.sin_sq_add_cos_sq (δ/2)]

theorem shell_mark_channel_sum (δ : ℝ) :
    ∑ b : Bool, ‖shellMarkAmplitude δ b‖^2 = 1 := by
  simp only [Fintype.sum_bool,Complex.sq_norm,Complex.normSq_apply]
  simp [shellMarkAmplitude,Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin]
  nlinarith [Real.sin_sq_add_cos_sq δ]

def shellMarkedWord (j : ℕ) (δ : ℝ) (b : Fin j → Bool) : ℂ := ∏ a, shellMarkAmplitude δ (b a)

theorem shell_mark_word_selected (j : ℕ) (δ : ℝ) :
    ‖shellMarkedWord j δ (fun _ => true)‖^2 = |Real.sin (δ/2)|^(2*j) := by
  simp only [shellMarkedWord,Finset.prod_const,Finset.card_univ,Fintype.card_fin,norm_pow]
  rw [←pow_mul, Nat.mul_comm, pow_mul,shell_mark_flip_sq, pow_mul,sq_abs]

theorem shell_mark_word_inclusive (j : ℕ) (δ : ℝ) :
    ∑ b : Fin j → Bool, ‖shellMarkedWord j δ b‖^2 = 1 := by
  simp only [shellMarkedWord,norm_prod,←Finset.prod_pow]
  rw [←Fintype.prod_sum (fun (_ : Fin j) (b : Bool) => ‖shellMarkAmplitude δ b‖^2)]
  simp only [shell_mark_channel_sum, Finset.prod_const_one]

/-- The inclusive return is also unchanged on rotating the readout basis. -/
theorem shell_inclusive_basis {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (B : OrthonormalBasis ι ℂ E) (U : E ≃ₗᵢ[ℂ] E) (v : E) (hv : ‖v‖ = 1) :
    ∑ i, ‖inner ℂ (B i) (U v)‖^2 = 1 := by rw [B.sum_sq_norm_inner_right,U.norm_map,hv,one_pow]

/-- Sharp short-duration test after integration over the marked fraction.
The necessary bound is from the interior band of fractions. Endpoint
fractions enter through the upper bound. -/
theorem shell_short_time_power_iff (j n : ℕ) {T c C : ℝ} (hT : 0 < T) (hc : 0 < c)
    (F : ℝ → ℝ) (hF : Measurable F)
    (hl : ∀ t ∈ Ioo 0 T, c*t^((j:ℝ)-(n:ℝ)/2-3) ≤ F t)
    (hu : ∀ t ∈ Ioo 0 T, F t ≤ C*t^((j:ℝ)-(n:ℝ)/2-3)) :
    IntegrableOn F (Ioo 0 T) ↔ 2+(n:ℝ)/2 < j := by
  let a := (j:ℝ)-(n:ℝ)/2-3
  constructor
  · intro h
    have hi : IntegrableOn (fun t : ℝ => t^a) (Ioo 0 T) := by
      apply (h.const_mul c⁻¹).mono' (by fun_prop)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)]
      simpa [a,hc.ne'] using mul_le_mul_of_nonneg_left (hl t ht) (inv_nonneg.mpr hc.le)
    have := (intervalIntegral.integrableOn_Ioo_rpow_iff hT).mp hi
    dsimp [a] at this; linarith
  · intro h
    have hi : IntegrableOn (fun t : ℝ => t^a) (Ioo 0 T) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hT).mpr (by dsimp [a]; linarith)
    apply (hi.const_mul C).mono' hF.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_of_nonneg ((mul_nonneg hc.le (Real.rpow_nonneg ht.1.le _)).trans (hl t ht))]
    exact hu t ht

end UV
