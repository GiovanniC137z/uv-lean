import UV.ContinueTwoBandDeterminantSeries

/-! Finite-section scalar source coefficients of the prepared determinant.
The electric perturbation is identical in the hopping and onsite factors. -/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator

namespace UV.SectorPlane

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem scalar_trace_series_summable (K : Matrix ι ι ℂ) (hK : ‖K‖ < 1) :
    Summable (fun n : ℕ => ‖(K^(n+1)).trace / (n+1)‖) := by
  rcases isEmpty_or_nonempty ι with h | h
  · simpa [Matrix.trace] using (summable_zero : Summable (fun _ : ℕ => (0:ℝ)))
  let τ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  apply ((summable_geometric_of_lt_one (norm_nonneg K) hK).mul_left (‖τ‖*‖K‖)).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro n
  rw [norm_div]
  have h : (1:ℝ) ≤ ‖(n:ℂ)+1‖ := by
    rw [←Nat.cast_one (R := ℂ),←Nat.cast_add,Complex.norm_natCast]
    exact_mod_cast Nat.le_add_left 1 n
  apply (div_le_self (norm_nonneg _) h).trans
  apply (τ.le_opNorm _).trans
  apply (mul_le_mul_of_nonneg_left (norm_pow_le K (n+1)) (norm_nonneg τ)).trans_eq
  rw [pow_succ]
  ring

private theorem scalar_factor (D V : Matrix ι ι ℂ) (hu : IsUnit D) (z : ℂ) :
    (D+z • V).det / D.det = (1-(-z) • (Ring.inverse D*V)).det := by
  have h : D * (Ring.inverse D*V) = V := by rw [←mul_assoc,Ring.mul_inverse_cancel _ hu,one_mul]
  have hd : D.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det D).mp hu)
  rw [show D+z • V = D*(1-(-z) • (Ring.inverse D*V)) by
    rw [mul_sub,mul_one,mul_smul_comm,h,neg_smul,sub_neg_eq_add],Matrix.det_mul]
  field_simp

/-- The normalized quotient at any finite cutoff has an absolutely
convergent complex logarithm near zero electric field. Its coefficient
at every positive power is the cyclic trace with the pure onsite word
removed at the same source, including the one-mark case. -/
theorem twoBand_finite_relative_source_series (D D₀ V : Matrix ι ι ℂ)
    (hD : IsUnit D) (h₀ : IsUnit D₀) (z : ℂ)
    (hz : ‖(-z) • (Ring.inverse D*V)‖ < 1) (hz₀ : ‖(-z) • (Ring.inverse D₀*V)‖ < 1) :
    let c := fun n : ℕ => (-z)^(n+1) *
      (((Ring.inverse D*V)^(n+1)).trace-((Ring.inverse D₀*V)^(n+1)).trace)/(n+1)
    Summable (fun n => ‖c n‖) ∧
      ((D+z • V).det/D.det) / ((D₀+z • V).det/D₀.det) = Complex.exp (-(∑' n, c n)) := by
  intro c
  let K := (-z) • (Ring.inverse D*V)
  let K₀ := (-z) • (Ring.inverse D₀*V)
  let t := fun (M : Matrix ι ι ℂ) (n : ℕ) => (M^(n+1)).trace/(n+1)
  have he (n : ℕ) : c n = t K n - t K₀ n := by
    simp only [c,t,K,K₀,smul_pow,Matrix.trace_smul,smul_eq_mul,mul_sub,sub_div]
  have h₁ := scalar_trace_series_summable K hz
  have h₂ := scalar_trace_series_summable K₀ hz₀
  constructor
  · exact (h₁.add h₂).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => (he n) ▸ norm_sub_le _ _
  · rw [scalar_factor D V hD,scalar_factor D₀ V h₀,twoBand_contractive_det_series _ hz,
      twoBand_contractive_det_series _ hz₀,←Complex.exp_sub]
    apply congrArg Complex.exp
    simp_rw [he]
    rw [Summable.tsum_sub h₁.of_norm h₂.of_norm]
    abel

end UV.SectorPlane
