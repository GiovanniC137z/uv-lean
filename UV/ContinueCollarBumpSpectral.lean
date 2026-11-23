import UV.ContinueCollarEigenTrace
import UV.AdvanceCollarResonanceHeat

/-! For a heat operator diagonal in a complete orthonormal basis, derive
the lower test estimate directly from the spectral weights of the input. -/

noncomputable section

open MeasureTheory Set Real
open scoped ComplexConjugate InnerProductSpace

namespace UV.CollarEigenmode

theorem discrete_heat_jensen {ι : Type*} (E w : ι → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hE : ∀ i,0 ≤ E i) (hw : ∀ i,0 ≤ w i) (hunit : HasSum w 1)
    (hint : Summable fun i => E i*w i) :
    exp (-t*∑' i,E i*w i) ≤ ∑' i,exp (-t*E i)*w i := by
  let m := ∑' i,E i*w i
  have hexp : Summable (fun i => exp (-t*E i)*w i) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (exp_nonneg _) (hw i))
      (fun i => mul_le_of_le_one_left (hw i) (exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (hE i)))) hunit.summable
  have haff := ((hunit.mul_left (1+t*m)).sub (hint.hasSum.mul_left t)).mul_left (exp (-t*m))
  have hminor (i : ι) : exp (-t*m)*((1+t*m)*w i-t*(E i*w i)) ≤ exp (-t*E i)*w i := by
    have h := mul_le_mul_of_nonneg_left (add_one_le_exp (t*m-t*E i)) (exp_nonneg (-t*m))
    rw [← exp_add,show -t*m+(t*m-t*E i) = -t*E i by ring] at h
    convert mul_le_mul_of_nonneg_right h (hw i) using 1; ring
  calc
    exp (-t*m) = exp (-t*m)*((1+t*m)*1-t*m) := by ring
    _ = _ := haff.tsum_eq.symm
    _ ≤ _ := haff.summable.tsum_le_tsum hminor hexp

theorem mode_heat_jensen {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) (E : ι → ℝ) {t : ℝ}
    (ht : 0 ≤ t) (hE : ∀ i,0 ≤ E i) (v : H) (hv : ‖v‖=1)
    (hact : ∀ i,b.repr (T v) i = (exp (-t*E i) : ℂ)*b.repr v i)
    (hform : Summable fun i => E i*‖b.repr v i‖^2) :
    Real.exp (-t*∑' i,E i*‖b.repr v i‖^2) ≤ (⟪v,T v⟫_ℂ).re := by
  have hunit := lp.hasSum_norm (p := 2) (by norm_num) (b.repr v)
  norm_num [b.repr.norm_map,hv] at hunit
  have h := discrete_heat_jensen E (fun i => ‖b.repr v i‖^2) ht hE (fun i => sq_nonneg _) hunit hform
  have hre := Complex.hasSum_re (b.hasSum_inner_mul_inner v (T v))
  have heq (i : ι) : (⟪v,b i⟫_ℂ * ⟪b i,T v⟫_ℂ).re = exp (-t*E i)*‖b.repr v i‖^2 := by
    rw [← b.repr_apply_apply,← inner_conj_symm,← b.repr_apply_apply,hact]
    rw [mul_left_comm,Complex.conj_mul']
    norm_cast
  simpa only [← hre.tsum_eq,heq] using h

end UV.CollarEigenmode
