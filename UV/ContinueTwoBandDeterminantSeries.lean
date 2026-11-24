import UV.ContinueTwoBandRelativeSchur
import UV.ContinueCompressedModesDeterminant
import Mathlib.Analysis.Calculus.SmoothSeries

/-! The complex finite-section determinant of the Schur product equals
the exponential of its convergent trace expansion on the norm ball.
No choice of a global complex logarithm of the determinant is needed. -/

noncomputable section
open Matrix Filter Set Metric Polynomial
open scoped Topology Matrix.Norms.L2Operator Polynomial

namespace UV.SectorPlane

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private abbrev Mat := Matrix ι ι ℂ

private theorem det_unit_tangent (C : Mat (ι := ι)) :
    HasDerivAt (fun z : ℂ => (1 + z • C).det) C.trace 0 := by
  let P := (1+(X : ℂ[X]) • C.map Polynomial.C).det
  have he (z : ℂ) : P.eval z = (1+z • C).det := by
    simp [P,eval_det,←smul_eq_mul_diagonal]
  have hd := P.hasDerivAt (0:ℂ)
  rw [show P.derivative.eval 0 = _ from Matrix.derivative_det_one_add_X_smul C] at hd
  simpa only [←he] using hd

private theorem schur_det_tangent (K : Mat (ι := ι)) (z : ℂ) (hz : ‖z • K‖ < 1) :
    let D : Mat := 1 - z • K
    HasDerivAt (fun w : ℂ => (1-w • K).det)
      (-(D.det * (Ring.inverse D * K).trace)) z := by
  intro D
  let A := -(Ring.inverse D * K)
  have hu : IsUnit D := (Units.oneSub (z • K) hz).isUnit
  have hDA : D*A = -K := by
    unfold A
    rw [mul_neg,←mul_assoc,Ring.mul_inverse_cancel _ hu,one_mul]
  have he (w : ℂ) : (1-w • K).det = D.det*(1+(w-z) • A).det := by
    rw [←Matrix.det_mul,mul_add,mul_one,mul_smul_comm,hDA,smul_neg,sub_smul]
    congr 1
    dsimp only [D]
    abel
  simp_rw [he]
  have h := ((show HasDerivAt (fun w : ℂ => (1+w • A).det) A.trace (z-z) by
    simpa only [sub_self] using det_unit_tangent A).comp_sub_const z z).const_mul D.det
  simpa only [A,Matrix.trace_neg,mul_neg] using h

private def traceSeriesTerm (K : Mat (ι := ι)) (n : ℕ) (z : ℂ) : ℂ :=
  z^(n+1) * (K^(n+1)).trace / (n+1)

private theorem trace_term_deriv (K : Mat (ι := ι)) (n : ℕ) (z : ℂ) :
    HasDerivAt (traceSeriesTerm K n) (z^n * (K^(n+1)).trace) z := by
  have hn : (n:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h := (((hasDerivAt_pow (n+1) z).mul_const (K^(n+1)).trace).div_const ((n:ℂ)+1))
  convert h using 1
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
  field_simp

private theorem trace_series_deriv [Nonempty ι] (K : Mat (ι := ι)) {R : ℝ} (hR : 0 < R)
    (hr : R*‖K‖ < 1) (z : ℂ) (hz : z ∈ ball 0 R) :
    HasDerivAt (fun w => ∑' n, traceSeriesTerm K n w) (Ring.inverse (1-z • K) * K).trace z := by
  let τ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  let u := fun n : ℕ => (‖τ‖*‖K‖)*(R*‖K‖)^n
  have hU : Summable u := (summable_geometric_of_lt_one (mul_nonneg hR.le (norm_nonneg _)) hr).mul_left _
  have hB (n : ℕ) (w : ℂ) (hw : w ∈ ball 0 R) :
      ‖w^n*(K^(n+1)).trace‖ ≤ u n := by
    have hx : ‖w‖ < R := by simpa only [mem_ball,dist_zero_right] using hw
    have ht : ‖(K^(n+1)).trace‖ ≤ ‖τ‖ * ‖K‖^(n+1) :=
      (τ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_pow_le K _) (norm_nonneg _))
    rw [norm_mul,norm_pow]
    apply (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx.le _) ht (norm_nonneg _) (by positivity)).trans_eq
    simp only [u,mul_pow,pow_succ]
    ring
  have hd := hasDerivAt_tsum_of_isPreconnected hU (isOpen_ball (x:=(0:ℂ)) (ε:=R))
    (convex_ball (0:ℂ) R).isPreconnected (fun n w _ => trace_term_deriv K n w)
    hB (mem_ball_self hR) (show Summable (fun n => traceSeriesTerm K n (0:ℂ)) by
      simpa [traceSeriesTerm] using (summable_zero : Summable (fun _ : ℕ => (0:ℂ)))) hz
  have hzk : ‖z • K‖ < 1 := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (le_of_lt (by simpa only [mem_ball,dist_zero_right] using hz : ‖z‖ < R))
      (norm_nonneg K)).trans_lt hr
  have hgeom : HasSum (fun n : ℕ => (z • K)^n) (Ring.inverse (1-z • K)) := by
    rw [show Ring.inverse (1-z • K) = ∑' n : ℕ, (z • K)^n from NormedRing.inverse_one_sub _ hzk]
    exact (summable_geometric_of_norm_lt_one hzk).hasSum
  have htrace := τ.hasSum (hgeom.mul_right K)
  have he (n : ℕ) : τ ((z • K)^n*K) = z^n*(K^(n+1)).trace := by
    change ((z • K)^n*K).trace = _
    rw [smul_pow,smul_mul_assoc,←pow_succ,Matrix.trace_smul,smul_eq_mul]
  simp only [he] at htrace
  rw [htrace.tsum_eq] at hd
  exact hd

/-- The equality holds for arbitrary complex slot matrices, including
nonnormal ones and rectangular pairs after forming their Schur product. -/
theorem twoBand_contractive_det_series (K : Mat (ι := ι)) (hK : ‖K‖ < 1) :
    (1-K).det = Complex.exp (-(∑' n : ℕ, (K^(n+1)).trace / (n+1))) := by
  rcases isEmpty_or_nonempty ι with h | h
  · simp [Matrix.trace]
  let R := 2/(1+‖K‖)
  have hp : 0 < 1+‖K‖ := by positivity
  have hR : 1 < R := (lt_div_iff₀ hp).mpr (by linarith)
  have hr : R*‖K‖ < 1 := by
    unfold R
    rw [div_mul_eq_mul_div,div_lt_iff₀ hp]
    linarith
  let L := fun z : ℂ => ∑' n, traceSeriesTerm K n z
  let f := fun z : ℂ => (1-z • K).det * Complex.exp (L z)
  have hf (z : ℂ) (hz : z ∈ ball 0 R) : HasDerivAt f 0 z := by
    have hzk : ‖z • K‖ < 1 := by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right (le_of_lt (by simpa only [mem_ball,dist_zero_right] using hz : ‖z‖ < R))
        (norm_nonneg K)).trans_lt hr
    have hd := schur_det_tangent K z hzk
    have hL := trace_series_deriv K (zero_lt_one.trans hR) hr z hz
    convert hd.mul (hL.cexp) using 1
    ring
  have hc := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0:ℂ) R).isPreconnected
    (fun z hz => (hf z hz).differentiableAt.differentiableWithinAt) (fun z hz => (hf z hz).deriv)
    (x := (1:ℂ)) (y := (0:ℂ)) (by simpa using hR) (mem_ball_self (zero_lt_one.trans hR))
  have hval : (1-K).det * Complex.exp (∑' n : ℕ, (K^(n+1)).trace/(n+1)) = 1 := by
    simpa [f,L,traceSeriesTerm] using hc
  rw [Complex.exp_neg]
  exact eq_inv_of_mul_eq_one_left hval

end UV.SectorPlane
