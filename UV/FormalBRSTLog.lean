import UV.FormalBRST
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! A local analytic logarithm of an arbitrary invertible formal body.
Its body logarithm is the actual convergent Taylor series about a nonzero
complex scalar center. Ward closure follows by continuous passage from
polynomials. No logarithmic differentiation or connected Ward identity is
included in the data. -/

noncomputable section
open scoped BigOperators Topology

namespace UV

variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem gradedDerivative_inverse_of_zero {σ : GradingInvolution A} {odd : Bool}
    (D : GradedDerivative σ odd) {b : A} (hb : IsUnit b) (hDb : D.d b = 0) :
    D.d (Ring.inverse b) = 0 := by
  have hu : IsUnit (if odd then σ.parity b else b) := by
    cases odd
    · exact hb
    · exact hb.map σ.parity.toRingHom
  have hp := D.leibniz b (Ring.inverse b)
  rw [Ring.mul_inverse_cancel b hb, gradedDerivative_one, hDb, zero_mul, zero_add] at hp
  apply hu.mul_left_cancel
  simpa only [mul_zero] using hp.symm

theorem formalGradedDerivative_C {σ : GradingInvolution A} {odd : Bool}
    (D : GradedDerivative σ odd) (b : A) :
    (formalGradedDerivative D).d (PowerSeries.C b) = PowerSeries.C (D.d b) := by
  ext n
  simp only [formalGradedDerivative_coeff, PowerSeries.coeff_C]
  split_ifs <;> simp

theorem formalGrading_C (σ : GradingInvolution A) (b : A) :
    (formalGrading σ).parity (PowerSeries.C b) = PowerSeries.C (σ.parity b) := by
  ext n
  simp only [formalGrading_coeff, PowerSeries.coeff_C]
  split_ifs <;> simp

section AnalyticBody

variable [TopologicalSpace A] [T2Space A] [Algebra ℂ A]

def localBodyLogTerm (c : ℂ) (b : A) (n : ℕ) : A :=
  (((-1 : ℚ)^n)/(n+1 : ℚ)) • (algebraMap ℂ A c⁻¹ * b-1)^(n+1)

def localBodyLog (c : ℂ) (b : A) : A :=
  algebraMap ℂ A (Complex.log c) + ∑' n, localBodyLogTerm c b n

omit [T2Space A] in
/-- Every finite Grassmann nilpotent logarithm is admitted without a norm
smallness restriction; the complete series is genuinely a finite sum. -/
theorem localBodyLogTerm_summable_of_nilpotent {c : ℂ} {b : A}
    (hnil : IsNilpotent (algebraMap ℂ A c⁻¹ * b-1)) :
    Summable (localBodyLogTerm c b) := by
  obtain ⟨N, hN⟩ := hnil
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro n hn
  have hnN : N ≤ n+1 := by simp only [Finset.mem_range] at hn; omega
  rw [localBodyLogTerm, pow_eq_zero_of_le hnN hN, smul_zero]

theorem local_body_log_ward {σ : GradingInvolution A} {odd : Bool}
    (D : GradedDerivative σ odd) (hD : Continuous D.d)
    (hscalar : ∀ c : ℂ, D.d (algebraMap ℂ A c) = 0)
    {c : ℂ} {b : A} (hDb : D.d b = 0)
    (hsum : Summable (localBodyLogTerm c b)) : D.d (localBodyLog c b) = 0 := by
  have hbase : D.d (algebraMap ℂ A c⁻¹ * b-1) = 0 := by
    rw [map_sub, D.leibniz, hscalar, hDb, zero_mul, mul_zero,
      add_zero, gradedDerivative_one, sub_zero]
  have hterm : ∀ n, D.d (localBodyLogTerm c b n) = 0 := by
    intro n
    rw [localBodyLogTerm, map_smul, gradedDerivative_power_of_zero D hbase, smul_zero]
  have hs := hsum.map_tsum D.d.toAddMonoidHom hD
  change D.d (∑' n, localBodyLogTerm c b n) = ∑' n, D.d (localBodyLogTerm c b n) at hs
  simp_rw [hterm] at hs
  rw [localBodyLog, map_add, hscalar]
  simpa only [zero_add, tsum_zero] using hs

theorem local_body_log_even (σ : GradingInvolution A) (hσ : Continuous σ.parity)
    (hscalar : ∀ c : ℂ, σ.parity (algebraMap ℂ A c) = algebraMap ℂ A c)
    {c : ℂ} {b : A} (hb : σ.parity b = b)
    (hsum : Summable (localBodyLogTerm c b)) : σ.parity (localBodyLog c b) = localBodyLog c b := by
  have hterm : ∀ n, σ.parity (localBodyLogTerm c b n) = localBodyLogTerm c b n := by
    intro n
    simp only [localBodyLogTerm, map_smul, map_pow, map_sub, map_mul, hscalar, hb, map_one]
  have hs := hsum.map_tsum σ.parity.toAddMonoidHom hσ
  change σ.parity (∑' n, localBodyLogTerm c b n) = ∑' n, σ.parity (localBodyLogTerm c b n) at hs
  simp_rw [hterm] at hs
  rw [localBodyLog, map_add, hscalar, hs]

def formalLocalConnectedLog (z : PowerSeries A) (c : ℂ) : PowerSeries A :=
  PowerSeries.C (localBodyLog c (PowerSeries.constantCoeff z)) +
    formalConnectedLog (PowerSeries.C (Ring.inverse (PowerSeries.constantCoeff z)) * z)

/-- General invertible-body connected closure. The full body logarithm is
an actual locally admitted convergent series and the positive formal part
uses the proved coefficient stabilization. In particular the body need not
be 1, and its Ward identity is derived from the partition series. -/
theorem formal_local_connected_log_ward {σ : GradingInvolution A} {odd : Bool}
    (D : GradedDerivative σ odd) (hD : Continuous D.d)
    (hscalar : ∀ c : ℂ, D.d (algebraMap ℂ A c) = 0)
    {z : PowerSeries A} {c : ℂ}
    (hbody : IsUnit (PowerSeries.constantCoeff z))
    (hlog : Summable (localBodyLogTerm c (PowerSeries.constantCoeff z)))
    (hWard : (formalGradedDerivative D).d z = 0) :
    (formalGradedDerivative D).d (formalLocalConnectedLog z c) = 0 := by
  have hDb : D.d (PowerSeries.constantCoeff z) = 0 := by
    have h := congrArg (PowerSeries.coeff 0) hWard
    simpa only [formalGradedDerivative_coeff, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_zero] using h
  have hDi := gradedDerivative_inverse_of_zero D hbody hDb
  have hnorm : PowerSeries.constantCoeff
      (PowerSeries.C (Ring.inverse (PowerSeries.constantCoeff z)) * z) = 1 := by
    simp only [map_mul, PowerSeries.constantCoeff_C]
    exact Ring.inverse_mul_cancel _ hbody
  have hnormWard : (formalGradedDerivative D).d
      (PowerSeries.C (Ring.inverse (PowerSeries.constantCoeff z)) * z) = 0 := by
    rw [(formalGradedDerivative D).leibniz, formalGradedDerivative_C, hDi, map_zero,
      zero_mul, hWard, mul_zero, add_zero]
  rw [formalLocalConnectedLog, map_add, formalGradedDerivative_C,
    local_body_log_ward D hD hscalar hDb hlog, map_zero,
    formal_connected_log_ward D hnorm hnormWard, add_zero]

theorem formal_local_connected_log_even (σ : GradingInvolution A)
    (hσ : Continuous σ.parity)
    (hscalar : ∀ c : ℂ, σ.parity (algebraMap ℂ A c) = algebraMap ℂ A c)
    {z : PowerSeries A} {c : ℂ} (hbody : IsUnit (PowerSeries.constantCoeff z))
    (hlog : Summable (localBodyLogTerm c (PowerSeries.constantCoeff z)))
    (heven : (formalGrading σ).parity z = z) :
    (formalGrading σ).parity (formalLocalConnectedLog z c) = formalLocalConnectedLog z c := by
  have hb : σ.parity (PowerSeries.constantCoeff z) = PowerSeries.constantCoeff z := by
    have h := congrArg (PowerSeries.coeff 0) heven
    simpa only [formalGrading_coeff, PowerSeries.coeff_zero_eq_constantCoeff_apply] using h
  have hi : σ.parity (Ring.inverse (PowerSeries.constantCoeff z)) =
      Ring.inverse (PowerSeries.constantCoeff z) := by
    have hm : PowerSeries.constantCoeff z * σ.parity (Ring.inverse (PowerSeries.constantCoeff z)) = 1 := by
      calc
        _ = σ.parity (PowerSeries.constantCoeff z) * σ.parity (Ring.inverse (PowerSeries.constantCoeff z)) := by rw [hb]
        _ = σ.parity (PowerSeries.constantCoeff z * Ring.inverse (PowerSeries.constantCoeff z)) := (map_mul _ _ _).symm
        _ = 1 := by rw [Ring.mul_inverse_cancel _ hbody, map_one]
    calc
      _ = (Ring.inverse (PowerSeries.constantCoeff z) * PowerSeries.constantCoeff z) *
          σ.parity (Ring.inverse (PowerSeries.constantCoeff z)) := by
        rw [Ring.inverse_mul_cancel _ hbody, one_mul]
      _ = _ := by rw [mul_assoc, hm, mul_one]
  have hn : (formalGrading σ).parity
      (PowerSeries.C (Ring.inverse (PowerSeries.constantCoeff z)) * z) =
      PowerSeries.C (Ring.inverse (PowerSeries.constantCoeff z)) * z := by
    rw [map_mul, formalGrading_C, hi, heven]
  rw [formalLocalConnectedLog, map_add, formalGrading_C,
    local_body_log_even σ hσ hscalar hb hlog, formalConnectedLog_even hn]

end AnalyticBody

section CompletedPartition

variable [TopologicalSpace A] [T2Space A] [IsTopologicalAddGroup A]
variable {B : Type*} [Ring B] [Algebra ℚ B]

def completedBRSTExp (X : A) : A := ∑' n, formalExpCoefficient X n

def completedBRSTPartition (expectation : A →ₗ[ℚ] B) (X : A) : B :=
  expectation (completedBRSTExp X)

/-- On a genuine completed exponential domain, invariant expectation gives
the actual partition Ward identity. The series degree is summed out here;
it is not relabeled as perturbative loop degree. -/
theorem completed_partition_ward
    {σA : GradingInvolution A} {σB : GradingInvolution B}
    (s : ClosedBRST σA) (Q : GradedDerivative σA true) (D : GradedDerivative σB true)
    (expectation : A →ₗ[ℚ] B) (X : A)
    (hX : Q.d X = -s.derivative.d X)
    (hinvariant : ∀ x, expectation (s.derivative.d x) = 0)
    (hdifferentiate : ∀ x, D.d (expectation x) = expectation (Q.d x))
    (hQ : Continuous Q.d) (hs : Continuous s.derivative.d)
    (hexp : Summable (formalExpCoefficient X)) :
    D.d (completedBRSTPartition expectation X) = 0 := by
  have hcoeff : ∀ n, Q.d (formalExpCoefficient X n) = -s.derivative.d (formalExpCoefficient X n) := by
    intro n
    unfold formalExpCoefficient
    rw [map_smul, map_smul, opposite_graded_derivatives_power s.derivative Q hX, smul_neg]
  have hQsum := hexp.map_tsum Q.d.toAddMonoidHom hQ
  have hssum := hexp.map_tsum s.derivative.d.toAddMonoidHom hs
  change Q.d (∑' n, formalExpCoefficient X n) = ∑' n, Q.d (formalExpCoefficient X n) at hQsum
  change s.derivative.d (∑' n, formalExpCoefficient X n) = ∑' n, s.derivative.d (formalExpCoefficient X n) at hssum
  have hactual : Q.d (completedBRSTExp X) = -s.derivative.d (completedBRSTExp X) := by
    rw [completedBRSTExp, hQsum, hssum]
    simp_rw [hcoeff]
    exact tsum_neg
  rw [completedBRSTPartition, hdifferentiate, hactual, map_neg, hinvariant, neg_zero]

omit [IsTopologicalAddGroup A] in
theorem completed_partition_even
    {σA : GradingInvolution A} {σB : GradingInvolution B}
    (expectation : A →ₗ[ℚ] B) {X : A}
    (hX : σA.parity X = X) (hσA : Continuous σA.parity)
    (hexp : Summable (formalExpCoefficient X))
    (hEparity : ∀ x, σB.parity (expectation x) = expectation (σA.parity x)) :
    σB.parity (completedBRSTPartition expectation X) = completedBRSTPartition expectation X := by
  have hcoeff : ∀ n, σA.parity (formalExpCoefficient X n) = formalExpCoefficient X n := by
    intro n
    simp only [formalExpCoefficient, map_smul, map_pow, hX]
  have hsum := hexp.map_tsum σA.parity.toAddMonoidHom hσA
  change σA.parity (∑' n, formalExpCoefficient X n) = ∑' n, σA.parity (formalExpCoefficient X n) at hsum
  simp_rw [hcoeff] at hsum
  rw [completedBRSTPartition, hEparity, completedBRSTExp, hsum]

variable [TopologicalSpace B] [T2Space B] [Algebra ℂ B]

/-- The complete expectation/exponential/logarithm pipeline. Its assumptions
are the admitted invariant differentiation domain and actual convergence of
the two defining series. It supplies no partition or connected Ward result. -/
theorem completed_partition_connected_ward
    {σA : GradingInvolution A} {σB : GradingInvolution B}
    (s : ClosedBRST σA) (Q : GradedDerivative σA true) (D : GradedDerivative σB true)
    (expectation : A →ₗ[ℚ] B) (X : A)
    (hX : Q.d X = -s.derivative.d X)
    (hinvariant : ∀ x, expectation (s.derivative.d x) = 0)
    (hdifferentiate : ∀ x, D.d (expectation x) = expectation (Q.d x))
    (hQ : Continuous Q.d) (hs : Continuous s.derivative.d) (hD : Continuous D.d)
    (hscalar : ∀ c : ℂ, D.d (algebraMap ℂ B c) = 0)
    (hexp : Summable (formalExpCoefficient X)) {c : ℂ}
    (hlog : Summable (localBodyLogTerm c (completedBRSTPartition expectation X))) :
    D.d (localBodyLog c (completedBRSTPartition expectation X)) = 0 := by
  exact local_body_log_ward D hD hscalar
    (completed_partition_ward s Q D expectation X hX hinvariant hdifferentiate hQ hs hexp) hlog

omit [IsTopologicalAddGroup A] in
theorem completed_partition_connected_even
    {σA : GradingInvolution A} {σB : GradingInvolution B}
    (expectation : A →ₗ[ℚ] B) {X : A}
    (hX : σA.parity X = X) (hσA : Continuous σA.parity) (hσB : Continuous σB.parity)
    (hexp : Summable (formalExpCoefficient X))
    (hEparity : ∀ x, σB.parity (expectation x) = expectation (σA.parity x))
    (hscalar : ∀ c : ℂ, σB.parity (algebraMap ℂ B c) = algebraMap ℂ B c) {c : ℂ}
    (hlog : Summable (localBodyLogTerm c (completedBRSTPartition expectation X))) :
    σB.parity (localBodyLog c (completedBRSTPartition expectation X)) =
      localBodyLog c (completedBRSTPartition expectation X) := by
  exact local_body_log_even σB hσB hscalar
    (completed_partition_even expectation hX hσA hexp hEparity) hlog

end CompletedPartition

/-- The actual local analytic logarithm series converges whenever its
normalized body lies in the unit ball around one. -/
theorem localBodyLogTerm_summable_of_norm_lt_one
    {R : Type*} [NormedRing R] [NormOneClass R] [NormedAlgebra ℚ R] [Algebra ℂ R] [CompleteSpace R]
    {c : ℂ} {b : R} (hsmall : ‖algebraMap ℂ R c⁻¹ * b-1‖ < 1) :
    Summable (localBodyLogTerm c b) := by
  let y : R := algebraMap ℂ R c⁻¹ * b-1
  have hy : ‖y‖ < 1 := hsmall
  have hgeom : Summable (fun n : ℕ => ‖y‖^n) :=
    summable_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)] using hy)
  have hmajor : Summable (fun n : ℕ => ‖y‖^(n+1)) := by
    simpa only [pow_succ] using hgeom.mul_right ‖y‖
  apply hmajor.of_norm_bounded
  intro n
  change ‖((((-1 : ℚ)^n)/(n+1 : ℚ)) • y^(n+1))‖ ≤ ‖y‖^(n+1)
  have hw : ‖(((-1 : ℚ)^n)/(n+1 : ℚ))‖ ≤ 1 := by
    simp only [norm_div, norm_pow, norm_neg, norm_one, one_pow]
    rw [show (n : ℚ)+1 = ((n+1 : ℕ) : ℚ) by simp]
    rw [← Rat.norm_cast_real]
    simp only [Rat.cast_natCast, Real.norm_eq_abs,
      abs_of_nonneg (show (0:ℝ) ≤ (n+1:ℕ) by positivity)]
    simpa only [one_div_one] using one_div_le_one_div_of_le
      (by norm_num : (0:ℝ)<1) (show (1:ℝ) ≤ (n+1 : ℕ) by exact_mod_cast (Nat.le_add_left 1 n))
  calc
    _ = ‖(((-1 : ℚ)^n)/(n+1 : ℚ))‖ * ‖y^(n+1)‖ := norm_smul _ _
    _ ≤ ‖y‖^(n+1) := (mul_le_of_le_one_left (norm_nonneg _) hw).trans (norm_pow_le _ _)

/-- On the scalar unit-centered disk the constructed logarithm is literally
the ordinary principal complex logarithm. This fixes its analytic meaning. -/
theorem localBodyLog_complex_eq_log {b : ℂ} (hb : ‖b-1‖ < 1) :
    localBodyLog 1 b = Complex.log b := by
  let f : ℕ → ℂ := fun n => (-1)^(n+1) * (b-1)^n / n
  have hs : HasSum f (Complex.log (1+(b-1))) := Complex.hasSum_taylorSeries_log hb
  have hshift : HasSum (fun n => f (n+1)) (Complex.log b) := by
    simpa only [f, Finset.sum_range_one, pow_zero, mul_one, Nat.cast_zero,
      div_zero, sub_zero, add_sub_cancel] using (hasSum_nat_add_iff' 1).mpr hs
  have he : (fun n => f (n+1)) = localBodyLogTerm (1 : ℂ) b := by
    funext n
    simp only [f, localBodyLogTerm, inv_one, map_one, one_mul, Rat.smul_def,
      Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_add, Rat.cast_natCast]
    rw [show n+1+1=n+2 by omega, pow_add]
    norm_num
    ring
  rw [he] at hshift
  simpa only [localBodyLog, Complex.log_one, map_zero, zero_add] using hshift.tsum_eq

end UV
