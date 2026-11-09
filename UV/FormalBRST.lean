import UV.BRST
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc

/-! Coefficientwise graded calculus on genuine formal power series.
The series variable is explicit: none of these results identifies exponential
degree with loop order. The normalized logarithm is constructed by stabilized
finite coefficients, not by a new logarithm or Ward-identity axiom. -/

noncomputable section
open scoped BigOperators

namespace UV

variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

def formalLinearMap (L : A →ₗ[ℚ] B) : PowerSeries A →ₗ[ℚ] PowerSeries B where
  toFun f := PowerSeries.mk (fun n => L (PowerSeries.coeff n f))
  map_add' f g := by ext n; simp
  map_smul' r f := by ext n; simp

@[simp] theorem formalLinearMap_coeff (L : A →ₗ[ℚ] B) (f : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (formalLinearMap L f) = L (PowerSeries.coeff n f) := by
  simp [formalLinearMap]

def formalGrading (σ : GradingInvolution A) : GradingInvolution (PowerSeries A) where
  parity := PowerSeries.mapAlgHom σ.parity
  involutive f := by
    ext n
    simpa only [PowerSeries.mapAlgHom_apply, PowerSeries.coeff_map] using
      σ.involutive (PowerSeries.coeff n f)

@[simp] theorem formalGrading_coeff (σ : GradingInvolution A) (f : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n ((formalGrading σ).parity f) = σ.parity (PowerSeries.coeff n f) := rfl

def formalGradedDerivative {σ : GradingInvolution A} {odd : Bool}
    (D : GradedDerivative σ odd) : GradedDerivative (formalGrading σ) odd where
  d := formalLinearMap D.d
  leibniz f g := by
    ext n
    rw [formalLinearMap_coeff, PowerSeries.coeff_mul, map_sum]
    simp_rw [D.leibniz]
    rw [Finset.sum_add_distrib]
    cases odd <;>
      simp only [Bool.false_eq_true, ite_false, ite_true,
        map_add, PowerSeries.coeff_mul, formalLinearMap_coeff, formalGrading_coeff]
  homogeneous f := by
    ext n
    simp only [formalLinearMap_coeff, formalGrading_coeff, PowerSeries.coeff_smul]
    exact D.homogeneous _

@[simp] theorem formalGradedDerivative_coeff {σ : GradingInvolution A} {odd : Bool}
    (D : GradedDerivative σ odd) (f : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n ((formalGradedDerivative D).d f) = D.d (PowerSeries.coeff n f) :=
  formalLinearMap_coeff D.d f n

def formalClosedBRST {σ : GradingInvolution A} (s : ClosedBRST σ) :
    ClosedBRST (formalGrading σ) where
  derivative := formalGradedDerivative s.derivative
  nilpotent f := by ext n; simp [s.nilpotent]
  parity_odd f := by
    ext n
    simp only [formalGradedDerivative_coeff, formalGrading_coeff, map_neg]
    exact s.parity_odd _

/-- Formal Ward closure is exactly coefficientwise Ward closure. The index
here can be chosen to be actual loop degree, independently of other series. -/
theorem formal_ward_iff {σ : GradingInvolution A} {odd : Bool}
    (D : GradedDerivative σ odd) (f : PowerSeries A) :
    (formalGradedDerivative D).d f = 0 ↔ ∀ n, D.d (PowerSeries.coeff n f) = 0 := by
  rw [← PowerSeries.forall_coeff_eq_zero]
  simp only [formalGradedDerivative_coeff]

omit [Algebra ℚ A] in
/-- A positive-order formal series has no coefficient in a power above the
selected degree. This is the stabilization used for the infinite logarithm. -/
theorem formal_positive_power_coeff_zero {f : PowerSeries A}
    (hf : PowerSeries.constantCoeff f = 0) {n k : ℕ} (hnk : n < k) :
    PowerSeries.coeff n (f^k) = 0 := by
  have ho : (1 : ℕ∞) ≤ f.order := by
    apply PowerSeries.nat_le_order
    intro j hj
    have hj0 : j = 0 := by omega
    simpa only [hj0, PowerSeries.coeff_zero_eq_constantCoeff_apply] using hf
  have hk : (k : ℕ∞) ≤ (f^k).order := by
    calc
      (k : ℕ∞) = k • (1 : ℕ∞) := by simp
      _ ≤ k • f.order := nsmul_le_nsmul_right ho k
      _ ≤ (f^k).order := PowerSeries.le_order_pow f k
  exact PowerSeries.coeff_of_lt_order n ((by exact_mod_cast hnk : (n : ℕ∞) < k).trans_le hk)

def formalConnectedLog (z : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk (fun n => PowerSeries.coeff n (finiteLogPolynomial z (n+1)))

@[simp] theorem formalConnectedLog_coeff (z : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (formalConnectedLog z) =
      PowerSeries.coeff n (finiteLogPolynomial z (n+1)) := by simp [formalConnectedLog]

/-- Every admissible finite truncation has the same coefficient as the full
formal logarithm. Thus this construction represents the complete normalized
formal logarithm, and is not a choice of one finite polynomial. -/
theorem formalConnectedLog_coeff_stable {z : PowerSeries A}
    (hz : PowerSeries.constantCoeff z = 1) {n N : ℕ} (hN : n < N) :
    PowerSeries.coeff n (formalConnectedLog z) =
      PowerSeries.coeff n (finiteLogPolynomial z N) := by
  have hpos : PowerSeries.constantCoeff (z-1) = 0 := by simp [hz]
  simp only [formalConnectedLog_coeff, finiteLogPolynomial, map_sum, PowerSeries.coeff_smul]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_iff.mpr hN))
  intro k hkN hkn
  have hnk : n < k+1 := by
    simp only [Finset.mem_range] at hkN hkn
    omega
  rw [formal_positive_power_coeff_zero hpos hnk, smul_zero]

theorem formalConnectedLog_constantCoeff {z : PowerSeries A}
    (hz : PowerSeries.constantCoeff z = 1) :
    PowerSeries.constantCoeff (formalConnectedLog z) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, formalConnectedLog_coeff]
  simp [finiteLogPolynomial, PowerSeries.coeff_zero_eq_constantCoeff_apply, hz]

/-- The connected Ward identity for the complete formal logarithm follows
from partition Ward closure and the proved stabilization. No analytic
logarithm rule or connected Ward conclusion is supplied. -/
theorem formal_connected_log_ward {σ : GradingInvolution A} {odd : Bool}
    (D : GradedDerivative σ odd) {z : PowerSeries A}
    (hz : PowerSeries.constantCoeff z = 1)
    (hWard : (formalGradedDerivative D).d z = 0) :
    (formalGradedDerivative D).d (formalConnectedLog z) = 0 := by
  apply PowerSeries.ext
  intro n
  rw [formalGradedDerivative_coeff, formalConnectedLog_coeff_stable hz (Nat.lt_succ_self n)]
  have h := congrArg (PowerSeries.coeff n)
    (finite_log_polynomial_ward (formalGradedDerivative D) hWard (n+1))
  simpa only [formalGradedDerivative_coeff, map_zero] using h

/-- The actual expectation of every exponential coefficient. Its variable
counts exponential degree; it is deliberately not called the loop variable. -/
def formalPartitionSeries (expectation : A →ₗ[ℚ] B) (X : A) : PowerSeries B :=
  PowerSeries.mk (fun n => expectation (formalExpCoefficient X n))

@[simp] theorem formalPartitionSeries_coeff (expectation : A →ₗ[ℚ] B) (X : A) (n : ℕ) :
    PowerSeries.coeff n (formalPartitionSeries expectation X) =
      expectation (formalExpCoefficient X n) := by simp [formalPartitionSeries]

theorem formalPartitionSeries_constantCoeff (expectation : A →ₗ[ℚ] B) (X : A) :
    PowerSeries.constantCoeff (formalPartitionSeries expectation X) = expectation 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, formalPartitionSeries_coeff]
  simp [formalExpCoefficient]

/-- Invariant expectation and differentiation under that expectation derive
Ward closure of the entire partition series. The exponent identity concerns
the constructed BRST/source differential, never the partition function. -/
theorem formal_partition_series_ward
    {σA : GradingInvolution A} {σB : GradingInvolution B}
    (s : ClosedBRST σA) (Q : GradedDerivative σA true) (D : GradedDerivative σB true)
    (expectation : A →ₗ[ℚ] B) (X : A)
    (hX : Q.d X = -s.derivative.d X)
    (hinvariant : ∀ x, expectation (s.derivative.d x) = 0)
    (hdifferentiate : ∀ x, D.d (expectation x) = expectation (Q.d x)) :
    (formalGradedDerivative D).d (formalPartitionSeries expectation X) = 0 := by
  rw [formal_ward_iff]
  intro n
  rw [formalPartitionSeries_coeff, hdifferentiate]
  have hpower := opposite_graded_derivatives_power s.derivative Q hX n
  have hcoeff : Q.d (formalExpCoefficient X n) =
      -s.derivative.d (formalExpCoefficient X n) := by
    unfold formalExpCoefficient
    rw [map_smul, map_smul, hpower, smul_neg]
  rw [hcoeff, map_neg, hinvariant, neg_zero]

/-- The completed connected logarithm is constructed from the actual
partition series and inherits Ward closure. This theorem has no truncation
order and no connected Ward identity among its hypotheses. -/
theorem formal_partition_connected_ward
    {σA : GradingInvolution A} {σB : GradingInvolution B}
    (s : ClosedBRST σA) (Q : GradedDerivative σA true) (D : GradedDerivative σB true)
    (expectation : A →ₗ[ℚ] B) (X : A)
    (hX : Q.d X = -s.derivative.d X)
    (hinvariant : ∀ x, expectation (s.derivative.d x) = 0)
    (hdifferentiate : ∀ x, D.d (expectation x) = expectation (Q.d x))
    (hnormalized : expectation 1 = 1) :
    (formalGradedDerivative D).d
      (formalConnectedLog (formalPartitionSeries expectation X)) = 0 := by
  apply formal_connected_log_ward D
  · rw [formalPartitionSeries_constantCoeff, hnormalized]
  · exact formal_partition_series_ward s Q D expectation X hX hinvariant hdifferentiate

/-- Parity of the actual partition series is derived from the even exponent
and a parity-respecting expectation. -/
theorem formalPartitionSeries_even
    {σA : GradingInvolution A} {σB : GradingInvolution B}
    (expectation : A →ₗ[ℚ] B) {X : A} (hX : σA.parity X = X)
    (hexpectation : ∀ x, σB.parity (expectation x) = expectation (σA.parity x)) :
    (formalGrading σB).parity (formalPartitionSeries expectation X) =
      formalPartitionSeries expectation X := by
  ext n
  rw [formalGrading_coeff, formalPartitionSeries_coeff, hexpectation]
  simp only [formalExpCoefficient, map_smul, map_pow, hX]

theorem formalConnectedLog_even {σ : GradingInvolution A} {z : PowerSeries A}
    (hz : (formalGrading σ).parity z = z) :
    (formalGrading σ).parity (formalConnectedLog z) = formalConnectedLog z := by
  ext n
  rw [formalGrading_coeff, formalConnectedLog_coeff]
  have h : (formalGrading σ).parity (finiteLogPolynomial z (n+1)) =
      finiteLogPolynomial z (n+1) := by simp [finiteLogPolynomial, hz]
  simpa only [formalGrading_coeff] using congrArg (PowerSeries.coeff n) h

end UV
