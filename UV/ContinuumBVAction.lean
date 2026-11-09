import UV.FormalBRSTLog
import UV.WeakFunctionalIntegral

/-! The actual signed continuum BV action and its source variation.
All contractions are genuine weak integrals. Canonical source/antifield
rules are imposed only on generators, and the BRST/source identities of
the constructed action and exponential are derived from them. -/

noncomputable section
open MeasureTheory

namespace UV

variable {X A : Type*} [MeasurableSpace X]
  [Ring A] [Algebra ℚ A] [Algebra ℝ A] [TopologicalSpace A] [SeparatingDual ℝ A]

theorem weakIntegral_gradedDerivative (μ : Measure X) {σ : GradingInvolution A}
    {odd : Bool} (D : GradedDerivative σ odd) (L : A →L[ℝ] A)
    (hL : ∀ f, L f = D.d f) {f : X → A} (hI : WeakIntegrable μ f) :
    D.d (weakIntegral μ f) = weakIntegral μ (fun x => D.d (f x)) := by
  calc
    _ = L (weakIntegral μ f) := (hL _).symm
    _ = weakIntegral μ (fun x => L (f x)) := (weakIntegral_map L hI).symm
    _ = _ := weakIntegral_congr (fun x => hL (f x))

theorem weakIntegral_parity (μ : Measure X) (σ : GradingInvolution A)
    (L : A →L[ℝ] A) (hL : ∀ f, L f = σ.parity f)
    {f : X → A} (hI : WeakIntegrable μ f) :
    σ.parity (weakIntegral μ f) = weakIntegral μ (fun x => σ.parity (f x)) := by
  calc
    _ = L (weakIntegral μ f) := (hL _).symm
    _ = weakIntegral μ (fun x => L (f x)) := (weakIntegral_map L hI).symm
    _ = _ := weakIntegral_congr (fun x => hL (f x))

def continuumBVAction (μ : Measure X) {σ : GradingInvolution A} (s : ClosedBRST σ)
    (ε : X → Bool) (S0 Ψ : A) (φ antifield : X → A) : A :=
  S0 + s.derivative.d Ψ + weakIntegral μ
    (fun x => koszulSign (ε x) • (antifield x * s.derivative.d (φ x)))

def continuumSourcePairing (μ : Measure X) (J φ : X → A) : A :=
  weakIntegral μ (fun x => J x * φ x)

def continuumBRSTSourceVariation (μ : Measure X) {σ : GradingInvolution A}
    (s : ClosedBRST σ) (ε : X → Bool) (J φ : X → A) : A :=
  weakIntegral μ (fun x => koszulSign (ε x) • (J x * s.derivative.d (φ x)))

theorem continuum_bv_action_brst_invariant (μ : Measure X) {σ : GradingInvolution A}
    (s : ClosedBRST σ) (Ls : A →L[ℝ] A) (hLs : ∀ f, Ls f = s.derivative.d f)
    (ε : X → Bool) (S0 Ψ : A) (φ antifield : X → A)
    (hS : s.derivative.d S0 = 0) (haf : ∀ x, s.derivative.d (antifield x) = 0)
    (hI : WeakIntegrable μ (fun x => koszulSign (ε x) •
      (antifield x * s.derivative.d (φ x)))) :
    s.derivative.d (continuumBVAction μ s ε S0 Ψ φ antifield) = 0 := by
  rw [continuumBVAction, map_add, map_add, hS, s.nilpotent,
    zero_add, zero_add, weakIntegral_gradedDerivative μ s.derivative Ls hLs hI]
  have hz : (fun x => s.derivative.d (koszulSign (ε x) •
      (antifield x * s.derivative.d (φ x)))) = fun _ => (0 : A) := by
    funext x
    rw [map_smul, s.derivative.leibniz, haf, s.nilpotent, zero_mul, mul_zero, add_zero, smul_zero]
  rw [hz, weakIntegral_zero]

theorem continuum_source_pairing_brst (μ : Measure X) {σ : GradingInvolution A}
    (s : ClosedBRST σ) (Ls : A →L[ℝ] A) (hLs : ∀ f, Ls f = s.derivative.d f)
    (ε : X → Bool) (J φ : X → A)
    (hJ : ∀ x, s.derivative.d (J x) = 0)
    (hparity : ∀ x, σ.parity (J x) = koszulSign (ε x) • J x)
    (hI : WeakIntegrable μ (fun x => J x * φ x)) :
    s.derivative.d (continuumSourcePairing μ J φ) = continuumBRSTSourceVariation μ s ε J φ := by
  rw [continuumSourcePairing, weakIntegral_gradedDerivative μ s.derivative Ls hLs hI]
  apply weakIntegral_congr
  intro x
  rw [s.derivative.leibniz, hJ, zero_mul, zero_add, if_pos rfl, hparity, smul_mul_assoc]

theorem continuum_bv_source_variation (μ : Measure X) {σ : GradingInvolution A}
    (s : ClosedBRST σ) (Q : GradedDerivative σ true)
    (LQ : A →L[ℝ] A) (hLQ : ∀ f, LQ f = Q.d f)
    (ε : X → Bool) (S0 Ψ : A) (φ antifield J : X → A)
    (hQS : Q.d S0 = 0) (hQΨ : Q.d (s.derivative.d Ψ) = 0)
    (hQaf : ∀ x, Q.d (antifield x) = J x)
    (hQvar : ∀ x, Q.d (s.derivative.d (φ x)) = 0)
    (hI : WeakIntegrable μ (fun x => koszulSign (ε x) •
      (antifield x * s.derivative.d (φ x)))) :
    Q.d (continuumBVAction μ s ε S0 Ψ φ antifield) = continuumBRSTSourceVariation μ s ε J φ := by
  rw [continuumBVAction, map_add, map_add, hQS, hQΨ,
    zero_add, zero_add, weakIntegral_gradedDerivative μ Q LQ hLQ hI]
  apply weakIntegral_congr
  intro x
  rw [map_smul, Q.leibniz, hQaf, hQvar, mul_zero, add_zero]

theorem continuum_source_pairing_source_ward_zero (μ : Measure X) {σ : GradingInvolution A}
    (Q : GradedDerivative σ true) (LQ : A →L[ℝ] A) (hLQ : ∀ f, LQ f = Q.d f)
    (J φ : X → A) (hQJ : ∀ x, Q.d (J x) = 0) (hQφ : ∀ x, Q.d (φ x) = 0)
    (hI : WeakIntegrable μ (fun x => J x * φ x)) :
    Q.d (continuumSourcePairing μ J φ) = 0 := by
  rw [continuumSourcePairing, weakIntegral_gradedDerivative μ Q LQ hLQ hI]
  have hz : (fun x => Q.d (J x * φ x)) = fun _ => (0 : A) := by
    funext x
    rw [Q.leibniz, hQJ, hQφ, zero_mul, mul_zero, add_zero]
  rw [hz, weakIntegral_zero]

/-- The source/BRST exponent identity is derived for the actual constructed
continuum action. None of its source or action Ward conclusions is assumed. -/
theorem continuum_bv_exponent_opposite_derivatives (μ : Measure X) {σ : GradingInvolution A}
    (s : ClosedBRST σ) (Q : GradedDerivative σ true)
    (Ls LQ : A →L[ℝ] A) (hLs : ∀ f, Ls f = s.derivative.d f) (hLQ : ∀ f, LQ f = Q.d f)
    (ε : X → Bool) (S0 Ψ : A) (φ antifield J : X → A)
    (hS : s.derivative.d S0 = 0) (haf : ∀ x, s.derivative.d (antifield x) = 0)
    (hJ : ∀ x, s.derivative.d (J x) = 0)
    (hparity : ∀ x, σ.parity (J x) = koszulSign (ε x) • J x)
    (hQS : Q.d S0 = 0) (hQΨ : Q.d (s.derivative.d Ψ) = 0)
    (hQaf : ∀ x, Q.d (antifield x) = J x)
    (hQvar : ∀ x, Q.d (s.derivative.d (φ x)) = 0)
    (hQJ : ∀ x, Q.d (J x) = 0) (hQφ : ∀ x, Q.d (φ x) = 0)
    (hIaf : WeakIntegrable μ (fun x => koszulSign (ε x) •
      (antifield x * s.derivative.d (φ x))))
    (hIpair : WeakIntegrable μ (fun x => J x * φ x)) :
    Q.d (-continuumBVAction μ s ε S0 Ψ φ antifield + continuumSourcePairing μ J φ) =
      -s.derivative.d (-continuumBVAction μ s ε S0 Ψ φ antifield + continuumSourcePairing μ J φ) := by
  rw [map_add, map_neg, continuum_bv_source_variation μ s Q LQ hLQ ε S0 Ψ φ antifield J hQS hQΨ hQaf hQvar hIaf,
    continuum_source_pairing_source_ward_zero μ Q LQ hLQ J φ hQJ hQφ hIpair,
    map_add, map_neg, continuum_bv_action_brst_invariant μ s Ls hLs ε S0 Ψ φ antifield hS haf hIaf,
    continuum_source_pairing_brst μ s Ls hLs ε J φ hJ hparity hIpair]
  simp

theorem continuum_bv_action_even (μ : Measure X) {σ : GradingInvolution A}
    (s : ClosedBRST σ) (Lσ : A →L[ℝ] A) (hLσ : ∀ f, Lσ f = σ.parity f)
    (ε : X → Bool) (S0 Ψ : A) (φ antifield : X → A)
    (hS : σ.parity S0 = S0) (hΨ : σ.parity Ψ = -Ψ)
    (hφ : ∀ x, σ.parity (φ x) = koszulSign (ε x) • φ x)
    (haf : ∀ x, σ.parity (antifield x) = koszulSign (!(ε x)) • antifield x)
    (hI : WeakIntegrable μ (fun x => koszulSign (ε x) •
      (antifield x * s.derivative.d (φ x)))) :
    σ.parity (continuumBVAction μ s ε S0 Ψ φ antifield) =
      continuumBVAction μ s ε S0 Ψ φ antifield := by
  have hg : σ.parity (s.derivative.d Ψ) = s.derivative.d Ψ := by
    have h := s.parity_odd Ψ
    rw [hΨ, map_neg] at h
    exact (neg_inj.mp h).symm
  have hv : ∀ x, σ.parity (s.derivative.d (φ x)) =
      -(koszulSign (ε x) • s.derivative.d (φ x)) := by
    intro x
    have h := congrArg Neg.neg (s.parity_odd (φ x))
    have hh : σ.parity (s.derivative.d (φ x)) = -s.derivative.d (σ.parity (φ x)) := by
      simpa only [neg_neg] using h.symm
    rw [hφ, map_smul] at hh
    exact hh
  rw [continuumBVAction, map_add, map_add, hS, hg, weakIntegral_parity μ σ Lσ hLσ hI]
  congr 1
  apply weakIntegral_congr
  intro x
  rw [map_smul, map_mul, haf, hv, koszulSign_not]
  simp only [neg_smul, neg_mul_neg, smul_mul_assoc, mul_smul_comm,
    smul_smul, koszulSign_square, one_smul]

theorem continuum_source_pairing_even (μ : Measure X) {σ : GradingInvolution A}
    (Lσ : A →L[ℝ] A) (hLσ : ∀ f, Lσ f = σ.parity f)
    (ε : X → Bool) (J φ : X → A)
    (hJ : ∀ x, σ.parity (J x) = koszulSign (ε x) • J x)
    (hφ : ∀ x, σ.parity (φ x) = koszulSign (ε x) • φ x)
    (hI : WeakIntegrable μ (fun x => J x * φ x)) :
    σ.parity (continuumSourcePairing μ J φ) = continuumSourcePairing μ J φ := by
  rw [continuumSourcePairing, weakIntegral_parity μ σ Lσ hLσ hI]
  apply weakIntegral_congr
  intro x
  rw [map_mul, hJ, hφ, smul_mul_assoc, mul_smul_comm, smul_smul,
    koszulSign_square, one_smul]

theorem continuum_bv_exponent_even (μ : Measure X) {σ : GradingInvolution A}
    (s : ClosedBRST σ) (Lσ : A →L[ℝ] A) (hLσ : ∀ f, Lσ f = σ.parity f)
    (ε : X → Bool) (S0 Ψ : A) (φ antifield J : X → A)
    (hS : σ.parity S0 = S0) (hΨ : σ.parity Ψ = -Ψ)
    (hJ : ∀ x, σ.parity (J x) = koszulSign (ε x) • J x)
    (hφ : ∀ x, σ.parity (φ x) = koszulSign (ε x) • φ x)
    (haf : ∀ x, σ.parity (antifield x) = koszulSign (!(ε x)) • antifield x)
    (hIaf : WeakIntegrable μ (fun x => koszulSign (ε x) •
      (antifield x * s.derivative.d (φ x))))
    (hIpair : WeakIntegrable μ (fun x => J x * φ x)) :
    σ.parity (-continuumBVAction μ s ε S0 Ψ φ antifield + continuumSourcePairing μ J φ) =
      -continuumBVAction μ s ε S0 Ψ φ antifield + continuumSourcePairing μ J φ := by
  rw [map_add, map_neg, continuum_bv_action_even μ s Lσ hLσ ε S0 Ψ φ antifield hS hΨ hφ haf hIaf,
    continuum_source_pairing_even μ Lσ hLσ ε J φ hJ hφ hIpair]

end UV
