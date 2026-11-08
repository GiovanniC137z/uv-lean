import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace UV

/-- The parity involution of a graded coefficient algebra. Homogeneous parity
is an eigenvalue condition; multiplication is not assumed commutative. -/
structure GradingInvolution (A : Type*) [Ring A] [Algebra ℚ A] where
  parity : A →ₐ[ℚ] A
  involutive : Function.Involutive parity

def koszulSign (odd : Bool) : ℚ := if odd then -1 else 1

theorem koszulSign_not (odd : Bool) : koszulSign (!odd) = -koszulSign odd := by
  cases odd <;> norm_num [koszulSign]

theorem koszulSign_square (odd : Bool) : koszulSign odd * koszulSign odd = 1 := by
  cases odd <;> norm_num [koszulSign]

/-- Left coordinate derivatives obey the graded Leibniz rule. -/
structure GradedDerivative {A : Type*} [Ring A] [Algebra ℚ A]
    (σ : GradingInvolution A) (odd : Bool) where
  d : A →ₗ[ℚ] A
  leibniz : ∀ x y, d (x * y) = d x * y + (if odd then σ.parity x else x) * d y
  homogeneous : ∀ x, d (σ.parity x) = koszulSign odd • σ.parity (d x)

/-- A closed off-shell BRST differential is odd and nilpotent on the whole
coefficient algebra, not merely on a selected numerical functional. -/
structure ClosedBRST {A : Type*} [Ring A] [Algebra ℚ A] (σ : GradingInvolution A) where
  derivative : GradedDerivative σ true
  nilpotent : ∀ x, derivative.d (derivative.d x) = 0
  parity_odd : ∀ x, derivative.d (σ.parity x) = -σ.parity (derivative.d x)

theorem gradedDerivative_one {A : Type*} [Ring A] [Algebra ℚ A]
    {σ : GradingInvolution A} {odd : Bool} (D : GradedDerivative σ odd) : D.d 1 = 0 := by
  have h := D.leibniz 1 1
  have hp : (if odd then σ.parity (1 : A) else 1) = 1 := by split <;> simp
  rw [one_mul, hp, mul_one, one_mul] at h
  exact (add_eq_left.mp h.symm)

def sourcePairing {I A : Type*} [Fintype I] [Ring A] (J φ : I → A) : A :=
  ∑ i, J i * φ i

/-- The source-first Koszul sign is derived from the odd Leibniz rule and
inert homogeneous sources. -/
theorem brst_source_first_sign {I A : Type*} [Fintype I] [Ring A] [Algebra ℚ A]
    {σ : GradingInvolution A} (s : ClosedBRST σ) (ε : I → Bool) (J φ : I → A)
    (hJ : ∀ i, s.derivative.d (J i) = 0)
    (hparity : ∀ i, σ.parity (J i) = koszulSign (ε i) • J i) :
    s.derivative.d (sourcePairing J φ) =
      ∑ i, koszulSign (ε i) • (J i * s.derivative.d (φ i)) := by
  unfold sourcePairing
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [s.derivative.leibniz, hJ i, zero_mul, zero_add, if_pos rfl, hparity i,
    smul_mul_assoc]

/-- The actual signed source-convention BV action for a closed algebra. -/
def bvMasterAction {I A : Type*} [Fintype I] [Ring A] [Algebra ℚ A]
    {σ : GradingInvolution A} (s : ClosedBRST σ) (ε : I → Bool)
    (S0 Ψ : A) (φ antifield : I → A) : A :=
  S0 + s.derivative.d Ψ + ∑ i, koszulSign (ε i) • (antifield i * s.derivative.d (φ i))

/-- Invariance is derived from the invariant completed action, exact gauge
fixing, inert antifields, and nilpotence. -/
theorem bvMasterAction_brst_invariant {I A : Type*} [Fintype I] [Ring A] [Algebra ℚ A]
    {σ : GradingInvolution A} (s : ClosedBRST σ) (ε : I → Bool)
    (S0 Ψ : A) (φ antifield : I → A) (hS : s.derivative.d S0 = 0)
    (haf : ∀ i, s.derivative.d (antifield i) = 0) :
    s.derivative.d (bvMasterAction s ε S0 Ψ φ antifield) = 0 := by
  simp only [bvMasterAction, map_add, map_sum, map_smul, hS, s.nilpotent, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  rw [s.derivative.leibniz, haf i, s.nilpotent, zero_mul, mul_zero, add_zero, smul_zero]

/-- Canonical antifield coordinates, including independence of fields and
sources. These are coordinate derivative laws, not a Ward identity. -/
structure BVCoordinates {I A : Type*} [Fintype I] [DecidableEq I] [Ring A] [Algebra ℚ A]
    (σ : GradingInvolution A) (ε : I → Bool) where
  field : I → A
  source : I → A
  antifield : I → A
  leftAntifield : ∀ i, GradedDerivative σ (!(ε i))
  antifield_coordinate : ∀ i j, (leftAntifield i).d (antifield j) = if j = i then 1 else 0
  field_independent : ∀ i j, (leftAntifield i).d (field j) = 0
  source_independent : ∀ i j, (leftAntifield i).d (source j) = 0
  field_parity : ∀ i, σ.parity (field i) = koszulSign (ε i) • field i
  source_parity : ∀ i, σ.parity (source i) = koszulSign (ε i) • source i
  antifield_parity : ∀ i, σ.parity (antifield i) = koszulSign (!(ε i)) • antifield i
  source_commutation : ∀ i x,
    source i * (if !(ε i) then σ.parity x else x) = σ.parity x * source i

/-- Differentiating the constructed master action gives its signed BRST
insertion; the result is not supplied as a premise. -/
theorem bvMasterAction_antifield_derivative {I A : Type*} [Fintype I] [DecidableEq I] [Ring A] [Algebra ℚ A]
    {σ : GradingInvolution A} {ε : I → Bool} (s : ClosedBRST σ)
    (c : BVCoordinates σ ε) (S0 Ψ : A)
    (hS : ∀ i, (c.leftAntifield i).d S0 = 0)
    (hΨ : ∀ i, (c.leftAntifield i).d (s.derivative.d Ψ) = 0)
    (hvariation : ∀ i j, (c.leftAntifield i).d (s.derivative.d (c.field j)) = 0)
    (i : I) :
    (c.leftAntifield i).d (bvMasterAction s ε S0 Ψ c.field c.antifield) =
      koszulSign (ε i) • s.derivative.d (c.field i) := by
  classical
  simp only [bvMasterAction, map_add, hS i, hΨ i, zero_add, map_sum, map_smul]
  have ht j : (c.leftAntifield i).d (c.antifield j * s.derivative.d (c.field j)) =
      if j = i then s.derivative.d (c.field j) else 0 := by
    rw [(c.leftAntifield i).leibniz, c.antifield_coordinate, hvariation,
      mul_zero, add_zero]
    split_ifs <;> simp
  simp_rw [ht]
  simp

/-- The source-contracted antifield derivative is constructed as an operator. -/
def sourceWardMap {I A : Type*} [Fintype I] [DecidableEq I] [Ring A] [Algebra ℚ A]
    {σ : GradingInvolution A} {ε : I → Bool} (c : BVCoordinates σ ε) : A →ₗ[ℚ] A :=
  ∑ i, (LinearMap.mulLeft ℚ (c.source i)).comp (c.leftAntifield i).d

theorem sourceWardMap_apply {I A : Type*} [Fintype I] [DecidableEq I] [Ring A] [Algebra ℚ A]
    {σ : GradingInvolution A} {ε : I → Bool} (c : BVCoordinates σ ε) (x : A) :
    sourceWardMap c x = ∑ i, c.source i * (c.leftAntifield i).d x := by
  simp [sourceWardMap]

/-- Canonical graded source commutation makes the source-contracted
antifield operator an odd graded derivative. -/
def sourceWardDerivative {I A : Type*} [Fintype I] [DecidableEq I] [Ring A] [Algebra ℚ A]
    {σ : GradingInvolution A} {ε : I → Bool} (c : BVCoordinates σ ε) :
    GradedDerivative σ true where
  d := sourceWardMap c
  leibniz x y := by
    simp only [sourceWardMap_apply, (c.leftAntifield _).leibniz,
      mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, c.source_commutation]
    exact mul_assoc _ _ _
  homogeneous x := by
    simp only [koszulSign, ite_true, neg_one_smul]
    simp only [sourceWardMap_apply, map_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [(c.leftAntifield i).homogeneous, map_mul, c.source_parity]
    simp only [koszulSign_not, neg_smul, mul_neg, smul_mul_assoc, mul_smul_comm]

/-- Graded derivatives agreeing up to a sign on an exponent agree up to that
sign on every formal exponential coefficient. No analytic exponential rule
or unproved change-of-variables formula is inserted here. -/
theorem opposite_graded_derivatives_power {A : Type*} [Ring A] [Algebra ℚ A]
    {σ : GradingInvolution A} (D Q : GradedDerivative σ true) {X : A}
    (hX : Q.d X = -D.d X) : ∀ n : ℕ, Q.d (X ^ n) = -D.d (X ^ n) := by
  intro n
  induction n with
  | zero => simp [gradedDerivative_one]
  | succ n ih =>
    rw [pow_succ, Q.leibniz, D.leibniz, ih, hX]
    simp [neg_mul, mul_neg, add_comm]

def formalExpCoefficient {A : Type*} [Ring A] [Algebra ℚ A] (X : A) (n : ℕ) : A :=
  ((n.factorial : ℚ)⁻¹) • X ^ n

/-- The algebraic invariant-measure/change-of-variables step, coefficient by
coefficient. The BV action and source variation are constructed. Invariance
of the expectation, source linearity, and differentiation under expectation
are the explicit measure/domain assumptions of the source theorem. -/
theorem brst_partition_coefficient_ward
    {I A B : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    {σ : GradingInvolution A} {ε : I → Bool} (s : ClosedBRST σ)
    (c : BVCoordinates σ ε) (S0 Ψ : A)
    (hSinv : s.derivative.d S0 = 0)
    (haf : ∀ i, s.derivative.d (c.antifield i) = 0)
    (hJ : ∀ i, s.derivative.d (c.source i) = 0)
    (hS : ∀ i, (c.leftAntifield i).d S0 = 0)
    (hΨ : ∀ i, (c.leftAntifield i).d (s.derivative.d Ψ) = 0)
    (hvariation : ∀ i j, (c.leftAntifield i).d (s.derivative.d (c.field j)) = 0)
    (expectation : A →ₗ[ℚ] B) (j : I → B) (δ : I → B →ₗ[ℚ] B)
    (hinvariant : ∀ x, expectation (s.derivative.d x) = 0)
    (hsource : ∀ i x, expectation (c.source i * x) = j i * expectation x)
    (hdifferentiate : ∀ i x, δ i (expectation x) = expectation ((c.leftAntifield i).d x))
    (n : ℕ) :
    (∑ i, j i * δ i (expectation (formalExpCoefficient
      (-bvMasterAction s ε S0 Ψ c.field c.antifield + sourcePairing c.source c.field) n))) = 0 := by
  let master := bvMasterAction s ε S0 Ψ c.field c.antifield
  let X := -master + sourcePairing c.source c.field
  have hsmaster : s.derivative.d master = 0 := bvMasterAction_brst_invariant s ε S0 Ψ _ _ hSinv haf
  have hQmaster : sourceWardMap c master = s.derivative.d (sourcePairing c.source c.field) := by
    rw [sourceWardMap_apply, brst_source_first_sign s ε _ _ hJ c.source_parity]
    apply Finset.sum_congr rfl
    intro i _
    rw [bvMasterAction_antifield_derivative s c S0 Ψ hS hΨ hvariation]
    exact mul_smul_comm _ _ _
  have hQpair : sourceWardMap c (sourcePairing c.source c.field) = 0 := by
    rw [sourceWardMap_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hd : (c.leftAntifield i).d (sourcePairing c.source c.field) = 0 := by
      unfold sourcePairing
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [(c.leftAntifield i).leibniz, c.source_independent, c.field_independent,
        zero_mul, mul_zero, add_zero]
    rw [hd, mul_zero]
  have hX : (sourceWardDerivative c).d X = -s.derivative.d X := by
    change sourceWardMap c (-master + sourcePairing c.source c.field) =
      -s.derivative.d (-master + sourcePairing c.source c.field)
    rw [map_add, map_neg, hQmaster, hQpair, map_add, map_neg, hsmaster]
    simp
  have hp := opposite_graded_derivatives_power s.derivative (sourceWardDerivative c) hX n
  have he : sourceWardMap c (formalExpCoefficient X n) =
      -s.derivative.d (formalExpCoefficient X n) := by
    change (sourceWardDerivative c).d (formalExpCoefficient X n) = _
    unfold formalExpCoefficient
    rw [map_smul, map_smul, hp, smul_neg]
  calc
    _ = expectation (sourceWardMap c (formalExpCoefficient X n)) := by
      rw [sourceWardMap_apply, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hdifferentiate, hsource]
    _ = 0 := by rw [he, map_neg, hinvariant, neg_zero]

/-- A finite Grassmann/logarithm truncation about the normalized body 1.
When the positive-degree part is nilpotent, the truncation is the complete
nilpotent logarithm; no analytic logarithm branch is silently chosen. -/
def finiteLogPolynomial {A : Type*} [Ring A] [Algebra ℚ A] (z : A) (N : ℕ) : A :=
  ∑ n ∈ Finset.range N, (((-1 : ℚ) ^ n) / (n + 1 : ℚ)) • (z - 1) ^ (n + 1)

theorem gradedDerivative_power_of_zero {A : Type*} [Ring A] [Algebra ℚ A]
    {σ : GradingInvolution A} {odd : Bool} (D : GradedDerivative σ odd)
    {x : A} (hx : D.d x = 0) : ∀ n : ℕ, D.d (x ^ n) = 0 := by
  intro n
  induction n with
  | zero => simpa only [pow_zero] using gradedDerivative_one D
  | succ n ih => rw [pow_succ, D.leibniz, ih, hx, zero_mul, mul_zero, add_zero]

/-- The connected Ward identity is derived for the actual finite logarithm
polynomial from the partition Ward identity and graded differentiation. -/
theorem finite_log_polynomial_ward {A : Type*} [Ring A] [Algebra ℚ A]
    {σ : GradingInvolution A} {odd : Bool} (D : GradedDerivative σ odd)
    {z : A} (hz : D.d z = 0) (N : ℕ) :
    D.d (finiteLogPolynomial z N) = 0 := by
  have hx : D.d (z - 1) = 0 := by rw [map_sub, hz, gradedDerivative_one, sub_zero]
  unfold finiteLogPolynomial
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro n _
  rw [map_smul, gradedDerivative_power_of_zero D hx, smul_zero]

/-- The standard finite exterior polynomial algebra has an actual parity
involution and actual odd coordinate contractions. -/
def exteriorGrading (V : Type*) [AddCommGroup V] [Module ℚ V] :
    GradingInvolution (ExteriorAlgebra ℚ V) where
  parity := CliffordAlgebra.involute
  involutive := CliffordAlgebra.involute_involutive

theorem exterior_contract_left_leibniz
    {V : Type*} [AddCommGroup V] [Module ℚ V] (d : Module.Dual ℚ V)
    (x y : ExteriorAlgebra ℚ V) :
    CliffordAlgebra.contractLeft d (x * y) =
      CliffordAlgebra.contractLeft d x * y +
        CliffordAlgebra.involute x * CliffordAlgebra.contractLeft d y := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap_mul]
  | add x z hx hz => simp only [add_mul, map_add, hx, hz]; abel
  | ι_mul v x hx =>
    rw [mul_assoc, CliffordAlgebra.contractLeft_ι_mul, hx,
      CliffordAlgebra.contractLeft_ι_mul, map_mul, CliffordAlgebra.involute_ι]
    simp only [Algebra.smul_def]
    noncomm_ring

theorem exterior_contract_parity_odd
    {V : Type*} [AddCommGroup V] [Module ℚ V] (d : Module.Dual ℚ V)
    (x : ExteriorAlgebra ℚ V) :
    CliffordAlgebra.contractLeft d (CliffordAlgebra.involute x) =
      -CliffordAlgebra.involute (CliffordAlgebra.contractLeft d x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x z hx hz => simp only [map_add, hx, hz]; abel
  | ι_mul v x hx =>
    simp only [map_mul, CliffordAlgebra.involute_ι, neg_mul, map_neg,
      CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, hx]
    noncomm_ring

def exteriorContractionBRST {V : Type*} [AddCommGroup V] [Module ℚ V]
    (d : Module.Dual ℚ V) : ClosedBRST (exteriorGrading V) where
  derivative := {
    d := CliffordAlgebra.contractLeft d
    leibniz := exterior_contract_left_leibniz d
    homogeneous := by
      intro x
      simpa only [koszulSign, ite_true, neg_one_smul] using exterior_contract_parity_odd d x }
  nilpotent := CliffordAlgebra.contractLeft_contractLeft d
  parity_odd := exterior_contract_parity_odd d

/-- The source-exchange minus sign for odd coordinates follows from concrete
exterior contractions, rather than a postulated covariance reciprocity. -/
theorem exterior_source_hessian_anticommutes
    {V : Type*} [AddCommGroup V] [Module ℚ V] (d e : Module.Dual ℚ V)
    (W : ExteriorAlgebra ℚ V) :
    CliffordAlgebra.contractLeft d (CliffordAlgebra.contractLeft e W) =
      -CliffordAlgebra.contractLeft e (CliffordAlgebra.contractLeft d W) :=
  CliffordAlgebra.contractLeft_comm d e W

def exteriorCoordinatePartial {n : ℕ} (i : Fin n) :
    ExteriorAlgebra ℚ (Fin n → ℚ) →ₗ[ℚ] ExteriorAlgebra ℚ (Fin n → ℚ) :=
  CliffordAlgebra.contractLeft (LinearMap.proj i)

theorem exteriorCoordinatePartial_generator {n : ℕ} (i j : Fin n) :
    exteriorCoordinatePartial i (ExteriorAlgebra.ι ℚ (Pi.single j (1 : ℚ))) =
      if j = i then 1 else 0 := by
  classical
  by_cases hij : j = i
  · subst j
    simp [exteriorCoordinatePartial, CliffordAlgebra.contractLeft_ι]
  · simp [exteriorCoordinatePartial, CliffordAlgebra.contractLeft_ι, hij, Ne.symm hij]

/-- Even polynomial source derivatives commute as actual derivations. -/
theorem polynomial_source_hessian_commutes {I : Type*} (i j : I)
    (W : MvPolynomial I ℚ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j W) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i W) := by
  classical
  have hp (a b : I) : MvPolynomial.pderiv a (MvPolynomial.X b : MvPolynomial I ℚ) =
      if b = a then 1 else 0 := by
    split_ifs with h
    · subst b; simp
    · exact MvPolynomial.pderiv_X_of_ne h
  have hc : ⁅(MvPolynomial.pderiv i : Derivation ℚ (MvPolynomial I ℚ) (MvPolynomial I ℚ)),
      (MvPolynomial.pderiv j : Derivation ℚ (MvPolynomial I ℚ) (MvPolynomial I ℚ))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    simp only [Derivation.commutator_apply, hp]
    split_ifs <;> simp
  have h := congrArg (fun D : Derivation ℚ (MvPolynomial I ℚ) (MvPolynomial I ℚ) => D W) hc
  simpa only [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero] using h

def sourceHessian {I A : Type*} [AddCommGroup A] [Module ℚ A]
    (D : I → A →ₗ[ℚ] A) (W : A) (i j : I) : A := D i (D j W)

/-- The source covariance is formed from two derivatives of the SAME
functional. Graded commutation is an operator law, as assumed in the source;
no covariance reciprocity is supplied as a premise. -/
theorem source_hessian_exchange {I A : Type*} [AddCommGroup A] [Module ℚ A]
    (ε : I → Bool) (D : I → A →ₗ[ℚ] A) (W : A)
    (hgraded : ∀ i j, (D i).comp (D j) =
      koszulSign (ε i && ε j) • (D j).comp (D i)) (i j : I) :
    sourceHessian D W i j = koszulSign (ε i && ε j) • sourceHessian D W j i :=
  congrArg (fun T : A →ₗ[ℚ] A => T W) (hgraded i j)

/-- Common source normalizations and character projections are linear and
preserve the exchange sign. -/
theorem mapped_source_hessian_exchange
    {I A B : Type*} [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B]
    (ε : I → Bool) (D : I → A →ₗ[ℚ] A) (W : A) (T : A →ₗ[ℚ] B)
    (hgraded : ∀ i j, (D i).comp (D j) =
      koszulSign (ε i && ε j) • (D j).comp (D i)) (i j : I) :
    T (sourceHessian D W i j) = koszulSign (ε i && ε j) • T (sourceHessian D W j i) := by
  rw [source_hessian_exchange ε D W hgraded, map_smul]

/-- Translation invariance converts endpoint exchange into position reversal. -/
theorem translation_invariant_source_hessian_reversal
    {I X A : Type*} [AddCommGroup X] [AddCommGroup A] [Module ℚ A]
    (ε : I → Bool) (D : (I × X) → A →ₗ[ℚ] A) (W : A)
    (hgraded : ∀ i j, (D i).comp (D j) =
      koszulSign (ε i.1 && ε j.1) • (D j).comp (D i))
    (htranslation : ∀ i j x y t,
      sourceHessian D W (i, x + t) (j, y + t) = sourceHessian D W (i, x) (j, y))
    (i j : I) (x : X) :
    sourceHessian D W (i, x) (j, 0) =
      koszulSign (ε i && ε j) • sourceHessian D W (j, -x) (i, 0) := by
  rw [source_hessian_exchange (fun z => ε z.1) D W hgraded]
  have ht := htranslation j i 0 x (-x)
  simpa only [zero_add, add_neg_cancel] using congrArg
    (fun a => koszulSign (ε i && ε j) • a) ht.symm

/-- Ordinary Euclidean Fourier transform of a source two-point coefficient. -/
def sourceFourier {n : ℕ} (C : EuclideanSpace ℝ (Fin n) → ℂ)
    (p : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∫ x, Complex.exp (-(Complex.I * ((inner ℝ p x : ℝ) : ℂ))) * C x

/-- Momentum reversal is an actual Haar change of variables, rather than an
assumed symmetry of an arbitrary running virtual-line datum. -/
theorem sourceFourier_reflection {n : ℕ}
    (C : EuclideanSpace ℝ (Fin n) → ℂ) (p : EuclideanSpace ℝ (Fin n)) :
    sourceFourier (fun x => C (-x)) p = sourceFourier C (-p) := by
  let e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearIsometryEquiv.neg ℝ
  have hn := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun x : EuclideanSpace ℝ (Fin n) =>
      Complex.exp (-(Complex.I * ((inner ℝ p x : ℝ) : ℂ))) * C (-x))
  simpa only [sourceFourier, e, LinearIsometryEquiv.coe_neg, inner_neg_right,
    inner_neg_left, neg_neg] using hn.symm

/-- Position and momentum reciprocity for a translation-invariant Hessian of
one source functional. The hypotheses concern graded derivative operators and
translation, never the desired covariance equality. -/
theorem source_hessian_fourier_exchange
    {I A : Type*} [AddCommGroup A] [Module ℚ A] {n : ℕ}
    (ε : I → Bool) (D : (I × EuclideanSpace ℝ (Fin n)) → A →ₗ[ℚ] A) (W : A)
    (T : A →ₗ[ℚ] ℂ)
    (hgraded : ∀ i j, (D i).comp (D j) =
      koszulSign (ε i.1 && ε j.1) • (D j).comp (D i))
    (htranslation : ∀ i j x y t,
      sourceHessian D W (i, x + t) (j, y + t) = sourceHessian D W (i, x) (j, y))
    (i j : I) (p : EuclideanSpace ℝ (Fin n)) :
    sourceFourier (fun x => T (sourceHessian D W (i, x) (j, 0))) p =
      ((koszulSign (ε i && ε j) : ℚ) : ℂ) *
        sourceFourier (fun x => T (sourceHessian D W (j, x) (i, 0))) (-p) := by
  have hp (x : EuclideanSpace ℝ (Fin n)) :
      T (sourceHessian D W (i, x) (j, 0)) =
        ((koszulSign (ε i && ε j) : ℚ) : ℂ) *
          T (sourceHessian D W (j, -x) (i, 0)) := by
    rw [translation_invariant_source_hessian_reversal ε D W hgraded htranslation, map_smul]
    exact Rat.smul_def _ _
  simp_rw [sourceFourier, hp]
  simp_rw [← mul_assoc, mul_comm _ (((koszulSign (ε i && ε j) : ℚ) : ℂ)), mul_assoc]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact sourceFourier_reflection (fun x => T (sourceHessian D W (j, x) (i, 0))) p

/-- Declared field/antifield parities and an odd gauge-fixing fermion make
the constructed BV action even, in the actual parity involution. -/
theorem bvMasterAction_even {I A : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] {σ : GradingInvolution A} {ε : I → Bool}
    (s : ClosedBRST σ) (c : BVCoordinates σ ε) (S0 Ψ : A)
    (hS : σ.parity S0 = S0) (hΨ : σ.parity Ψ = -Ψ) :
    σ.parity (bvMasterAction s ε S0 Ψ c.field c.antifield) =
      bvMasterAction s ε S0 Ψ c.field c.antifield := by
  have hfix : σ.parity (s.derivative.d Ψ) = s.derivative.d Ψ := by
    have h := s.parity_odd Ψ
    rw [hΨ, map_neg] at h
    exact (neg_inj.mp h).symm
  have hvar i : σ.parity (s.derivative.d (c.field i)) =
      -(koszulSign (ε i) • s.derivative.d (c.field i)) := by
    have h := congrArg Neg.neg (s.parity_odd (c.field i))
    have h' : σ.parity (s.derivative.d (c.field i)) =
        -s.derivative.d (σ.parity (c.field i)) := by
      simpa only [neg_neg] using h.symm
    rw [c.field_parity, map_smul] at h'
    exact h'
  simp only [bvMasterAction, map_add, map_sum, map_smul, hS, hfix]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, c.antifield_parity, hvar, koszulSign_not]
  simp only [neg_smul, neg_mul_neg, smul_mul_assoc, mul_smul_comm,
    smul_smul, koszulSign_square, one_smul]

/-- The identical commuting scalar consequence is an even momentum-space
coefficient, derived from the common source Hessian and translation law. -/
theorem identical_commuting_source_fourier_even
    {I A : Type*} [AddCommGroup A] [Module ℚ A] {n : ℕ}
    (ε : I → Bool) (D : (I × EuclideanSpace ℝ (Fin n)) → A →ₗ[ℚ] A) (W : A)
    (T : A →ₗ[ℚ] ℂ)
    (hgraded : ∀ i j, (D i).comp (D j) =
      koszulSign (ε i.1 && ε j.1) • (D j).comp (D i))
    (htranslation : ∀ i j x y t,
      sourceHessian D W (i, x + t) (j, y + t) = sourceHessian D W (i, x) (j, y))
    (i : I) (hε : ε i = false) (p : EuclideanSpace ℝ (Fin n)) :
    sourceFourier (fun x => T (sourceHessian D W (i, x) (i, 0))) p =
      sourceFourier (fun x => T (sourceHessian D W (i, x) (i, 0))) (-p) := by
  simpa only [hε, Bool.false_and, koszulSign, Bool.false_eq_true, ite_false,
    Rat.cast_one, one_mul] using
    source_hessian_fourier_exchange ε D W T hgraded htranslation i i p

end UV
