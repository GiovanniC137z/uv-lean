import UV.BRST
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Algebra.Ring.Basic

/-! A graded coordinate chain rule and the signed Legendre identities. The
effective action is constructed from a genuine inverse source-gradient
coordinate substitution; no effective-action derivative is an input. -/

noncomputable section
open scoped BigOperators

namespace UV

/-- Supercommutativity is stated for homogeneous coefficients, with arbitrary
second factor. This is the parity-involution form of the Grassmann sign. -/
structure SupercommutativeGrading {A : Type*} [Ring A] [Algebra ℚ A]
    (σ : GradingInvolution A) : Prop where
  commute : ∀ (odd : Bool) (a : A), σ.parity a = koszulSign odd • a →
    ∀ b : A, a * b = (if odd then σ.parity b else b) * a

structure GradedCoordinates (I A : Type*) [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] (σ : GradingInvolution A) (ε : I → Bool) where
  coord : I → A
  coordD : ∀ i, GradedDerivative σ (ε i)
  coordinate : ∀ i j, (coordD i).d (coord j) = if j = i then 1 else 0
  parity : ∀ i, σ.parity (coord i) = koszulSign (ε i) • coord i

theorem gradedDerivative_algebraMap {A : Type*} [Ring A] [Algebra ℚ A]
    {σ : GradingInvolution A} {odd : Bool} (D : GradedDerivative σ odd) (r : ℚ) :
    D.d (algebraMap ℚ A r) = 0 := by
  have he : algebraMap ℚ A r = r • (1 : A) := by simp [Algebra.smul_def]
  rw [he, map_smul, gradedDerivative_one, smul_zero]

theorem gradedDerivative_homogeneous_value {A : Type*} [Ring A] [Algebra ℚ A]
    {σ : GradingInvolution A} {δ p : Bool} (D : GradedDerivative σ δ) {x : A}
    (hx : σ.parity x = koszulSign p • x) :
    σ.parity (D.d x) = koszulSign (Bool.xor δ p) • D.d x := by
  have h := D.homogeneous x
  rw [hx, map_smul] at h
  cases δ <;> cases p <;> simp [koszulSign] at h ⊢
  · exact h.symm
  · exact h.symm
  · simpa only [neg_neg] using congrArg Neg.neg h.symm
  · exact h.symm

theorem graded_jacobian_coefficient_commute
    {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    {σA : GradingInvolution A} {σB : GradingInvolution B}
    (hB : SupercommutativeGrading σB) (Φ : A →ₐ[ℚ] B)
    (hΦ : ∀ x, Φ (σA.parity x) = σB.parity (Φ x))
    {δ p : Bool} (D : GradedDerivative σB δ) {u : A}
    (hu : σA.parity u = koszulSign p • u) (x : A) :
    D.d (Φ u) * Φ (if p then σA.parity x else x) =
      (if δ then σB.parity (Φ x) else Φ x) * D.d (Φ u) := by
  have hpu : σB.parity (Φ u) = koszulSign p • Φ u := by
    rw [← hΦ, hu, map_smul]
  have hc := hB.commute (Bool.xor δ p) (D.d (Φ u)) (gradedDerivative_homogeneous_value D hpu)
  cases δ <;> cases p
  · exact hc (Φ x)
  · have hh := hc (σB.parity (Φ x))
    change D.d (Φ u) * σB.parity (Φ x) = σB.parity (σB.parity (Φ x)) * D.d (Φ u) at hh
    rw [σB.involutive] at hh
    simpa [hΦ] using hh
  · exact hc (Φ x)
  · simpa [hΦ] using hc (σB.parity (Φ x))

def gradedJacobianPullback {I A B : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : I → Bool}
    (c : GradedCoordinates I A σA ε) (Φ : A →ₐ[ℚ] B) {δ : Bool}
    (D : GradedDerivative σB δ) (f : A) : B :=
  ∑ i, D.d (Φ (c.coord i)) * Φ ((c.coordD i).d f)

theorem graded_jacobian_leibniz
    {I A B : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : I → Bool}
    (c : GradedCoordinates I A σA ε) (hB : SupercommutativeGrading σB)
    (Φ : A →ₐ[ℚ] B) (hΦ : ∀ x, Φ (σA.parity x) = σB.parity (Φ x))
    {δ : Bool} (D : GradedDerivative σB δ) (f g : A) :
    gradedJacobianPullback c Φ D (f * g) =
      gradedJacobianPullback c Φ D f * Φ g +
        (if δ then σB.parity (Φ f) else Φ f) * gradedJacobianPullback c Φ D g := by
  simp only [gradedJacobianPullback, (c.coordD _).leibniz, map_add, map_mul,
    mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact (mul_assoc _ _ _).symm
  · apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, graded_jacobian_coefficient_commute hB Φ hΦ D (c.parity i), mul_assoc]

theorem graded_chain_rule_on_coordinate_algebra
    {I A B : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : I → Bool}
    (c : GradedCoordinates I A σA ε) (hB : SupercommutativeGrading σB)
    (Φ : A →ₐ[ℚ] B) (hΦ : ∀ x, Φ (σA.parity x) = σB.parity (Φ x))
    {δ : Bool} (D : GradedDerivative σB δ) {f : A}
    (hf : f ∈ Algebra.adjoin ℚ (Set.range c.coord)) :
    D.d (Φ f) = gradedJacobianPullback c Φ D f := by
  induction hf using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    simp only [gradedJacobianPullback, c.coordinate]
    simp
  | algebraMap r =>
    rw [Φ.commutes r]
    simp [gradedJacobianPullback, gradedDerivative_algebraMap]
  | add f g _ _ hf hg =>
    simp only [map_add, hf, hg, gradedJacobianPullback, mul_add, Finset.sum_add_distrib]
  | mul f g _ _ hf hg =>
    rw [map_mul, D.leibniz, hf, hg, graded_jacobian_leibniz c hB Φ hΦ D]

theorem graded_chain_rule_with_inert_coefficients
    {I A B : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : I → Bool}
    (c : GradedCoordinates I A σA ε) (hB : SupercommutativeGrading σB)
    (Φ : A →ₐ[ℚ] B) (hΦ : ∀ x, Φ (σA.parity x) = σB.parity (Φ x))
    {δ : Bool} (D : GradedDerivative σB δ) (C : Set A)
    (hC : ∀ r ∈ C, D.d (Φ r) = 0)
    (hpartialC : ∀ i r, r ∈ C → (c.coordD i).d r = 0) {f : A}
    (hf : f ∈ Algebra.adjoin ℚ (C ∪ Set.range c.coord)) :
    D.d (Φ f) = gradedJacobianPullback c Φ D f := by
  induction hf using Algebra.adjoin_induction with
  | mem u hu =>
    rcases hu with hu | hu
    · rw [hC u hu]
      simp [gradedJacobianPullback, hpartialC _ _ hu]
    · exact graded_chain_rule_on_coordinate_algebra c hB Φ hΦ D (Algebra.subset_adjoin hu)
  | algebraMap r =>
    rw [Φ.commutes r]
    simp [gradedJacobianPullback, gradedDerivative_algebraMap]
  | add f g _ _ hf hg =>
    simp only [map_add, hf, hg, gradedJacobianPullback, mul_add, Finset.sum_add_distrib]
  | mul f g _ _ hf hg =>
    rw [map_mul, D.leibniz, hf, hg, graded_jacobian_leibniz c hB Φ hΦ D]

/-- The algebraic chain rule extends to an admitted completion by actual
continuity and density. No chain rule for the selected functional is assumed. -/
theorem graded_chain_rule_on_completion
    {I A B : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    [TopologicalSpace A] [TopologicalSpace B] [T2Space B] [IsTopologicalRing B]
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : I → Bool}
    (c : GradedCoordinates I A σA ε) (hB : SupercommutativeGrading σB)
    (Φ : A →ₐ[ℚ] B) (hΦ : ∀ x, Φ (σA.parity x) = σB.parity (Φ x))
    {δ : Bool} (D : GradedDerivative σB δ) (C : Set A)
    (hC : ∀ r ∈ C, D.d (Φ r) = 0)
    (hpartialC : ∀ i r, r ∈ C → (c.coordD i).d r = 0)
    (hdense : Dense (Algebra.adjoin ℚ (C ∪ Set.range c.coord) : Set A))
    (hcontΦ : Continuous Φ) (hcontD : Continuous D.d)
    (hcontpartial : ∀ i, Continuous (c.coordD i).d) (f : A) :
    D.d (Φ f) = gradedJacobianPullback c Φ D f := by
  have hleft : Continuous (fun f : A => D.d (Φ f)) := hcontD.comp hcontΦ
  have hright : Continuous (gradedJacobianPullback c Φ D) := by
    unfold gradedJacobianPullback
    exact continuous_finset_sum _ (fun i _ => continuous_const.mul (hcontΦ.comp (hcontpartial i)))
  have he := Continuous.ext_on hdense hleft hright
    (fun f hf => graded_chain_rule_with_inert_coefficients c hB Φ hΦ D C hC hpartialC hf)
  exact congr_fun he f

def bvCoordinateParity {I : Type*} (ε : I → Bool) : I ⊕ I → Bool :=
  Sum.elim ε (fun i => !(ε i))

/-- An admitted common graded functional calculus and an actual inverse
source-gradient coordinate map. Polynomial density and continuous partials
make the chain rule a theorem. Inert coefficients can include parameters and
the formal loop variable. Neither Legendre derivative identity is a field. -/
structure GradedLegendreChart (I A B : Type*) [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    [TopologicalSpace A] [TopologicalSpace B]
    (σA : GradingInvolution A) (σB : GradingInvolution B) (ε : I → Bool) (W : A) where
  source : GradedCoordinates (I ⊕ I) A σA (bvCoordinateParity ε)
  target : GradedCoordinates (I ⊕ I) B σB (bvCoordinateParity ε)
  pull : A ≃ₐ[ℚ] B
  preserves_parity : ∀ x, pull (σA.parity x) = σB.parity (pull x)
  antifields_fixed : ∀ i, pull (source.coord (Sum.inr i)) = target.coord (Sum.inr i)
  inverse_gradient : ∀ i, pull ((source.coordD (Sum.inl i)).d W) = target.coord (Sum.inl i)
  coefficients : Set A
  source_inert : ∀ i r, r ∈ coefficients → (source.coordD i).d r = 0
  target_inert : ∀ i r, r ∈ coefficients → (target.coordD i).d (pull r) = 0
  polynomial_dense : Dense (Algebra.adjoin ℚ (coefficients ∪ Set.range source.coord) : Set A)
  pull_continuous : Continuous pull
  inverse_continuous : Continuous pull.symm
  source_partials_continuous : ∀ i, Continuous (source.coordD i).d
  target_partials_continuous : ∀ i, Continuous (target.coordD i).d

def gradedLegendreAction
    {I A B : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    [TopologicalSpace A] [TopologicalSpace B]
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : I → Bool} {W : A}
    (c : GradedLegendreChart I A B σA σB ε W) : B :=
  sourcePairing (fun i => c.pull (c.source.coord (Sum.inl i)))
    (fun i => c.target.coord (Sum.inl i)) - c.pull W

theorem legendre_field_pullback_chain
    {I A B : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    [TopologicalSpace A] [TopologicalSpace B] [T2Space B] [IsTopologicalRing B]
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : I → Bool} {W : A}
    (c : GradedLegendreChart I A B σA σB ε W) (hB : SupercommutativeGrading σB) (i : I) :
    (c.target.coordD (Sum.inl i)).d (c.pull W) =
      ∑ j, (c.target.coordD (Sum.inl i)).d (c.pull (c.source.coord (Sum.inl j))) *
        c.target.coord (Sum.inl j) := by
  have h := graded_chain_rule_on_completion c.source hB c.pull.toAlgHom c.preserves_parity
    (c.target.coordD (Sum.inl i)) c.coefficients (c.target_inert (Sum.inl i)) c.source_inert
    c.polynomial_dense c.pull_continuous (c.target_partials_continuous (Sum.inl i))
    c.source_partials_continuous W
  simpa [gradedJacobianPullback, Fintype.sum_sum_type, c.inverse_gradient, c.antifields_fixed,
    c.target.coordinate] using h

theorem legendre_antifield_pullback_chain
    {I A B : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    [TopologicalSpace A] [TopologicalSpace B] [T2Space B] [IsTopologicalRing B]
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : I → Bool} {W : A}
    (c : GradedLegendreChart I A B σA σB ε W) (hB : SupercommutativeGrading σB) (i : I) :
    (c.target.coordD (Sum.inr i)).d (c.pull W) =
      (∑ j, (c.target.coordD (Sum.inr i)).d (c.pull (c.source.coord (Sum.inl j))) *
        c.target.coord (Sum.inl j)) + c.pull ((c.source.coordD (Sum.inr i)).d W) := by
  have h := graded_chain_rule_on_completion c.source hB c.pull.toAlgHom c.preserves_parity
    (c.target.coordD (Sum.inr i)) c.coefficients (c.target_inert (Sum.inr i)) c.source_inert
    c.polynomial_dense c.pull_continuous (c.target_partials_continuous (Sum.inr i))
    c.source_partials_continuous W
  simpa [gradedJacobianPullback, Fintype.sum_sum_type, c.inverse_gradient, c.antifields_fixed,
    c.target.coordinate] using h

theorem legendre_pulled_source_parity
    {I A B : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    [TopologicalSpace A] [TopologicalSpace B]
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : I → Bool} {W : A}
    (c : GradedLegendreChart I A B σA σB ε W) (i : I) :
    σB.parity (c.pull (c.source.coord (Sum.inl i))) =
      koszulSign (ε i) • c.pull (c.source.coord (Sum.inl i)) := by
  rw [← c.preserves_parity, c.source.parity, map_smul]
  rfl

theorem graded_legendre_left_field_derivative
    {I A B : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    [TopologicalSpace A] [TopologicalSpace B] [T2Space B] [IsTopologicalRing B]
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : I → Bool} {W : A}
    (c : GradedLegendreChart I A B σA σB ε W) (hB : SupercommutativeGrading σB) (i : I) :
    (c.target.coordD (Sum.inl i)).d (gradedLegendreAction c) =
      koszulSign (ε i) • c.pull (c.source.coord (Sum.inl i)) := by
  unfold gradedLegendreAction sourcePairing
  simp only [map_sub, map_sum, (c.target.coordD (Sum.inl i)).leibniz,
    Finset.sum_add_distrib, c.target.coordinate, Sum.inl.injEq, mul_ite, mul_one, mul_zero]
  rw [legendre_field_pullback_chain c hB]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hpar := legendre_pulled_source_parity c i
  cases he : ε i <;> simp [bvCoordinateParity, he, koszulSign] at hpar ⊢
  exact hpar

theorem graded_legendre_left_antifield_derivative
    {I A B : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    [TopologicalSpace A] [TopologicalSpace B] [T2Space B] [IsTopologicalRing B]
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : I → Bool} {W : A}
    (c : GradedLegendreChart I A B σA σB ε W) (hB : SupercommutativeGrading σB) (i : I) :
    (c.target.coordD (Sum.inr i)).d (gradedLegendreAction c) =
      -c.pull ((c.source.coordD (Sum.inr i)).d W) := by
  unfold gradedLegendreAction sourcePairing
  simp only [map_sub, map_sum, (c.target.coordD (Sum.inr i)).leibniz,
    c.target.coordinate, Sum.inl_ne_inr, ite_false, mul_zero, add_zero]
  rw [legendre_antifield_pullback_chain c hB]
  abel

/-- Right derivatives are constructed from left derivatives and the parity
involution. Their right Leibniz rule is proved below. -/
def rightGradedDerivative {A : Type*} [Ring A] [Algebra ℚ A]
    {σ : GradingInvolution A} {odd : Bool} (D : GradedDerivative σ odd) (f : A) : A :=
  if odd then σ.parity (D.d f) else D.d f

theorem rightGradedDerivative_leibniz {A : Type*} [Ring A] [Algebra ℚ A]
    {σ : GradingInvolution A} {odd : Bool} (D : GradedDerivative σ odd) (f g : A) :
    rightGradedDerivative D (f * g) = f * rightGradedDerivative D g +
      rightGradedDerivative D f * (if odd then σ.parity g else g) := by
  cases odd
  · simp only [rightGradedDerivative, Bool.false_eq_true, ite_false, D.leibniz]
    exact add_comm _ _
  · simp only [rightGradedDerivative, ite_true, D.leibniz, map_add, map_mul]
    rw [σ.involutive]
    exact add_comm _ _

theorem rightGradedDerivative_of_even {A : Type*} [Ring A] [Algebra ℚ A]
    {σ : GradingInvolution A} {odd : Bool} (D : GradedDerivative σ odd)
    {f : A} (hf : σ.parity f = f) :
    rightGradedDerivative D f = koszulSign odd • D.d f := by
  have h := gradedDerivative_homogeneous_value (p := false) D (by simpa [koszulSign] using hf)
  cases odd
  · simp [rightGradedDerivative, koszulSign]
  · simpa [rightGradedDerivative, koszulSign] using h

theorem graded_legendre_even
    {I A B : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    [TopologicalSpace A] [TopologicalSpace B]
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : I → Bool} {W : A}
    (c : GradedLegendreChart I A B σA σB ε W) (hW : σA.parity W = W) :
    σB.parity (gradedLegendreAction c) = gradedLegendreAction c := by
  have hWp : σB.parity (c.pull W) = c.pull W := by rw [← c.preserves_parity, hW]
  unfold gradedLegendreAction sourcePairing
  rw [map_sub, map_sum, hWp]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, legendre_pulled_source_parity c i, c.target.parity]
  cases h : ε i <;> simp [bvCoordinateParity, h, koszulSign]

theorem graded_legendre_right_field_derivative
    {I A B : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    [TopologicalSpace A] [TopologicalSpace B] [T2Space B] [IsTopologicalRing B]
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : I → Bool} {W : A}
    (c : GradedLegendreChart I A B σA σB ε W) (hB : SupercommutativeGrading σB)
    (hW : σA.parity W = W) (i : I) :
    rightGradedDerivative (c.target.coordD (Sum.inl i)) (gradedLegendreAction c) =
      c.pull (c.source.coord (Sum.inl i)) := by
  rw [rightGradedDerivative_of_even _ (graded_legendre_even c hW),
    graded_legendre_left_field_derivative c hB i]
  change koszulSign (ε i) • (koszulSign (ε i) • _) = _
  rw [smul_smul, koszulSign_square, one_smul]

def canonicalAntibracket {I A : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] {σ : GradingInvolution A} {ε : I → Bool}
    (c : GradedCoordinates (I ⊕ I) A σ (bvCoordinateParity ε)) (F G : A) : A :=
  ∑ i, (rightGradedDerivative (c.coordD (Sum.inl i)) F * (c.coordD (Sum.inr i)).d G -
    rightGradedDerivative (c.coordD (Sum.inr i)) F * (c.coordD (Sum.inl i)).d G)

theorem even_field_antifield_derivatives_commute
    {I A : Type*} [Fintype I] [DecidableEq I] [Ring A] [Algebra ℚ A]
    {σ : GradingInvolution A} {ε : I → Bool}
    (c : GradedCoordinates (I ⊕ I) A σ (bvCoordinateParity ε)) (hA : SupercommutativeGrading σ)
    {F : A} (hF : σ.parity F = F) (i : I) :
    (c.coordD (Sum.inr i)).d F * (c.coordD (Sum.inl i)).d F =
      (c.coordD (Sum.inl i)).d F * (c.coordD (Sum.inr i)).d F := by
  have hfield := gradedDerivative_homogeneous_value (p := false) (c.coordD (Sum.inl i))
    (by simpa [koszulSign] using hF)
  have haf := gradedDerivative_homogeneous_value (p := false) (c.coordD (Sum.inr i))
    (by simpa [koszulSign] using hF)
  cases he : ε i
  · have heven : σ.parity ((c.coordD (Sum.inl i)).d F) = (c.coordD (Sum.inl i)).d F := by
      simpa [bvCoordinateParity, he, koszulSign] using hfield
    exact (hA.commute false _ (by simpa [koszulSign] using heven) _).symm
  · have heven : σ.parity ((c.coordD (Sum.inr i)).d F) = (c.coordD (Sum.inr i)).d F := by
      simpa [bvCoordinateParity, he, koszulSign] using haf
    exact hA.commute false _ (by simpa [koszulSign] using heven) _

theorem canonical_antibracket_even
    {I A : Type*} [Fintype I] [DecidableEq I] [Ring A] [Algebra ℚ A]
    {σ : GradingInvolution A} {ε : I → Bool}
    (c : GradedCoordinates (I ⊕ I) A σ (bvCoordinateParity ε)) (hA : SupercommutativeGrading σ)
    {F : A} (hF : σ.parity F = F) :
    canonicalAntibracket c F F = (2 : ℚ) •
      (∑ i, rightGradedDerivative (c.coordD (Sum.inl i)) F * (c.coordD (Sum.inr i)).d F) := by
  unfold canonicalAntibracket
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [rightGradedDerivative_of_even _ hF, bvCoordinateParity, Sum.elim_inl,
    Sum.elim_inr, koszulSign_not, neg_smul, neg_mul, sub_neg_eq_add, smul_mul_assoc]
  rw [even_field_antifield_derivatives_commute c hA hF i, two_smul ℚ]

/-- The connected Ward identity transfers through the actual Legendre map.
It is the connected identity, not an effective-action identity, that is the
input to this theorem. -/
theorem graded_legendre_connected_ward_transfer
    {I A B : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    [TopologicalSpace A] [TopologicalSpace B] [T2Space B] [IsTopologicalRing B]
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : I → Bool} {W : A}
    (c : GradedLegendreChart I A B σA σB ε W) (hB : SupercommutativeGrading σB)
    (hW : σA.parity W = W)
    (hWard : (∑ i, c.source.coord (Sum.inl i) * (c.source.coordD (Sum.inr i)).d W) = 0) :
    (∑ i, rightGradedDerivative (c.target.coordD (Sum.inl i)) (gradedLegendreAction c) *
      (c.target.coordD (Sum.inr i)).d (gradedLegendreAction c)) = 0 := by
  simp_rw [graded_legendre_right_field_derivative c hB hW, graded_legendre_left_antifield_derivative c hB]
  have h := congrArg c.pull hWard
  simp only [map_sum, map_mul, map_zero] at h
  simpa only [mul_neg, Finset.sum_neg_distrib, neg_zero] using congrArg Neg.neg h

/-- Conditional exact Slavnov--Taylor identity on the admitted graded
Legendre chart. The signed derivative identities and the even-antibracket
factor of two are proved, rather than postulated. -/
theorem graded_legendre_slavnov_taylor
    {I A B : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    [TopologicalSpace A] [TopologicalSpace B] [T2Space B] [IsTopologicalRing B]
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : I → Bool} {W : A}
    (c : GradedLegendreChart I A B σA σB ε W) (hB : SupercommutativeGrading σB)
    (hW : σA.parity W = W)
    (hWard : (∑ i, c.source.coord (Sum.inl i) * (c.source.coordD (Sum.inr i)).d W) = 0) :
    (1 / 2 : ℚ) • canonicalAntibracket c.target (gradedLegendreAction c) (gradedLegendreAction c) = 0 := by
  rw [canonical_antibracket_even c.target hB (graded_legendre_even c hW),
    graded_legendre_connected_ward_transfer c hB hW hWard, smul_zero, smul_zero]

theorem finiteLogPolynomial_even {A : Type*} [Ring A] [Algebra ℚ A]
    (σ : GradingInvolution A) {z : A} (hz : σ.parity z = z) (N : ℕ) :
    σ.parity (finiteLogPolynomial z N) = finiteLogPolynomial z N := by
  simp [finiteLogPolynomial, hz]

/-- Direct bridge to the connected Ward operator already constructed in
`UV.BRST`. The coordinate matching concerns source normalization and
antifield derivatives, not the effective action or its master equation. -/
theorem connected_ward_legendre_slavnov_taylor
    {I A B : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    [TopologicalSpace A] [TopologicalSpace B] [T2Space B] [IsTopologicalRing B]
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : I → Bool} {W : A}
    (bvc : BVCoordinates σA ε) (c : GradedLegendreChart I A B σA σB ε W)
    (hB : SupercommutativeGrading σB) (hW : σA.parity W = W)
    (hsource : ∀ i, c.source.coord (Sum.inl i) = bvc.source i)
    (haf : ∀ i, (c.source.coordD (Sum.inr i)).d = (bvc.leftAntifield i).d)
    (hWard : (sourceWardDerivative bvc).d W = 0) :
    (1 / 2 : ℚ) • canonicalAntibracket c.target (gradedLegendreAction c) (gradedLegendreAction c) = 0 := by
  apply graded_legendre_slavnov_taylor c hB hW
  change sourceWardMap bvc W = 0 at hWard
  rw [sourceWardMap_apply] at hWard
  simpa only [hsource, haf] using hWard

/-- The actual finite-logarithm connected Ward theorem feeds the Legendre
step. Evenness of the connected functional is derived from even partition
data, and the signed effective-action master equation is then proved. -/
theorem finite_log_legendre_slavnov_taylor
    {I A B : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    [TopologicalSpace A] [TopologicalSpace B] [T2Space B] [IsTopologicalRing B]
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : I → Bool}
    (bvc : BVCoordinates σA ε) (z : A) (N : ℕ)
    (c : GradedLegendreChart I A B σA σB ε (finiteLogPolynomial z N))
    (hB : SupercommutativeGrading σB) (hzEven : σA.parity z = z)
    (hsource : ∀ i, c.source.coord (Sum.inl i) = bvc.source i)
    (haf : ∀ i, (c.source.coordD (Sum.inr i)).d = (bvc.leftAntifield i).d)
    (hzWard : (sourceWardDerivative bvc).d z = 0) :
    (1 / 2 : ℚ) • canonicalAntibracket c.target (gradedLegendreAction c) (gradedLegendreAction c) = 0 := by
  exact connected_ward_legendre_slavnov_taylor bvc c hB (finiteLogPolynomial_even σA hzEven N)
    hsource haf (finite_log_polynomial_ward (sourceWardDerivative bvc) hzWard N)

theorem graded_legendre_ST_coefficient
    {I A B C : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    [AddCommGroup C] [Module ℚ C]
    [TopologicalSpace A] [TopologicalSpace B] [T2Space B] [IsTopologicalRing B]
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : I → Bool} {W : A}
    (c : GradedLegendreChart I A B σA σB ε W) (hB : SupercommutativeGrading σB)
    (hW : σA.parity W = W)
    (hWard : (∑ i, c.source.coord (Sum.inl i) * (c.source.coordD (Sum.inr i)).d W) = 0)
    (coefficient : B →ₗ[ℚ] C) :
    coefficient ((1 / 2 : ℚ) • canonicalAntibracket c.target (gradedLegendreAction c) (gradedLegendreAction c)) = 0 := by
  rw [graded_legendre_slavnov_taylor c hB hW hWard, map_zero]

end UV
