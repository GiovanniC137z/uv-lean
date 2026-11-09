import UV.LegendreBRST
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Graded variational calculus with genuine measure-space contractions.
Canonical coordinate agreement is imposed only on a dense algebra of smeared
generators. The chain rule for all admitted functionals, including the connected
functional, is derived by the graded Leibniz rule and continuity. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace UV

theorem continuum_graded_coefficient_commute
    {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    {σA : GradingInvolution A} {σB : GradingInvolution B}
    (hB : SupercommutativeGrading σB) (Φ : A →ₐ[ℚ] B)
    (hΦ : ∀ f, Φ (σA.parity f) = σB.parity (Φ f))
    {δ p : Bool} {v : B}
    (hv : σB.parity v = koszulSign (Bool.xor δ p) • v) (f : A) :
    v * Φ (if p then σA.parity f else f) =
      (if δ then σB.parity (Φ f) else Φ f) * v := by
  have hc := hB.commute (Bool.xor δ p) v hv
  cases δ <;> cases p
  · exact hc (Φ f)
  · have h := hc (σB.parity (Φ f))
    change v * σB.parity (Φ f) = σB.parity (σB.parity (Φ f)) * v at h
    rw [σB.involutive] at h
    simpa [hΦ] using h
  · exact hc (Φ f)
  · simpa [hΦ] using hc (σB.parity (Φ f))

variable {X A B : Type*} [MeasurableSpace X]
  [Ring A] [Algebra ℚ A]
  [NormedRing B] [NormedSpace ℝ B] [Algebra ℚ B] [CompleteSpace B]
  [SMulCommClass ℝ B B] [IsScalarTower ℝ B B]

def continuumJacobianIntegral (μ : Measure X) {σA : GradingInvolution A}
    {ε : X → Bool} (dcoord : ∀ x, GradedDerivative σA (ε x))
    (Φ : A →ₐ[ℚ] B) (v : X → B) (f : A) : B :=
  ∫ x, v x * Φ ((dcoord x).d f) ∂μ

omit [CompleteSpace B] [SMulCommClass ℝ B B] [IsScalarTower ℝ B B] in
theorem continuumJacobianIntegral_add (μ : Measure X) {σA : GradingInvolution A}
    {ε : X → Bool} (dcoord : ∀ x, GradedDerivative σA (ε x))
    (Φ : A →ₐ[ℚ] B) (v : X → B) (f g : A)
    (hf : Integrable (fun x => v x * Φ ((dcoord x).d f)) μ)
    (hg : Integrable (fun x => v x * Φ ((dcoord x).d g)) μ) :
    continuumJacobianIntegral μ dcoord Φ v (f+g) =
      continuumJacobianIntegral μ dcoord Φ v f + continuumJacobianIntegral μ dcoord Φ v g := by
  simp only [continuumJacobianIntegral, map_add, mul_add]
  exact integral_add hf hg

omit [CompleteSpace B] [SMulCommClass ℝ B B] [IsScalarTower ℝ B B] in
theorem continuumJacobianIntegral_algebraMap (μ : Measure X) {σA : GradingInvolution A}
    {ε : X → Bool} (dcoord : ∀ x, GradedDerivative σA (ε x))
    (Φ : A →ₐ[ℚ] B) (v : X → B) (r : ℚ) :
    continuumJacobianIntegral μ dcoord Φ v (algebraMap ℚ A r) = 0 := by
  simp [continuumJacobianIntegral, gradedDerivative_algebraMap]

omit [CompleteSpace B] in
theorem continuumJacobianIntegral_leibniz (μ : Measure X)
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : X → Bool}
    (dcoord : ∀ x, GradedDerivative σA (ε x))
    (hB : SupercommutativeGrading σB) (Φ : A →ₐ[ℚ] B)
    (hΦ : ∀ f, Φ (σA.parity f) = σB.parity (Φ f))
    {δ : Bool} (v : X → B)
    (hv : ∀ x, σB.parity (v x) = koszulSign (Bool.xor δ (ε x)) • v x)
    (f g : A)
    (hf : Integrable (fun x => v x * Φ ((dcoord x).d f)) μ)
    (hg : Integrable (fun x => v x * Φ ((dcoord x).d g)) μ) :
    continuumJacobianIntegral μ dcoord Φ v (f*g) =
      continuumJacobianIntegral μ dcoord Φ v f * Φ g +
        (if δ then σB.parity (Φ f) else Φ f) * continuumJacobianIntegral μ dcoord Φ v g := by
  have he : (fun x => v x * Φ ((dcoord x).d (f*g))) =
      fun x => (v x * Φ ((dcoord x).d f)) * Φ g +
        (if δ then σB.parity (Φ f) else Φ f) * (v x * Φ ((dcoord x).d g)) := by
    funext x
    rw [(dcoord x).leibniz, map_add, map_mul, map_mul, mul_add]
    congr 1
    · exact (mul_assoc _ _ _).symm
    · rw [← mul_assoc, continuum_graded_coefficient_commute hB Φ hΦ (hv x), mul_assoc]
  unfold continuumJacobianIntegral
  rw [he, integral_add (hf.mul_const _) (hg.const_mul _),
    integral_mul_const_of_integrable hf, integral_const_mul_of_integrable hg]

omit [CompleteSpace B] in
/-- Agreement on a generating family derives the full continuum pullback
chain rule on its polynomial algebra. The residual derivative is the
fixed-antifield variation; it is an actual graded derivative on the source. -/
theorem continuum_chain_rule_on_coordinate_algebra
    (μ : Measure X) {σA : GradingInvolution A} {σB : GradingInvolution B}
    {ε : X → Bool} (dcoord : ∀ x, GradedDerivative σA (ε x))
    (hB : SupercommutativeGrading σB) (Φ : A →ₐ[ℚ] B)
    (hΦ : ∀ f, Φ (σA.parity f) = σB.parity (Φ f))
    {δ : Bool} (D : GradedDerivative σB δ) (E : GradedDerivative σA δ)
    (v : X → B)
    (hv : ∀ x, σB.parity (v x) = koszulSign (Bool.xor δ (ε x)) • v x)
    (hI : ∀ f, Integrable (fun x => v x * Φ ((dcoord x).d f)) μ)
    (S : Set A)
    (hcoord : ∀ f ∈ S, D.d (Φ f) = continuumJacobianIntegral μ dcoord Φ v f + Φ (E.d f))
    {f : A} (hf : f ∈ Algebra.adjoin ℚ S) :
    D.d (Φ f) = continuumJacobianIntegral μ dcoord Φ v f + Φ (E.d f) := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf => exact hcoord f hf
  | algebraMap r =>
    rw [Φ.commutes r, gradedDerivative_algebraMap,
      continuumJacobianIntegral_algebraMap, gradedDerivative_algebraMap]
    simp
  | add f g _ _ hf hg =>
    rw [map_add, map_add, hf, hg, continuumJacobianIntegral_add μ dcoord Φ v f g (hI f) (hI g),
      map_add, map_add]
    abel
  | mul f g _ _ hf hg =>
    rw [map_mul, D.leibniz, hf, hg,
      continuumJacobianIntegral_leibniz μ dcoord hB Φ hΦ v hv f g (hI f) (hI g),
      E.leibniz, map_add, map_mul, map_mul]
    have hpar : Φ (if δ then σA.parity f else f) =
        (if δ then σB.parity (Φ f) else Φ f) := by cases δ <;> simp [hΦ]
    rw [hpar]
    noncomm_ring

omit [CompleteSpace B] in
/-- Actual integral contractions and dense smeared polynomial coordinates
give the chain rule on the admitted completion, without a finite index set. -/
theorem continuum_chain_rule_on_completion
    [TopologicalSpace A] (μ : Measure X)
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : X → Bool}
    (dcoord : ∀ x, GradedDerivative σA (ε x))
    (hB : SupercommutativeGrading σB) (Φ : A →ₐ[ℚ] B)
    (hΦ : ∀ f, Φ (σA.parity f) = σB.parity (Φ f))
    {δ : Bool} (D : GradedDerivative σB δ) (E : GradedDerivative σA δ)
    (v : X → B)
    (hv : ∀ x, σB.parity (v x) = koszulSign (Bool.xor δ (ε x)) • v x)
    (hI : ∀ f, Integrable (fun x => v x * Φ ((dcoord x).d f)) μ)
    (S : Set A) (hdense : Dense (Algebra.adjoin ℚ S : Set A))
    (hcoord : ∀ f ∈ S, D.d (Φ f) = continuumJacobianIntegral μ dcoord Φ v f + Φ (E.d f))
    (hleft : Continuous (fun f => D.d (Φ f)))
    (hjac : Continuous (continuumJacobianIntegral μ dcoord Φ v))
    (hres : Continuous (fun f => Φ (E.d f))) (f : A) :
    D.d (Φ f) = continuumJacobianIntegral μ dcoord Φ v f + Φ (E.d f) := by
  exact congr_fun (Continuous.ext_on hdense hleft (hjac.add hres)
    (fun f hf => continuum_chain_rule_on_coordinate_algebra μ dcoord hB Φ hΦ D E v hv hI S hcoord hf)) f

def continuumLegendreAction (μ : Measure X) (J φ : X → B)
    (Φ : A →ₐ[ℚ] B) (W : A) : B := (∫ x, J x * φ x ∂μ) - Φ W

omit [SMulCommClass ℝ B B] [IsScalarTower ℝ B B] in
/-- A continuous real-linear realization of the admitted graded derivative
commutes with the actual Bochner integral. The product rule is then derived
pointwise from the graded Leibniz law. -/
theorem continuum_pairing_derivative (μ : Measure X)
    {σB : GradingInvolution B} {δ : Bool} (D : GradedDerivative σB δ)
    (L : B →L[ℝ] B) (hL : ∀ f, L f = D.d f) (J φ : X → B)
    (hI : Integrable (fun x => J x * φ x) μ)
    (hDJ : Integrable (fun x => D.d (J x) * φ x) μ)
    (hDφ : Integrable (fun x => (if δ then σB.parity (J x) else J x) * D.d (φ x)) μ) :
    D.d (∫ x, J x * φ x ∂μ) =
      (∫ x, D.d (J x) * φ x ∂μ) +
        ∫ x, (if δ then σB.parity (J x) else J x) * D.d (φ x) ∂μ := by
  calc
    _ = L (∫ x, J x * φ x ∂μ) := (hL _).symm
    _ = ∫ x, L (J x * φ x) ∂μ := (L.integral_comp_comm hI).symm
    _ = _ := by simp_rw [hL, D.leibniz]; exact integral_add hDJ hDφ

/-- The actual source-first Legendre variation on a continuum contraction.
Only coordinate-generator agreement is assumed. Its chain rule at W and
the cancellation of the source-Jacobian terms are conclusions. -/
theorem continuum_legendre_variation
    [TopologicalSpace A] (μ : Measure X)
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : X → Bool}
    (dcoord : ∀ x, GradedDerivative σA (ε x))
    (hB : SupercommutativeGrading σB) (Φ : A →ₐ[ℚ] B)
    (hΦ : ∀ f, Φ (σA.parity f) = σB.parity (Φ f))
    {δ : Bool} (D : GradedDerivative σB δ) (E : GradedDerivative σA δ)
    (L : B →L[ℝ] B) (hL : ∀ f, L f = D.d f) (J φ : X → B) (W : A)
    (hJ : ∀ x, σB.parity (J x) = koszulSign (ε x) • J x)
    (hgradient : ∀ x, Φ ((dcoord x).d W) = φ x)
    (hgradI : ∀ f, Integrable (fun x => D.d (J x) * Φ ((dcoord x).d f)) μ)
    (S : Set A) (hdense : Dense (Algebra.adjoin ℚ S : Set A))
    (hcoord : ∀ f ∈ S, D.d (Φ f) =
      continuumJacobianIntegral μ dcoord Φ (fun x => D.d (J x)) f + Φ (E.d f))
    (hleft : Continuous (fun f => D.d (Φ f)))
    (hjac : Continuous (continuumJacobianIntegral μ dcoord Φ (fun x => D.d (J x))))
    (hres : Continuous (fun f => Φ (E.d f)))
    (hI : Integrable (fun x => J x * φ x) μ)
    (hDφ : Integrable (fun x => (if δ then σB.parity (J x) else J x) * D.d (φ x)) μ) :
    D.d (continuumLegendreAction μ J φ Φ W) =
      (∫ x, (if δ then σB.parity (J x) else J x) * D.d (φ x) ∂μ) - Φ (E.d W) := by
  have hv : ∀ x, σB.parity (D.d (J x)) =
      koszulSign (Bool.xor δ (ε x)) • D.d (J x) :=
    fun x => gradedDerivative_homogeneous_value D (hJ x)
  have hchain := continuum_chain_rule_on_completion μ dcoord hB Φ hΦ D E
    (fun x => D.d (J x)) hv hgradI S hdense hcoord hleft hjac hres W
  have hDJ : Integrable (fun x => D.d (J x) * φ x) μ := by
    simpa only [hgradient] using hgradI W
  unfold continuumLegendreAction
  rw [map_sub, continuum_pairing_derivative μ D L hL J φ hI hDJ hDφ, hchain]
  have hH : continuumJacobianIntegral μ dcoord Φ (fun x => D.d (J x)) W =
      ∫ x, D.d (J x) * φ x ∂μ := by simp only [continuumJacobianIntegral, hgradient]
  rw [hH]
  abel

end UV
