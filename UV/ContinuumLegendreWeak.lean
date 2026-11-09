import UV.ContinuumLegendre
import UV.WeakFunctionalIntegral

/-! Continuum Legendre calculus in a locally convex functional algebra.
Integrals are actual scalar-tested weak integrals, so no Banach norm or
bounded canonical bosonic derivative is imposed on the functional algebra. -/

noncomputable section
open MeasureTheory

namespace UV

variable {X A B : Type*} [MeasurableSpace X]
  [Ring A] [Algebra ℚ A]
  [Ring B] [Algebra ℚ B] [Algebra ℝ B] [TopologicalSpace B]
  [IsTopologicalRing B] [SeparatingDual ℝ B]

def weakMulLeft (b : B) : B →L[ℝ] B :=
  { LinearMap.mulLeft ℝ b with cont := continuous_const.mul continuous_id }

def weakMulRight (b : B) : B →L[ℝ] B :=
  { LinearMap.mulRight ℝ b with cont := continuous_id.mul continuous_const }

omit [Algebra ℚ B] [SeparatingDual ℝ B] in
theorem WeakIntegrable.const_mul' {μ : Measure X} {f : X → B}
    (hf : WeakIntegrable μ f) (b : B) : WeakIntegrable μ (fun x => b * f x) :=
  hf.map (weakMulLeft b)

omit [Algebra ℚ B] [SeparatingDual ℝ B] in
theorem WeakIntegrable.mul_const' {μ : Measure X} {f : X → B}
    (hf : WeakIntegrable μ f) (b : B) : WeakIntegrable μ (fun x => f x * b) :=
  hf.map (weakMulRight b)

omit [Algebra ℚ B] in
theorem weakIntegral_const_mul' {μ : Measure X} {f : X → B}
    (hf : WeakIntegrable μ f) (b : B) :
    weakIntegral μ (fun x => b * f x) = b * weakIntegral μ f :=
  weakIntegral_map (weakMulLeft b) hf

omit [Algebra ℚ B] in
theorem weakIntegral_mul_const' {μ : Measure X} {f : X → B}
    (hf : WeakIntegrable μ f) (b : B) :
    weakIntegral μ (fun x => f x * b) = weakIntegral μ f * b :=
  weakIntegral_map (weakMulRight b) hf

def weakJacobianIntegral (μ : Measure X) {σA : GradingInvolution A}
    {ε : X → Bool} (dcoord : ∀ x, GradedDerivative σA (ε x))
    (Φ : A →ₐ[ℚ] B) (v : X → B) (f : A) : B :=
  weakIntegral μ (fun x => v x * Φ ((dcoord x).d f))

omit [IsTopologicalRing B] in
theorem weakJacobianIntegral_add (μ : Measure X) {σA : GradingInvolution A}
    {ε : X → Bool} (dcoord : ∀ x, GradedDerivative σA (ε x))
    (Φ : A →ₐ[ℚ] B) (v : X → B) (f g : A)
    (hf : WeakIntegrable μ (fun x => v x * Φ ((dcoord x).d f)))
    (hg : WeakIntegrable μ (fun x => v x * Φ ((dcoord x).d g))) :
    weakJacobianIntegral μ dcoord Φ v (f+g) =
      weakJacobianIntegral μ dcoord Φ v f + weakJacobianIntegral μ dcoord Φ v g := by
  simp only [weakJacobianIntegral, map_add, mul_add]
  exact weakIntegral_add hf hg

omit [IsTopologicalRing B] in
theorem weakJacobianIntegral_algebraMap (μ : Measure X) {σA : GradingInvolution A}
    {ε : X → Bool} (dcoord : ∀ x, GradedDerivative σA (ε x))
    (Φ : A →ₐ[ℚ] B) (v : X → B) (r : ℚ) :
    weakJacobianIntegral μ dcoord Φ v (algebraMap ℚ A r) = 0 := by
  simp [weakJacobianIntegral, gradedDerivative_algebraMap, weakIntegral_zero]

theorem weakJacobianIntegral_leibniz (μ : Measure X)
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : X → Bool}
    (dcoord : ∀ x, GradedDerivative σA (ε x))
    (hB : SupercommutativeGrading σB) (Φ : A →ₐ[ℚ] B)
    (hΦ : ∀ f, Φ (σA.parity f) = σB.parity (Φ f))
    {δ : Bool} (v : X → B)
    (hv : ∀ x, σB.parity (v x) = koszulSign (Bool.xor δ (ε x)) • v x)
    (f g : A)
    (hf : WeakIntegrable μ (fun x => v x * Φ ((dcoord x).d f)))
    (hg : WeakIntegrable μ (fun x => v x * Φ ((dcoord x).d g))) :
    weakJacobianIntegral μ dcoord Φ v (f*g) =
      weakJacobianIntegral μ dcoord Φ v f * Φ g +
        (if δ then σB.parity (Φ f) else Φ f) * weakJacobianIntegral μ dcoord Φ v g := by
  have he : (fun x => v x * Φ ((dcoord x).d (f*g))) =
      fun x => (v x * Φ ((dcoord x).d f)) * Φ g +
        (if δ then σB.parity (Φ f) else Φ f) * (v x * Φ ((dcoord x).d g)) := by
    funext x
    rw [(dcoord x).leibniz, map_add, map_mul, map_mul, mul_add]
    congr 1
    · exact (mul_assoc _ _ _).symm
    · rw [← mul_assoc, continuum_graded_coefficient_commute hB Φ hΦ (hv x), mul_assoc]
  unfold weakJacobianIntegral
  rw [he, weakIntegral_add (hf.mul_const' _) (hg.const_mul' _),
    weakIntegral_mul_const' hf, weakIntegral_const_mul' hg]

theorem weak_continuum_chain_rule_on_coordinate_algebra
    (μ : Measure X) {σA : GradingInvolution A} {σB : GradingInvolution B}
    {ε : X → Bool} (dcoord : ∀ x, GradedDerivative σA (ε x))
    (hB : SupercommutativeGrading σB) (Φ : A →ₐ[ℚ] B)
    (hΦ : ∀ f, Φ (σA.parity f) = σB.parity (Φ f))
    {δ : Bool} (D : GradedDerivative σB δ) (E : GradedDerivative σA δ)
    (v : X → B)
    (hv : ∀ x, σB.parity (v x) = koszulSign (Bool.xor δ (ε x)) • v x)
    (hI : ∀ f, WeakIntegrable μ (fun x => v x * Φ ((dcoord x).d f)))
    (S : Set A)
    (hcoord : ∀ f ∈ S, D.d (Φ f) = weakJacobianIntegral μ dcoord Φ v f + Φ (E.d f))
    {f : A} (hf : f ∈ Algebra.adjoin ℚ S) :
    D.d (Φ f) = weakJacobianIntegral μ dcoord Φ v f + Φ (E.d f) := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf => exact hcoord f hf
  | algebraMap r =>
    rw [Φ.commutes r, gradedDerivative_algebraMap,
      weakJacobianIntegral_algebraMap, gradedDerivative_algebraMap]
    simp
  | add f g _ _ hf hg =>
    rw [map_add, map_add, hf, hg, weakJacobianIntegral_add μ dcoord Φ v f g (hI f) (hI g),
      map_add, map_add]
    abel
  | mul f g _ _ hf hg =>
    rw [map_mul, D.leibniz, hf, hg,
      weakJacobianIntegral_leibniz μ dcoord hB Φ hΦ v hv f g (hI f) (hI g),
      E.leibniz, map_add, map_mul, map_mul]
    have hpar : Φ (if δ then σA.parity f else f) =
        (if δ then σB.parity (Φ f) else Φ f) := by cases δ <;> simp [hΦ]
    rw [hpar]
    noncomm_ring

theorem weak_continuum_chain_rule_on_completion
    [TopologicalSpace A] [T2Space B] (μ : Measure X)
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : X → Bool}
    (dcoord : ∀ x, GradedDerivative σA (ε x))
    (hB : SupercommutativeGrading σB) (Φ : A →ₐ[ℚ] B)
    (hΦ : ∀ f, Φ (σA.parity f) = σB.parity (Φ f))
    {δ : Bool} (D : GradedDerivative σB δ) (E : GradedDerivative σA δ)
    (v : X → B)
    (hv : ∀ x, σB.parity (v x) = koszulSign (Bool.xor δ (ε x)) • v x)
    (hI : ∀ f, WeakIntegrable μ (fun x => v x * Φ ((dcoord x).d f)))
    (S : Set A) (hdense : Dense (Algebra.adjoin ℚ S : Set A))
    (hcoord : ∀ f ∈ S, D.d (Φ f) = weakJacobianIntegral μ dcoord Φ v f + Φ (E.d f))
    (hleft : Continuous (fun f => D.d (Φ f)))
    (hjac : Continuous (weakJacobianIntegral μ dcoord Φ v))
    (hres : Continuous (fun f => Φ (E.d f))) (f : A) :
    D.d (Φ f) = weakJacobianIntegral μ dcoord Φ v f + Φ (E.d f) := by
  exact congr_fun (Continuous.ext_on hdense hleft (hjac.add hres)
    (fun f hf => weak_continuum_chain_rule_on_coordinate_algebra μ dcoord hB Φ hΦ D E v hv hI S hcoord hf)) f

def weakContinuumLegendreAction (μ : Measure X) (J φ : X → B)
    (Φ : A →ₐ[ℚ] B) (W : A) : B := weakIntegral μ (fun x => J x * φ x) - Φ W

omit [IsTopologicalRing B] in
theorem weak_continuum_pairing_derivative (μ : Measure X)
    {σB : GradingInvolution B} {δ : Bool} (D : GradedDerivative σB δ)
    (L : B →L[ℝ] B) (hL : ∀ f, L f = D.d f) (J φ : X → B)
    (hI : WeakIntegrable μ (fun x => J x * φ x))
    (hDJ : WeakIntegrable μ (fun x => D.d (J x) * φ x))
    (hDφ : WeakIntegrable μ (fun x => (if δ then σB.parity (J x) else J x) * D.d (φ x))) :
    D.d (weakIntegral μ (fun x => J x * φ x)) =
      weakIntegral μ (fun x => D.d (J x) * φ x) +
        weakIntegral μ (fun x => (if δ then σB.parity (J x) else J x) * D.d (φ x)) := by
  calc
    _ = L (weakIntegral μ (fun x => J x * φ x)) := (hL _).symm
    _ = weakIntegral μ (fun x => L (J x * φ x)) := (weakIntegral_map L hI).symm
    _ = _ := by simp_rw [hL, D.leibniz]; exact weakIntegral_add hDJ hDφ

theorem weak_continuum_legendre_variation
    [TopologicalSpace A] [T2Space B] (μ : Measure X)
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : X → Bool}
    (dcoord : ∀ x, GradedDerivative σA (ε x))
    (hB : SupercommutativeGrading σB) (Φ : A →ₐ[ℚ] B)
    (hΦ : ∀ f, Φ (σA.parity f) = σB.parity (Φ f))
    {δ : Bool} (D : GradedDerivative σB δ) (E : GradedDerivative σA δ)
    (L : B →L[ℝ] B) (hL : ∀ f, L f = D.d f) (J φ : X → B) (W : A)
    (hJ : ∀ x, σB.parity (J x) = koszulSign (ε x) • J x)
    (hgradient : ∀ x, Φ ((dcoord x).d W) = φ x)
    (hgradI : ∀ f, WeakIntegrable μ (fun x => D.d (J x) * Φ ((dcoord x).d f)))
    (S : Set A) (hdense : Dense (Algebra.adjoin ℚ S : Set A))
    (hcoord : ∀ f ∈ S, D.d (Φ f) =
      weakJacobianIntegral μ dcoord Φ (fun x => D.d (J x)) f + Φ (E.d f))
    (hleft : Continuous (fun f => D.d (Φ f)))
    (hjac : Continuous (weakJacobianIntegral μ dcoord Φ (fun x => D.d (J x))))
    (hres : Continuous (fun f => Φ (E.d f)))
    (hI : WeakIntegrable μ (fun x => J x * φ x))
    (hDφ : WeakIntegrable μ (fun x => (if δ then σB.parity (J x) else J x) * D.d (φ x))) :
    D.d (weakContinuumLegendreAction μ J φ Φ W) =
      weakIntegral μ (fun x => (if δ then σB.parity (J x) else J x) * D.d (φ x)) - Φ (E.d W) := by
  have hv : ∀ x, σB.parity (D.d (J x)) =
      koszulSign (Bool.xor δ (ε x)) • D.d (J x) :=
    fun x => gradedDerivative_homogeneous_value D (hJ x)
  have hchain := weak_continuum_chain_rule_on_completion μ dcoord hB Φ hΦ D E
    (fun x => D.d (J x)) hv hgradI S hdense hcoord hleft hjac hres W
  have hDJ : WeakIntegrable μ (fun x => D.d (J x) * φ x) := by
    simpa only [hgradient] using hgradI W
  unfold weakContinuumLegendreAction
  rw [map_sub, weak_continuum_pairing_derivative μ D L hL J φ hI hDJ hDφ, hchain]
  have hH : weakJacobianIntegral μ dcoord Φ (fun x => D.d (J x)) W =
      weakIntegral μ (fun x => D.d (J x) * φ x) := by simp only [weakJacobianIntegral, hgradient]
  rw [hH]
  abel

end UV
