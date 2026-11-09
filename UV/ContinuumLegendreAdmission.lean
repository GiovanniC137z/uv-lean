import UV.ContinuumLegendreWeak

/-! A common smeared functional domain for the continuum Legendre step.
The admission data concerns canonical test variations and dense coordinate
generators. Effective-action derivatives are derived, never admission fields. -/

noncomputable section
open MeasureTheory

namespace UV

def zeroGradedDerivative {A : Type*} [Ring A] [Algebra ℚ A]
    (σ : GradingInvolution A) (δ : Bool) : GradedDerivative σ δ where
  d := 0
  leibniz f g := by simp
  homogeneous f := by simp

variable {X A B : Type*} [MeasurableSpace X]
  [Ring A] [Algebra ℚ A] [Algebra ℝ A] [TopologicalSpace A]
  [IsTopologicalRing A] [ContinuousSMul ℝ A] [T2Space A] [SeparatingDual ℝ A]
  [Ring B] [Algebra ℚ B] [Algebra ℝ B] [TopologicalSpace B]
  [IsTopologicalRing B] [ContinuousSMul ℝ B] [T2Space B] [SeparatingDual ℝ B]

structure WeakLegendreVariationAdmission (μ : Measure X)
    {σA : GradingInvolution A} {σB : GradingInvolution B} {ε : X → Bool}
    (dcoord : ∀ x, GradedDerivative σA (ε x)) (Φ : A →ₐ[ℚ] B)
    (J : X → B) (S : Set A) {δ : Bool}
    (D : GradedDerivative σB δ) (E : GradedDerivative σA δ) : Prop where
  derivative_continuous : Continuous D.d
  integrable : ∀ f, WeakIntegrable μ (fun x => D.d (J x) * Φ ((dcoord x).d f))
  coordinate : ∀ f ∈ S, D.d (Φ f) =
    weakJacobianIntegral μ dcoord Φ (fun x => D.d (J x)) f + Φ (E.d f)
  jacobian_continuous : Continuous (weakJacobianIntegral μ dcoord Φ (fun x => D.d (J x)))
  residual_continuous : Continuous (fun f => Φ (E.d f))

/-- Test directions carry their species parity, while spacetime is the
arbitrary measure space X. Canonical variations are stated only after
smearing; no ordinary-function Dirac delta is postulated. -/
structure WeakContinuumLegendreDomain (μ : Measure X)
    (σA : GradingInvolution A) (σB : GradingInvolution B)
    (ε : X → Bool) (W : A) (G : Type*) (T : Bool → Type*) where
  sourceD : ∀ x, GradedDerivative σA (ε x)
  sourceAfD : ∀ x, GradedDerivative σA (!(ε x))
  pull : A →ₐ[ℚ] B
  pull_continuous : Continuous pull
  preserves_parity : ∀ f, pull (σA.parity f) = σB.parity (pull f)
  supercommutative : SupercommutativeGrading σB
  parity_continuous : Continuous σB.parity
  source : X → B
  source_parity : ∀ x, σB.parity (source x) = koszulSign (ε x) • source x
  generator : G → A
  polynomial_dense : Dense (Algebra.adjoin ℚ (Set.range generator) : Set A)
  test : ∀ δ, T δ → X → ℝ
  test_support : ∀ δ t x, ε x ≠ δ → test δ t x = 0
  fieldD : ∀ δ, T δ → GradedDerivative σB δ
  antifieldD : ∀ δ, T δ → GradedDerivative σB (!δ)
  residualAfD : ∀ δ, T δ → GradedDerivative σA (!δ)
  field_admission : ∀ δ t, WeakLegendreVariationAdmission μ sourceD pull source
    (Set.range generator) (fieldD δ t) (zeroGradedDerivative σA δ)
  antifield_admission : ∀ δ t, WeakLegendreVariationAdmission μ sourceD pull source
    (Set.range generator) (antifieldD δ t) (residualAfD δ t)
  inverse_gradient_coordinate : ∀ δ t x,
    (fieldD δ t).d (pull ((sourceD x).d W)) = test δ t x • (1 : B)
  fixed_antifield_gradient : ∀ δ t x,
    (antifieldD δ t).d (pull ((sourceD x).d W)) = 0
  residual_antifield_integrable : ∀ δ t f,
    WeakIntegrable μ (fun x => test δ t x • (sourceAfD x).d f)
  residual_antifield_representation : ∀ δ t f,
    (residualAfD δ t).d f = weakIntegral μ (fun x => test δ t x • (sourceAfD x).d f)
  legendre_pair_integrable : WeakIntegrable μ
    (fun x => source x * pull ((sourceD x).d W))
  source_test_integrable : ∀ δ t, WeakIntegrable μ (fun x => test δ t x • source x)
  test_separates : ∀ u v : X → B,
    (∀ δ t, WeakIntegrable μ (fun x => test δ t x • u x)) →
    (∀ δ t, WeakIntegrable μ (fun x => test δ t x • v x)) →
    (∀ δ t, weakIntegral μ (fun x => test δ t x • u x) =
      weakIntegral μ (fun x => test δ t x • v x)) → u =ᵐ[μ] v
  sourceWard : GradedDerivative σA true
  ward_integrable : ∀ f, WeakIntegrable μ
    (fun x => source x * pull ((sourceAfD x).d f))
  ward_representation : ∀ f, pull (sourceWard.d f) = weakIntegral μ
    (fun x => source x * pull ((sourceAfD x).d f))

def weakEffectiveAction {μ : Measure X} {σA : GradingInvolution A}
    {σB : GradingInvolution B} {ε : X → Bool} {W : A} {G : Type*} {T : Bool → Type*}
    (c : WeakContinuumLegendreDomain μ σA σB ε W G T) : B :=
  weakContinuumLegendreAction μ c.source (fun x => c.pull ((c.sourceD x).d W)) c.pull W

omit [IsTopologicalRing A] [ContinuousSMul ℝ A] [T2Space A] [SeparatingDual ℝ A]
  [IsTopologicalRing B] in
theorem weak_effective_action_even {μ : Measure X} {σA : GradingInvolution A}
    {σB : GradingInvolution B} {ε : X → Bool} {W : A} {G : Type*} {T : Bool → Type*}
    (c : WeakContinuumLegendreDomain μ σA σB ε W G T) (hW : σA.parity W = W) :
    σB.parity (weakEffectiveAction c) = weakEffectiveAction c := by
  let P := σB.parity.toAddMonoidHom.toRealLinearMap c.parity_continuous
  have hp x : σB.parity (c.pull ((c.sourceD x).d W)) =
      koszulSign (ε x) • c.pull ((c.sourceD x).d W) := by
    rw [← c.preserves_parity]
    have h := gradedDerivative_homogeneous_value (p := false) (c.sourceD x)
      (by simpa [koszulSign] using hW)
    simpa [map_smul] using congrArg c.pull h
  have he x : σB.parity (c.source x * c.pull ((c.sourceD x).d W)) =
      c.source x * c.pull ((c.sourceD x).d W) := by
    rw [map_mul, c.source_parity, hp]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, koszulSign_square, one_smul]
  have hi : σB.parity (weakIntegral μ (fun x => c.source x * c.pull ((c.sourceD x).d W))) =
      weakIntegral μ (fun x => c.source x * c.pull ((c.sourceD x).d W)) := by
    change P _ = _
    rw [← weakIntegral_map P c.legendre_pair_integrable]
    exact weakIntegral_congr he
  unfold weakEffectiveAction weakContinuumLegendreAction
  rw [map_sub, hi, ← c.preserves_parity, hW]

omit [IsTopologicalRing B] [ContinuousSMul ℝ B] [T2Space B] in
theorem weakIntegral_koszulSign {μ : Measure X} {f : X → B}
    (hf : WeakIntegrable μ f) (δ : Bool) :
    weakIntegral μ (fun x => koszulSign δ • f x) = koszulSign δ • weakIntegral μ f := by
  cases δ <;> simp [koszulSign, weakIntegral_neg hf]

omit [IsTopologicalRing B] [ContinuousSMul ℝ B] [T2Space B] [SeparatingDual ℝ B] in
theorem WeakIntegrable.koszulSign {μ : Measure X} {f : X → B}
    (hf : WeakIntegrable μ f) (δ : Bool) :
    WeakIntegrable μ (fun x => koszulSign δ • f x) := by
  cases δ
  · simpa [UV.koszulSign] using hf
  · simpa [UV.koszulSign] using hf.neg

omit [IsTopologicalRing A] [ContinuousSMul ℝ A] [T2Space A] [SeparatingDual ℝ A] in
theorem weak_effective_action_right_field_variation
    {μ : Measure X} {σA : GradingInvolution A} {σB : GradingInvolution B}
    {ε : X → Bool} {W : A} {G : Type*} {T : Bool → Type*}
    (c : WeakContinuumLegendreDomain μ σA σB ε W G T)
    (hW : σA.parity W = W) (δ : Bool) (t : T δ) :
    rightGradedDerivative (c.fieldD δ t) (weakEffectiveAction c) =
      weakIntegral μ (fun x => c.test δ t x • c.source x) := by
  let D := c.fieldD δ t
  let L := D.d.toAddMonoidHom.toRealLinearMap (c.field_admission δ t).derivative_continuous
  have he x : (if δ then σB.parity (c.source x) else c.source x) *
      D.d (c.pull ((c.sourceD x).d W)) = koszulSign δ • (c.test δ t x • c.source x) := by
    rw [c.inverse_gradient_coordinate]
    by_cases hx : ε x = δ
    · have hj := c.source_parity x
      rw [hx] at hj
      cases δ <;> simp [koszulSign, hj]
    · rw [c.test_support δ t x hx]
      simp
  have hDφ : WeakIntegrable μ (fun x => (if δ then σB.parity (c.source x) else c.source x) *
      D.d (c.pull ((c.sourceD x).d W))) :=
    ((c.source_test_integrable δ t).koszulSign δ).congr_ae
      (Filter.Eventually.of_forall (fun x => (he x).symm))
  have hv := weak_continuum_legendre_variation μ c.sourceD c.supercommutative c.pull
    c.preserves_parity D (zeroGradedDerivative σA δ) L (fun _ => rfl)
    c.source (fun x => c.pull ((c.sourceD x).d W)) W c.source_parity (fun _ => rfl)
    (c.field_admission δ t).integrable (Set.range c.generator) c.polynomial_dense
    (c.field_admission δ t).coordinate
    ((c.field_admission δ t).derivative_continuous.comp c.pull_continuous)
    (c.field_admission δ t).jacobian_continuous (c.field_admission δ t).residual_continuous
    c.legendre_pair_integrable hDφ
  change D.d (weakEffectiveAction c) = _ at hv
  rw [show (fun x => (if δ then σB.parity (c.source x) else c.source x) *
    D.d (c.pull ((c.sourceD x).d W))) = fun x => koszulSign δ • (c.test δ t x • c.source x)
      from funext he, weakIntegral_koszulSign (c.source_test_integrable δ t) δ] at hv
  simp only [zeroGradedDerivative, LinearMap.zero_apply, map_zero, sub_zero] at hv
  rw [rightGradedDerivative_of_even _ (weak_effective_action_even c hW), hv,
    smul_smul, koszulSign_square, one_smul]

omit [IsTopologicalRing A] [T2Space A] [SeparatingDual ℝ A] in
theorem weak_effective_action_left_antifield_variation
    {μ : Measure X} {σA : GradingInvolution A} {σB : GradingInvolution B}
    {ε : X → Bool} {W : A} {G : Type*} {T : Bool → Type*}
    (c : WeakContinuumLegendreDomain μ σA σB ε W G T) (δ : Bool) (t : T δ) :
    (c.antifieldD δ t).d (weakEffectiveAction c) =
      weakIntegral μ (fun x => c.test δ t x • (-c.pull ((c.sourceAfD x).d W))) := by
  let D := c.antifieldD δ t
  let L := D.d.toAddMonoidHom.toRealLinearMap (c.antifield_admission δ t).derivative_continuous
  let ΦL := c.pull.toAddMonoidHom.toRealLinearMap c.pull_continuous
  have hzero (x : X) : D.d (c.pull ((c.sourceD x).d W)) = 0 := c.fixed_antifield_gradient δ t x
  have hDφ : WeakIntegrable μ (fun x => (if !δ then σB.parity (c.source x) else c.source x) *
      D.d (c.pull ((c.sourceD x).d W))) := by
    simpa only [hzero, mul_zero] using (weakIntegrable_zero μ :
      WeakIntegrable μ (fun _ : X => (0 : B)))
  have hv := weak_continuum_legendre_variation μ c.sourceD c.supercommutative c.pull
    c.preserves_parity D (c.residualAfD δ t) L (fun _ => rfl)
    c.source (fun x => c.pull ((c.sourceD x).d W)) W c.source_parity (fun _ => rfl)
    (c.antifield_admission δ t).integrable (Set.range c.generator) c.polynomial_dense
    (c.antifield_admission δ t).coordinate
    ((c.antifield_admission δ t).derivative_continuous.comp c.pull_continuous)
    (c.antifield_admission δ t).jacobian_continuous (c.antifield_admission δ t).residual_continuous
    c.legendre_pair_integrable hDφ
  change D.d (weakEffectiveAction c) = _ at hv
  simp only [hzero, mul_zero, weakIntegral_zero, zero_sub] at hv
  rw [hv, c.residual_antifield_representation]
  have hmap := weakIntegral_map ΦL (c.residual_antifield_integrable δ t W)
  have hI : WeakIntegrable μ (fun x => c.test δ t x • c.pull ((c.sourceAfD x).d W)) := by
    simpa only [map_smul] using (c.residual_antifield_integrable δ t W).map ΦL
  have hmap' : c.pull (weakIntegral μ (fun x => c.test δ t x • (c.sourceAfD x).d W)) =
      weakIntegral μ (fun x => c.test δ t x • c.pull ((c.sourceAfD x).d W)) := by
    simpa only [map_smul] using hmap.symm
  rw [hmap']
  symm
  simpa only [smul_neg] using weakIntegral_neg hI

end UV
