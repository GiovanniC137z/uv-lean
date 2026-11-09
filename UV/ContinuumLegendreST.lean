import UV.ContinuumLegendreAdmission

/-! Actual smeared derivatives determine the effective-action gradient
profiles. Their weak-integral antibracket vanishes by the connected Ward
identity; no effective-action derivative is an admission premise. -/

noncomputable section
open MeasureTheory

namespace UV

variable {X A B : Type*} [MeasurableSpace X]
  [Ring A] [Algebra ℚ A] [Algebra ℝ A] [TopologicalSpace A]
  [IsTopologicalRing A] [ContinuousSMul ℝ A] [T2Space A] [SeparatingDual ℝ A]
  [Ring B] [Algebra ℚ B] [Algebra ℝ B] [TopologicalSpace B]
  [IsTopologicalRing B] [ContinuousSMul ℝ B] [T2Space B] [SeparatingDual ℝ B]
  {μ : Measure X} {σA : GradingInvolution A} {σB : GradingInvolution B}
  {ε : X → Bool} {W : A} {G : Type*} {T : Bool → Type*}

/-- Variational gradients are densities representing all admitted smeared
directional derivatives. The test-space separation law makes them unique
almost everywhere, rather than choosing arbitrary pointwise δ coordinates. -/
structure WeakEffectiveGradientPair
    (c : WeakContinuumLegendreDomain μ σA σB ε W G T) (F : B) where
  rightField : X → B
  leftAntifield : X → B
  field_integrable : ∀ δ t, WeakIntegrable μ (fun x => c.test δ t x • rightField x)
  antifield_integrable : ∀ δ t, WeakIntegrable μ (fun x => c.test δ t x • leftAntifield x)
  field_representation : ∀ δ t, rightGradedDerivative (c.fieldD δ t) F =
    weakIntegral μ (fun x => c.test δ t x • rightField x)
  antifield_representation : ∀ δ t, (c.antifieldD δ t).d F =
    weakIntegral μ (fun x => c.test δ t x • leftAntifield x)

omit [IsTopologicalRing A] [ContinuousSMul ℝ A] [T2Space A] [SeparatingDual ℝ A]
  [IsTopologicalRing B] [ContinuousSMul ℝ B] [T2Space B] [SeparatingDual ℝ B] in
theorem weak_effective_gradients_unique
    (c : WeakContinuumLegendreDomain μ σA σB ε W G T) {F : B}
    (p q : WeakEffectiveGradientPair c F) :
    p.rightField =ᵐ[μ] q.rightField ∧ p.leftAntifield =ᵐ[μ] q.leftAntifield := by
  exact ⟨c.test_separates _ _ p.field_integrable q.field_integrable
    (fun δ t => (p.field_representation δ t).symm.trans (q.field_representation δ t)),
    c.test_separates _ _ p.antifield_integrable q.antifield_integrable
    (fun δ t => (p.antifield_representation δ t).symm.trans (q.antifield_representation δ t))⟩

/-- The constructed source-first Γ has the actual source as its right field
gradient and the negative pulled connected antifield gradient. These are
proved representations, not fields of the admitted chart. -/
def weakEffectiveActionGradients
    (c : WeakContinuumLegendreDomain μ σA σB ε W G T) (hW : σA.parity W = W) :
    WeakEffectiveGradientPair c (weakEffectiveAction c) where
  rightField := c.source
  leftAntifield := fun x => -c.pull ((c.sourceAfD x).d W)
  field_integrable := c.source_test_integrable
  antifield_integrable δ t := by
    let ΦL := c.pull.toAddMonoidHom.toRealLinearMap c.pull_continuous
    have hi := (c.residual_antifield_integrable δ t W).map ΦL
    simpa only [map_smul, smul_neg] using hi.neg
  field_representation := weak_effective_action_right_field_variation c hW
  antifield_representation := weak_effective_action_left_antifield_variation c

/-- The canonical bracket uses the actual variational gradient densities;
the involution converts the other two left/right derivatives as usual. -/
def weakCanonicalAntibracket
    (c : WeakContinuumLegendreDomain μ σA σB ε W G T) {F H : B}
    (p : WeakEffectiveGradientPair c F) (q : WeakEffectiveGradientPair c H) : B :=
  weakIntegral μ (fun x => p.rightField x * q.leftAntifield x -
    (if !(ε x) then σB.parity (p.leftAntifield x) else p.leftAntifield x) *
      (if ε x then σB.parity (q.rightField x) else q.rightField x))

omit [Algebra ℝ B] [TopologicalSpace B] [IsTopologicalRing B]
  [ContinuousSMul ℝ B] [T2Space B] [SeparatingDual ℝ B] in
theorem weak_even_gradient_integrand
    (hB : SupercommutativeGrading σB) (p : Bool) (J L : B)
    (hJ : σB.parity J = koszulSign p • J)
    (hL : σB.parity L = koszulSign (!p) • L) :
    J*L - (if !p then σB.parity L else L) * (if p then σB.parity J else J) = J*L+J*L := by
  cases p
  · simp only [koszulSign, Bool.false_eq_true, ite_false, one_smul,
      Bool.not_false, ite_true, neg_one_smul] at hJ hL ⊢
    rw [hL, neg_mul, sub_neg_eq_add]
    exact congrArg (fun a => J*L+a) (hB.commute false J (by simpa [koszulSign] using hJ) L).symm
  · simp only [koszulSign, ite_true, neg_one_smul, Bool.not_true,
      Bool.false_eq_true, ite_false, one_smul] at hJ hL ⊢
    rw [hJ, mul_neg, sub_neg_eq_add]
    exact congrArg (fun a => J*L+a) (hB.commute false L (by simpa [koszulSign] using hL) J)

omit [IsTopologicalRing A] [T2Space A] [SeparatingDual ℝ A] in
/-- Conditional exact continuum ST identity. The effective action, both
variational derivatives and their uniqueness have already been constructed;
the input is the connected Ward equation on W. -/
theorem weak_continuum_legendre_slavnov_taylor
    (c : WeakContinuumLegendreDomain μ σA σB ε W G T)
    (hW : σA.parity W = W) (hWard : c.sourceWard.d W = 0) :
    (1/2 : ℚ) • weakCanonicalAntibracket c
      (weakEffectiveActionGradients c hW) (weakEffectiveActionGradients c hW) = 0 := by
  let ψ : X → B := fun x => c.pull ((c.sourceAfD x).d W)
  have hp (x : X) : σB.parity (ψ x) = koszulSign (!(ε x)) • ψ x := by
    dsimp only [ψ]
    rw [← c.preserves_parity]
    have h := gradedDerivative_homogeneous_value (p := false) (c.sourceAfD x)
      (by simpa [koszulSign] using hW)
    simpa [map_smul] using congrArg c.pull h
  have hl (x : X) : σB.parity (-ψ x) = koszulSign (!(ε x)) • (-ψ x) := by
    rw [map_neg, hp, smul_neg]
  have he (x : X) := weak_even_gradient_integrand c.supercommutative (ε x)
    (c.source x) (-ψ x) (c.source_parity x) (hl x)
  have hi : WeakIntegrable μ (fun x => c.source x * (-ψ x)) := by
    simpa only [ψ, mul_neg] using (c.ward_integrable W).neg
  have hz : weakIntegral μ (fun x => c.source x * ψ x) = 0 := by
    rw [← c.ward_representation W, hWard, map_zero]
  have hz' : weakIntegral μ (fun x => c.source x * (-ψ x)) = 0 := by
    have hn : weakIntegral μ (fun x => -(c.source x * ψ x)) =
        -weakIntegral μ (fun x => c.source x * ψ x) := weakIntegral_neg (c.ward_integrable W)
    simpa only [mul_neg, hz, neg_zero] using hn
  have hbr : weakCanonicalAntibracket c
      (weakEffectiveActionGradients c hW) (weakEffectiveActionGradients c hW) = 0 := by
    unfold weakCanonicalAntibracket
    change weakIntegral μ (fun x => c.source x * (-ψ x) -
      (if !(ε x) then σB.parity (-ψ x) else -ψ x) *
        (if ε x then σB.parity (c.source x) else c.source x)) = 0
    rw [show (fun x => c.source x * (-ψ x) -
      (if !(ε x) then σB.parity (-ψ x) else -ψ x) *
        (if ε x then σB.parity (c.source x) else c.source x)) =
        fun x => c.source x * (-ψ x) + c.source x * (-ψ x) from funext he,
      weakIntegral_add hi hi, hz', add_zero]
  rw [hbr, smul_zero]

end UV
