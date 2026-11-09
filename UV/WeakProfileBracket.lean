import UV.ContinuumLegendreST
import UV.FormalBRSTHierarchy
import UV.FormalBRSTTopology

/-! The bilinear antibracket is constructed from actual weak-integral
variational gradients on an admitted regular functional subalgebra.
The larger coefficient algebra may also contain point-source coefficients;
no regular gradient is required for every such point coefficient. -/

noncomputable section
open MeasureTheory
open scoped BigOperators PowerSeries.WithPiTopology

namespace UV

variable {X A B : Type*} [MeasurableSpace X]
  [Ring A] [Algebra ℚ A] [Algebra ℝ A] [TopologicalSpace A]
  [IsTopologicalRing A] [ContinuousSMul ℝ A] [T2Space A] [SeparatingDual ℝ A]
  [Ring B] [Algebra ℚ B] [Algebra ℝ B] [TopologicalSpace B]
  [IsTopologicalRing B] [ContinuousSMul ℝ B] [T2Space B] [SeparatingDual ℝ B]
  {μ : Measure X} {σA : GradingInvolution A} {σB : GradingInvolution B}
  {ε : X → Bool} {W : A} {G : Type*} {T : Bool → Type*}

omit [ContinuousSMul ℝ B] [T2Space B] [SeparatingDual ℝ B] in
theorem WeakIntegrable.rat_smul {f : X → B} (hf : WeakIntegrable μ f) (r : ℚ) :
    WeakIntegrable μ (fun x => r • f x) := by
  simpa only [Algebra.smul_def] using hf.const_mul' (algebraMap ℚ B r)

omit [ContinuousSMul ℝ B] [T2Space B] in
theorem weakIntegral_rat_smul {f : X → B} (hf : WeakIntegrable μ f) (r : ℚ) :
    weakIntegral μ (fun x => r • f x) = r • weakIntegral μ f := by
  simpa only [Algebra.smul_def] using weakIntegral_const_mul' hf (algebraMap ℚ B r)

def weakProfilePair (σ : GradingInvolution B) (p : Bool) (r l r' l' : B) : B :=
  r*l' - (if !p then σ.parity l else l) * (if p then σ.parity r' else r')

omit [Algebra ℝ B] [TopologicalSpace B] [IsTopologicalRing B]
  [ContinuousSMul ℝ B] [T2Space B] [SeparatingDual ℝ B] in
theorem weakProfilePair_add_left (σ : GradingInvolution B) (p : Bool)
    (r l s m u v : B) :
    weakProfilePair σ p (r+s) (l+m) u v =
      weakProfilePair σ p r l u v + weakProfilePair σ p s m u v := by
  cases p <;> simp only [weakProfilePair, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ite_false, ite_true, map_add] <;> noncomm_ring

omit [Algebra ℝ B] [TopologicalSpace B] [IsTopologicalRing B]
  [ContinuousSMul ℝ B] [T2Space B] [SeparatingDual ℝ B] in
theorem weakProfilePair_add_right (σ : GradingInvolution B) (p : Bool)
    (r l s m u v : B) :
    weakProfilePair σ p r l (s+u) (m+v) =
      weakProfilePair σ p r l s m + weakProfilePair σ p r l u v := by
  cases p <;> simp only [weakProfilePair, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ite_false, ite_true, map_add] <;> noncomm_ring

omit [Algebra ℝ B] [TopologicalSpace B] [IsTopologicalRing B]
  [ContinuousSMul ℝ B] [T2Space B] [SeparatingDual ℝ B] in
theorem weakProfilePair_smul_left (σ : GradingInvolution B) (p : Bool)
    (q : ℚ) (r l u v : B) :
    weakProfilePair σ p (q•r) (q•l) u v = q • weakProfilePair σ p r l u v := by
  cases p <;> simp only [weakProfilePair, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ite_false, ite_true, map_smul, smul_mul_assoc, smul_sub]

omit [Algebra ℝ B] [TopologicalSpace B] [IsTopologicalRing B]
  [ContinuousSMul ℝ B] [T2Space B] [SeparatingDual ℝ B] in
theorem weakProfilePair_smul_right (σ : GradingInvolution B) (p : Bool)
    (q : ℚ) (r l u v : B) :
    weakProfilePair σ p r l (q•u) (q•v) = q • weakProfilePair σ p r l u v := by
  cases p <;> simp only [weakProfilePair, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ite_false, ite_true, map_smul, mul_smul_comm, smul_sub]

/-- The regular functional domain supplies linear variational gradients and
closure of their actual integral bracket. It contains no master equation. -/
structure WeakRegularGradientCalculus
    (c : WeakContinuumLegendreDomain μ σA σB ε W G T) (U : Subalgebra ℚ B) where
  rightField : U →ₗ[ℚ] (X → B)
  leftAntifield : U →ₗ[ℚ] (X → B)
  field_integrable : ∀ (F : U) δ t, WeakIntegrable μ (fun x => c.test δ t x • rightField F x)
  antifield_integrable : ∀ (F : U) δ t, WeakIntegrable μ (fun x => c.test δ t x • leftAntifield F x)
  field_representation : ∀ (F : U) δ t, rightGradedDerivative (c.fieldD δ t) (F : B) =
    weakIntegral μ (fun x => c.test δ t x • rightField F x)
  antifield_representation : ∀ (F : U) δ t, (c.antifieldD δ t).d (F : B) =
    weakIntegral μ (fun x => c.test δ t x • leftAntifield F x)
  bracket_integrable : ∀ F H, WeakIntegrable μ (fun x =>
    weakProfilePair σB (ε x) (rightField F x) (leftAntifield F x)
      (rightField H x) (leftAntifield H x))
  bracket_closed : ∀ F H, weakIntegral μ (fun x =>
    weakProfilePair σB (ε x) (rightField F x) (leftAntifield F x)
      (rightField H x) (leftAntifield H x)) ∈ U

def weakRegularGradientPair
    {c : WeakContinuumLegendreDomain μ σA σB ε W G T} {U : Subalgebra ℚ B}
    (v : WeakRegularGradientCalculus c U) (F : U) : WeakEffectiveGradientPair c (F : B) where
  rightField := v.rightField F
  leftAntifield := v.leftAntifield F
  field_integrable := v.field_integrable F
  antifield_integrable := v.antifield_integrable F
  field_representation := v.field_representation F
  antifield_representation := v.antifield_representation F

def weakRegularBracket
    {c : WeakContinuumLegendreDomain μ σA σB ε W G T} {U : Subalgebra ℚ B}
    (v : WeakRegularGradientCalculus c U) : U →ₗ[ℚ] U →ₗ[ℚ] U where
  toFun F :=
    { toFun := fun H => ⟨weakIntegral μ (fun x => weakProfilePair σB (ε x)
        (v.rightField F x) (v.leftAntifield F x) (v.rightField H x) (v.leftAntifield H x)),
        v.bracket_closed F H⟩
      map_add' H K := by
        apply Subtype.ext
        change weakIntegral μ (fun x => weakProfilePair σB (ε x)
          (v.rightField F x) (v.leftAntifield F x)
          (v.rightField (H+K) x) (v.leftAntifield (H+K) x)) = _
        simp only [map_add, Pi.add_apply, weakProfilePair_add_right]
        exact weakIntegral_add (v.bracket_integrable F H) (v.bracket_integrable F K)
      map_smul' q H := by
        apply Subtype.ext
        change weakIntegral μ (fun x => weakProfilePair σB (ε x)
          (v.rightField F x) (v.leftAntifield F x)
          (v.rightField (q•H) x) (v.leftAntifield (q•H) x)) = _
        simp only [map_smul, Pi.smul_apply, weakProfilePair_smul_right]
        exact weakIntegral_rat_smul (v.bracket_integrable F H) q }
  map_add' F H := by
    apply LinearMap.ext
    intro K
    apply Subtype.ext
    change weakIntegral μ (fun x => weakProfilePair σB (ε x)
      (v.rightField (F+H) x) (v.leftAntifield (F+H) x)
      (v.rightField K x) (v.leftAntifield K x)) = _
    simp only [map_add, Pi.add_apply, weakProfilePair_add_left]
    exact weakIntegral_add (v.bracket_integrable F K) (v.bracket_integrable H K)
  map_smul' q F := by
    apply LinearMap.ext
    intro H
    apply Subtype.ext
    change weakIntegral μ (fun x => weakProfilePair σB (ε x)
      (v.rightField (q•F) x) (v.leftAntifield (q•F) x)
      (v.rightField H x) (v.leftAntifield H x)) = _
    simp only [map_smul, Pi.smul_apply, weakProfilePair_smul_left]
    exact weakIntegral_rat_smul (v.bracket_integrable F H) q

omit [IsTopologicalRing A] [ContinuousSMul ℝ A] [T2Space A] [SeparatingDual ℝ A]
  [ContinuousSMul ℝ B] [T2Space B] in
theorem weakRegularBracket_apply
    {c : WeakContinuumLegendreDomain μ σA σB ε W G T} {U : Subalgebra ℚ B}
    (v : WeakRegularGradientCalculus c U) (F H : U) :
    (weakRegularBracket v F H : B) = weakCanonicalAntibracket c
      (weakRegularGradientPair v F) (weakRegularGradientPair v H) := rfl

omit [IsTopologicalRing A] [T2Space A] [SeparatingDual ℝ A] in
/-- Membership in the common regular domain is an admission condition.
The effective-action master equation on that domain follows from its
proved, uniquely represented variational gradients. -/
theorem weak_regular_effective_action_ST
    {c : WeakContinuumLegendreDomain μ σA σB ε W G T} {U : Subalgebra ℚ B}
    (v : WeakRegularGradientCalculus c U) (hΓ : weakEffectiveAction c ∈ U)
    (hW : σA.parity W = W) (hWard : c.sourceWard.d W = 0) :
    (1/2 : ℚ) • weakRegularBracket v ⟨weakEffectiveAction c, hΓ⟩
      ⟨weakEffectiveAction c, hΓ⟩ = 0 := by
  let Γ : U := ⟨weakEffectiveAction c, hΓ⟩
  let p := weakRegularGradientPair v Γ
  let q := weakEffectiveActionGradients c hW
  have huniq := weak_effective_gradients_unique c p q
  have heq : (fun x => weakProfilePair σB (ε x) (v.rightField Γ x)
      (v.leftAntifield Γ x) (v.rightField Γ x) (v.leftAntifield Γ x)) =ᵐ[μ]
      (fun x => q.rightField x * q.leftAntifield x -
        (if !(ε x) then σB.parity (q.leftAntifield x) else q.leftAntifield x) *
          (if ε x then σB.parity (q.rightField x) else q.rightField x)) := by
    filter_upwards [huniq.1, huniq.2] with x hr ha
    change v.rightField Γ x = q.rightField x at hr
    change v.leftAntifield Γ x = q.leftAntifield x at ha
    simp only [weakProfilePair, hr, ha]
  have hi := weakIntegral_congr_ae (v.bracket_integrable Γ Γ) heq
  have hst := weak_continuum_legendre_slavnov_taylor c hW hWard
  apply Subtype.ext
  change (1/2 : ℚ) • weakCanonicalAntibracket c p p = 0
  change weakCanonicalAntibracket c p p = weakCanonicalAntibracket c q q at hi
  rw [hi]
  exact hst

end UV
