import UV.ContinuationCompletedST
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Coefficientwise comparison limits on one fixed ST domain. The
argument takes limits of the actual antibracket contractions individually
and uses only a finite convolution at each loop order. -/

noncomputable section
open Filter MeasureTheory UV.ContinuationGraph UV.ContinuationCompleted
open scoped BigOperators Topology

namespace UV.FurtherCompletedST

variable {B : Type*} [Ring B] [Algebra ℚ B] [Algebra ℝ B] [TopologicalSpace B]
variable {U : Subalgebra ℚ B} {R : Type*} {l : Filter R}

/-- Scalar limits on the separating dual suffice for the master identity.
The comparison sum can have a breaking term, expressed in the unscaled
antibracket convention, provided that term tends weakly to zero. -/
theorem formal_master_of_weak_contraction_limits [SeparatingDual ℝ B] [l.NeBot]
    (β : U →ₗ[ℚ] U →ₗ[ℚ] U) (Γ : PowerSeries U)
    (stage : R → PowerSeries U) (breaking : ℕ → R → B)
    (hbreaking : ∀ n (ℓ : B →L[ℝ] ℝ), Tendsto (fun t => ℓ (breaking n t)) l (𝓝 0))
    (hstage : ∀ n, ∀ᶠ t in l, (↑(∑ j ∈ Finset.range (n+1),
      β (PowerSeries.coeff j (stage t)) (PowerSeries.coeff (n-j) (stage t))) : B) =
        breaking n t)
    (hcontract : ∀ n j, j < n+1 → ∀ ℓ : B →L[ℝ] ℝ,
      Tendsto (fun t => ℓ (β (PowerSeries.coeff j (stage t))
        (PowerSeries.coeff (n-j) (stage t)))) l
        (𝓝 (ℓ (β (PowerSeries.coeff j Γ) (PowerSeries.coeff (n-j) Γ))))) :
    formalMasterSeries β Γ = 0 := by
  apply (formal_master_iff β Γ).mpr
  intro n
  suffices hz : ∑ j ∈ Finset.range (n+1),
      β (PowerSeries.coeff j Γ) (PowerSeries.coeff (n-j) Γ) = 0 by
    rw [hz, smul_zero]
  apply Subtype.ext
  change (↑(∑ j ∈ Finset.range (n+1),
    β (PowerSeries.coeff j Γ) (PowerSeries.coeff (n-j) Γ)) : B) = 0
  apply weakDual_ext
  intro ℓ
  have hsum := tendsto_finset_sum (Finset.range (n+1))
    (fun j hj => hcontract n j (Finset.mem_range.mp hj) ℓ)
  have hscalar (s : Finset ℕ) (f : ℕ → U) : ℓ ((∑ j ∈ s, f j : U) : B) = ∑ j ∈ s, ℓ (f j) :=
    map_sum (ℓ.toAddMonoidHom.comp U.val.toAddMonoidHom) f s
  have heq : (fun t => ℓ (breaking n t)) =ᶠ[l] (fun t =>
      ∑ j ∈ Finset.range (n+1),
        ℓ (β (PowerSeries.coeff j (stage t)) (PowerSeries.coeff (n-j) (stage t)))) := by
    filter_upwards [hstage n] with t ht
    rw [← ht, hscalar]
  rw [hscalar, map_zero]
  exact
    tendsto_nhds_unique hsum ((hbreaking n ℓ).congr' heq)

omit [Algebra ℚ B] in
/-- Scalar dominated convergence supplies a concrete sufficient test for
comparison of the actual weak integrals. Both endpoints are represented
integrals on the same measure space. The bound is needed only eventually. -/
theorem weak_integral_test_tendsto {X : Type*} [MeasurableSpace X] [l.IsCountablyGenerated]
    {μ : Measure X} (stage : R → X → B) (target : X → B)
    (hstage : ∀ᶠ t in l, WeakIntegrable μ (stage t)) (htarget : WeakIntegrable μ target)
    (ℓ : B →L[ℝ] ℝ) (bound : X → ℝ) (hbound : Integrable bound μ)
    (hdom : ∀ᶠ t in l, ∀ᵐ x ∂μ, ‖ℓ (stage t x)‖ ≤ bound x)
    (hlimit : ∀ᵐ x ∂μ, Tendsto (fun t => ℓ (stage t x)) l (𝓝 (ℓ (target x)))) :
    Tendsto (fun t => ℓ (weakIntegral μ (stage t))) l (𝓝 (ℓ (weakIntegral μ target))) := by
  rw [weakIntegral_apply htarget]
  apply (tendsto_integral_filter_of_dominated_convergence
    (μ := μ) bound (hstage.mono (fun _ h => (h.1 ℓ).aestronglyMeasurable))
    hdom hbound hlimit).congr'
  exact hstage.mono (fun _ h => (weakIntegral_apply h ℓ).symm)

section ActualGraphs

variable {X S : Type*} [MeasurableSpace X]
    [Ring S] [Algebra ℚ S] [Algebra ℝ S] [TopologicalSpace S]
    [IsTopologicalRing B] [ContinuousSMul ℝ B] [T2Space B] [SeparatingDual ℝ B]
    {μ : Measure X} {σS : GradingInvolution S} {σB : GradingInvolution B}
    {ε : X → Bool} {G : Type*} {T : Bool → Type*} {W : Bool → S}
    {c : ∀ k, WeakContinuumLegendreDomain μ σS σB ε (W k) G T}

/-- The integrand of the canonical antibracket on the regular domain. -/
def contractionProfile {k : Bool}
    (v : WeakRegularGradientCalculus (c k) U) (f g : U) (x : X) : B :=
  weakProfilePair σB (ε x) (v.rightField f x) (v.leftAntifield f x)
    (v.rightField g x) (v.leftAntifield g x)

omit [ContinuousSMul ℝ B] [T2Space B] in
/-- An integrable eventual majorant and an almost-everywhere scalar limit
of the actual gradient contraction verify the corresponding weak limit
required in the ST comparison. -/
theorem contraction_tendsto_of_dominated [l.IsCountablyGenerated]
    {k : Bool} (v : WeakRegularGradientCalculus (c k) U)
    (f g : R → U) (f₀ g₀ : U)
    (ℓ : B →L[ℝ] ℝ) (bound : X → ℝ) (hbound : Integrable bound μ)
    (hdom : ∀ᶠ t in l, ∀ᵐ x ∂μ, ‖ℓ (contractionProfile v (f t) (g t) x)‖ ≤ bound x)
    (hlimit : ∀ᵐ x ∂μ, Tendsto (fun t => ℓ (contractionProfile v (f t) (g t) x)) l
      (𝓝 (ℓ (contractionProfile v f₀ g₀ x)))) :
    Tendsto (fun t => ℓ (weakRegularBracket v (f t) (g t))) l
      (𝓝 (ℓ (weakRegularBracket v f₀ g₀))) :=
  weak_integral_test_tendsto (fun t => contractionProfile v (f t) (g t))
    (contractionProfile v f₀ g₀)
    (Eventually.of_forall (fun t => v.bracket_integrable (f t) (g t)))
    (v.bracket_integrable f₀ g₀) ℓ bound hbound hdom hlimit

omit [ContinuousSMul ℝ B] [T2Space B] in
/-- Comparison on a common fixed graph declaration and actual gradient
domain. Each comparison coefficient and target coefficient is reconstructed
from its own finite graph sum. Weak agreement of the individual canonical
contractions transfers the loop identities to the target graph action and
to both carrier characters. -/
theorem fixed_action_comparison_slavnov_taylor [l.NeBot]
    {E Action Support Infrared P I : Type} [NormedAddCommGroup E]
    (D : GraphDeclaration E Action Support Infrared)
    (a : GraphDeclaration E Action Support Infrared → ExpandedCompletedGraphAction P I)
    (aStage : R → GraphDeclaration E Action Support Infrared → ExpandedCompletedGraphAction P I)
    (Γ : Bool → PowerSeries U) (stage : R → Bool → PowerSeries U)
    (r : ExpandedCompletedGraphRealization (a D) Γ)
    (rStage : ∀ t, ExpandedCompletedGraphRealization (aStage t D) (stage t))
    (v : ∀ k, WeakRegularGradientCalculus (c k) U)
    (breaking : Bool → ℕ → R → B)
    (hbreaking : ∀ k n (ℓ : B →L[ℝ] ℝ),
      Tendsto (fun t => ℓ (breaking k n t)) l (𝓝 0))
    (hstage : ∀ k n, ∀ᶠ t in l, (↑(∑ j ∈ Finset.range (n+1),
      weakRegularBracket (v k) (PowerSeries.coeff j (stage t k))
        (PowerSeries.coeff (n-j) (stage t k))) : B) = breaking k n t)
    (hcontract : ∀ k n j, j < n+1 → ∀ ℓ : B →L[ℝ] ℝ,
      Tendsto (fun t => ℓ (weakRegularBracket (v k)
        ((rStage t).reconstruct (ContinuationCompleted.completedGraphCoefficient (aStage t D) j k))
        ((rStage t).reconstruct (ContinuationCompleted.completedGraphCoefficient (aStage t D) (n-j) k)))) l
        (𝓝 (ℓ (weakRegularBracket (v k)
          (r.reconstruct (ContinuationCompleted.completedGraphCoefficient (a D) j k))
          (r.reconstruct (ContinuationCompleted.completedGraphCoefficient (a D) (n-j) k)))))) :
    (∀ k, formalMasterSeries (weakRegularBracket (v k)) (Γ k) = 0) ∧
    formalMasterSeries (pairedRegularBracket (weakRegularBracket (v false))
      (weakRegularBracket (v true))) (pairedFormalAction (Γ false) (Γ true)) = 0 ∧
    (∀ n k i g p, Integrable (((a D).graph n k i g).integrand p)
      ((a D).graph n k i g).measure) ∧
    (∀ n k i p, ‖r.insertion (PowerSeries.coeff n (Γ k)) i p‖ ≤
      ContinuationCompleted.completedGraphBudget (a D) n k i) := by
  have hmaster (k : Bool) : formalMasterSeries (weakRegularBracket (v k)) (Γ k) = 0 := by
    apply formal_master_of_weak_contraction_limits (weakRegularBracket (v k)) (Γ k)
      (fun t => stage t k) (breaking k) (hbreaking k) (hstage k)
    intro n j hj ℓ
    simpa only [r.coefficient, (rStage _).coefficient] using hcontract k n j hj ℓ
  exact ⟨hmaster, paired_formal_master_zero (hmaster false) (hmaster true),
    ContinuationCompleted.completedGraph_integrable (a D), fun n k => ContinuationCompleted.completedGraphRealization_insertion_norm_le r k n⟩

end ActualGraphs

end UV.FurtherCompletedST
