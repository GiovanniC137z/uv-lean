import UV.WeakFormalIntegral

/-! The formal loop hierarchy belongs to the same continuum effective
action. The regular coefficient bracket is the actual variational-profile
integral, and the loop variable uses the actual product topology. -/

noncomputable section
open MeasureTheory
open scoped BigOperators PowerSeries.WithPiTopology

namespace UV

theorem powerSeries_separatingDual {B : Type*} [Ring B] [Algebra ℝ B]
    [TopologicalSpace B] [SeparatingDual ℝ B] : SeparatingDual ℝ (PowerSeries B) := by
  constructor
  intro F hF
  have hn : ∃ n, PowerSeries.coeff n F ≠ 0 := by
    by_contra hh
    push_neg at hh
    apply hF
    ext n
    simpa using hh n
  obtain ⟨n, hn⟩ := hn
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_ne_zero (R := ℝ) hn
  exact ⟨ℓ.comp (powerSeriesCoeffCLM n), hℓ⟩

theorem formal_rightGradedDerivative_coeff
    {B : Type*} [Ring B] [Algebra ℚ B] {σ : GradingInvolution B} {δ : Bool}
    (D : GradedDerivative σ δ) (F : PowerSeries B) (n : ℕ) :
    PowerSeries.coeff n (rightGradedDerivative (formalGradedDerivative D) F) =
      rightGradedDerivative D (PowerSeries.coeff n F) := by
  cases δ <;> simp only [rightGradedDerivative, Bool.false_eq_true, ite_false,
    ite_true, formalGrading_coeff, formalGradedDerivative, formalLinearMap_coeff]

variable {X A S B : Type*} [MeasurableSpace X]
  [Ring A] [Algebra ℚ A] [Algebra ℝ A] [TopologicalSpace A]
  [IsTopologicalRing A] [ContinuousSMul ℝ A] [T2Space A] [SeparatingDual ℝ A]
  [Ring S] [Algebra ℚ S] [Algebra ℝ S] [TopologicalSpace S]
  [IsTopologicalRing S] [ContinuousSMul ℝ S] [T2Space S] [SeparatingDual ℝ S]
  [Ring B] [Algebra ℚ B] [Algebra ℝ B] [TopologicalSpace B]
  [IsTopologicalRing B] [ContinuousSMul ℝ B] [T2Space B] [SeparatingDual ℝ B]
  {μ : Measure X} {σA : GradingInvolution A} {σS : GradingInvolution S}
  {σB : GradingInvolution B} {ε : X → Bool} {W₀ : A} {W : S}
  {G₀ G : Type*} {T : Bool → Type*}

/-- The formal profile derivatives are proved to represent the actual
continuum test derivatives. The frame matching is independent of Γ. -/
def formalRegularGradientPair
    (c₀ : WeakContinuumLegendreDomain μ σA σB ε W₀ G₀ T)
    (c : WeakContinuumLegendreDomain μ σS (formalGrading σB) ε W G T)
    {U : Subalgebra ℚ B} (v : WeakRegularGradientCalculus c₀ U) (Γ : PowerSeries U)
    (hfield : ∀ δ t, c.fieldD δ t = formalGradedDerivative (c₀.fieldD δ t))
    (haf : ∀ δ t, c.antifieldD δ t = formalGradedDerivative (c₀.antifieldD δ t))
    (htest : ∀ δ t, c.test δ t = c₀.test δ t)
    (hR : ∀ δ t, WeakIntegrable μ (fun x => c₀.test δ t x • weakFormalRightProfile v Γ x))
    (hL : ∀ δ t, WeakIntegrable μ (fun x => c₀.test δ t x • weakFormalLeftProfile v Γ x)) :
    WeakEffectiveGradientPair c (PowerSeries.map U.val.toRingHom Γ) where
  rightField := weakFormalRightProfile v Γ
  leftAntifield := weakFormalLeftProfile v Γ
  field_integrable δ t := by simpa only [htest] using hR δ t
  antifield_integrable δ t := by simpa only [htest] using hL δ t
  field_representation δ t := by
    apply PowerSeries.ext
    intro n
    rw [hfield, formal_rightGradedDerivative_coeff,
      weakIntegral_formalCoeff n (by simpa only [htest] using hR δ t)]
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_smul, htest,
      weakFormalRightProfile, PowerSeries.coeff_mk]
    exact v.field_representation (PowerSeries.coeff n Γ) δ t
  antifield_representation δ t := by
    apply PowerSeries.ext
    intro n
    rw [haf, show (formalGradedDerivative (c₀.antifieldD δ t)).d =
      formalLinearMap (c₀.antifieldD δ t).d from rfl, formalLinearMap_coeff,
      weakIntegral_formalCoeff n (by simpa only [htest] using hL δ t)]
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_smul, htest,
      weakFormalLeftProfile, PowerSeries.coeff_mk]
    exact v.antifield_representation (PowerSeries.coeff n Γ) δ t

omit [IsTopologicalRing A] [ContinuousSMul ℝ A] [T2Space A] [SeparatingDual ℝ A]
  [IsTopologicalRing S] [T2Space S] [SeparatingDual ℝ S] in
/-- The whole formal master equation is the equation of the very same
continuum Legendre action. Frame matching is generic, and the regular
bracket is constructed from actual variational profiles, not supplied as
an arbitrary bilinear operation or as a master-equation premise. -/
theorem continuum_formal_master_from_legendre
    (c₀ : WeakContinuumLegendreDomain μ σA σB ε W₀ G₀ T)
    (c : WeakContinuumLegendreDomain μ σS (formalGrading σB) ε W G T)
    {U : Subalgebra ℚ B} (v : WeakRegularGradientCalculus c₀ U) (Γ : PowerSeries U)
    (hfield : ∀ δ t, c.fieldD δ t = formalGradedDerivative (c₀.fieldD δ t))
    (haf : ∀ δ t, c.antifieldD δ t = formalGradedDerivative (c₀.antifieldD δ t))
    (htest : ∀ δ t, c.test δ t = c₀.test δ t)
    (hR : ∀ δ t, WeakIntegrable μ (fun x => c₀.test δ t x • weakFormalRightProfile v Γ x))
    (hL : ∀ δ t, WeakIntegrable μ (fun x => c₀.test δ t x • weakFormalLeftProfile v Γ x))
    (hI : WeakIntegrable μ (fun x => weakProfilePair (formalGrading σB) (ε x)
      (weakFormalRightProfile v Γ x) (weakFormalLeftProfile v Γ x)
      (weakFormalRightProfile v Γ x) (weakFormalLeftProfile v Γ x)))
    (hΓ : weakEffectiveAction c = PowerSeries.map U.val.toRingHom Γ)
    (hW : σS.parity W = W) (hWard : c.sourceWard.d W = 0) :
    formalMasterSeries (weakRegularBracket v) Γ = 0 := by
  letI := powerSeries_separatingDual (B := B)
  let p := formalRegularGradientPair c₀ c v Γ hfield haf htest hR hL
  let q := weakEffectiveActionGradients c hW
  have hr : weakFormalRightProfile v Γ =ᵐ[μ] q.rightField :=
    c.test_separates _ _ p.field_integrable q.field_integrable (fun δ t =>
      (p.field_representation δ t).symm.trans (by
        rw [← hΓ]
        exact q.field_representation δ t))
  have hl : weakFormalLeftProfile v Γ =ᵐ[μ] q.leftAntifield :=
    c.test_separates _ _ p.antifield_integrable q.antifield_integrable (fun δ t =>
      (p.antifield_representation δ t).symm.trans (by
        rw [← hΓ]
        exact q.antifield_representation δ t))
  have heq : (fun x => weakProfilePair (formalGrading σB) (ε x)
      (weakFormalRightProfile v Γ x) (weakFormalLeftProfile v Γ x)
      (weakFormalRightProfile v Γ x) (weakFormalLeftProfile v Γ x)) =ᵐ[μ]
      (fun x => q.rightField x * q.leftAntifield x -
        (if !(ε x) then (formalGrading σB).parity (q.leftAntifield x) else q.leftAntifield x) *
          (if ε x then (formalGrading σB).parity (q.rightField x) else q.rightField x)) := by
    filter_upwards [hr, hl] with x hx hy
    simp only [weakProfilePair, hx, hy]
  have hv := weakIntegral_congr_ae hI heq
  have hactual : (1/2 : ℚ) • weakIntegral μ (fun x => weakProfilePair (formalGrading σB) (ε x)
      (weakFormalRightProfile v Γ x) (weakFormalLeftProfile v Γ x)
      (weakFormalRightProfile v Γ x) (weakFormalLeftProfile v Γ x)) = 0 := by
    rw [hv]
    exact weak_continuum_legendre_slavnov_taylor c hW hWard
  rw [weakFormalRegularBracket_eq v Γ Γ hI] at hactual
  have hmap : PowerSeries.map U.val.toRingHom (formalMasterSeries (weakRegularBracket v) Γ) = 0 := by
    change (PowerSeries.mapAlgHom U.val) ((1/2 : ℚ) • formalBilinear (weakRegularBracket v) Γ Γ) = 0
    rw [map_smul]
    exact hactual
  apply PowerSeries.map_injective U.val.toRingHom Subtype.val_injective
  simpa only [map_zero] using hmap

end UV
