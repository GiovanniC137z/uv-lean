import UV.ContinueMomentumRoutingPackets

/-! Joint absolute convergence with external-transfer decay supplied
by the individual charged integrals. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter

namespace UV

variable {V Z : Type*} [Fintype V] [MeasurableSpace Z] {X : V → Type*}
variable [∀ v, MeasurableSpace (X v)]

theorem momentum_weighted_joint (σ : (v : V) → Measure (X v)) [∀ v, SigmaFinite (σ v)]
    (μ : Measure Z) [SFinite μ] {W : Z → ℂ} (hw : Measurable W) {F : (v : V) → Z → X v → ℂ}
    (hm : ∀ v, Measurable (fun t : Z × X v => F v t.1 t.2)) (hi : ∀ v z, Integrable (F v z) (σ v))
    (a : V → Z → ℝ) (hJ : Integrable (fun z => ‖W z‖*∏ v,a v z) μ) (g : V → ℝ)
    (hb : ∀ v z, (∫ t, ‖F v z t‖ ∂σ v) ≤ g v*a v z) :
    Integrable (wilsonJointFactors W F) (μ.prod (Measure.pi σ)) ∧
      (∫ t, ‖wilsonJointFactors W F t‖ ∂μ.prod (Measure.pi σ)) ≤
        (∏ v,g v)*(∫ z, ‖W z‖*∏ v,a v z ∂μ) := by
  have hj := wilson_factors_measurable hw hm
  have hh (z : Z) : (∫ x, ‖wilsonJointFactors W F (z,x)‖ ∂Measure.pi σ) ≤
      (∏ v,g v)*(‖W z‖*∏ v,a v z) := by
    simp only [wilsonJointFactors,norm_mul,norm_prod,integral_const_mul]
    rw [integral_fintype_prod_eq_prod (fun v x => ‖F v z x‖)]
    apply (mul_le_mul_of_nonneg_left (Finset.prod_le_prod
      (fun v _ => integral_nonneg fun t => norm_nonneg (F v z t)) (fun v _ => hb v z)) (norm_nonneg (W z))).trans_eq
    rw [Finset.prod_mul_distrib]; ring
  have h := hJ.const_mul (∏ v,g v)
  have hI : Integrable (wilsonJointFactors W F) (μ.prod (Measure.pi σ)) := by
    apply (integrable_prod_iff hj.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall (fun z => (Integrable.fintype_prod_dep fun v => hi v z).const_mul (W z)),?_⟩
    apply h.mono' hj.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    apply Eventually.of_forall fun z => ?_
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact hh z
  refine ⟨hI,?_⟩
  rw [integral_prod _ hI.norm,← integral_const_mul]
  exact integral_mono hI.integral_norm_prod_left h hh

theorem momentum_weighted_joint_windings (σ : (v : V) → Measure (X v)) [∀ v, SigmaFinite (σ v)]
    (μ : Measure Z) [SFinite μ] {W : Z → ℂ} (hw : Measurable W) {F : (V → ℤ) → (v : V) → Z → X v → ℂ}
    (hm : ∀ w v, Measurable (fun t : Z × X v => F w v t.1 t.2))
    (hi : ∀ w v z, Integrable (F w v z) (σ v))
    (a : V → Z → ℝ) (hJ : Integrable (fun z => ‖W z‖*∏ v,a v z) μ) (g : V → ℤ → ℝ)
    (hg : ∀ v w, 0 ≤ g v w) (hs : ∀ v, Summable (g v))
    (hb : ∀ w v z, (∫ t, ‖F w v z t‖ ∂σ v) ≤ g v (w v)*a v z) :
    (∀ w, Integrable (wilsonJointFactors W (F w)) (μ.prod (Measure.pi σ))) ∧
    Summable (fun w => ∫ t, ‖wilsonJointFactors W (F w) t‖ ∂μ.prod (Measure.pi σ)) := by
  have h (w) := momentum_weighted_joint σ μ hw (hm w) (hi w) a hJ (fun v => g v (w v)) (hb w)
  exact ⟨fun w => (h w).1, Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun w => (h w).2) ((wilson_summable_product hg hs).mul_right _)⟩

end UV
