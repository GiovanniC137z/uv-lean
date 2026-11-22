import UV.GlobalConvergence
import UV.HeatMeasure
import Mathlib.MeasureTheory.Integral.Prod

/-! Selected-line convergence for an arbitrary joint law of the heat parameters. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal BigOperators

namespace UV.RevisionJointHeat

/-- One conditional line at a dimensionful heat parameter. -/
def heatLine (lapse m : ℝ) (q : LoopMomentum) : ℝ :=
  exp (-lapse * ‖q‖ ^ 2) / (‖q‖ ^ 2 + m ^ 2)

/-- Exact massless one-line Gaussian integral. -/
def gaussianBudget (d lapse : ℝ) : ℝ :=
  π ^ 2 * Gamma (1 + d / 2) * lapse ^ (-(1 + d / 2))

private theorem dirac_selected_line {lapse : ℝ} (hlapse : 0 < lapse) (m : ℝ) (q : LoopMomentum) :
    selectedLine (Measure.dirac lapse) 1 m q = heatLine lapse m q := by
  unfold selectedLine positiveLaplace heatLine
  rw [Measure.restrict_eq_self_of_ae_mem (by simpa [ae_dirac_iff] using hlapse),
    lintegral_dirac, ENNReal.toReal_ofReal (exp_nonneg _)]
  simp

private theorem dirac_inverse_moment {lapse : ℝ} (hlapse : 0 < lapse) (u : ℝ) :
    inverseMoment (Measure.dirac lapse) u = ENNReal.ofReal (lapse ^ (-u)) := by
  unfold inverseMoment
  rw [Measure.restrict_eq_self_of_ae_mem (by simpa [ae_dirac_iff] using hlapse), lintegral_dirac]

private theorem dirac_line_budget {lapse : ℝ} (hlapse : 0 < lapse) (d : ℝ) :
    lineMomentBound (Measure.dirac lapse) 1 d = gaussianBudget d lapse := by
  unfold lineMomentBound gaussianBudget
  rw [dirac_inverse_moment hlapse, ENNReal.toReal_ofReal (Real.rpow_nonneg hlapse.le _)]
  simp

/-- The selected-line product times the remaining graph coefficient. The latter
already contains the complete unselected lines, vertices, and insertions. -/
def heatGraph {ι X P F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (lapse : ι → X → ℝ) (m : ι → ℝ) (e : (ι → LoopMomentum) ≃L[ℝ] (ι → LoopMomentum))
    (b : P → ι → LoopMomentum) (R : P → X → (ι → LoopMomentum) → F)
    (p : P) (z : X × (ι → LoopMomentum)) : F :=
  (∏ j, heatLine (lapse j z.1) (m j) ((e z.2 + b p) j)) • R p z.1 (e z.2 + b p)

/-- At fixed joint heat parameters the original selected-line estimate can be
applied with a point mass at each parameter. The resulting budget is a function
of the actual joint sample, so it can be integrated without assuming independent
heat variables. Even the complete envelope coefficients may depend on the sample. -/
theorem conditionalHeatGraph_bound
    {ι A X P F : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (lapse : ι → X → ℝ) (m : ι → ℝ) (d : A → ι → ℝ) (c : A → X → ℝ)
    (hd : ∀ α j, 0 ≤ d α j) (hc : ∀ α x, 0 ≤ c α x)
    (C : Matrix ι ι ℝ) (e : (ι → LoopMomentum) ≃L[ℝ] (ι → LoopMomentum))
    (he : LinearMap.toMatrix (loopProductBasis ι) (loopProductBasis ι) e.toLinearMap =
      Matrix.kronecker C (1 : Matrix (Fin 4) (Fin 4) ℝ))
    (b : P → ι → LoopMomentum) (R : P → X → (ι → LoopMomentum) → F)
    (hR : ∀ p x, AEStronglyMeasurable (R p x) (Measure.pi fun _ : ι => volume))
    (hbound : ∀ p x q, ‖R p x q‖ ≤ ∑ α, c α x * ∏ j, (1 + ‖q j‖ ^ d α j))
    (p : P) (x : X) (hlapse : ∀ j, 0 < lapse j x) :
    Integrable (fun k => heatGraph lapse m e b R p (x, k)) (Measure.pi fun _ : ι => volume) ∧
    (∫ k, ‖heatGraph lapse m e b R p (x, k)‖ / (2 * π) ^ (4 * Fintype.card ι)
      ∂(Measure.pi fun _ : ι => volume)) ≤
    (|Matrix.det C| ^ (-4 : ℝ) / (2 * π) ^ (4 * Fintype.card ι)) *
      ∑ α, c α x * ∏ j, (gaussianBudget 0 (lapse j x) + gaussianBudget (d α j) (lapse j x)) := by
  classical
  let ρ : ι → Measure ℝ := fun j => Measure.dirac (lapse j x)
  haveI : ∀ j, IsFiniteMeasure (ρ j) := fun j => by dsimp [ρ]; infer_instance
  let D : ι → ℝ := fun j => ∑ α, d α j
  have hf : ∀ p, AEStronglyMeasurable (fun q =>
      (∏ j, selectedLine (ρ j) 1 (m j) (q j)) • R p x q)
      (Measure.pi fun _ : ι => volume) := by
    intro p
    apply AEStronglyMeasurable.smul _ (hR p x)
    apply Measurable.aestronglyMeasurable
    exact Finset.measurable_prod _ fun j _ => (selectedLine_measurable (ρ j) 1 (m j)).comp
      (measurable_pi_apply j)
  have hb := fun p q => complete_envelope_selected_bound ρ (fun _ => 1) m d
    (fun α => c α x) q (R p x q) (hbound p x q)
  have ha : ∀ _ : ι, (0 : ℝ) < (1 : ℝ) := fun _ => one_pos
  have hneg : ∀ j, ρ j (Iio 0) = 0 := by
    intro j
    rw [show ρ j = Measure.dirac (lapse j x) by rfl, Measure.dirac_apply' _ measurableSet_Iio]
    simp [not_lt.mpr (hlapse j).le]
  have hzero : ∀ j, ρ j {0} = 0 := by
    intro j
    simp [ρ, (hlapse j).ne']
  have hD : ∀ α j, d α j ≤ D j := fun α j =>
    Finset.single_le_sum (fun a _ => hd a j) (Finset.mem_univ α)
  have hM : ∀ j, inverseMoment (ρ j) (1 + D j / 2) < ⊤ := by
    intro j
    rw [show ρ j = Measure.dirac (lapse j x) by rfl, dirac_inverse_moment (hlapse j)]
    exact ENNReal.ofReal_lt_top
  have hbound' : ∀ p q,
      ‖(∏ j, selectedLine (ρ j) 1 (m j) (q j)) • R p x q‖ ≤
      ∑ α, c α x * ∏ j, ((1 + ‖q j‖ ^ d α j) *
        laplace (ρ j) ((1 : ℝ) ^ 2 * ‖q j‖ ^ 2) / (‖q j‖ ^ 2 + (m j) ^ 2)) := by
    intro p q
    simpa only [selectedWeight_eq_full_laplace (ρ _) (hneg _) (hzero _)] using hb p q
  have h := optimized_selected_lines ρ hneg hzero (fun _ => 1) m D d (fun α => c α x)
    ha hd hD (fun α => hc α x) hM C (loopProductBasis ι) e he b
    (fun p q => (∏ j, selectedLine (ρ j) 1 (m j) (q j)) • R p x q) hf hbound' p
  simpa only [heatGraph, ρ, dirac_selected_line (hlapse _), dirac_line_budget (hlapse _)] using h

/-- The joint budget before the affine Jacobian and Fourier normalization. -/
def jointBudget {ι A X : Type*} [Fintype ι] [Fintype A]
    (lapse : ι → X → ℝ) (d : A → ι → ℝ) (c : A → X → ℝ) (x : X) : ℝ :=
  ∑ α, c α x * ∏ j, (gaussianBudget 0 (lapse j x) + gaussianBudget (d α j) (lapse j x))

/-- The joint absolute graph coefficient is integrable on the joint sample and
momentum product measure. The two orders of integration agree. Here `X` can
contain both the line heat parameters and the shared geometric data on which
`R` and the envelope constants depend. No independence is required for `ρ`. -/
theorem joint_heat_selected_lines
    {ι A X P F : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (ρ : Measure X) [IsFiniteMeasure ρ]
    (lapse : ι → X → ℝ) (m : ι → ℝ) (d : A → ι → ℝ) (c : A → X → ℝ)
    (hlapse : ∀ᵐ x ∂ρ, ∀ j, 0 < lapse j x)
    (hmlapse : ∀ j, Measurable (lapse j))
    (hd : ∀ α j, 0 ≤ d α j) (hc : ∀ α x, 0 ≤ c α x)
    (C : Matrix ι ι ℝ) (e : (ι → LoopMomentum) ≃L[ℝ] (ι → LoopMomentum))
    (he : LinearMap.toMatrix (loopProductBasis ι) (loopProductBasis ι) e.toLinearMap =
      Matrix.kronecker C (1 : Matrix (Fin 4) (Fin 4) ℝ))
    (b : P → ι → LoopMomentum) (R : P → X → (ι → LoopMomentum) → F)
    (hR : ∀ p, StronglyMeasurable (Function.uncurry (R p)))
    (hbound : ∀ p x q, ‖R p x q‖ ≤ ∑ α, c α x * ∏ j, (1 + ‖q j‖ ^ d α j))
    (hM : Integrable (jointBudget lapse d c) ρ) :
    ∀ p,
    let ω := (2 * π) ^ (4 * Fintype.card ι)
    let μ := Measure.pi fun _ : ι => (volume : Measure LoopMomentum)
    let f := heatGraph lapse m e b R p
    Integrable f (ρ.prod μ) ∧
    (∫ x, (∫ k, ‖f (x, k)‖ / ω ∂μ) ∂ρ) ≤
      (|Matrix.det C| ^ (-4 : ℝ) / ω) * ∫ x, jointBudget lapse d c x ∂ρ ∧
    (∫ x, (∫ k, f (x, k) ∂μ) ∂ρ) = ∫ k, (∫ x, f (x, k) ∂ρ) ∂μ := by
  intro p ω μ f
  have hω : 0 < ω := by dsimp [ω]; positivity
  have hfix := conditionalHeatGraph_bound lapse m d c hd hc C e he b R (fun p' x =>
    ((hR p').comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable) hbound p
  have hfm : StronglyMeasurable f := by
    unfold f heatGraph
    apply StronglyMeasurable.smul
    · apply Measurable.stronglyMeasurable
      apply Finset.measurable_prod
      intro j _
      dsimp only [heatLine]
      have he' : Measurable (fun z : X × (ι → LoopMomentum) => (e z.2 + b p) j) :=
        (measurable_pi_apply j).comp ((e.continuous.measurable.comp measurable_snd).add measurable_const)
      have hx : Measurable (fun z : X × (ι → LoopMomentum) => lapse j z.1) :=
        (hmlapse j).comp measurable_fst
      fun_prop
    · exact (hR p).comp_measurable (measurable_fst.prodMk
        ((e.continuous.measurable.comp measurable_snd).add measurable_const))
  have hm : AEStronglyMeasurable f (ρ.prod μ) := hfm.aestronglyMeasurable
  have hbound' : ∀ᵐ x ∂ρ, (∫ k, ‖f (x, k)‖ ∂μ) ≤
      |Matrix.det C| ^ (-4 : ℝ) * jointBudget lapse d c x := by
    filter_upwards [hlapse] with x hx
    have h := (hfix x hx).2
    change (∫ k, ‖f (x, k)‖ / ω ∂μ) ≤
      (|Matrix.det C| ^ (-4 : ℝ) / ω) * jointBudget lapse d c x at h
    rw [integral_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hω] at h
    exact h
  have hi : Integrable f (ρ.prod μ) := by
    apply (integrable_prod_iff hm).mpr
    refine ⟨hlapse.mono fun x hx => (hfix x hx).1, ?_⟩
    apply (hM.const_mul (|Matrix.det C| ^ (-4 : ℝ))).mono' hm.norm.integral_prod_right'
    filter_upwards [hbound'] with x hx
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact hx
  refine ⟨hi, ?_, integral_prod _ hi |>.symm.trans (integral_prod_symm _ hi)⟩
  simp_rw [integral_div]
  rw [div_mul_eq_mul_div, ← integral_const_mul]
  apply div_le_div_of_nonneg_right _ hω.le
  exact integral_mono_ae (integrable_prod_iff hm |>.mp hi).2
    (hM.const_mul (|Matrix.det C| ^ (-4 : ℝ))) hbound'

end UV.RevisionJointHeat
