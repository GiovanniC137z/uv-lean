import UV.Holomorphy
import UV.PoleCertificates
import Mathlib.MeasureTheory.Integral.Prod

/-! Local contour exchange from the source's pointwise measurable samples,
almost everywhere continuous contour traces, and a common L1 majorant.
Joint measurability and absolute product integrability are conclusions. -/

noncomputable section
open MeasureTheory Filter Set Metric Complex TopologicalSpace
open scoped Topology

namespace UV

/-- The Carathéodory conclusion also holds for merely a.e. measurable point
samples. Finite sample approximants handle all exceptional sets before the
limit along the continuous parameter traces is taken. -/
theorem contour_joint_aestronglyMeasurable_of_ae_samples
    {T X : Type*} [TopologicalSpace T] [MetrizableSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [OpensMeasurableSpace T] [MeasurableSpace X]
    (ν : Measure T) (μ : Measure X) (F : T → X → ℂ)
    (hm : ∀ t, AEStronglyMeasurable (F t) μ)
    (hc : ∀ᵐ ξ ∂μ, Continuous (fun t => F t ξ)) :
    AEStronglyMeasurable (Function.uncurry F) (ν.prod μ) := by
  classical
  let p : ℕ → SimpleFunc T T := stronglyMeasurable_id.approx
  have hp : ∀ t, Tendsto (fun n => p n t) atTop (𝓝 t) :=
    stronglyMeasurable_id.tendsto_approx
  have hsample (n : ℕ) : AEStronglyMeasurable
      (fun z : T × X => F (p n z.1) z.2) (ν.prod μ) := by
    let A := (p n).range
    let G : A → X → ℂ := fun a => (hm a).mk (F a)
    have hG : Measurable (fun z : A × X => G z.1 z.2) :=
      measurable_from_prod_countable_right (fun a => (hm a).stronglyMeasurable_mk.measurable)
    let q : T → A := fun t => ⟨p n t, SimpleFunc.mem_range_self _ _⟩
    have hq : Measurable q := (p n).measurable.subtype_mk
    have hmeas : StronglyMeasurable (fun z : T × X => G (q z.1) z.2) :=
      (hG.comp ((hq.comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable
    apply hmeas.aestronglyMeasurable.congr
    have heq : ∀ᵐ ξ ∂μ, ∀ a : A, G a ξ = F a ξ :=
      ae_all_iff.mpr (fun a => Filter.EventuallyEq.symm (hm a).ae_eq_mk)
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := ν) (ν := μ)).ae heq] with z hz
    exact hz (q z.1)
  apply aestronglyMeasurable_of_tendsto_ae atTop hsample
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := ν) (ν := μ)).ae hc] with z hz
  exact hz.continuousAt.tendsto.comp (hp z.1)

theorem contour_weighted_product_integrable_of_ae_samples
    {T X : Type*} [TopologicalSpace T] [MetrizableSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [OpensMeasurableSpace T] [MeasurableSpace X]
    (ν : Measure T) (μ : Measure X) (F : T → X → ℂ) (w : T → ℂ)
    (hm : ∀ t, AEStronglyMeasurable (F t) μ)
    (hc : ∀ᵐ ξ ∂μ, Continuous (fun t => F t ξ))
    {M : X → ℝ} (hM : Integrable M μ) (hw : Integrable w ν)
    (hb : ∀ᵐ ξ ∂μ, ∀ t, ‖F t ξ‖ ≤ M ξ) :
    Integrable (fun z : T × X => w z.1 * F z.1 z.2) (ν.prod μ) := by
  apply (hw.norm.mul_prod hM).mono'
    (hw.aestronglyMeasurable.comp_fst.mul
      (contour_joint_aestronglyMeasurable_of_ae_samples ν μ F hm hc))
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := ν) (ν := μ)).ae hb] with z hz
  change ‖w z.1 * F z.1 z.2‖ ≤ ‖w z.1‖ * M z.2
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hz z.1) (norm_nonneg _)

/-- Carathéodory joint measurability after discarding one common null set of
discontinuous parameter traces. No joint measurability premise is needed. -/
theorem contour_joint_aestronglyMeasurable
    {T X : Type*} [TopologicalSpace T] [MetrizableSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [OpensMeasurableSpace T] [MeasurableSpace X]
    (ν : Measure T) (μ : Measure X) (F : T → X → ℂ)
    (hm : ∀ t, StronglyMeasurable (F t))
    (hc : ∀ᵐ ξ ∂μ, Continuous (fun t => F t ξ)) :
    AEStronglyMeasurable (Function.uncurry F) (ν.prod μ) := by
  classical
  have hbad : μ {ξ | ¬ Continuous (fun t => F t ξ)} = 0 := ae_iff.mp hc
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ := exists_measurable_superset_of_null hbad
  let G : T → X → ℂ := fun t => Nᶜ.indicator (F t)
  have hmG : ∀ t, StronglyMeasurable (G t) := fun t => (hm t).indicator hNmeas.compl
  have hcG : ∀ ξ, Continuous (fun t => G t ξ) := by
    intro ξ
    by_cases hξ : ξ ∈ N
    · simpa [G, hξ] using
        (continuous_const : Continuous (fun _ : T => (0 : ℂ)))
    · have hcont : Continuous (fun t => F t ξ) := by
        by_contra h
        exact hξ (hNsub h)
      simpa only [G, indicator_of_mem (show ξ ∈ Nᶜ from hξ)] using hcont
  have hmunc := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcG hmG
  apply hmunc.aestronglyMeasurable.congr
  have hgood : ∀ᵐ ξ ∂μ, ξ ∉ N := by simpa only [ae_iff, not_not] using hNnull
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := ν) (ν := μ)).ae hgood] with z hz
  simp only [Function.uncurry, G, indicator_of_mem (show z.2 ∈ Nᶜ from hz)]

/-- The common graph majorant times an integrable contour weight is an
absolute product majorant, proved from the separate source hypotheses. -/
theorem contour_weighted_product_integrable
    {T X : Type*} [TopologicalSpace T] [MetrizableSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [OpensMeasurableSpace T] [MeasurableSpace X]
    (ν : Measure T) (μ : Measure X) (F : T → X → ℂ) (w : T → ℂ)
    (hm : ∀ t, StronglyMeasurable (F t))
    (hc : ∀ᵐ ξ ∂μ, Continuous (fun t => F t ξ))
    {M : X → ℝ} (hM : Integrable M μ) (hw : Integrable w ν)
    (hb : ∀ᵐ ξ ∂μ, ∀ t, ‖F t ξ‖ ≤ M ξ) :
    Integrable (fun z : T × X => w z.1 * F z.1 z.2) (ν.prod μ) := by
  have hdom := hw.norm.mul_prod hM
  apply hdom.mono'
    (hw.aestronglyMeasurable.comp_fst.mul (contour_joint_aestronglyMeasurable ν μ F hm hc))
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := ν) (ν := μ)).ae hb] with z hz
  change ‖w z.1 * F z.1 z.2‖ ≤ ‖w z.1‖ * M z.2
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hz z.1) (norm_nonneg _)

/-- Weighted local contour integration commutes with the graph
representation integral by the derived absolute product bound. -/
theorem contour_representation_integral_exchange
    {T X : Type*} [TopologicalSpace T] [MetrizableSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [OpensMeasurableSpace T] [MeasurableSpace X]
    (ν : Measure T) [SigmaFinite ν] (μ : Measure X) [SigmaFinite μ]
    (F : T → X → ℂ) (w : T → ℂ)
    (hm : ∀ t, StronglyMeasurable (F t))
    (hc : ∀ᵐ ξ ∂μ, Continuous (fun t => F t ξ))
    {M : X → ℝ} (hM : Integrable M μ) (hw : Integrable w ν)
    (hb : ∀ᵐ ξ ∂μ, ∀ t, ‖F t ξ‖ ≤ M ξ) :
    (∫ t, w t * (∫ ξ, F t ξ ∂μ) ∂ν) = ∫ ξ, (∫ t, w t * F t ξ ∂ν) ∂μ := by
  have hi := contour_weighted_product_integrable ν μ F w hm hc hM hw hb
  simpa only [integral_const_mul] using
    integral_integral_swap (μ := ν) (ν := μ) (f := fun t ξ => w t * F t ξ) hi

/-- Actual circle contour exchange in the source common-majorant theorem.
Measurable point samples and a.e. continuous sphere traces suffice. -/
theorem circle_representation_integral_exchange
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (F : ℂ → X → ℂ) (c : ℂ) (r : ℝ)
    (hm : ∀ z ∈ sphere c |r|, Measurable (F z))
    (hc : ∀ᵐ ξ ∂μ, ContinuousOn (fun z => F z ξ) (sphere c |r|))
    {M : X → ℝ} (hM : Integrable M μ)
    (hb : ∀ᵐ ξ ∂μ, ∀ z ∈ sphere c |r|, ‖F z ξ‖ ≤ M ξ) :
    circleIntegral (fun z => ∫ ξ, F z ξ ∂μ) c r =
      ∫ ξ, circleIntegral (fun z => F z ξ) c r ∂μ := by
  have htrace : ∀ᵐ ξ ∂μ, Continuous (fun t : ℝ => F (circleMap c r t) ξ) := by
    filter_upwards [hc] with ξ hξ
    exact hξ.comp_continuous (continuous_circleMap c r) (circleMap_mem_sphere' c r)
  have hbound : ∀ᵐ ξ ∂μ, ∀ t : ℝ, ‖F (circleMap c r t) ξ‖ ≤ M ξ := by
    filter_upwards [hb] with ξ hξ
    exact fun t => hξ _ (circleMap_mem_sphere' c r t)
  have hweight : Integrable (fun t : ℝ => deriv (circleMap c r) t)
      (volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))) := by
    have hcont : Continuous (fun t : ℝ => deriv (circleMap c r) t) := by
      simp only [deriv_circleMap]
      exact (continuous_circleMap 0 r).mul continuous_const
    have hw : IntervalIntegrable (fun t : ℝ => deriv (circleMap c r) t)
        volume 0 (2 * Real.pi) := hcont.intervalIntegrable _ _
    exact hw.def'
  have hi := contour_weighted_product_integrable
    (volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))) μ
    (fun t ξ => F (circleMap c r t) ξ) (fun t => deriv (circleMap c r) t)
    (fun t => (hm _ (circleMap_mem_sphere' c r t)).stronglyMeasurable)
    htrace hM hweight hbound
  have hswap := intervalIntegral_integral_swap (μ := μ)
    (f := fun t ξ => deriv (circleMap c r) t * F (circleMap c r t) ξ) hi
  simp only [circleIntegral, smul_eq_mul]
  simpa only [integral_const_mul] using hswap

/-- Full local contour exchange on a compact parameter space from the
source's compact common-majorant hypotheses. The curve may lie in an
arbitrary finite complex momentum domain. -/
theorem compact_contour_exchange_from_graph_majorants
    {H T X : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [TopologicalSpace T] [MetrizableSpace T] [SecondCountableTopology T]
    [CompactSpace T] [MeasurableSpace T] [OpensMeasurableSpace T] [MeasurableSpace X]
    (ν : Measure T) [SigmaFinite ν] (μ : Measure X) [SigmaFinite μ]
    {Ω : Set H} (F : H → X → ℂ)
    (hm : ∀ z ∈ Ω, Measurable (F z))
    (hd : ∀ᵐ ξ ∂μ, DifferentiableOn ℂ (fun z => F z ξ) Ω)
    (hb : ∀ K : Set H, IsCompact K → K ⊆ Ω → ∃ M : X → ℝ,
      Integrable M μ ∧ ∀ᵐ ξ ∂μ, ∀ z ∈ K, ‖F z ξ‖ ≤ M ξ)
    (γ : T → H) (hγ : Continuous γ) (hγΩ : ∀ t, γ t ∈ Ω)
    (w : T → ℂ) (hw : Integrable w ν) :
    (∫ t, w t * (∫ ξ, F (γ t) ξ ∂μ) ∂ν) =
      ∫ ξ, (∫ t, w t * F (γ t) ξ ∂ν) ∂μ := by
  have hrange : range γ ⊆ Ω := by
    rintro _ ⟨t, rfl⟩
    exact hγΩ t
  obtain ⟨M, hM, hbM⟩ := hb (range γ) (isCompact_range hγ) hrange
  have hcF : ∀ᵐ ξ ∂μ, Continuous (fun t => F (γ t) ξ) := by
    filter_upwards [hd] with ξ hξ
    exact hξ.continuousOn.comp_continuous hγ hγΩ
  have hbF : ∀ᵐ ξ ∂μ, ∀ t, ‖F (γ t) ξ‖ ≤ M ξ := by
    filter_upwards [hbM] with ξ hξ
    exact fun t => hξ _ (mem_range_self t)
  exact contour_representation_integral_exchange ν μ (fun t ξ => F (γ t) ξ) w
    (fun t => (hm _ (hγΩ t)).stronglyMeasurable) hcF hM hw hbF

/-- The sharp one-variable external derivative budget. All derivative orders
are actual iterated complex derivatives, with the exact factorial. -/
theorem one_variable_cauchy_derivative_budget {f : ℂ → ℂ} {c : ℂ} {r C : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (closedBall c r))
    (hb : ∀ z ∈ sphere c r, ‖f z‖ ≤ C) (n : ℕ) :
    ‖iteratedDeriv n f c‖ ≤ (n.factorial : ℝ) * r⁻¹ ^ n * C := by
  let g : ℂ → ℂ := fun z => f (c + z)
  have hmaps : MapsTo (fun z : ℂ => c + z) (closedBall 0 r) (closedBall c r) := by
    intro z hz
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hz
  have hlin : Differentiable ℂ (fun z : ℂ => c + z) := differentiable_id.const_add c
  have hg : DifferentiableOn ℂ g (closedBall 0 r) := hf.comp hlin.differentiableOn hmaps
  have hbG : ∀ z ∈ sphere (0 : ℂ) r, ‖g z‖ ≤ C := by
    intro z hz
    apply hb (c + z)
    simpa only [mem_sphere, dist_eq_norm, add_sub_cancel_left, sub_zero] using hz
  have hcoef := pole_cauchy_coefficient_bound hr hg hbG n
  have he : ‖poleTaylorCoeff g n‖ = ‖iteratedDeriv n f c‖ / (n.factorial : ℝ) := by
    unfold poleTaylorCoeff
    rw [norm_div]
    have hshift := congrFun (iteratedDeriv_comp_const_add n f c) 0
    simp only [add_zero] at hshift
    rw [hshift]
    simp only [Complex.norm_natCast]
  rw [he] at hcoef
  have hfact : 0 < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have h := (div_le_iff₀ hfact).mp hcoef
  convert h using 1
  ring

/-- Source-format one-variable Cauchy budget for the integrated graph, using
its complete pointwise complex majorant. -/
theorem graph_one_variable_cauchy_budget
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {F : ℂ → X → ℂ}
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hm : ∀ z ∈ Ω, AEStronglyMeasurable (F z) μ)
    (hd : ∀ᵐ ξ ∂μ, DifferentiableOn ℂ (fun z => F z ξ) Ω)
    (hb : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∃ M : X → ℝ,
      Integrable M μ ∧ ∀ᵐ ξ ∂μ, ∀ z ∈ K, ‖F z ξ‖ ≤ M ξ)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hclosed : closedBall c r ⊆ Ω)
    {M : X → ℝ} (hM : Integrable M μ)
    (hbound : ∀ᵐ ξ ∂μ, ∀ z ∈ closedBall c r, ‖F z ξ‖ ≤ M ξ) (n : ℕ) :
    ‖iteratedDeriv n (fun z => ∫ ξ, F z ξ ∂μ) c‖ ≤
      (n.factorial : ℝ) * r⁻¹ ^ n * ∫ ξ, M ξ ∂μ := by
  apply one_variable_cauchy_derivative_budget hr
    ((holomorphy_from_compact_graph_majorants hΩ hm hd hb).mono hclosed)
  intro z hz
  apply norm_integral_le_of_norm_le hM
  filter_upwards [hbound] with ξ hξ
  exact hξ z (sphere_subset_closedBall hz)

/-- Pointwise measurable samples and a.e. continuous traces also make the
actual contour integral measurable in the representation variable. -/
theorem circle_representation_aestronglyMeasurable
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (F : ℂ → X → ℂ) (c : ℂ) (r : ℝ)
    (hm : ∀ z ∈ sphere c |r|, Measurable (F z))
    (hc : ∀ᵐ ξ ∂μ, ContinuousOn (fun z => F z ξ) (sphere c |r|)) :
    AEStronglyMeasurable (fun ξ => circleIntegral (fun z => F z ξ) c r) μ := by
  let ν := volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))
  have htrace : ∀ᵐ ξ ∂μ, Continuous (fun t : ℝ => F (circleMap c r t) ξ) := by
    filter_upwards [hc] with ξ hξ
    exact hξ.comp_continuous (continuous_circleMap c r) (circleMap_mem_sphere' c r)
  have hjoint := contour_joint_aestronglyMeasurable ν μ
    (fun t ξ => F (circleMap c r t) ξ)
    (fun t => (hm _ (circleMap_mem_sphere' c r t)).stronglyMeasurable) htrace
  have hderiv : Continuous (fun t : ℝ => deriv (circleMap c r) t) := by
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 r).mul continuous_const
  have hprod : AEStronglyMeasurable (fun z : ℝ × X =>
      deriv (circleMap c r) z.1 * F (circleMap c r z.1) z.2) (ν.prod μ) :=
    hderiv.aestronglyMeasurable.comp_fst.mul hjoint
  have hinner := hprod.prod_swap.integral_prod_right'
  simpa only [circleIntegral, smul_eq_mul, intervalIntegral.integral_of_le Real.two_pi_pos.le,
    ν, uIoc_of_le Real.two_pi_pos.le] using hinner

theorem circle_representation_aestronglyMeasurable_of_ae_samples
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (F : ℂ → X → ℂ) (c : ℂ) (r : ℝ)
    (hm : ∀ z ∈ sphere c |r|, AEStronglyMeasurable (F z) μ)
    (hc : ∀ᵐ ξ ∂μ, ContinuousOn (fun z => F z ξ) (sphere c |r|)) :
    AEStronglyMeasurable (fun ξ => circleIntegral (fun z => F z ξ) c r) μ := by
  let ν := volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))
  have htrace : ∀ᵐ ξ ∂μ, Continuous (fun t : ℝ => F (circleMap c r t) ξ) := by
    filter_upwards [hc] with ξ hξ
    exact hξ.comp_continuous (continuous_circleMap c r) (circleMap_mem_sphere' c r)
  have hjoint := contour_joint_aestronglyMeasurable_of_ae_samples ν μ
    (fun t ξ => F (circleMap c r t) ξ) (fun t => hm _ (circleMap_mem_sphere' c r t)) htrace
  have hderiv : Continuous (fun t : ℝ => deriv (circleMap c r) t) := by
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 r).mul continuous_const
  have hprod : AEStronglyMeasurable (fun z : ℝ × X =>
      deriv (circleMap c r) z.1 * F (circleMap c r z.1) z.2) (ν.prod μ) :=
    hderiv.aestronglyMeasurable.comp_fst.mul hjoint
  have hinner := hprod.prod_swap.integral_prod_right'
  simpa only [circleIntegral, smul_eq_mul, intervalIntegral.integral_of_le Real.two_pi_pos.le,
    ν, uIoc_of_le Real.two_pi_pos.le] using hinner

theorem circle_representation_integral_exchange_of_ae_samples
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (F : ℂ → X → ℂ) (c : ℂ) (r : ℝ)
    (hm : ∀ z ∈ sphere c |r|, AEStronglyMeasurable (F z) μ)
    (hc : ∀ᵐ ξ ∂μ, ContinuousOn (fun z => F z ξ) (sphere c |r|))
    {M : X → ℝ} (hM : Integrable M μ)
    (hb : ∀ᵐ ξ ∂μ, ∀ z ∈ sphere c |r|, ‖F z ξ‖ ≤ M ξ) :
    circleIntegral (fun z => ∫ ξ, F z ξ ∂μ) c r =
      ∫ ξ, circleIntegral (fun z => F z ξ) c r ∂μ := by
  have htrace : ∀ᵐ ξ ∂μ, Continuous (fun t : ℝ => F (circleMap c r t) ξ) := by
    filter_upwards [hc] with ξ hξ
    exact hξ.comp_continuous (continuous_circleMap c r) (circleMap_mem_sphere' c r)
  have hbound : ∀ᵐ ξ ∂μ, ∀ t : ℝ, ‖F (circleMap c r t) ξ‖ ≤ M ξ := by
    filter_upwards [hb] with ξ hξ
    exact fun t => hξ _ (circleMap_mem_sphere' c r t)
  have hweight : Integrable (fun t : ℝ => deriv (circleMap c r) t)
      (volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))) := by
    have hcont : Continuous (fun t : ℝ => deriv (circleMap c r) t) := by
      simp only [deriv_circleMap]
      exact (continuous_circleMap 0 r).mul continuous_const
    exact (show IntervalIntegrable (fun t : ℝ => deriv (circleMap c r) t)
      volume 0 (2 * Real.pi) from hcont.intervalIntegrable _ _).def'
  have hi := contour_weighted_product_integrable_of_ae_samples
    (volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))) μ
    (fun t ξ => F (circleMap c r t) ξ) (fun t => deriv (circleMap c r) t)
    (fun t => hm _ (circleMap_mem_sphere' c r t)) htrace hM hweight hbound
  have hswap := intervalIntegral_integral_swap (μ := μ)
    (f := fun t ξ => deriv (circleMap c r) t * F (circleMap c r t) ξ) hi
  simp only [circleIntegral, smul_eq_mul]
  simpa only [integral_const_mul] using hswap

/-- Cauchy's actual all-order derivative formula, proved by uniqueness of
the analytic power series rather than supplied as a derivative premise. -/
theorem one_variable_cauchy_derivative_formula {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (closedBall c r)) (n : ℕ) :
    iteratedDeriv n f c = (n.factorial : ℂ) * (2 * Real.pi * I : ℂ)⁻¹ *
      circleIntegral (fun z => (z - c)⁻¹ ^ n * ((z - c)⁻¹ * f z)) c r := by
  let rn : NNReal := ⟨r, hr.le⟩
  have hp := hf.hasFPowerSeriesOnBall (R := rn) hr
  have heq := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries
    ((hf.analyticAt (closedBall_mem_nhds _ hr)).hasFPowerSeriesAt)
  have hc : cauchyPowerSeries f c r n (fun _ => (1 : ℂ)) =
      iteratedDeriv n f c / (n.factorial : ℂ) := by
    have h := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p n (fun _ => (1 : ℂ))) heq
    simpa [FormalMultilinearSeries.ofScalars, rn] using h
  rw [cauchyPowerSeries_apply] at hc
  simp only [one_div, smul_eq_mul] at hc
  have hfact : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  calc
    _ = (n.factorial : ℂ) * (iteratedDeriv n f c / (n.factorial : ℂ)) := by field_simp
    _ = _ := by rw [← hc]; ring

/-- All scalar complex derivative orders commute with graph integration.
Derivative measurability is derived from the actual Cauchy formula, and the
integrable derivative bound is derived from the complete common majorant. -/
theorem graph_iteratedDeriv_commutes_of_ae_samples
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {F : ℂ → X → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hm : ∀ z ∈ Ω, AEStronglyMeasurable (F z) μ)
    (hd : ∀ᵐ ξ ∂μ, DifferentiableOn ℂ (fun z => F z ξ) Ω)
    (hb : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∃ M : X → ℝ,
      Integrable M μ ∧ ∀ᵐ ξ ∂μ, ∀ z ∈ K, ‖F z ξ‖ ≤ M ξ)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hclosed : closedBall c r ⊆ Ω)
    {M : X → ℝ} (hM : Integrable M μ)
    (hbound : ∀ᵐ ξ ∂μ, ∀ z ∈ closedBall c r, ‖F z ξ‖ ≤ M ξ) (n : ℕ) :
    Integrable (fun ξ => iteratedDeriv n (fun z => F z ξ) c) μ ∧
      iteratedDeriv n (fun z => ∫ ξ, F z ξ ∂μ) c =
        ∫ ξ, iteratedDeriv n (fun z => F z ξ) c ∂μ := by
  let Q : ℂ → X → ℂ := fun z ξ => (z - c)⁻¹ ^ n * ((z - c)⁻¹ * F z ξ)
  have hrabs : |r| = r := abs_of_pos hr
  have hQm : ∀ z ∈ sphere c |r|, AEStronglyMeasurable (Q z) μ := by
    intro z hz
    exact aestronglyMeasurable_const.mul (aestronglyMeasurable_const.mul
      (hm z (hclosed (sphere_subset_closedBall (hrabs ▸ hz)))))
  have hQcont : ∀ᵐ ξ ∂μ, ContinuousOn (fun z => Q z ξ) (sphere c |r|) := by
    filter_upwards [hd] with ξ hξ
    have hne : ∀ z ∈ sphere c |r|, z - c ≠ 0 := by
      intro z hz
      have hdist : dist z c = r := by simpa only [mem_sphere, hrabs] using hz
      exact sub_ne_zero.mpr (dist_pos.mp (by simpa only [hdist] using hr))
    have hk := (continuousOn_id.sub continuousOn_const).inv₀ hne
    exact (hk.pow n).mul (hk.mul (hξ.continuousOn.mono
      (fun _ hz => hclosed (sphere_subset_closedBall (hrabs ▸ hz)))))
  have hQbound : ∀ᵐ ξ ∂μ, ∀ z ∈ sphere c |r|,
      ‖Q z ξ‖ ≤ (r⁻¹ ^ n * r⁻¹) * M ξ := by
    filter_upwards [hbound] with ξ hξ
    intro z hz
    have hz' : z ∈ sphere c r := hrabs ▸ hz
    have hzNorm : ‖z - c‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hz'
    simp only [Q, norm_mul, norm_pow, norm_inv, hzNorm]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (hξ z (sphere_subset_closedBall hz')) (show 0 ≤ r⁻¹ ^ n * r⁻¹ by positivity)
  have hQM := hM.const_mul (r⁻¹ ^ n * r⁻¹)
  have hswap := circle_representation_integral_exchange_of_ae_samples μ Q c r hQm hQcont hQM hQbound
  have hmCircle := circle_representation_aestronglyMeasurable_of_ae_samples μ Q c r hQm hQcont
  have hformula : ∀ᵐ ξ ∂μ, iteratedDeriv n (fun z => F z ξ) c =
      (n.factorial : ℂ) * (2 * Real.pi * I : ℂ)⁻¹ * circleIntegral (fun z => Q z ξ) c r := by
    filter_upwards [hd] with ξ hξ
    exact one_variable_cauchy_derivative_formula hr (hξ.mono hclosed) n
  have hmD : AEStronglyMeasurable (fun ξ => iteratedDeriv n (fun z => F z ξ) c) μ :=
    ((hmCircle.const_mul ((n.factorial : ℂ) * (2 * Real.pi * I : ℂ)⁻¹))).congr
      (Filter.EventuallyEq.symm hformula)
  have hID : Integrable (fun ξ => iteratedDeriv n (fun z => F z ξ) c) μ := by
    apply (hM.const_mul ((n.factorial : ℝ) * r⁻¹ ^ n)).mono' hmD
    filter_upwards [hd, hbound] with ξ hξ hξbound
    exact one_variable_cauchy_derivative_budget hr (hξ.mono hclosed)
      (fun z hz => hξbound z (sphere_subset_closedBall hz)) n
  refine ⟨hID, ?_⟩
  have hg := holomorphy_from_compact_graph_majorants hΩ hm hd hb
  rw [one_variable_cauchy_derivative_formula hr (hg.mono hclosed) n]
  have hswap' : circleIntegral (fun z => (z - c)⁻¹ ^ n * ((z - c)⁻¹ * ∫ ξ, F z ξ ∂μ)) c r =
      ∫ ξ, circleIntegral (fun z => Q z ξ) c r ∂μ := by
    simpa only [Q, integral_const_mul] using hswap
  rw [hswap', ← integral_const_mul]
  exact integral_congr_ae (Filter.EventuallyEq.symm hformula)

/-- The source measurable-sample formulation of the all-order exchange. -/
theorem graph_iteratedDeriv_commutes
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {F : ℂ → X → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hm : ∀ z ∈ Ω, Measurable (F z))
    (hd : ∀ᵐ ξ ∂μ, DifferentiableOn ℂ (fun z => F z ξ) Ω)
    (hb : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∃ M : X → ℝ,
      Integrable M μ ∧ ∀ᵐ ξ ∂μ, ∀ z ∈ K, ‖F z ξ‖ ≤ M ξ)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hclosed : closedBall c r ⊆ Ω)
    {M : X → ℝ} (hM : Integrable M μ)
    (hbound : ∀ᵐ ξ ∂μ, ∀ z ∈ closedBall c r, ‖F z ξ‖ ≤ M ξ) (n : ℕ) :
    Integrable (fun ξ => iteratedDeriv n (fun z => F z ξ) c) μ ∧
      iteratedDeriv n (fun z => ∫ ξ, F z ξ ∂μ) c =
        ∫ ξ, iteratedDeriv n (fun z => F z ξ) c ∂μ :=
  graph_iteratedDeriv_commutes_of_ae_samples μ hΩ
    (fun z hz => (hm z hz).aestronglyMeasurable) hd hb hr hclosed hM hbound n

end UV
