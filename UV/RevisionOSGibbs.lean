import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! Integration and one-sided variation of the actual normalized Gibbs tilt
used in the scalar reflection tests. The tilt is bounded for every positive
coupling when the potential has a deterministic lower bound. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace UV

variable {X : Type*} [MeasurableSpace X]

def osGibbsWeight (V : X → ℝ) (g : ℝ) (x : X) : ℝ := Real.exp (-(g * V x))

def osGibbsNumerator (μ : Measure X) (V A : X → ℝ) (g : ℝ) : ℝ :=
  ∫ x, A x * osGibbsWeight V g x ∂μ

def osGibbsPartition (μ : Measure X) (V : X → ℝ) (g : ℝ) : ℝ :=
  ∫ x, osGibbsWeight V g x ∂μ

def osGibbsExpectation (μ : Measure X) (V A : X → ℝ) (g : ℝ) : ℝ :=
  osGibbsNumerator μ V A g / osGibbsPartition μ V g

def osGibbsMeasure (μ : Measure X) (V : X → ℝ) (g : ℝ) : Measure X :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (osGibbsWeight V g x / osGibbsPartition μ V g))

omit [MeasurableSpace X] in
theorem osGibbsWeight_le {V : X → ℝ} {L g : ℝ} (hg : 0 ≤ g) {x : X}
    (hV : -L ≤ V x) : osGibbsWeight V g x ≤ Real.exp (g * L) := by
  apply Real.exp_le_exp.mpr
  exact neg_le_of_neg_le (by simpa using mul_le_mul_of_nonneg_left hV hg)

theorem osGibbsNumerator_integrable {μ : Measure X} {V A : X → ℝ} {L g : ℝ}
    (hV : AEMeasurable V μ) (hA : Integrable A μ) (hL : ∀ᵐ x ∂μ, -L ≤ V x)
    (hg : 0 ≤ g) : Integrable (fun x ↦ A x * osGibbsWeight V g x) μ := by
  have he : AEMeasurable (osGibbsWeight V g) μ := by
    unfold osGibbsWeight
    fun_prop
  apply (hA.norm.mul_const (Real.exp (g * L))).mono' (hA.aestronglyMeasurable.mul he.aestronglyMeasurable)
  filter_upwards [hL] with x hx
  change ‖A x * osGibbsWeight V g x‖ ≤ _
  rw [norm_mul, Real.norm_of_nonneg (show 0 ≤ osGibbsWeight V g x from (Real.exp_pos _).le)]
  exact mul_le_mul_of_nonneg_left (osGibbsWeight_le hg hx) (norm_nonneg _)

theorem osGibbsWeight_integrable {μ : Measure X} [IsFiniteMeasure μ] {V : X → ℝ}
    {L g : ℝ} (hV : AEMeasurable V μ) (hL : ∀ᵐ x ∂μ, -L ≤ V x) (hg : 0 ≤ g) :
    Integrable (osGibbsWeight V g) μ := by
  simpa using osGibbsNumerator_integrable hV (integrable_const (1 : ℝ)) hL hg

theorem osGibbsPartition_pos {μ : Measure X} [IsProbabilityMeasure μ] {V : X → ℝ}
    {L g : ℝ} (hV : AEMeasurable V μ) (hL : ∀ᵐ x ∂μ, -L ≤ V x) (hg : 0 ≤ g) :
    0 < osGibbsPartition μ V g := by
  apply (integral_pos_iff_support_of_nonneg (fun _ ↦ (Real.exp_pos _).le)
    (osGibbsWeight_integrable hV hL hg)).2
  have h : Function.support (osGibbsWeight V g) = univ := by
    ext x
    simp [osGibbsWeight, Real.exp_ne_zero]
  change 0 < μ (Function.support (osGibbsWeight V g))
  rw [h, measure_univ]
  simp

theorem osGibbsPartition_le {μ : Measure X} [IsProbabilityMeasure μ] {V : X → ℝ}
    {L g : ℝ} (hV : AEMeasurable V μ) (hL : ∀ᵐ x ∂μ, -L ≤ V x) (hg : 0 ≤ g) :
    osGibbsPartition μ V g ≤ Real.exp (g * L) := by
  have h := integral_mono_ae (osGibbsWeight_integrable hV hL hg)
    (integrable_const (Real.exp (g * L))) (hL.mono fun x hx ↦ osGibbsWeight_le hg hx)
  simpa [osGibbsPartition] using h

theorem osGibbsPartition_ge_one_of_centered {μ : Measure X} [IsProbabilityMeasure μ]
    {V : X → ℝ} {L g : ℝ} (hV : Integrable V μ) (hL : ∀ᵐ x ∂μ, -L ≤ V x)
    (hg : 0 ≤ g) (hcenter : (∫ x, V x ∂μ) = 0) : 1 ≤ osGibbsPartition μ V g := by
  have ha : Integrable (fun x ↦ 1 + (-g) * V x) μ := (integrable_const _).add (hV.const_mul _)
  have hb : (∫ x, 1 + (-g) * V x ∂μ) ≤ osGibbsPartition μ V g :=
    integral_mono_ae ha (osGibbsWeight_integrable hV.aemeasurable hL hg)
      (Eventually.of_forall fun x ↦ by
        rw [osGibbsWeight, ← neg_mul]
        exact Real.add_one_le_exp _ |>.trans_eq' (add_comm _ _))
  rw [integral_add (integrable_const _) (hV.const_mul _), integral_const_mul, hcenter,
    mul_zero, add_zero, integral_const] at hb
  simpa [Measure.real] using hb

theorem osGibbsMeasure_probability {μ : Measure X} [IsProbabilityMeasure μ]
    {V : X → ℝ} {L g : ℝ} (hV : AEMeasurable V μ) (hL : ∀ᵐ x ∂μ, -L ≤ V x)
    (hg : 0 ≤ g) : IsProbabilityMeasure (osGibbsMeasure μ V g) := by
  have hp := osGibbsPartition_pos hV hL hg
  have hi := (osGibbsWeight_integrable hV hL hg).div_const (osGibbsPartition μ V g)
  constructor
  unfold osGibbsMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall fun _ ↦ div_nonneg (Real.exp_pos _).le hp.le),
    integral_div]
  change ENNReal.ofReal (osGibbsPartition μ V g / osGibbsPartition μ V g) = 1
  rw [div_self hp.ne', ENNReal.ofReal_one]

theorem osGibbsMeasure_integrable {μ : Measure X} [IsProbabilityMeasure μ]
    {V A : X → ℝ} {L g : ℝ} (hV : Measurable V) (hA : Integrable A μ)
    (hL : ∀ᵐ x ∂μ, -L ≤ V x) (hg : 0 ≤ g) : Integrable A (osGibbsMeasure μ V g) := by
  have hp := osGibbsPartition_pos hV.aemeasurable hL hg
  have hw : Measurable (fun x ↦ ENNReal.ofReal (osGibbsWeight V g x /
      osGibbsPartition μ V g)) := by unfold osGibbsWeight; fun_prop
  apply (integrable_withDensity_iff_integrable_smul' hw
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mpr
  apply ((osGibbsNumerator_integrable hV.aemeasurable hA hL hg).div_const
    (osGibbsPartition μ V g)).congr
  filter_upwards with x
  have hx : 0 ≤ osGibbsWeight V g x := (Real.exp_pos _).le
  rw [ENNReal.toReal_ofReal (div_nonneg hx hp.le), smul_eq_mul]
  ring

theorem osGibbsMeasure_expectation {μ : Measure X} [IsProbabilityMeasure μ]
    {V A : X → ℝ} {L g : ℝ} (hV : Measurable V)
    (hL : ∀ᵐ x ∂μ, -L ≤ V x) (hg : 0 ≤ g) :
    (∫ x, A x ∂osGibbsMeasure μ V g) = osGibbsExpectation μ V A g := by
  have hp := osGibbsPartition_pos hV.aemeasurable hL hg
  have hw : Measurable (fun x ↦ ENNReal.ofReal (osGibbsWeight V g x /
      osGibbsPartition μ V g)) := by unfold osGibbsWeight; fun_prop
  rw [osGibbsMeasure, integral_withDensity_eq_integral_toReal_smul hw
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  unfold osGibbsExpectation osGibbsNumerator
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards with x
  have hx : 0 ≤ osGibbsWeight V g x := (Real.exp_pos _).le
  rw [ENNReal.toReal_ofReal (div_nonneg hx hp.le), smul_eq_mul]
  ring

/-- The exact right derivative of an unnormalized Gibbs integral. A single
integrable moment of the observable times the potential supplies the
majorant in the difference quotient. -/
theorem osGibbsNumerator_hasRightDeriv {μ : Measure X} {V A : X → ℝ} {L : ℝ}
    (hV : AEMeasurable V μ) (hA : Integrable A μ) (hAV : Integrable (fun x ↦ A x * V x) μ)
    (hL : ∀ᵐ x ∂μ, -L ≤ V x) (hL0 : 0 ≤ L) :
    HasDerivWithinAt (osGibbsNumerator μ V A) (-(∫ x, A x * V x ∂μ)) (Ioi 0) 0 := by
  apply (hasDerivWithinAt_iff_tendsto_slope' (notMem_Ioi_self : (0 : ℝ) ∉ Ioi 0)).mpr
  have hD (x : X) (g : ℝ) : HasDerivAt (fun t ↦ A x * osGibbsWeight V t x)
      (A x * ((-V x) * osGibbsWeight V g x)) g := by
    unfold osGibbsWeight
    convert (((hasDerivAt_id g).mul_const (-V x)).exp.const_mul (A x)) using 1
    · funext t
      congr 2
      simp only [id_eq]
      ring
    · simp [id_eq, neg_mul, mul_comm]
  have hnorm {x : X} (hx : -L ≤ V x) {g : ℝ} (hg : g ∈ Icc (0 : ℝ) 1) :
      ‖A x * ((-V x) * osGibbsWeight V g x)‖ ≤ ‖A x * V x‖ * Real.exp L := by
    rw [norm_mul, norm_mul, norm_neg, ← mul_assoc, ← norm_mul,
      Real.norm_of_nonneg (show 0 ≤ osGibbsWeight V g x from (Real.exp_pos _).le)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (osGibbsWeight_le hg.1 hx).trans (Real.exp_le_exp.mpr (by nlinarith [hg.2]))
  have hlim : Tendsto (fun g : ℝ ↦ ∫ x, slope (fun t ↦ A x * osGibbsWeight V t x) 0 g ∂μ)
      (𝓝[Ioi 0] 0) (𝓝 (∫ x, -(A x * V x) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x ↦ ‖A x * V x‖ * Real.exp L)
    · refine Eventually.of_forall fun g ↦ ?_
      have hW : ∀ t : ℝ, AEMeasurable (osGibbsWeight V t) μ := fun t ↦ by
        unfold osGibbsWeight
        fun_prop
      simp only [slope_def_field, sub_zero]
      exact (((hA.aemeasurable.mul (hW g)).sub (hA.aemeasurable.mul (hW 0))).div_const g).aestronglyMeasurable
    · have he : ∀ᶠ g : ℝ in 𝓝[Ioi 0] (0 : ℝ), g ∈ Ioc (0 : ℝ) 1 := by
        have h₁ : ∀ᶠ g : ℝ in 𝓝[Ioi 0] (0 : ℝ), g ∈ Ioi 0 := eventually_mem_nhdsWithin
        have h₂ : ∀ᶠ g : ℝ in 𝓝[Ioi 0] (0 : ℝ), g ∈ Iio 1 :=
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num))
        filter_upwards [h₁, h₂] with g hg₁ hg₂ using ⟨hg₁, hg₂.le⟩
      filter_upwards [he] with g hg
      filter_upwards [hL] with x hx
      have hb := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun t _ ↦ (hD x t).hasDerivWithinAt) (fun _ ht ↦ hnorm hx ht)
        (left_mem_Icc.mpr (by norm_num)) ⟨hg.1.le, hg.2⟩
      rw [slope_def_field, sub_zero, norm_div, Real.norm_of_nonneg hg.1.le]
      exact (div_le_iff₀ hg.1).mpr (by simpa [Real.norm_of_nonneg hg.1.le] using hb)
    · exact hAV.norm.mul_const _
    · refine Eventually.of_forall fun x ↦ ?_
      have h := (hD x 0).hasDerivWithinAt (s := Ioi 0)
      have he : A x * ((-V x) * osGibbsWeight V 0 x) = -(A x * V x) := by
        simp [osGibbsWeight, mul_neg]
      rw [he] at h
      exact (hasDerivWithinAt_iff_tendsto_slope' (notMem_Ioi_self : (0 : ℝ) ∉ Ioi 0)).mp h
  rw [integral_neg] at hlim
  apply hlim.congr'
  filter_upwards [eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0)] with g hg
  simp only [slope_def_field, sub_zero]
  rw [integral_div, integral_sub (osGibbsNumerator_integrable hV hA hL hg.le)
    (osGibbsNumerator_integrable hV hA hL le_rfl)]
  rfl

/-- At a free null vector the normalized right derivative is exactly the
negative mixed moment with the potential. -/
theorem osGibbsExpectation_hasRightDeriv_of_null {μ : Measure X} [IsProbabilityMeasure μ]
    {V A : X → ℝ} {L : ℝ} (hV : Integrable V μ) (hA : Integrable A μ)
    (hAV : Integrable (fun x ↦ A x * V x) μ) (hL : ∀ᵐ x ∂μ, -L ≤ V x)
    (hL0 : 0 ≤ L) (hnull : (∫ x, A x ∂μ) = 0) :
    HasDerivWithinAt (osGibbsExpectation μ V A) (-(∫ x, A x * V x ∂μ)) (Ioi 0) 0 := by
  have hN := osGibbsNumerator_hasRightDeriv hV.aemeasurable hA hAV hL hL0
  have hP := osGibbsNumerator_hasRightDeriv hV.aemeasurable (integrable_const (1 : ℝ))
    (by simpa using hV) hL hL0
  have hE : osGibbsNumerator μ V (fun _ ↦ 1) = osGibbsPartition μ V := by
    funext g
    simp [osGibbsNumerator, osGibbsPartition]
  rw [hE] at hP
  have hP0 : osGibbsPartition μ V 0 = 1 := by simp [osGibbsPartition, osGibbsWeight]
  have hN0 : osGibbsNumerator μ V A 0 = 0 := by simp [osGibbsNumerator, osGibbsWeight, hnull]
  convert hN.div hP (by simp [hP0]) using 1
  simp [hN0, hP0]

/-- A positive mixed moment with the potential makes the normalized null
norm strictly negative for every sufficiently small positive coupling. -/
theorem osGibbsExpectation_eventually_neg_of_null {μ : Measure X} [IsProbabilityMeasure μ]
    {V A : X → ℝ} {L : ℝ} (hV : Integrable V μ) (hA : Integrable A μ)
    (hAV : Integrable (fun x ↦ A x * V x) μ) (hL : ∀ᵐ x ∂μ, -L ≤ V x)
    (hL0 : 0 ≤ L) (hnull : (∫ x, A x ∂μ) = 0)
    (hpos : 0 < ∫ x, A x * V x ∂μ) :
    ∀ᶠ g : ℝ in 𝓝[Ioi 0] 0, osGibbsExpectation μ V A g < 0 := by
  have hD := osGibbsExpectation_hasRightDeriv_of_null hV hA hAV hL hL0 hnull
  have h := (hasDerivWithinAt_iff_tendsto_slope' (notMem_Ioi_self : (0 : ℝ) ∉ Ioi 0)).mp hD
  have hs := h.eventually (gt_mem_nhds (neg_neg_of_pos hpos))
  have h0 : osGibbsExpectation μ V A 0 = 0 := by
    simp [osGibbsExpectation, osGibbsNumerator, osGibbsWeight, hnull]
  filter_upwards [hs, eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0)] with g hsg hg
  rw [slope_def_field, sub_zero, h0, sub_zero] at hsg
  exact (div_lt_iff₀ hg).mp hsg |>.trans_le (by simp)

end UV
