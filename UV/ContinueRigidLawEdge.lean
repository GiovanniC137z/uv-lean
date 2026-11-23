import UV.ContinueRigidLawDensity
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-! The charge edge law for the gamma distribution convolved with the rigid
source's compound-Poisson law. The positive-jump contribution gains one power
of the emitted energy relative to the atom contribution. -/

noncomputable section

open MeasureTheory Set Real Filter ProbabilityTheory Asymptotics
open scoped ENNReal MeasureTheory Interval Topology

namespace UV.ContinueRigidLaw

/-- A density version separating the zero-jump and positive-jump contributions. -/
def gammaPoissonDensity (f : ℝ → ℝ≥0∞) (α B x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (exp (-((volume : Measure ℝ).withDensity f).real univ)) * gammaPDF α B x +
    translatedDensity (gammaMeasure α B) (positiveJumpDensity f) x

theorem gammaPoissonDensity_represents {f : ℝ → ℝ≥0∞}
    [IsFiniteMeasure ((volume : Measure ℝ).withDensity f)] (hf : Measurable f)
    {α B : ℝ} (hα : 0 < α) (hB : 0 < B) :
    gammaMeasure α B ∗ compoundPoisson (volume.withDensity f) =
      volume.withDensity (gammaPoissonDensity f α B) := by
  let η := (volume : Measure ℝ).withDensity f
  let c := ENNReal.ofReal (exp (-(η.real univ)))
  haveI := isProbabilityMeasure_gammaMeasure hα hB
  have hg : Measurable (gammaPDF α B) := (measurable_gammaPDFReal _ _).ennreal_ofReal
  have hp : Measurable (positiveJumpDensity f) := measurable_positiveJumpDensity hf
  rw [compoundPoisson_eq_atom_add_density hf, Measure.conv_add, Measure.conv_smul_right,
    Measure.conv_dirac_zero, conv_withDensity_eq _ hp]
  change c • volume.withDensity (gammaPDF α B) +
    volume.withDensity (translatedDensity (gammaMeasure α B) (positiveJumpDensity f)) = _
  rw [← withDensity_smul c hg]
  exact (withDensity_add_left (measurable_const.mul hg) _).symm

theorem lintegral_gammaPDF_le {α B x : ℝ} (hα : 0 < α) (hB : 0 < B) (hx : 0 < x) :
    ∫⁻ y in Ioc 0 x, gammaPDF α B y ≤ ENNReal.ofReal ((B^α/Gamma α) * x^α/α) := by
  let C := B^α/Gamma α
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp : -1 < α-1 := by linarith
  have hpint : IntervalIntegrable (fun y : ℝ ↦ y ^ (α-1)) volume 0 x :=
    intervalIntegral.intervalIntegrable_rpow' hp
  calc
    _ ≤ ∫⁻ y in Ioc 0 x, ENNReal.ofReal (C*y^(α-1)) := by
      refine setLIntegral_mono' measurableSet_Ioc fun y hy ↦ ?_
      have hy₀ := hy.1
      rw [gammaPDF_of_nonneg hy₀.le]
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_of_le_one_right (mul_nonneg hC (rpow_nonneg hy₀.le _))
        (exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hB.le hy₀.le)))
    _ = _ := by
      have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 x)] (fun y ↦ C*y^(α-1)) :=
        (ae_restrict_iff' measurableSet_Ioc).mpr <| ae_of_all _ fun y hy ↦
          mul_nonneg hC (rpow_nonneg hy.1.le _)
      rw [← ofReal_integral_eq_lintegral_ofReal (hpint.1.const_mul C) hnn,
        ← intervalIntegral.integral_of_le hx.le, intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl hp), sub_add_cancel, zero_rpow hα.ne', sub_zero]
      congr 1
      ring

/-- The positive-jump density is bounded by an explicit multiple of `x^α`. -/
theorem gammaPoissonRemainder_le {f : ℝ → ℝ≥0∞}
    [IsFiniteMeasure ((volume : Measure ℝ).withDensity f)] (hf : Measurable f)
    {K : ℝ≥0∞} (hfK : ∀ y, f y ≤ K) (hf₀ : ∀ y ≤ 0, f y = 0)
    {α B x : ℝ} (hα : 0 < α) (hB : 0 < B) (hx : 0 < x) :
    translatedDensity (gammaMeasure α B) (positiveJumpDensity f) x ≤
      K * ENNReal.ofReal ((B^α/Gamma α) * x^α/α) := by
  have hg : Measurable (gammaPDF α B) := (measurable_gammaPDFReal _ _).ennreal_ofReal
  have hp : Measurable (positiveJumpDensity f) := measurable_positiveJumpDensity hf
  unfold translatedDensity gammaMeasure
  have hp' : Measurable (fun z : ℝ ↦ positiveJumpDensity f (x-z)) :=
    hp.comp (by fun_prop)
  rw [lintegral_withDensity_eq_lintegral_mul _ hg hp']
  change (∫⁻ z, gammaPDF α B z * positiveJumpDensity f (x-z)) ≤ _
  have hset :
      (∫⁻ z, gammaPDF α B z * positiveJumpDensity f (x-z)) =
      ∫⁻ z in Icc 0 x, gammaPDF α B z * positiveJumpDensity f (x-z) := by
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro z
    by_cases hz : z ∈ Icc 0 x
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz]
      by_cases hz₀ : 0 ≤ z
      · have hzx : x ≤ z := by
          by_contra! he
          exact hz ⟨hz₀,he.le⟩
        rw [positiveJumpDensity_of_nonpos hf₀ (sub_nonpos.mpr hzx), mul_zero]
      · rw [gammaPDF_of_neg (lt_of_not_ge hz₀), zero_mul]
  rw [hset, ← restrict_Ioc_eq_restrict_Icc]
  calc
    _ ≤ ∫⁻ z in Ioc 0 x, K * gammaPDF α B z := by
      apply lintegral_mono
      intro z
      change gammaPDF α B z * positiveJumpDensity f (x-z) ≤ K * gammaPDF α B z
      rw [mul_comm K]
      exact mul_le_mul_left' (positiveJumpDensity_le hfK _) _
    _ = K * ∫⁻ z in Ioc 0 x, gammaPDF α B z := lintegral_const_mul _ hg
    _ ≤ _ := mul_le_mul_left' (lintegral_gammaPDF_le hα hB hx) _

/-- The manuscript's charge density above the threshold, with a quantitative positive error. -/
theorem gammaPoissonDensity_edge {f : ℝ → ℝ≥0∞}
    [IsFiniteMeasure ((volume : Measure ℝ).withDensity f)] (hf : Measurable f)
    {K : ℝ} (hK : 0 ≤ K) (hfK : ∀ y, f y ≤ ENNReal.ofReal K)
    (hf₀ : ∀ y ≤ 0, f y = 0) {α B x : ℝ} (hα : 0 < α) (hB : 0 < B) (hx : 0 < x) :
    ∃ R : ℝ, 0 ≤ R ∧ R ≤ K * (B^α/Gamma α) * x^α/α ∧
      (gammaPoissonDensity f α B x).toReal =
        exp (-((volume : Measure ℝ).withDensity f).real univ) *
            (B^α/Gamma α) * x^(α-1) * exp (-(B*x)) + R := by
  have hR := gammaPoissonRemainder_le hf hfK hf₀ hα hB hx
  have hRfinite : translatedDensity (gammaMeasure α B) (positiveJumpDensity f) x ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hR
  refine ⟨(translatedDensity (gammaMeasure α B) (positiveJumpDensity f) x).toReal,
    ENNReal.toReal_nonneg, ?_, ?_⟩
  · have hbnd := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hR
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK, ENNReal.toReal_ofReal (by positivity)] at hbnd
    convert hbnd using 1
    ring
  · unfold gammaPoissonDensity
    rw [gammaPDF_of_nonneg hx.le, ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hRfinite,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos _).le,
      ENNReal.toReal_ofReal (by positivity)]
    congr 1
    ring

/-- The ratio to the manuscript's leading power tends to one at the charge edge. -/
theorem gammaPoissonDensity_asymptotic {f : ℝ → ℝ≥0∞}
    [IsFiniteMeasure ((volume : Measure ℝ).withDensity f)] (hf : Measurable f)
    {K : ℝ} (hK : 0 ≤ K) (hfK : ∀ y, f y ≤ ENNReal.ofReal K)
    (hf₀ : ∀ y ≤ 0, f y = 0) {α B : ℝ} (hα : 0 < α) (hB : 0 < B) :
    (fun x ↦ (gammaPoissonDensity f α B x).toReal) ~[𝓝[>] (0 : ℝ)]
      fun x ↦ exp (-((volume : Measure ℝ).withDensity f).real univ) *
        (B^α/Gamma α) * x^(α-1) := by
  let m := exp (-((volume : Measure ℝ).withDensity f).real univ)
  let A := B^α/Gamma α
  have hm : 0 < m := exp_pos _
  have hA : 0 < A := by dsimp [A]; positivity
  have hp : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), 0 < x := self_mem_nhdsWithin
  have hbase {x : ℝ} (hx : 0 < x) : 0 < m*A*x^(α-1) :=
    mul_pos (mul_pos hm hA) (rpow_pos_of_pos hx _)
  change (fun x ↦ (gammaPoissonDensity f α B x).toReal) ~[𝓝[>] (0 : ℝ)]
    (fun x ↦ m*A*x^(α-1))
  rw [isEquivalent_iff_tendsto_one (hp.mono fun _ hx ↦ (hbase hx).ne')]
  let lower := fun x : ℝ ↦ exp (-(B*x))
  let upper := fun x : ℝ ↦ lower x + (K/(m*α))*x
  have hlo : Tendsto lower (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hc : Continuous lower := by dsimp [lower]; fun_prop
    have ht := hc.continuousWithinAt (s := Ioi 0) (x := (0 : ℝ))
    change Tendsto lower (𝓝[>] (0 : ℝ)) (𝓝 (lower 0)) at ht
    simpa [lower] using ht
  have hup : Tendsto upper (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hc : Continuous upper := by dsimp [upper, lower]; fun_prop
    have ht := hc.continuousWithinAt (s := Ioi 0) (x := (0 : ℝ))
    change Tendsto upper (𝓝[>] (0 : ℝ)) (𝓝 (upper 0)) at ht
    simpa [upper, lower] using ht
  have hbetween : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      lower x ≤ (gammaPoissonDensity f α B x).toReal / (m*A*x^(α-1)) ∧
      (gammaPoissonDensity f α B x).toReal / (m*A*x^(α-1)) ≤ upper x := by
    filter_upwards [hp] with x hx
    obtain ⟨R, hR, hRK, he⟩ := gammaPoissonDensity_edge hf hK hfK hf₀ hα hB hx
    change (gammaPoissonDensity f α B x).toReal = m*A*x^(α-1)*lower x + R at he
    change R ≤ K*A*x^α/α at hRK
    have hxp : x^α = x^(α-1)*x := by
      calc
        x^α = x^((α-1)+1) := by congr 1; ring
        _ = _ := by rw [rpow_add hx, rpow_one]
    constructor
    · rw [he, le_div_iff₀ (hbase hx)]
      linarith [mul_comm (lower x) (m*A*x^(α-1))]
    · change (gammaPoissonDensity f α B x).toReal / (m*A*x^(α-1)) ≤
        lower x + (K/(m*α))*x
      rw [he, div_le_iff₀ (hbase hx), add_mul]
      calc
        _ = lower x * (m*A*x^(α-1)) + R := by ring
        _ ≤ lower x * (m*A*x^(α-1)) + K*A*x^α/α := add_le_add_left hRK _
        _ = _ := by
          rw [hxp]
          field_simp [hm.ne', hα.ne']
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
    (hbetween.mono fun _ hx ↦ hx.1) (hbetween.mono fun _ hx ↦ hx.2)

/-- The emitted-energy density and its leading coefficient, before translating by `E_*`. -/
theorem emittedEnergyLaw_density_edge (ν : Measure ℝ) [IsFiniteMeasure ν] {b₀ B : ℝ}
    (hb₀ : 0 < b₀) (hB : b₀ ≤ B) (hν : ∀ᵐ b ∂ν, b₀ ≤ b ∧ b ≤ B)
    (hα : 0 < ν.real univ) :
    let α := ν.real univ
    let M := (residualMeasure ν B).real univ
    let f := gammaPoissonDensity (residual ν B) α B
    emittedEnergyLaw ν B = volume.withDensity f ∧
      (fun x ↦ (f x).toReal) ~[𝓝[>] (0 : ℝ)]
        fun x ↦ exp (-M) * (B^α/Gamma α) * x^(α-1) := by
  haveI : IsFiniteMeasure ((volume : Measure ℝ).withDensity (residual ν B)) :=
    finite_residualMeasure ν hb₀ hB hν
  have hBpos := hb₀.trans_le hB
  have hf := measurable_residual ν B
  refine ⟨gammaPoissonDensity_represents hf hα hBpos, ?_⟩
  have hzero (y : ℝ) (hy : y ≤ 0) : residual ν B y = 0 :=
    indicator_of_notMem (not_lt.mpr hy) _
  have hbound (y : ℝ) : residual ν B y ≤ ENNReal.ofReal (B * ν.real univ) := by
    rw [ENNReal.ofReal_mul hBpos.le, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top ν _)]
    exact residual_le ν (hν.mono fun _ hb ↦ hb₀.le.trans hb.1)
  exact gammaPoissonDensity_asymptotic hf (mul_nonneg hBpos.le ENNReal.toReal_nonneg)
    hbound hzero hα hBpos

end UV.ContinueRigidLaw
