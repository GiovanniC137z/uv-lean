import UV.FiniteOrders

/-! The revised forest envelope admits every positive coercive power. -/

noncomputable section

open MeasureTheory Set Real
open scoped BigOperators ENNReal NNReal Nat

namespace UV

/-- On the UV half-line any positive stretched exponential absorbs every
fixed power. A sufficiently high term of the exponential series gives
an explicit integrable comparison. -/
theorem stretched_sector_integrable {a η : ℝ} (ha : 0 < a) (hη : 0 < η) (s : ℝ) :
    IntegrableOn (fun R : ℝ => R ^ s * Real.exp (-a * R ^ η)) (Ioi 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((s + 1) / η)
  have hsn : s - η * n < -1 := by
    have := (div_lt_iff₀ hη).mp hn
    linarith
  apply ((integrableOn_Ioi_rpow_of_lt hsn zero_lt_one).const_mul
    ((n ! : ℝ) / a ^ n)).mono'
  · have hm : Measurable (fun R : ℝ => R ^ s * Real.exp (-a * R ^ η)) := by fun_prop
    exact hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with R hR
  have hRp : 0 < R := lt_trans zero_lt_one hR
  have hp : 0 < R ^ η := Real.rpow_pos_of_pos hRp _
  have haR : 0 < a * R ^ η := mul_pos ha hp
  have hfac : 0 < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hpow : 0 < (a * R ^ η) ^ n := pow_pos haR _
  have h1 : Real.exp (-a * R ^ η) ≤ (n ! : ℝ) / (a * R ^ η) ^ n := by
    rw [neg_mul, Real.exp_neg]
    apply (le_div_iff₀ hpow).mpr
    exact (inv_mul_le_iff₀ (Real.exp_pos _)).mpr
      ((div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp _ haR.le n))
  rw [Real.norm_of_nonneg (by positivity)]
  refine (mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hRp.le _)).trans_eq ?_
  rw [mul_pow, ← Real.rpow_mul_natCast hRp.le, Real.rpow_sub hRp]
  ring

/-- The revised sector's exact one-dimensional envelope. -/
def revisedSectorScale (controlled : Bool) (ω a η R : ℝ) : ℝ :=
  if controlled then R ^ (ω - 1) * Real.exp (-a * R ^ η) else R ^ (ω - 1)

theorem revised_sector_scale_integrable (controlled : Bool) (ω a η : ℝ)
    (h : if controlled then 0 < a ∧ 0 < η else ω < 0) :
    IntegrableOn (revisedSectorScale controlled ω a η) (Ioi 1) := by
  cases controlled with
  | false => exact sector_power_integrable h
  | true => exact stretched_sector_integrable h.1 h.2 _

theorem revised_sector_envelope_integrable {ι A : Type*} [Fintype ι]
    [MeasurableSpace A] {ν : Measure A} [IsFiniteMeasure ν]
    (controlled : ι → Bool) (ω a η : ι → ℝ) (C : ℝ)
    (h : ∀ i, if controlled i then 0 < a i ∧ 0 < η i else ω i < 0) :
    Integrable (fun x : (ι → ℝ) × A =>
      C * ∏ i, revisedSectorScale (controlled i) (ω i) (a i) (η i) (x.1 i))
      ((Measure.pi (fun _ : ι => volume.restrict (Ioi (1 : ℝ)))).prod ν) := by
  have hp := Integrable.fintype_prod (fun i => revised_sector_scale_integrable
    (controlled i) (ω i) (a i) (η i) (h i))
  simpa only [mul_one] using (hp.mul_prod (integrable_const (μ := ν) (1 : ℝ))).const_mul C

/-- Revised forest convergence with the actual Jacobian and arbitrary positive
coercive exponents, uniform over the external data. -/
theorem revised_uniform_forest_convergence
    {P H X : Type*} [Fintype H] [MeasurableSpace X]
    {A : H → Type*} [∀ h, MeasurableSpace (A h)]
    (r : H → ℕ) (ν : ∀ h, Measure (A h)) [∀ h, IsFiniteMeasure (ν h)]
    (μ μIR : Measure X) (σ : ∀ h, ((Fin (r h) → ℝ) × A h) → X)
    (J : ∀ h, ((Fin (r h) → ℝ) × A h) → ℝ≥0)
    (controlled : ∀ h, Fin (r h) → Bool) (ω a η : ∀ h, Fin (r h) → ℝ)
    (C : H → ℝ) (f : P → X → ℂ) (hf : ∀ p, StronglyMeasurable (f p))
    (hσ : ∀ h, Measurable (σ h)) (hJ : ∀ h, Measurable (J h))
    (gIR : X → ℝ) (hgIR : Integrable gIR μIR)
    (hIR : ∀ p, ∀ᵐ x ∂μIR, ‖f p x‖ ≤ gIR x)
    (hscale : ∀ h i, if controlled h i then 0 < a h i ∧ 0 < η h i else ω h i < 0)
    (henvelope : ∀ p h, ∀ᵐ x ∂((Measure.pi (fun _ : Fin (r h) =>
      volume.restrict (Ioi (1 : ℝ)))).prod (ν h)),
      ‖J h x • f p (σ h x)‖ ≤ C h * ∏ i,
        revisedSectorScale (controlled h i) (ω h i) (a h i) (η h i) (x.1 i))
    (hcover : μ ≤ μIR + ∑ h, Measure.map (σ h)
      (Measure.withDensity
        ((Measure.pi (fun _ : Fin (r h) => volume.restrict (Ioi (1 : ℝ)))).prod (ν h))
        (fun x => (J h x : ℝ≥0∞)))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p, Integrable (f p) μ ∧ (∫ x, ‖f p x‖ ∂μ) ≤ B := by
  classical
  let β h := (Measure.pi (fun _ : Fin (r h) => volume.restrict (Ioi (1 : ℝ)))).prod (ν h)
  let env h (x : (Fin (r h) → ℝ) × A h) := C h * ∏ i,
    revisedSectorScale (controlled h i) (ω h i) (a h i) (η h i) (x.1 i)
  let m h := Measure.map (σ h) ((β h).withDensity (fun x => (J h x : ℝ≥0∞)))
  have he h : Integrable (env h) (β h) :=
    revised_sector_envelope_integrable (controlled h) (ω h) (a h) (η h) (C h) (hscale h)
  have hw p h : Integrable (fun x => J h x • f p (σ h x)) (β h) :=
    (he h).mono' ((hJ h).aestronglyMeasurable.smul
      ((hf p).comp_measurable (hσ h)).aestronglyMeasurable) (henvelope p h)
  have hm p h : Integrable (f p) (m h) :=
    (integrable_map_measure (hf p).aestronglyMeasurable (hσ h).aemeasurable).mpr
      ((integrable_withDensity_iff_integrable_smul (hJ h)).mpr (hw p h))
  have hsum p : Integrable (f p) (∑ h, m h) :=
    integrable_finset_sum_measure.mpr fun h _ => hm p h
  have hir p : Integrable (f p) μIR :=
    hgIR.mono' (hf p).aestronglyMeasurable (hIR p)
  have hm_bound p h : (∫ x, ‖f p x‖ ∂m h) ≤ ∫ x, env h x ∂β h := by
    rw [integral_map_of_stronglyMeasurable (hσ h) (hf p).norm,
      integral_withDensity_eq_integral_smul (hJ h)]
    have heq : (fun x => J h x • ‖f p (σ h x)‖) =
        (fun x => ‖J h x • f p (σ h x)‖) := by
      funext x
      change (J h x : ℝ) * ‖f p (σ h x)‖ = ‖(J h x : ℝ) • f p (σ h x)‖
      rw [norm_smul, Real.norm_of_nonneg (J h x).coe_nonneg]
    rw [heq]
    exact integral_mono_ae (hw p h).norm (he h) (henvelope p h)
  let B := (∫ x, gIR x ∂μIR) + ∑ h, ∫ x, env h x ∂β h
  refine ⟨max 0 B, le_max_left _ _, fun p => ?_⟩
  have hv := (hir p).add_measure (hsum p)
  refine ⟨hv.mono_measure hcover, ?_⟩
  calc
    _ ≤ ∫ x, ‖f p x‖ ∂(μIR + ∑ h, m h) :=
      integral_mono_measure hcover (Filter.Eventually.of_forall fun x => norm_nonneg _) hv.norm
    _ = (∫ x, ‖f p x‖ ∂μIR) + ∑ h, ∫ x, ‖f p x‖ ∂m h := by
      rw [integral_add_measure (hir p).norm (hsum p).norm,
        integral_finset_sum_measure (fun h _ => (hm p h).norm)]
    _ ≤ B := add_le_add (integral_mono_ae (hir p).norm hgIR (hIR p))
      (Finset.sum_le_sum fun h _ => hm_bound p h)
    _ ≤ max 0 B := le_max_right _ _

end UV
