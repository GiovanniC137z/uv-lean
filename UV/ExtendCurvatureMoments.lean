import UV.ExtendCurvatureGibbs

/-! Finite elementary-mode observables and common Gaussian moment majorants
for the same normalized finite-coupling torus source. -/

noncomputable section

open MeasureTheory Real Filter
open scoped Topology ENNReal BigOperators

namespace UV.ExtendCurvatureMoments

open UV.NextCurvatureLaw UV.ExtendCurvatureGibbs UV.RevisionCurvatureDeterminant

def fixedReadout {n : ℕ} (S : Finset (ModeSlot n)) (p : Preparation n) : S → ℝ :=
  fun i => depthRescale p.1 p.2 i.1

def cutoffReadout {n : ℕ} (S : Finset (ModeSlot n)) (Λ : ℝ) (p : Preparation n) : S → ℝ :=
  fun i => if latticeFrequency i.1.1 ≤ Λ then depthRescale p.1 p.2 i.1 else 0

theorem fixedReadout_measurable {n : ℕ} (S : Finset (ModeSlot n)) :
    Measurable (fixedReadout S) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply i.1).comp (depthRescale_jointly_measurable n)

theorem cutoffReadout_measurable {n : ℕ} (S : Finset (ModeSlot n)) (Λ : ℝ) :
    Measurable (cutoffReadout S Λ) := by
  apply measurable_pi_lambda
  intro i
  unfold cutoffReadout
  split
  · exact (measurable_pi_apply i.1).comp (depthRescale_jointly_measurable n)
  · exact measurable_const

theorem cutoffReadout_eventually_eq {n : ℕ} (S : Finset (ModeSlot n)) :
    ∀ᶠ Λ : ℝ in atTop, cutoffReadout S Λ = fixedReadout S := by
  refine eventually_atTop.mpr ⟨∑ i ∈ S, latticeFrequency i.1, ?_⟩
  intro Λ hΛ
  funext p i
  have hi : latticeFrequency i.1.1 ≤ Λ :=
    (Finset.single_le_sum (f := fun j : ModeSlot n => latticeFrequency j.1)
      (fun _ _ => sqrt_nonneg _) i.2).trans hΛ
  simp [cutoffReadout, fixedReadout, hi]

/-- Normalized expectations of literal finite-mode observables converge
along all real spherical cutoffs. The common absolute envelope can be
nonconstant, as happens for polynomial moments. -/
theorem normalized_observable_limit {n : ℕ} (hn : 0 < n) (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ)
    (hpos : μ (Set.Ioi 0) ≠ 0) {g : ℝ} (hg : 0 ≤ g) (S : Finset (ModeSlot n))
    (F : (S → ℝ) → ℝ) (hm : Measurable F) (b : Preparation n → ℝ)
    (hb : Integrable b (preparationMeasure n μ))
    (hF : ∀ Λ p, ‖F (cutoffReadout S Λ p)‖ ≤ b p) :
    Integrable (fun p => fullWeight B g p * F (fixedReadout S p)) (preparationMeasure n μ) ∧
    Tendsto (fun Λ : ℝ =>
      (∫ p, cutoffWeight B g Λ p * F (cutoffReadout S Λ p) ∂preparationMeasure n μ) /
      (∫ p, cutoffWeight B g Λ p ∂preparationMeasure n μ))
      atTop (𝓝 ((∫ p, fullWeight B g p * F (fixedReadout S p) ∂preparationMeasure n μ) /
        partition B μ g)) := by
  have hnorm (Λ : ℝ) (p : Preparation n) : ‖cutoffWeight B g Λ p‖ ≤ 1 := by
    have hh := cutoffWeight_range B hg Λ p
    simpa only [Real.norm_of_nonneg hh.1] using hh.2
  have hf (p : Preparation n) : ‖F (fixedReadout S p)‖ ≤ b p := by
    obtain ⟨Λ, hΛ⟩ := (cutoffReadout_eventually_eq S).exists
    simpa only [hΛ] using hF Λ p
  have hFmeas := (hm.comp (fixedReadout_measurable S)).aestronglyMeasurable
    (μ := preparationMeasure n μ)
  have hwmeas := fullWeight_aestronglyMeasurable hn B μ hμ hg
  have htarget_norm (p : Preparation n) : ‖fullWeight B g p‖ ≤ 1 := by
    have hh := fullWeight_range B hg p
    simpa only [Real.norm_of_nonneg hh.1] using hh.2
  have htarget : Integrable
      (fun p => fullWeight B g p * F (fixedReadout S p)) (preparationMeasure n μ) := by
    refine hb.mono' (hwmeas.mul hFmeas) (Eventually.of_forall fun p => ?_)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (htarget_norm p)).trans (hf p)
  have hw := ae_weight_limit hn B μ hμ hg
  have hWm : ∀ᶠ Λ : ℝ in atTop,
      AEStronglyMeasurable (cutoffWeight B g Λ) (preparationMeasure n μ) :=
    Eventually.of_forall fun Λ => (cutoffWeight_measurable B g Λ).aestronglyMeasurable
  have hz := (partition_pos_le hn B μ hμ hpos hg).1.ne'
  have hden := tendsto_integral_filter_of_dominated_convergence
    (μ := preparationMeasure n μ) (fun _ => (1 : ℝ)) hWm
    (Eventually.of_forall fun Λ => Eventually.of_forall (hnorm Λ)) (integrable_const 1) hw
  have hnum := tendsto_integral_filter_of_dominated_convergence
    (μ := preparationMeasure n μ) (f := fun p => fullWeight B g p * F (fixedReadout S p)) b
    (Eventually.of_forall fun Λ => ((cutoffWeight_measurable B g Λ).mul
      (hm.comp (cutoffReadout_measurable S Λ))).aestronglyMeasurable)
    (Eventually.of_forall fun Λ => Eventually.of_forall fun p => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hnorm Λ p)).trans (hF Λ p)) hb (by
        filter_upwards [hw] with p hp
        have he : (fun Λ : ℝ => F (cutoffReadout S Λ p)) =ᶠ[atTop] (fun _ => F (fixedReadout S p)) :=
          (cutoffReadout_eventually_eq S).mono fun Λ h => congrArg F (congrFun h p)
        exact hp.mul (tendsto_const_nhds.congr' he.symm))
  exact ⟨htarget, hnum.div hden hz⟩

theorem bounded_finite_observable_limit {n : ℕ} (hn : 0 < n) (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ)
    (hpos : μ (Set.Ioi 0) ≠ 0) {g : ℝ} (hg : 0 ≤ g) (S : Finset (ModeSlot n))
    (F : (S → ℝ) → ℝ) (hm : Measurable F) {C : ℝ} (hF : ∀ x, ‖F x‖ ≤ C) :
    Tendsto (fun Λ : ℝ =>
      (∫ p, cutoffWeight B g Λ p * F (cutoffReadout S Λ p) ∂preparationMeasure n μ) /
      (∫ p, cutoffWeight B g Λ p ∂preparationMeasure n μ))
      atTop (𝓝 ((∫ p, fullWeight B g p * F (fixedReadout S p) ∂preparationMeasure n μ) /
        partition B μ g)) :=
  (normalized_observable_limit hn B μ hμ hpos hg S F hm (fun _ => C) (integrable_const C)
    (fun _ _ => hF _)).2

def monomial {n : ℕ} {S : Finset (ModeSlot n)} (powers : S → ℕ) (u : S → ℝ) : ℝ :=
  ∏ i, u i ^ powers i

private def varianceEnvelope {n : ℕ} (i : ModeSlot n) : ℝ :=
  sqrt (2 * (latticeFrequency i.1 ^ 2)⁻¹)

private theorem norm_cutoffReadout_le {n : ℕ} (S : Finset (ModeSlot n))
    (Λ : ℝ) (p : Preparation n) (i : S) :
    ‖cutoffReadout S Λ p i‖ ≤ varianceEnvelope i.1 * |p.2 i.1| := by
  unfold cutoffReadout
  split
  · unfold depthRescale varianceEnvelope
    rw [norm_mul, Real.norm_of_nonneg (sqrt_nonneg _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (sqrt_le_sqrt (mul_le_mul_of_nonneg_left (mode_covariance_le_boundary _ _) zero_le_two))
      (abs_nonneg _)
  · simp only [norm_zero]
    exact mul_nonneg (sqrt_nonneg _) (abs_nonneg _)

private theorem absoluteBasePower_integrable (q : ℕ) :
    Integrable (fun x : ℝ => |x| ^ q) sourceGaussianBase := by
  have h := sourceGaussian_power_integrable (1/2 : ℝ) q
  have he : sourceGaussian (1/2 : ℝ) = sourceGaussianBase := by
    unfold sourceGaussian
    norm_num
  simpa only [he, norm_pow, Real.norm_eq_abs] using h.norm

def monomialEnvelope {n : ℕ} {S : Finset (ModeSlot n)} (powers : S → ℕ) (X : ModeSlot n → ℝ) : ℝ :=
  ∏ i : S, (varianceEnvelope i.1 * |X i.1|) ^ powers i

private theorem monomialEnvelope_integrable {n : ℕ} (S : Finset (ModeSlot n))
    (powers : S → ℕ) : Integrable (monomialEnvelope powers) (commonGaussian n) := by
  have hp : MeasurePreserving S.restrict (commonGaussian n)
      (Measure.pi (fun _ : S => sourceGaussianBase)) :=
    ⟨Finset.measurable_restrict _, Measure.infinitePi_map_restrict _⟩
  let f (i : S) (x : ℝ) : ℝ := (varianceEnvelope i.1 * |x|)^powers i
  have hf (i : S) : Integrable (f i) sourceGaussianBase := by
    unfold f
    rw [show (fun x : ℝ => (varianceEnvelope i.1 * |x|)^powers i) =
        (fun x : ℝ => (varianceEnvelope i.1)^powers i * |x|^powers i) by
      funext x; rw [mul_pow]]
    exact (absoluteBasePower_integrable (powers i)).const_mul _
  have h := hp.integrable_comp_of_integrable (Integrable.fintype_prod hf)
  simpa only [monomialEnvelope, Function.comp_def, Finset.restrict, f] using h

/-- Every polynomial monomial of fixed elementary Fourier coordinates has
a common integrable envelope, with the exact Gaussian covariance bound. -/
theorem normalized_monomial_limit {n : ℕ} (hn : 0 < n) (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ)
    (hpos : μ (Set.Ioi 0) ≠ 0) {g : ℝ} (hg : 0 ≤ g) (S : Finset (ModeSlot n))
    (powers : S → ℕ) :
    Integrable (fun p => fullWeight B g p * monomial powers (fixedReadout S p))
      (preparationMeasure n μ) ∧
    Tendsto (fun Λ : ℝ =>
      (∫ p, cutoffWeight B g Λ p * monomial powers (cutoffReadout S Λ p)
        ∂preparationMeasure n μ) /
      (∫ p, cutoffWeight B g Λ p ∂preparationMeasure n μ))
      atTop (𝓝 ((∫ p, fullWeight B g p * monomial powers (fixedReadout S p)
        ∂preparationMeasure n μ) / partition B μ g)) := by
  have hm : Measurable (monomial powers) := by unfold monomial; fun_prop
  have hb : Integrable (fun p : Preparation n => monomialEnvelope powers p.2)
      (preparationMeasure n μ) := (monomialEnvelope_integrable S powers).comp_snd μ
  refine normalized_observable_limit hn B μ hμ hpos hg S (monomial powers) hm
    (fun p => monomialEnvelope powers p.2) hb (fun Λ p => ?_)
  unfold monomial monomialEnvelope
  rw [norm_prod]
  simp_rw [norm_pow]
  exact Finset.prod_le_prod (fun _ _ => by positivity)
    (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (norm_cutoffReadout_le S Λ p i) _)

end UV.ExtendCurvatureMoments
