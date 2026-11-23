import UV.ResumeStableRemainder
import UV.ResumeConePole

/-! The stable-half single-line discontinuity on a test that can meet
the cone tip. Both sheets, the sine term and the shell delta are tested
in the original intrinsic four-momentum measure. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology

theorem shellSquare_continuous : Continuous (fun q : ℝ × Spatial => shellSquare q.1 q.2) := by
  unfold shellSquare
  fun_prop

/-- The null cone is a null set for the four-dimensional bulk measure,
even though it supports the separate shell distribution. -/
theorem massless_shell_nonzero_ae : ∀ᵐ q : ℝ × Spatial ∂volume, shellSquare q.1 q.2 ≠ 0 := by
  have hm : MeasurableSet {q : ℝ × Spatial | shellSquare q.1 q.2 ≠ 0} :=
    (measurableSet_eq_fun shellSquare_continuous.measurable measurable_const).compl
  change ∀ᵐ q ∂((volume : Measure ℝ).prod (volume : Measure Spatial)), shellSquare q.1 q.2 ≠ 0
  rw [Measure.ae_prod_iff_ae_ae hm, Measure.ae_ae_comm hm]
  refine Eventually.of_forall fun p => ?_
  have hp : ∀ᵐ t : ℝ ∂volume, t ≠ ‖p‖ := by rw [ae_iff]; simp
  have hn : ∀ᵐ t : ℝ ∂volume, t ≠ -‖p‖ := by rw [ae_iff]; simp
  filter_upwards [hp, hn] with t ht ht'
  intro h
  have he : t ^ 2 = ‖p‖ ^ 2 := sub_eq_zero.mp h
  exact (eq_or_eq_neg_of_sq_eq_sq t ‖p‖ he).elim ht ht'

/-- The regular timelike sine weight in the massless discontinuity. -/
def masslessStableSine (a : ℝ) (q : ℝ × Spatial) : ℝ :=
  if 0 < shellSquare q.1 q.2 then
    Real.sin (a * Real.sqrt (shellSquare q.1 q.2)) / shellSquare q.1 q.2
  else 0

theorem masslessStableSine_measurable (a : ℝ) : Measurable (masslessStableSine a) := by
  unfold masslessStableSine
  apply Measurable.ite (measurableSet_lt measurable_const shellSquare_continuous.measurable)
  · exact ((Real.continuous_sin.comp
      (continuous_const.mul (Real.continuous_sqrt.comp shellSquare_continuous))).measurable).div
      shellSquare_continuous.measurable
  · exact measurable_const

theorem masslessStableSine_norm_le {a : ℝ} (ha : 0 ≤ a) (q : ℝ × Spatial) :
    ‖masslessStableSine a q‖ ≤ a * inverseRootAbs (shellSquare q.1 q.2) := by
  let w := shellSquare q.1 q.2
  by_cases hw : 0 < w
  · have hr : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw
    unfold masslessStableSine
    rw [if_pos hw, Real.norm_eq_abs, abs_div, abs_of_pos hw]
    have hs := Real.abs_sin_le_abs (x := a * Real.sqrt w)
    rw [abs_of_nonneg (mul_nonneg ha hr.le)] at hs
    calc
      _ ≤ (a * Real.sqrt w) / w := div_le_div_of_nonneg_right hs hw.le
      _ = a * inverseRootAbs w := by
        rw [inverseRootAbs, abs_of_pos hw]
        field_simp [hr.ne', hw.ne']
        linear_combination a * Real.sq_sqrt hw.le
  · unfold masslessStableSine
    rw [if_neg hw, norm_zero]
    exact mul_nonneg ha (inverseRootAbs_nonneg _)

theorem integrableOn_massless_stable_sine_box {R a : ℝ} (hR : 0 < R) (ha : 0 ≤ a) :
    IntegrableOn (masslessStableSine a) (Icc (-R) R ×ˢ Metric.closedBall (0 : Spatial) R) := by
  change IntegrableOn _ _ ((volume : Measure ℝ).prod (volume : Measure Spatial))
  exact ((integrableOn_inverse_root_shell_box hR).const_mul a).mono'
    (masslessStableSine_measurable a).aestronglyMeasurable
    (Eventually.of_forall (masslessStableSine_norm_le ha))

theorem exists_cone_test_box {f : ℝ × Spatial → ℝ} (hf : HasCompactSupport f) :
    ∃ R > 0, ∀ q, q ∉ Icc (-R) R ×ˢ Metric.closedBall (0 : Spatial) R → f q = 0 := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ × Spatial)).mp hf.isBounded
  let R := max 1 r
  refine ⟨R, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro q hq
  by_contra H
  have hb : ‖q‖ ≤ r := by
    simpa using hr (subset_tsupport f (show q ∈ Function.support f from H))
  have hn : ‖q‖ ≤ R := hb.trans (le_max_right _ _)
  change max ‖q.1‖ ‖q.2‖ ≤ R at hn
  apply hq
  exact ⟨abs_le.mp ((le_max_left _ _).trans hn),
    by simpa using (le_max_right ‖q.1‖ ‖q.2‖).trans hn⟩

variable {E : Type*} [NormedAddCommGroup E]

theorem Plane.massless_stable_regular_test_limit (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    {a : ℝ} (ha : 0 ≤ a) {f : ℝ × Spatial → ℝ}
    (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun h : ℝ => ∫ q : ℝ × Spatial,
      (diamond.stableHalfRegular εPos a (shellSquare q.1 q.2) h -
        diamond.stableHalfRegular εNeg a (shellSquare q.1 q.2) h) * (f q : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ q : ℝ × Spatial,
        (2 * Complex.I * (masslessStableSine a q : ℂ)) * (f q : ℂ))) := by
  obtain ⟨R, hR, hzero⟩ := exists_cone_test_box hs
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hs
  let S := Icc (-R) R ×ˢ Metric.closedBall (0 : Spatial) R
  let μ := (volume : Measure (ℝ × Spatial)).restrict S
  let F (h : ℝ) (q : ℝ × Spatial) :=
    (diamond.stableHalfRegular εPos a (shellSquare q.1 q.2) h -
      diamond.stableHalfRegular εNeg a (shellSquare q.1 q.2) h) * (f q : ℂ)
  let G (q : ℝ × Spatial) :=
    (2 * Complex.I * (masslessStableSine a q : ℂ)) * (f q : ℂ)
  have hei (g : ℝ × Spatial → ℂ) (hg : ∀ q ∉ S, g q = 0) :
      (∫ q, g q ∂μ) = ∫ q, g q := setIntegral_eq_integral_of_forall_compl_eq_zero hg
  have hbound : Integrable (fun q : ℝ × Spatial =>
      (2 * a * C) * inverseRootAbs (shellSquare q.1 q.2)) μ :=
    (integrableOn_inverse_root_shell_box hR).const_mul _
  have hne : ∀ᵐ q ∂μ, shellSquare q.1 q.2 ≠ 0 :=
    (ae_mono Measure.restrict_le_self) massless_shell_nonzero_ae
  have h₀ := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
    (μ := μ) (F := F) (f := G) _ ?_ ?_ hbound ?_
  · rw [hei G (fun q hq => by simp [G, hzero q hq])] at h₀
    refine h₀.congr' (Eventually.of_forall fun h =>
      hei (F h) (fun q hq => by simp [F, hzero q hq]))
  · exact Eventually.of_forall fun h =>
      ((((diamond.stable_half_regular_measurable εPos a h).comp shellSquare_continuous.measurable).sub
        ((diamond.stable_half_regular_measurable εNeg a h).comp shellSquare_continuous.measurable)).mul
        (Complex.continuous_ofReal.comp hf).measurable).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with h hh
    filter_upwards [hne] with q hq
    have hhp : 0 < h := hh
    have h₁ := diamond.stable_half_regular_norm_bound εPos ha hq hhp
    have h₂ := diamond.stable_half_regular_norm_bound εNeg ha hq hhp
    unfold F
    rw [norm_mul, Complex.norm_real]
    calc
      _ ≤ (a * inverseRootAbs (shellSquare q.1 q.2) +
          a * inverseRootAbs (shellSquare q.1 q.2)) * ‖f q‖ :=
        mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add h₁ h₂)) (norm_nonneg _)
      _ ≤ _ := by
        have hn := inverseRootAbs_nonneg (shellSquare q.1 q.2)
        have hh := mul_le_mul_of_nonneg_left (hC q) (mul_nonneg ha hn)
        nlinarith
  · filter_upwards [hne] with q hq
    have ht := diamond.stable_half_regular_jump_limit εPos εNeg hPos hNeg a hq
    have he :
        (if 0 < shellSquare q.1 q.2 then 2 * Complex.I *
          ((Real.sin (a * Real.sqrt (shellSquare q.1 q.2)) / shellSquare q.1 q.2 : ℝ) : ℂ) else 0) =
        2 * Complex.I * (masslessStableSine a q : ℂ) := by
      by_cases hw : 0 < shellSquare q.1 q.2 <;> simp [masslessStableSine, hw]
    rw [he] at ht
    exact ht.mul_const (f q : ℂ)

/-- The actual single-line kernel coefficient on the massless sheet. -/
def Plane.masslessStablePairing (diamond : Plane E) (ε : Evolution) (a : ℝ)
    (f : ℝ × Spatial → ℝ) (h : ℝ) : ℂ :=
  if hh : 0 < h then
    ∫ q : ℝ × Spatial, (diamond.stableHalfCoefficient ε a (shellSquare q.1 q.2) h *
      diamond.poleCoefficient ε ⟨h, hh⟩ (shellSquare q.1 q.2)) * (f q : ℂ)
  else 0

/-- The massless single-line jump across the full cone, including its
tip, for compact continuous tests. The shell delta has no cut selector. -/
theorem Plane.massless_stable_jump (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    {a : ℝ} (ha : 0 ≤ a) {f : ℝ × Spatial → ℝ}
    (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun h => diamond.masslessStablePairing εPos a f h -
      diamond.masslessStablePairing εNeg a f h) (𝓝[>] (0 : ℝ))
      (𝓝 ((∫ q : ℝ × Spatial, (2 * Complex.I * (masslessStableSine a q : ℂ)) * (f q : ℂ)) -
        2 * (Real.pi : ℂ) * Complex.I * (fullShellTest 0 f : ℂ))) := by
  have hP := pole_poisson_full_shell_limit 0 hf hs
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] at hP
  have hD := (Complex.continuous_ofReal.continuousAt.tendsto.comp hP).const_mul
    (2 * Complex.I)
  have hR := diamond.massless_stable_regular_test_limit εPos εNeg hPos hNeg ha hf hs
  have H := hR.sub hD
  have hlim : (2 * Complex.I) * ((Real.pi * fullShellTest 0 f : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * (fullShellTest 0 f : ℂ) := by push_cast; ring
  rw [hlim] at H
  refine H.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hp : 0 < h := hh
  let w (q : ℝ × Spatial) := shellSquare q.1 q.2
  let RP (ε : Evolution) (q : ℝ × Spatial) := diamond.poleCoefficient ε ⟨h, hp⟩ (w q)
  let K (ε : Evolution) (q : ℝ × Spatial) := diamond.stableHalfCoefficient ε a (w q) h
  have hRC (ε : Evolution) : Continuous (RP ε) :=
    (diamond.pole_coefficient_continuous ε ⟨h, hp⟩).comp shellSquare_continuous
  have hKC (ε : Evolution) : Continuous (K ε) := by
    have hZ : Continuous (fun q : ℝ × Spatial =>
        -(diamond.shiftedShellCoefficient ε ⟨h, hp⟩ (w q))) :=
      ((Complex.continuous_ofReal.comp shellSquare_continuous).add continuous_const).neg
    have haZ : ∀ q : ℝ × Spatial,
        -(diamond.shiftedShellCoefficient ε ⟨h, hp⟩ (w q)) ∈ Complex.slitPlane := by
      intro q
      apply Complex.mem_slitPlane_iff.mpr
      right
      have he : diamond.eta ε ≠ 0 := by
        intro hZ
        simpa [hZ] using diamond.eta_sq ε
      simpa [Plane.shiftedShellCoefficient] using (neg_ne_zero.mpr (mul_ne_zero he hp.ne'))
    have hSK : Continuous (fun q : ℝ × Spatial =>
        principalSqrt (-(diamond.shiftedShellCoefficient ε ⟨h, hp⟩ (w q)))) :=
      continuous_iff_continuousAt.mpr fun q => by
        have H := ContinuousAt.comp
          (f := fun q : ℝ × Spatial => -(diamond.shiftedShellCoefficient ε ⟨h, hp⟩ (w q)))
          (principalSqrt_hasDerivAt (haZ q)).continuousAt (hZ.continuousAt (x := q))
        exact H
    change Continuous (fun q => diamond.stableHalfCoefficient ε a (w q) h)
    simp only [Plane.stableHalfCoefficient, hp, dite_true, diamond.stable_half_numerator_characters]
    exact Complex.continuous_exp.comp (continuous_const.mul hSK)
  have hfC : Continuous (fun q => (f q : ℂ)) := Complex.continuous_ofReal.comp hf
  have hfS : HasCompactSupport (fun q => (f q : ℂ)) :=
    hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hi {u : ℝ × Spatial → ℂ} (hu : Continuous u) :
      Integrable (fun q => u q * (f q : ℂ)) :=
    (hu.mul hfC).integrable_of_hasCompactSupport (hfS.mul_left (f := u))
  have hA (ε : Evolution) : Integrable (fun q => (K ε q * RP ε q) * (f q : ℂ)) :=
    hi ((hKC ε).mul (hRC ε))
  have hB : Integrable (fun q =>
      ((K εPos q - 1) * RP εPos q - (K εNeg q - 1) * RP εNeg q) * (f q : ℂ)) :=
    hi ((((hKC εPos).sub continuous_const).mul (hRC εPos)).sub
      (((hKC εNeg).sub continuous_const).mul (hRC εNeg)))
  have hC : Integrable (fun q => (2 * Complex.I) *
      ((polePoisson h (w q) * f q : ℝ) : ℂ)) := by
    have hpc := continuous_iff_continuousAt.mpr fun x =>
      (polePoisson_hasDerivAt hp x).continuousAt
    have ht := hi (Complex.continuous_ofReal.comp (hpc.comp shellSquare_continuous))
    simpa only [Complex.ofReal_mul] using ht.const_mul (2 * Complex.I)
  dsimp only [Function.comp_apply]
  rw [← integral_complex_ofReal, ← integral_const_mul]
  simp only [Plane.stableHalfRegular, Plane.masslessStablePairing, dif_pos hp]
  change (∫ q, ((K εPos q - 1) * RP εPos q -
        (K εNeg q - 1) * RP εNeg q) * (f q : ℂ)) -
      (∫ q, (2 * Complex.I) * ((polePoisson h (w q) * f q : ℝ) : ℂ)) =
    (∫ q, (K εPos q * RP εPos q) * (f q : ℂ)) -
      (∫ q, (K εNeg q * RP εNeg q) * (f q : ℂ))
  rw [← integral_sub hB hC, ← integral_sub (hA εPos) (hA εNeg)]
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  have hd : RP εPos q - RP εNeg q = -(2 * Complex.I) *
      (polePoisson h (w q) : ℂ) := by
    dsimp [RP]
    rw [diamond.pole_coefficient_split, diamond.pole_coefficient_split, hPos, hNeg]
    push_cast
    ring
  change (((K εPos q - 1) * RP εPos q - (K εNeg q - 1) * RP εNeg q) * (f q : ℂ)) -
    (2 * Complex.I) * ((polePoisson h (w q) * f q : ℝ) : ℂ) =
    (K εPos q * RP εPos q) * (f q : ℂ) - (K εNeg q * RP εNeg q) * (f q : ℂ)
  push_cast
  linear_combination -(f q : ℂ) * hd

/-- Reconstruction of the entire massless jump in the original
directed quotient, with both shell sheets and the sine term intact. -/
theorem Plane.massless_stable_directed_jump {E : Type*} [NormedAddCommGroup E]
    (diamond : Plane E) (εPos εNeg : Evolution)
    (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    {a : ℝ} (ha : 0 ≤ a) {f : ℝ × Spatial → ℝ}
    (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun h => directed (diamond.masslessStablePairing εPos a f h -
      diamond.masslessStablePairing εNeg a f h)) (𝓝[>] (0 : ℝ))
      (𝓝 (directed ((∫ q : ℝ × Spatial,
        (2 * Complex.I * (masslessStableSine a q : ℂ)) * (f q : ℂ)) -
        2 * (Real.pi : ℂ) * Complex.I * (fullShellTest 0 f : ℂ)))) :=
  directed_shell_readout_continuous.continuousAt.tendsto.comp
    (diamond.massless_stable_jump εPos εNeg hPos hNeg ha hf hs)

end UV.SectorPlane
