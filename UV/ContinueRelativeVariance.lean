import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Calculus.Taylor
import UV.SectorPlaneGaugeData

/-! The common-depth transverse soft coefficient of the fourth-order response. -/

noncomputable section

namespace UV.RelativeSoft

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators RealInnerProductSpace
open UV.SectorPlane

/-- The positive depths of the normalized preparation law in the soft test. -/
abbrev Depth := Set.Ioo (0 : ℝ) 1

/-- The longitudinal spatial unit direction in the Euclidean carrier. -/
def softLongitudinal : ConeUnitDirection :=
  ⟨WithLp.toLp 2 ((0 : ℝ), EuclideanSpace.single (0 : Fin 3) (1 : ℝ)), by simp⟩

/-- The transverse spatial unit polarization in the same carrier. -/
def softTransverse : ConeUnitDirection :=
  ⟨WithLp.toLp 2 ((0 : ℝ), EuclideanSpace.single (1 : Fin 3) (1 : ℝ)), by simp⟩

theorem softTransverse_perpendicular : ⟪softLongitudinal.val, softTransverse.val⟫ = 0 := by
  simp [softLongitudinal, softTransverse, WithLp.prod_inner_apply,
    EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

def softRayMomentum (t : ℝ) : EuclideanPlaneMomentum := t • softLongitudinal.val

theorem softRayMomentum_norm (t : ℝ) : ‖softRayMomentum t‖ = |t| := by
  rw [softRayMomentum, norm_smul, softLongitudinal.property, mul_one, Real.norm_eq_abs]

theorem softRayMomentum_transverse (t : ℝ) : ⟪softRayMomentum t, softTransverse.val⟫ = 0 := by
  rw [softRayMomentum, real_inner_smul_left, softTransverse_perpendicular, mul_zero]

def softRayIndex (j : Fin 4) : ℝ := j.val + 1

def softRayWeight (j : Fin 4) : ℝ :=
  match j.val with
  | 0 => 1
  | 1 => -3
  | 2 => 3
  | _ => -1

private theorem softRayWeight_zero : softRayWeight 0 = 1 := rfl
private theorem softRayWeight_one : softRayWeight 1 = -3 := rfl
private theorem softRayWeight_two : softRayWeight 2 = 3 := rfl
private theorem softRayWeight_three : softRayWeight 3 = -1 := rfl

theorem softRayIndex_pos (j : Fin 4) : 0 < softRayIndex j := by
  unfold softRayIndex
  positivity

theorem softRay_polynomial_jet (a b c x : ℝ) :
    ∑ j, softRayWeight j *
      (a + b * (softRayIndex j * x) + c * (softRayIndex j * x) ^ 2) = 0 := by
  norm_num [Fin.sum_univ_four, softRayWeight_zero, softRayWeight_one, softRayWeight_two,
    softRayWeight_three, softRayIndex]
  ring

theorem softRay_inverse_square_weights :
    ∑ j, softRayWeight j / softRayIndex j ^ 2 = (25 : ℝ) / 48 := by
  norm_num [Fin.sum_univ_four, softRayWeight_zero, softRayWeight_one, softRayWeight_two,
    softRayWeight_three, softRayIndex]

theorem softRay_absolute_cubic_weights :
    ∑ j, |softRayWeight j| * softRayIndex j ^ 3 = (170 : ℝ) := by
  norm_num [Fin.sum_univ_four, softRayWeight_zero, softRayWeight_one, softRayWeight_two,
    softRayWeight_three, softRayIndex]

theorem softRay_absolute_weights : ∑ j, |softRayWeight j| = (8 : ℝ) := by
  norm_num [Fin.sum_univ_four, softRayWeight_zero, softRayWeight_one, softRayWeight_two,
    softRayWeight_three]

/-- The four rays annihilate the quadratic Taylor jet with an explicit cubic remainder. -/
theorem softRay_third_difference_bound {k : Fin 4 → ℝ} {R M a b c : ℝ}
    (h : ∀ j, |k j - (a + b * (softRayIndex j / R) + c * (softRayIndex j / R) ^ 2)| ≤
      M * (softRayIndex j / R) ^ 3) :
    |∑ j, softRayWeight j * k j| ≤ 170 * M / R ^ 3 := by
  let q (j : Fin 4) := a + b * (softRayIndex j / R) + c * (softRayIndex j / R) ^ 2
  have hq : ∑ j, softRayWeight j * q j = 0 := by
    simpa [q, div_eq_mul_inv] using softRay_polynomial_jet a b c R⁻¹
  have hsum : (∑ j, softRayWeight j * k j) =
      ∑ j, softRayWeight j * (k j - q j) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, hq, sub_zero]
  rw [hsum]
  calc
    |∑ j, softRayWeight j * (k j - q j)| ≤
        ∑ j, |softRayWeight j * (k j - q j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |softRayWeight j| * (M * (softRayIndex j / R) ^ 3) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (h j) (abs_nonneg _)
    _ = (∑ j, |softRayWeight j| * softRayIndex j ^ 3) * (M / R ^ 3) := by
      rw [Finset.sum_mul]
      congr 1 with j
      rw [div_pow]
      ring
    _ = 170 * M / R ^ 3 := by rw [softRay_absolute_cubic_weights, mul_div_assoc]

/-- A third derivative bound on the interpolated soft ray gives the cubic
finite-difference estimate at the four nonzero lattice momenta. -/
theorem softRay_third_difference_of_contDiff {k : ℝ → ℝ} {R M : ℝ}
    (hR : 1 ≤ R) (hM : 0 ≤ M)
    (hk : ContDiffOn ℝ 3 k (Icc 0 4))
    (hderiv : ∀ t ∈ Icc 0 4, ‖iteratedDerivWithin 3 k (Icc 0 4) t‖ ≤ M) :
    |∑ j, softRayWeight j * k (softRayIndex j / R)| ≤ 170 * M / R ^ 3 := by
  apply softRay_third_difference_bound (a := k 0)
    (b := iteratedDerivWithin 1 k (Icc 0 4) 0)
    (c := iteratedDerivWithin 2 k (Icc 0 4) 0 / 2)
  intro j
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hj : softRayIndex j ≤ 4 := by
    unfold softRayIndex
    have hh : (j.val : ℝ) < 4 := by exact_mod_cast j.isLt
    have hl : j.val ≤ 3 := by omega
    have hc : (j.val : ℝ) ≤ 3 := by exact_mod_cast hl
    linarith
  have hmem : softRayIndex j / R ∈ Icc (0 : ℝ) 4 := by
    refine ⟨div_nonneg (softRayIndex_pos j).le hRpos.le, (div_le_iff₀ hRpos).mpr ?_⟩
    nlinarith
  have hTaylor := taylor_mean_remainder_bound (n := 2) (a := (0 : ℝ)) (b := 4)
    (by norm_num) (by simpa using hk) hmem (C := M) (by simpa using hderiv)
  norm_num [taylorWithinEval_succ, Real.norm_eq_abs, ← iteratedDerivWithin_one] at hTaylor
  refine (le_trans ?_ (le_trans hTaylor ?_))
  · apply le_of_eq
    congr 1
    ring
  · have ht := mul_nonneg hM (pow_nonneg hmem.1 3)
    linarith

/-- The scalar proper fourth coefficient after inversion, in the convention
`Π = C⁻¹ - G⁻¹` for the transverse unit coordinate. -/
def softFourthCoefficient (μ : Measure Depth) (u v k : Depth → ℝ) (t : ℝ) : ℝ :=
  (∫ r, u r ∂μ) + covariance v k μ + variance k μ / t ^ 2

/-- In the transverse coordinate the massless Maxwell denominator is the
squared length of the actual Euclidean soft momentum. -/
theorem softFourthCoefficient_ray (μ : Measure Depth) (u v k : Depth → ℝ) (t : ℝ) :
    softFourthCoefficient μ u v k t =
      (∫ r, u r ∂μ) + covariance v k μ + variance k μ / ‖softRayMomentum t‖ ^ 2 := by
  rw [softFourthCoefficient, softRayMomentum_norm, sq_abs]

/-- A deterministic depth removes the covariance and variance terms. -/
theorem softFourthCoefficient_dirac (r : Depth) (u v k : Depth → ℝ) (t : ℝ) :
    softFourthCoefficient (Measure.dirac r) u v k t = u r := by
  simp [softFourthCoefficient, covariance]

/-- If the shifted-source fourth coefficient is the given fourth contraction,
the inverse-propagator expansion replaces its raw second moment by the variance. -/
theorem softFourth_from_inverse_coefficients {μ : Measure Depth} [IsProbabilityMeasure μ]
    {u v k : Depth → ℝ} (hk : MemLp k 2 μ) {t : ℝ}
    (ht : t ≠ 0) {g2 g4 : ℝ}
    (hg2 : g2 = (t ^ 2)⁻¹ ^ 2 * (∫ r, k r ∂μ))
    (hg4 : g4 = (t ^ 2)⁻¹ ^ 2 *
      ((∫ r, u r ∂μ) + covariance v k μ + (∫ r, k r ^ 2 ∂μ) / t ^ 2)) :
    g4 / ((t ^ 2)⁻¹ ^ 2) - g2 ^ 2 / ((t ^ 2)⁻¹ ^ 3) =
      softFourthCoefficient μ u v k t := by
  rw [hg2, hg4, softFourthCoefficient, variance_eq_sub hk]
  change _ = (∫ r, u r ∂μ) + covariance v k μ +
    ((∫ r, k r ^ 2 ∂μ) - (∫ r, k r ∂μ) ^ 2) / t ^ 2
  field_simp
  ring

/-- The manuscript's inverse-depth assumption supplies an L² envelope for
each fixed polynomial cost in inverse depth. -/
theorem softEnvelope_memLp_of_inverseMoments {μ : Measure Depth} [IsProbabilityMeasure μ]
    (hμ : ∀ N : ℕ, Integrable (fun r : Depth => ((r : ℝ)⁻¹) ^ N) μ) (N : ℕ) (C : ℝ) :
    MemLp (fun r : Depth => C * (1 + ((r : ℝ)⁻¹) ^ N)) 2 μ := by
  have h := hμ N
  have hN : MemLp (fun r : Depth => ((r : ℝ)⁻¹) ^ N) 2 μ := by
    apply (memLp_two_iff_integrable_sq h.aestronglyMeasurable).mpr
    simp_rw [← pow_mul]
    exact hμ (N * 2)
  exact ((memLp_const (1 : ℝ)).add hN).const_mul C

/-- The normalized preparation law gives positive mass to every positive-depth
interval adjoining zero. -/
def ChargesDepthTip (μ : Measure Depth) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → μ {r | (r : ℝ) < δ} ≠ 0

/-- A coefficient diverging negatively at the depth tip has strictly positive
variance under the normalized common-depth law. -/
theorem softVariance_pos_of_tip {μ : Measure Depth} [IsProbabilityMeasure μ]
    (hμ : ChargesDepthTip μ) {k : Depth → ℝ} (hk : MemLp k 2 μ)
    (htip : ∀ M : ℝ, ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ r : Depth, (r : ℝ) < δ → k r < M) :
    0 < variance k μ := by
  refine (variance_nonneg k μ).lt_of_ne ?_
  intro hzero
  have hezero : evariance k μ = 0 := by
    rw [← ofReal_variance hk, ← hzero, ENNReal.ofReal_zero]
  have hae := (evariance_eq_zero_iff hk.aemeasurable).mp hezero
  obtain ⟨δ, hδ, hδ1, ht⟩ := htip (∫ r, k r ∂μ)
  apply hμ δ hδ hδ1
  refine measure_mono_null (fun r hr => ?_) (ae_iff.mp hae)
  exact (ht r hr).ne

/-- A tip asymptotic measured against the actual positive squared width. -/
theorem softTip_negative_of_scaled_limit {k s : Depth → ℝ} {c : ℝ} (hc : c < 0)
    (hs : ∀ r, 0 < s r)
    (hs₀ : Tendsto s (comap (fun r : Depth => (r : ℝ)) (𝓝[>] (0 : ℝ))) (𝓝 0))
    (hks : Tendsto (fun r => s r * k r)
      (comap (fun r : Depth => (r : ℝ)) (𝓝[>] (0 : ℝ))) (𝓝 c)) :
    ∀ M : ℝ, ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ r : Depth, (r : ℝ) < δ → k r < M := by
  intro M
  let l := comap (fun r : Depth => (r : ℝ)) (𝓝[>] (0 : ℝ))
  have hd : Tendsto (fun r => s r * k r - s r * M) l (𝓝 c) := by
    simpa using hks.sub (hs₀.mul_const M)
  have he : ∀ᶠ r in l, k r < M := by
    filter_upwards [hd.eventually_lt_const hc] with r hr
    exact lt_of_mul_lt_mul_left (sub_neg.mp hr) (hs r).le
  obtain ⟨S, hS, hsub⟩ := mem_comap.mp he
  obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhdsWithin_iff.mp hS
  refine ⟨min ε (1/2), lt_min hε (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro r hr
  apply hsub
  apply hεS
  exact ⟨by simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos r.property.1] using
    hr.trans_le (min_le_left _ _), r.property.1⟩

/-- The squared Gaussian width appearing in the common-depth law. -/
def softDepthWidthSq (κ α : ℝ) (r : Depth) : ℝ := κ * (r : ℝ) ^ α

theorem softDepthWidthSq_pos {κ α : ℝ} (hκ : 0 < κ) (r : Depth) :
    0 < softDepthWidthSq κ α r :=
  mul_pos hκ (Real.rpow_pos_of_pos r.property.1 _)

theorem softDepthWidthSq_tendsto_zero {κ α : ℝ} (hα : 0 < α) :
    Tendsto (softDepthWidthSq κ α)
      (comap (fun r : Depth => (r : ℝ)) (𝓝[>] (0 : ℝ))) (𝓝 0) := by
  have hl : Tendsto (fun r : Depth => (r : ℝ))
      (comap (fun r : Depth => (r : ℝ)) (𝓝[>] (0 : ℝ))) (𝓝 0) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have hc : Tendsto (fun x : ℝ => κ * x ^ α) (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow hα.ne'] using
      ((Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.const_mul κ)
  exact hc.comp hl

theorem softVariance_pos_of_squared_width {μ : Measure Depth} [IsProbabilityMeasure μ]
    (hμ : ChargesDepthTip μ) {k : Depth → ℝ} (hk : MemLp k 2 μ) {κ α c : ℝ}
    (hκ : 0 < κ) (hα : 0 < α) (hc : c < 0)
    (htip : Tendsto (fun r => softDepthWidthSq κ α r * k r)
      (comap (fun r : Depth => (r : ℝ)) (𝓝[>] (0 : ℝ))) (𝓝 c)) :
    0 < variance k μ :=
  softVariance_pos_of_tip hμ hk
    (softTip_negative_of_scaled_limit hc (softDepthWidthSq_pos hκ) (softDepthWidthSq_tendsto_zero hα) htip)

end UV.RelativeSoft
