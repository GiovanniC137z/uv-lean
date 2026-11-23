import UV.ContinueRelativeVariance

/-! The finite-difference limit after matching the one-loop soft response. -/

noncomputable section

namespace UV.RelativeSoft

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

private theorem softCovariance_bound {μ : Measure Depth} [IsProbabilityMeasure μ]
    {M v d : Depth → ℝ} (hM : MemLp M 2 μ) (hMpos : ∀ r, 0 ≤ M r)
    (hv : MemLp v 2 μ) (hd : MemLp d 2 μ) {a b : ℝ} (ha : 0 ≤ a)
    (hva : ∀ r, |v r| ≤ a * M r) (hdb : ∀ r, |d r| ≤ b * M r) :
    |covariance v d μ| ≤ a * b *
      ((∫ r, M r ^ 2 ∂μ) + (∫ r, M r ∂μ) ^ 2) := by
  let i := ∫ r, M r ∂μ
  let i₂ := ∫ r, M r ^ 2 ∂μ
  have hI : Integrable M μ := hM.integrable one_le_two
  have hI₂ := (memLp_two_iff_integrable_sq hM.aestronglyMeasurable).mp hM
  have hi : 0 ≤ i := integral_nonneg hMpos
  have hvi : |∫ r, v r ∂μ| ≤ a * i := by
    simpa [Real.norm_eq_abs, integral_const_mul, i] using
      (norm_integral_le_of_norm_le (f := v) (hI.const_mul a)
        (Eventually.of_forall (fun r => by simpa [Real.norm_eq_abs] using hva r)))
  have hdi : |∫ r, d r ∂μ| ≤ b * i := by
    simpa [Real.norm_eq_abs, integral_const_mul, i] using
      (norm_integral_le_of_norm_le (f := d) (hI.const_mul b)
        (Eventually.of_forall (fun r => by simpa [Real.norm_eq_abs] using hdb r)))
  have hvdi : |∫ r, (v * d) r ∂μ| ≤ a * b * i₂ := by
    have hab (r : Depth) : ‖(v * d) r‖ ≤ (a * b) * M r ^ 2 := by
      simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
      calc
        |v r| * |d r| ≤ (a * M r) * (b * M r) :=
          mul_le_mul (hva r) (hdb r) (abs_nonneg _) (mul_nonneg ha (hMpos r))
        _ = _ := by ring
    simpa [Real.norm_eq_abs, integral_const_mul, i₂] using
      (norm_integral_le_of_norm_le (hI₂.const_mul (a * b)) (Eventually.of_forall hab))
  rw [covariance_eq_sub hv hd]
  calc
    _ ≤ |∫ r, (v * d) r ∂μ| + |(∫ r, v r ∂μ) * (∫ r, d r ∂μ)| := abs_sub _ _
    _ ≤ a * b * i₂ + (a * i) * (b * i) := by
      rw [abs_mul]
      exact add_le_add hvdi (mul_le_mul hvi hdi (abs_nonneg _) (mul_nonneg ha hi))
    _ = _ := by dsimp only [i, i₂]; ring

private theorem softVariance_of_dominated_convergence {μ : Measure Depth} [IsProbabilityMeasure μ]
    {M k₀ : Depth → ℝ} {k : ℝ → Depth → ℝ} (hM : MemLp M 2 μ) (hk₀ : MemLp k₀ 2 μ)
    (hk : ∀ᶠ R in atTop, MemLp (k R) 2 μ)
    (hbound : ∀ᶠ R in atTop, ∀ᵐ r ∂μ, |k R r| ≤ M r)
    (hlim : ∀ᵐ r ∂μ, Tendsto (fun R => k R r) atTop (𝓝 (k₀ r))) :
    Tendsto (fun R => variance (k R) μ) atTop (𝓝 (variance k₀ μ)) := by
  have hfirst := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop) M
    (hk.mono (fun R hR => hR.aestronglyMeasurable)) (by simpa [Real.norm_eq_abs] using hbound)
    (hM.integrable one_le_two) hlim
  have hsbound : ∀ᶠ R in atTop, ∀ᵐ r ∂μ, ‖k R r ^ 2‖ ≤ M r ^ 2 := by
    filter_upwards [hbound] with R hR
    filter_upwards [hR] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hr 2
  have hsecond := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun R r => k R r ^ 2) (f := fun r => k₀ r ^ 2) (fun r => M r ^ 2)
    (hk.mono fun R hR => ((memLp_two_iff_integrable_sq hR.aestronglyMeasurable).mp hR).aestronglyMeasurable)
    hsbound ((memLp_two_iff_integrable_sq hM.aestronglyMeasurable).mp hM)
    (hlim.mono fun r hr => hr.pow 2)
  rw [variance_eq_sub hk₀]
  apply (hsecond.sub (hfirst.pow 2)).congr'
  exact hk.mono (fun R hR => (variance_eq_sub hR).symm)

/-- Finite-volume data for the stated common-depth fourth coefficient.
The marked-symbol derivatives, vacuum volume bound, and charged Riemann
convergence enter as analytic hypotheses on the coefficients. -/
structure SoftVarianceData (μ : Measure Depth) where
  u : ℝ → Fin 4 → Depth → ℝ
  v : ℝ → Depth → ℝ
  k : ℝ → Depth → ℝ → ℝ
  k₀ : Depth → ℝ
  envelope : Depth → ℝ
  envelope_memLp : MemLp envelope 2 μ
  envelope_nonneg : ∀ r, 0 ≤ envelope r
  u_meas : ∀ R ≥ 1, ∀ j, AEStronglyMeasurable (u R j) μ
  v_meas : ∀ R ≥ 1, AEStronglyMeasurable (v R) μ
  k_meas : ∀ R ≥ 1, ∀ j : Fin 4,
    AEStronglyMeasurable (fun r => k R r (softRayIndex j / R)) μ
  u_bound : ∀ R ≥ 1, ∀ j r, |u R j r| ≤ envelope r
  v_bound : ∀ R ≥ 1, ∀ r, |v R r| ≤ (2 * Real.pi * R) ^ 4 * envelope r
  k_bound : ∀ R ≥ 1, ∀ j : Fin 4, ∀ r, |k R r (softRayIndex j / R)| ≤ envelope r
  k_contDiff : ∀ R ≥ 1, ∀ r, ContDiffOn ℝ 3 (k R r) (Icc 0 4)
  k_deriv_bound : ∀ R ≥ 1, ∀ r, ∀ t ∈ Icc 0 4,
    ‖iteratedDerivWithin 3 (k R r) (Icc 0 4) t‖ ≤ envelope r
  k_tendsto : ∀ j : Fin 4, ∀ᵐ r ∂μ,
    Tendsto (fun R => k R r (softRayIndex j / R)) atTop (𝓝 (k₀ r))

section

variable {μ : Measure Depth} (D : SoftVarianceData μ)

/-- The fourth-order coefficient along the j-th positive longitudinal
momentum with transverse unit polarization. -/
def SoftVarianceData.coefficient (R : ℝ) (j : Fin 4) : ℝ :=
  softFourthCoefficient μ (D.u R j) (D.v R) (fun r => D.k R r (softRayIndex j / R))
    (softRayIndex j / R)

private def SoftVarianceData.sampled (R : ℝ) (j : Fin 4) (r : Depth) : ℝ :=
  D.k R r (softRayIndex j / R)

private def SoftVarianceData.difference (R : ℝ) (r : Depth) : ℝ :=
  ∑ j, softRayWeight j * D.sampled R j r

private theorem SoftVarianceData.sampled_memLp {R : ℝ} (hR : 1 ≤ R) (j : Fin 4) :
    MemLp (D.sampled R j) 2 μ := by
  refine D.envelope_memLp.mono' (D.k_meas R hR j) (Eventually.of_forall fun r => ?_)
  exact by simpa [Real.norm_eq_abs, SoftVarianceData.sampled] using D.k_bound R hR j r

/-- The fixed-depth ray limit is square integrable under the same envelope. -/
theorem SoftVarianceData.k₀_memLp : MemLp D.k₀ 2 μ := by
  have hR : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hMeas : AEStronglyMeasurable D.k₀ μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n : ℕ => D.k_meas ((n : ℝ) + 1) (by linarith [Nat.cast_nonneg (α := ℝ) n]) 0)
      ((D.k_tendsto 0).mono fun _ h => h.comp hR)
  apply D.envelope_memLp.mono' hMeas
  filter_upwards [D.k_tendsto 0] with r hr
  apply le_of_tendsto hr.norm
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  simpa [Real.norm_eq_abs] using D.k_bound R hR 0 r

private theorem SoftVarianceData.v_memLp {R : ℝ} (hR : 1 ≤ R) : MemLp (D.v R) 2 μ := by
  refine (D.envelope_memLp.const_mul ((2 * Real.pi * R) ^ 4)).mono'
    (D.v_meas R hR) (Eventually.of_forall fun r => ?_)
  exact by simpa [Real.norm_eq_abs] using D.v_bound R hR r

/-- At each retained nonzero ray momentum the single-loop, covariance, and
variance depth integrals in the SoftVarianceData.coefficient are finite. -/
theorem SoftVarianceData.retainedDepthIntegrable [IsProbabilityMeasure μ] {R : ℝ} (hR : 1 ≤ R) (j : Fin 4) :
    Integrable (D.u R j) μ ∧
    Integrable (fun r => D.v R r * D.k R r (softRayIndex j / R)) μ ∧
    Integrable (fun r => D.k R r (softRayIndex j / R) ^ 2) μ := by
  have hk := D.sampled_memLp hR j
  refine ⟨?_, (D.v_memLp hR).integrable_mul hk, ?_⟩
  · apply (D.envelope_memLp.integrable one_le_two).mono' (D.u_meas R hR j)
    exact Eventually.of_forall fun r => by simpa [Real.norm_eq_abs] using D.u_bound R hR j r
  · exact (memLp_two_iff_integrable_sq hk.aestronglyMeasurable).mp hk

private theorem SoftVarianceData.difference_memLp {R : ℝ} (hR : 1 ≤ R) : MemLp (D.difference R) 2 μ :=
  memLp_finset_sum _ fun j _ => (D.sampled_memLp hR j).const_mul (softRayWeight j)

private theorem SoftVarianceData.difference_bound {R : ℝ} (hR : 1 ≤ R) (r : Depth) :
    |D.difference R r| ≤ 170 / R ^ 3 * D.envelope r := by
  simpa [SoftVarianceData.difference, SoftVarianceData.sampled, div_mul_eq_mul_div] using
    softRay_third_difference_of_contDiff hR (D.envelope_nonneg r)
      (D.k_contDiff R hR r) (D.k_deriv_bound R hR r)

variable [IsProbabilityMeasure μ]

private theorem SoftVarianceData.tendsto_contracted_expectation :
    Tendsto (fun R : ℝ => R⁻¹ ^ 2 * ∑ j, softRayWeight j * ∫ r, D.u R j r ∂μ) atTop (𝓝 0) := by
  let i := ∫ r, D.envelope r ∂μ
  have h := (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)).pow 2
  have h₀ : Tendsto (fun R : ℝ => R⁻¹ ^ 2 * (8 * i)) atTop (𝓝 0) := by
    simpa using h.mul_const (8 * i)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_ h₀
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    _ ≤ ∑ j, |softRayWeight j * ∫ r, D.u R j r ∂μ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |softRayWeight j| * i := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa [Real.norm_eq_abs, i] using
        norm_integral_le_of_norm_le (f := D.u R j) (D.envelope_memLp.integrable one_le_two)
          (Eventually.of_forall fun r => by simpa [Real.norm_eq_abs] using D.u_bound R hR j r)
    _ = _ := by rw [← Finset.sum_mul, softRay_absolute_weights]

private theorem SoftVarianceData.contracted_covariance {R : ℝ} (hR : 1 ≤ R) :
    (∑ j, softRayWeight j * covariance (D.v R) (D.sampled R j) μ) =
      covariance (D.v R) (D.difference R) μ := by
  unfold SoftVarianceData.difference
  rw [covariance_fun_sum_right (Y := D.v R) (X := fun j r => softRayWeight j * D.sampled R j r)
    (fun j => (D.sampled_memLp hR j).const_mul (softRayWeight j)) (D.v_memLp hR)]
  simp_rw [covariance_mul_right]

private theorem SoftVarianceData.tendsto_contracted_covariance :
    Tendsto (fun R : ℝ => R⁻¹ ^ 2 * ∑ j, softRayWeight j *
      covariance (D.v R) (D.sampled R j) μ) atTop (𝓝 0) := by
  let i := (∫ r, D.envelope r ^ 2 ∂μ) + (∫ r, D.envelope r ∂μ) ^ 2
  let a := (2 * Real.pi) ^ 4 * 170 * i
  have h₀ : Tendsto (fun R : ℝ => a * R⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)).const_mul a
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_ h₀
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have hRp : 0 < R := zero_lt_one.trans_le hR
  rw [D.contracted_covariance hR, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  have hc := softCovariance_bound D.envelope_memLp D.envelope_nonneg
    (D.v_memLp hR) (D.difference_memLp hR) (by positivity)
    (D.v_bound R hR) (D.difference_bound hR)
  calc
    _ ≤ R⁻¹ ^ 2 * ((2 * Real.pi * R) ^ 4 * (170 / R ^ 3) * i) :=
      mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    _ = a * R⁻¹ := by
      dsimp only [a]
      field_simp

private theorem SoftVarianceData.tendsto_contracted_variance :
    Tendsto (fun R : ℝ => ∑ j, softRayWeight j / softRayIndex j ^ 2 *
      variance (D.sampled R j) μ) atTop (𝓝 ((25 : ℝ) / 48 * variance D.k₀ μ)) := by
  rw [← softRay_inverse_square_weights, Finset.sum_mul]
  apply tendsto_finset_sum
  intro j _
  apply Filter.Tendsto.const_mul
  refine softVariance_of_dominated_convergence D.envelope_memLp D.k₀_memLp
    ((eventually_ge_atTop (1 : ℝ)).mono fun _ hR => D.sampled_memLp hR j) ?_ (D.k_tendsto j)
  exact (eventually_ge_atTop (1 : ℝ)).mono fun R hR =>
    Eventually.of_forall (fun r => D.k_bound R hR j r)

/-- Equation eq:spec-uv-soft-variance for the coefficients of the specified
common-depth action, once the marked-kernel and charged-sum estimates hold. -/
theorem SoftVarianceData.commonDepthSoftVariance_limit :
    Tendsto (fun R : ℝ => R⁻¹ ^ 2 * ∑ j, softRayWeight j * D.coefficient R j)
      atTop (𝓝 ((25 : ℝ) / 48 * variance D.k₀ μ)) := by
  have h := (D.tendsto_contracted_expectation.add D.tendsto_contracted_covariance).add
    D.tendsto_contracted_variance
  simp only [add_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have hRp : 0 < R := zero_lt_one.trans_le hR
  simp only [SoftVarianceData.coefficient, softFourthCoefficient]
  simp_rw [mul_add, Finset.sum_add_distrib]
  have hV (j : Fin 4) :
      R⁻¹ ^ 2 * (softRayWeight j * (variance (D.sampled R j) μ / (softRayIndex j / R) ^ 2)) =
        softRayWeight j / softRayIndex j ^ 2 * variance (D.sampled R j) μ := by
    have hj := (softRayIndex_pos j).ne'
    field_simp
  have hSum :
      R⁻¹ ^ 2 * (∑ j, softRayWeight j * (variance (D.sampled R j) μ / (softRayIndex j / R) ^ 2)) =
        ∑ j, softRayWeight j / softRayIndex j ^ 2 * variance (D.sampled R j) μ := by
    rw [Finset.mul_sum]
    simp_rw [hV]
  rw [mul_add, mul_add]
  exact congrArg (fun x =>
    R⁻¹ ^ 2 * (∑ j, softRayWeight j * ∫ r, D.u R j r ∂μ) +
      R⁻¹ ^ 2 * (∑ j, softRayWeight j * covariance (D.v R) (D.sampled R j) μ) + x)
    hSum.symm

/-- The limit remains strictly positive if the mean is tuned to zero. -/
theorem SoftVarianceData.commonDepthSoftVariance_positive
    (hμ : ChargesDepthTip μ) {κ α c : ℝ} (hκ : 0 < κ) (hα : 0 < α) (hc : c < 0)
    (htip : Tendsto (fun r => softDepthWidthSq κ α r * D.k₀ r)
      (comap (fun r : Depth => (r : ℝ)) (𝓝[>] (0 : ℝ))) (𝓝 c)) :
    0 < (25 : ℝ) / 48 * variance D.k₀ μ :=
  mul_pos (by norm_num) (softVariance_pos_of_squared_width hμ D.k₀_memLp hκ hα hc htip)

/-- A positive variance forces fourth-order coefficients of arbitrarily large
absolute size in arbitrarily large volumes. -/
theorem SoftVarianceData.commonDepthSoftVariance_unbounded (hvar : 0 < variance D.k₀ μ) (R₀ C : ℝ) :
    ∃ R ≥ R₀, 1 ≤ R ∧ ∃ j, C < |D.coefficient R j| := by
  let a := (25 : ℝ) / 48 * variance D.k₀ μ
  have ha : 0 < a := mul_pos (by norm_num) hvar
  have hbig := D.commonDepthSoftVariance_limit.eventually_const_lt (show a / 2 < a by linarith)
  have hzero : Tendsto (fun R : ℝ => R⁻¹ ^ 2 * (8 * C)) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)).pow 2
    simpa using h.mul_const (8 * C)
  have hsmall := hzero.eventually_lt_const (show 0 < a / 2 by linarith)
  have he : ∀ᶠ R : ℝ in atTop, R₀ ≤ R ∧ 1 ≤ R ∧
      a / 2 < R⁻¹ ^ 2 * (∑ j, softRayWeight j * D.coefficient R j) ∧
      R⁻¹ ^ 2 * (8 * C) < a / 2 :=
    (eventually_ge_atTop R₀).and ((eventually_ge_atTop 1).and (hbig.and hsmall))
  obtain ⟨R, hR, hRone, hb, hs⟩ := he.exists
  refine ⟨R, hR, hRone, ?_⟩
  by_contra! hC
  have hsum : (∑ j, softRayWeight j * D.coefficient R j) ≤ 8 * C := calc
    _ ≤ |∑ j, softRayWeight j * D.coefficient R j| := le_abs_self _
    _ ≤ ∑ j, |softRayWeight j * D.coefficient R j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |softRayWeight j| * C := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hC j) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, softRay_absolute_weights]
  exact (not_lt_of_ge (mul_le_mul_of_nonneg_left hsum (sq_nonneg R⁻¹))) (hs.trans hb)

end

end UV.RelativeSoft
