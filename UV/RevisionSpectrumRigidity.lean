import UV.StableMomentThreshold

/-! Rigidity of positive sampled Stieltjes covariances. The total mass and
first moment are derived from the samples before using the variance identity. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UV.RevisionSpectrum

private theorem normalizedKernel_tendsto {x : ℕ → ℝ} (hx : ∀ n, 0 < x n)
    (hxTop : Tendsto x atTop atTop) (s : ℝ) (hs : 0 ≤ s) :
    Tendsto (fun n => x n / (x n+s)) atTop (𝓝 1) := by
  have hi := tendsto_inv_atTop_zero.comp hxTop
  have h : Tendsto (fun n => 1+s*(x n)⁻¹) atTop (𝓝 (1:ℝ)) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).add
      (hi.const_mul s))
  have h' := h.inv₀ (by norm_num)
  simp only [inv_one] at h'
  apply h'.congr (fun n => ?_)
  dsimp only
  field_simp [ne_of_gt (hx n), ne_of_gt (add_pos_of_pos_of_nonneg (hx n) hs)]

private theorem normalizedMoment_lintegral {ρ : Measure ℝ} {x : ℕ → ℝ}
    (hx : ∀ n, 0 < x n) (hmono : Monotone x) (hxTop : Tendsto x atTop atTop)
    (hs : ∀ᵐ s ∂ρ, 0 ≤ s) {f : ℝ → ℝ}
    (hf₀ : ∀ᵐ s ∂ρ, 0 ≤ f s)
    (hint : ∀ n, Integrable (fun s => x n/(x n+s)*f s) ρ)
    {r : ℝ}
    (hlim : Tendsto (fun n => ∫ s, x n/(x n+s)*f s ∂ρ) atTop (𝓝 r)) :
    (∫⁻ s, ENNReal.ofReal (f s) ∂ρ) = ENNReal.ofReal r := by
  have hM := lintegral_tendsto_of_tendsto_of_monotone
    (μ := ρ) (F := fun s => ENNReal.ofReal (f s))
    (f := fun n s => ENNReal.ofReal (x n/(x n+s)*f s))
    (fun n => (hint n).aestronglyMeasurable.aemeasurable.ennreal_ofReal) (by
      filter_upwards [hs, hf₀] with s hsp hfp
      intro n m hnm
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ hfp
      rw [div_le_div_iff₀ (add_pos_of_pos_of_nonneg (hx n) hsp)
        (add_pos_of_pos_of_nonneg (hx m) hsp)]
      nlinarith [mul_nonneg (sub_nonneg.mpr (hmono hnm)) hsp]) (by
      filter_upwards [hs] with s hsp
      simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((normalizedKernel_tendsto hx hxTop s hsp).mul_const (f s)))
  apply tendsto_nhds_unique hM
  apply (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim).congr
  intro n
  exact ofReal_integral_eq_lintegral_ofReal (hint n) (by
    filter_upwards [hs, hf₀] with s hsp hfp
    exact mul_nonneg (div_nonneg (hx _).le (add_nonneg (hx _).le hsp)) hfp)

/-- A positive spectral measure on nonnegative squared energies is forced to
be a unit atom by agreement with the free Stieltjes covariance through the
third inverse power. The hypothesis is imposed only along the sampled
frequencies. No finite-mass or moment assumption is required. -/
theorem sampled_photon_spectral_rigidity (ρ : Measure ℝ) (a : ℝ)
    (ha : 0 ≤ a) (hs : ∀ᵐ s ∂ρ, 0 ≤ s) (x : ℕ → ℝ)
    (hx : ∀ n, 0 < x n) (hmono : Monotone x) (hxTop : Tendsto x atTop atTop)
    (hInt : ∀ n, Integrable (fun s => (x n+s)⁻¹) ρ)
    (herror : Tendsto (fun n => (x n)^3 *
      ((∫ s, (x n+s)⁻¹ ∂ρ) - (x n+a)⁻¹)) atTop (𝓝 0)) :
    ρ = Measure.dirac a := by
  let G := fun n => ∫ s : ℝ, (x n+s)⁻¹ ∂ρ
  let G₀ := fun n => (x n+a)⁻¹
  let err := fun n => x n ^ 3 * (G n - G₀ n)
  have hinv := tendsto_inv_atTop_zero.comp hxTop
  have herror₂ : Tendsto (fun n => x n ^ 2 * (G n-G₀ n)) atTop (𝓝 0) := by
    have h : Tendsto (fun n => (x n)⁻¹ * err n) atTop (𝓝 0) := by
      simpa using hinv.mul herror
    exact h.congr (fun n => by dsimp [err]; field_simp [ne_of_gt (hx n)])
  have herror₁ : Tendsto (fun n => x n * (G n-G₀ n)) atTop (𝓝 0) := by
    have h := hinv.mul herror₂
    simp only [mul_zero] at h
    exact h.congr (fun n => by dsimp only [Function.comp_apply]; field_simp [ne_of_gt (hx n)])
  have hfree₁ : Tendsto (fun n => x n * G₀ n) atTop (𝓝 1) := by
    simpa [G₀, div_eq_mul_inv] using normalizedKernel_tendsto hx hxTop a ha
  have hG₁ : Tendsto (fun n => x n * G n) atTop (𝓝 1) := by
    have h := hfree₁.add herror₁
    simp only [add_zero] at h
    exact h.congr (fun _ => by ring)
  have hmass_lim : Tendsto (fun n => ∫ s, x n/(x n+s)*(1:ℝ) ∂ρ) atTop (𝓝 1) := by
    simpa only [mul_one, div_eq_mul_inv, integral_const_mul, G] using hG₁
  have hmass := normalizedMoment_lintegral hx hmono hxTop hs (f := fun _ => 1)
    (Eventually.of_forall fun _ => zero_le_one)
    (fun n => by simpa only [mul_one, div_eq_mul_inv] using (hInt n).const_mul (x n)) hmass_lim
  have hρ : ρ univ = 1 := by simpa using hmass
  letI : IsFiniteMeasure ρ := ⟨by rw [hρ]; exact ENNReal.one_lt_top⟩
  have hfree₂ : Tendsto (fun n => x n*(1-x n*G₀ n)) atTop (𝓝 a) := by
    have h := hfree₁.const_mul a
    simp only [mul_one] at h
    refine h.congr (fun n => ?_)
    have hpos : 0 < x n+a := add_pos_of_pos_of_nonneg (hx n) ha
    dsimp [G₀]
    field_simp [hpos.ne']
    ring
  have hG₂ : Tendsto (fun n => x n*(1-x n*G n)) atTop (𝓝 a) := by
    have h := hfree₂.sub herror₂
    simp only [sub_zero] at h
    exact h.congr (fun _ => by ring)
  have hmoment₁_int (n : ℕ) : Integrable (fun s => x n/(x n+s)*s) ρ := by
    apply (integrable_const (μ := ρ) (x n)).mono' (by fun_prop)
    filter_upwards [hs] with s hsp
    have hpos : 0 < x n+s := add_pos_of_pos_of_nonneg (hx n) hsp
    rw [Real.norm_of_nonneg (mul_nonneg (div_nonneg (hx n).le hpos.le) hsp),
      div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith [sq_nonneg (x n)]
  have hmoment₁_eq (n : ℕ) : (∫ s, x n/(x n+s)*s ∂ρ) = x n*(1-x n*G n) := by
    calc
      _ = ∫ s, x n - x n ^ 2 * (x n+s)⁻¹ ∂ρ := by
        apply integral_congr_ae
        filter_upwards [hs] with s hsp
        field_simp [ne_of_gt (add_pos_of_pos_of_nonneg (hx n) hsp)]
        ring
      _ = _ := by
        rw [integral_sub (integrable_const _) ((hInt n).const_mul _), integral_const,
          integral_const_mul, Measure.real, hρ, ENNReal.toReal_one, one_smul]
        change x n - x n^2*G n = _
        ring
  have hmoment₁_lim : Tendsto (fun n => ∫ s, x n/(x n+s)*s ∂ρ) atTop (𝓝 a) :=
    hG₂.congr (fun n => (hmoment₁_eq n).symm)
  have hm₁ := normalizedMoment_lintegral hx hmono hxTop hs (f := fun s => s) hs hmoment₁_int hmoment₁_lim
  have hm₁_int : Integrable (fun s : ℝ => s) ρ :=
    (lintegral_ofReal_ne_top_iff_integrable (f := fun s : ℝ => s)
      measurable_id.aestronglyMeasurable hs).mp
      (by rw [hm₁]; exact ENNReal.ofReal_ne_top)
  have hm₁_real : (∫ s, s ∂ρ) = a := by
    rw [integral_eq_lintegral_of_nonneg_ae hs measurable_id.aestronglyMeasurable, hm₁,
      ENNReal.toReal_ofReal ha]
  have hvariance_identity (n : ℕ) :
      (fun s : ℝ => x n/(x n+s)*(s-a)^2) =ᵐ[ρ]
        (fun s => x n*s - x n*(x n+2*a) + (x n*(x n+a)^2)*(x n+s)⁻¹) := by
    filter_upwards [hs] with s hsp
    field_simp [ne_of_gt (add_pos_of_pos_of_nonneg (hx n) hsp)]
    ring
  have hvariance_int (n : ℕ) : Integrable (fun s => x n/(x n+s)*(s-a)^2) ρ :=
    (((hm₁_int.const_mul (x n)).sub (integrable_const _)).add
      ((hInt n).const_mul _)).congr (hvariance_identity n).symm
  have hvariance_eq (n : ℕ) : (∫ s, x n/(x n+s)*(s-a)^2 ∂ρ) =
      x n*(x n+a)^2*(G n-G₀ n) := by
    have first : Integrable (fun s : ℝ => x n*s-x n*(x n+2*a)) ρ :=
      (hm₁_int.const_mul (x n)).sub (integrable_const _)
    have second := (hInt n).const_mul (x n*(x n+a)^2)
    rw [integral_congr_ae (hvariance_identity n), integral_add first second,
      integral_sub (hm₁_int.const_mul _) (integrable_const _), integral_const_mul,
      integral_const_mul, integral_const, Measure.real, hρ, ENNReal.toReal_one, one_smul,
      hm₁_real]
    simp only [integral_const_mul]
    have hpos : 0 < x n+a := add_pos_of_pos_of_nonneg (hx n) ha
    change x n*a - x n*(x n+2*a) + (x n*(x n+a)^2)*G n = _
    dsimp only [G₀]
    field_simp [hpos.ne']
    ring
  have hr : Tendsto (fun n => 1 + a*(x n)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).add
      (hinv.const_mul a)
  have hvariance_lim : Tendsto (fun n => ∫ s, x n/(x n+s)*(s-a)^2 ∂ρ) atTop (𝓝 0) := by
    have h := (hr.pow 2).mul herror
    simp only [one_pow, mul_zero] at h
    apply h.congr (fun n => ?_)
    rw [hvariance_eq]
    change (1+a*(x n)⁻¹)^2 * (x n ^ 3 * (G n-G₀ n)) = _
    field_simp [ne_of_gt (hx n)]
  have hv := normalizedMoment_lintegral hx hmono hxTop hs (f := fun s => (s-a)^2)
    (Eventually.of_forall fun _ => sq_nonneg _) hvariance_int hvariance_lim
  rw [ENNReal.ofReal_zero] at hv
  have hzero := (lintegral_eq_zero_iff' (by fun_prop :
    AEMeasurable (fun s : ℝ => ENNReal.ofReal ((s-a)^2)) ρ)).mp hv
  have hsupport : ∀ᵐ s ∂ρ, s = a := by
    filter_upwards [hzero] with s h
    have hle := ENNReal.ofReal_eq_zero.mp h
    have heq : s-a = 0 := by nlinarith
    linarith
  ext B hB
  rw [Measure.dirac_apply' a hB]
  by_cases h : a ∈ B
  · rw [Set.indicator_of_mem h]
    have heq : B =ᶠ[ae ρ] univ := by
      filter_upwards [hsupport] with s hsa
      rw [hsa]
      apply propext
      change a ∈ B ↔ a ∈ univ
      simpa using h
    rw [measure_congr heq, hρ]
    rfl
  · rw [Set.indicator_of_notMem h]
    have heq : B =ᶠ[ae ρ] (∅ : Set ℝ) := by
      filter_upwards [hsupport] with s hsa
      rw [hsa]
      apply propext
      change a ∈ B ↔ a ∈ (∅ : Set ℝ)
      simpa using h
    rw [measure_congr heq, measure_empty]

end UV.RevisionSpectrum
