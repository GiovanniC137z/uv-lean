import UV.ContinueNormalHolonomyBridge
import UV.ContinueNormalHolonomyProperTime

/-! The radial expectation and its excursion envelope under a positive
bridge law. The continuum heat-kernel identification and the bridge
supremum law are explicit inputs. -/

noncomputable section

open Real Set Filter MeasureTheory
open scoped Topology

namespace UV.ContinueNormalHolonomy

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Relative radial bridge integrand averaged over the bridge law. -/
def quarticRelativeBridgeExpectation (μ : Measure Ω)
    (B : Ω → ℝ → ℝ) (a t x : ℝ) : ℝ :=
  ∫ ω, quarticRelativeBridgeWeight a t x (B ω) ∂μ

theorem quarticRelativeBridgeExpectation_tendsto (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Ω → ℝ → ℝ) (a : ℝ) {x : ℝ} (hx : 0 < x)
    (hpaths : ∀ᵐ ω ∂μ, Measurable (B ω) ∧ ∃ K, ∀ u ∈ Icc (0 : ℝ) 1, |B ω u| ≤ K)
    (hm : ∀ᶠ t : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (fun ω => quarticRelativeBridgeWeight a t x (B ω)) μ) :
    Tendsto (fun t => quarticRelativeBridgeExpectation μ B a t x) (𝓝[>] 0)
      (𝓝 (relativeNormalTheta (x ^ (8 : ℕ))⁻¹ a)) := by
  obtain ⟨C, hC, hb⟩ := relativeNormalTheta_bounded
  have hdom : ∃ C, ∀ᶠ t : ℝ in 𝓝[>] 0,
      ∀ᵐ ω ∂μ, ‖quarticRelativeBridgeWeight a t x (B ω)‖ ≤ C := by
    refine ⟨C, ?_⟩
    have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
    filter_upwards [hpos] with t ht
    exact ae_of_all _ fun ω => by
      obtain ⟨hn, hu⟩ := quarticRelativeBridgeWeight_bounded hC hb a ht.le x (B ω)
      exact (Real.norm_of_nonneg hn).trans_le hu
  have hlim : ∀ᵐ ω ∂μ,
      Tendsto (fun t => quarticRelativeBridgeWeight a t x (B ω)) (𝓝[>] 0)
        (𝓝 (relativeNormalTheta (x ^ (8 : ℕ))⁻¹ a)) := by
    filter_upwards [hpaths] with ω hω
    obtain ⟨hm', K, hK⟩ := hω
    exact quarticRelativeBridgeWeight_tendsto hx (B ω) hm' hK a
  have h := tendsto_integral_filter_of_norm_le_const hm hdom hlim
  simpa [quarticRelativeBridgeExpectation] using h

/-- A sub-Gaussian supremum tail gives the two terms in the radial
domination. The cut-off path integrand is zero when either boundary kills it. -/
theorem quarticRelativeBridgeExpectation_envelope (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Ω → ℝ → ℝ) (M : Ω → ℝ) (hM : Measurable M)
    (hpaths : ∀ᵐ ω ∂μ, ∀ u ∈ Icc (0 : ℝ) 1, |B ω u| ≤ M ω)
    {A c : ℝ}
    (htail : ∀ r : ℝ, 0 ≤ r → μ.real {ω | r < M ω} ≤ A * Real.exp (-(c * r ^ 2)))
    (hm : ∀ (a t x : ℝ), AEStronglyMeasurable (fun ω => quarticRelativeBridgeWeight a t x (B ω)) μ) :
    ∃ Cg Cs : ℝ, 0 ≤ Cg ∧ 0 ≤ Cs ∧
      ∀ (a t x : ℝ), 0 < t → t ≤ 1 →
        0 ≤ quarticRelativeBridgeExpectation μ B a t x ∧
        quarticRelativeBridgeExpectation μ B a t x ≤ Cg ∧
        (2 ≤ x → quarticRelativeBridgeExpectation μ B a t x ≤
          Cs * Real.exp (-(Real.pi ^ 2 * (x / 2) ^ (8 : ℕ) / 4)) +
          Cg * A * Real.exp (-(c * (x / 2) ^ (2 : ℕ)))) := by
  obtain ⟨Cg, hCg, hg⟩ := relativeNormalTheta_bounded
  obtain ⟨Cs, hCs, hs⟩ := relativeNormalTheta_small_width
  refine ⟨Cg, Cs, hCg, hCs, ?_⟩
  intro a t x ht ht1
  let F (ω : Ω) := quarticRelativeBridgeWeight a t x (B ω)
  have hb (ω : Ω) : 0 ≤ F ω ∧ F ω ≤ Cg :=
    quarticRelativeBridgeWeight_bounded hCg hg a ht.le x (B ω)
  have hI : Integrable F μ := (integrable_const Cg).mono' (hm a t x)
    (ae_of_all _ fun ω => by simpa only [Real.norm_of_nonneg (hb ω).1] using (hb ω).2)
  have hIg : (∫ ω, F ω ∂μ) ≤ Cg := by
    calc
      _ ≤ ∫ _ : Ω, Cg ∂μ := integral_mono hI (integrable_const _) (fun ω => (hb ω).2)
      _ = _ := by simp
  refine ⟨integral_nonneg (fun ω => (hb ω).1), hIg, ?_⟩
  intro hx
  let D := {ω | x / 2 < M ω}
  let E := Cs * Real.exp (-(Real.pi ^ 2 * (x / 2) ^ (8 : ℕ) / 4))
  have hD : MeasurableSet D := hM measurableSet_Ioi
  have hE : 0 ≤ E := by positivity
  have hmajor : ∀ᵐ ω ∂μ, F ω ≤ E + D.indicator (fun _ => Cg) ω := by
    filter_upwards [hpaths] with ω hω
    by_cases hbad : ω ∈ D
    · rw [indicator_of_mem hbad]
      exact (hb ω).2.trans (le_add_of_nonneg_left hE)
    · rw [indicator_of_notMem hbad, add_zero]
      apply quarticRelativeBridgeWeight_confined hCs hs a ht.le hx (B ω)
      intro u hu
      have hMω : M ω ≤ x / 2 := le_of_not_gt hbad
      have hpow : t ^ (3 / 8 : ℝ) ≤ 1 := by
        simpa only [Real.one_rpow] using Real.rpow_le_rpow ht.le ht1 (by norm_num : 0 ≤ (3 / 8 : ℝ))
      have hh : |t ^ (3 / 8 : ℝ) * B ω u| ≤ x / 2 := by
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _)]
        exact (mul_le_of_le_one_left (abs_nonneg _) hpow).trans ((hω u hu).trans hMω)
      have hl := (abs_le.mp hh).1
      unfold quarticBridgeRescaled
      linarith
  have hmajor_int : Integrable (fun ω => E + D.indicator (fun _ => Cg) ω) μ :=
    (integrable_const E).add ((integrable_const Cg).indicator hD)
  calc
    _ ≤ ∫ ω, E + D.indicator (fun _ => Cg) ω ∂μ := integral_mono_ae hI hmajor_int hmajor
    _ = E + μ.real D * Cg := by
      rw [integral_add (integrable_const E) ((integrable_const Cg).indicator hD),
        integral_indicator hD, integral_const, integral_const]
      simp [measureReal_def, smul_eq_mul]
    _ ≤ _ := by
      rw [show Cg * A * Real.exp (-(c * (x / 2) ^ (2 : ℕ))) =
        (A * Real.exp (-(c * (x / 2) ^ (2 : ℕ)))) * Cg by ring]
      exact add_le_add_left (mul_le_mul_of_nonneg_right (htail (x / 2) (by linarith)) hCg) _

/-- The exact (t^{3/8}) relative-trace asymptote from a radial
Feynman–Kac representation and a sub-Gaussian bridge supremum bound. -/
theorem quarticRelativeTrace_of_bridge_law (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Ω → ℝ → ℝ) (M : Ω → ℝ) (hM : Measurable M)
    (hpaths : ∀ᵐ ω ∂μ, Measurable (B ω) ∧ ∀ u ∈ Icc (0 : ℝ) 1, |B ω u| ≤ M ω)
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c)
    (htail : ∀ r : ℝ, 0 ≤ r → μ.real {ω | r < M ω} ≤ A * Real.exp (-(c * r ^ 2)))
    (hm : ∀ (a t x : ℝ), AEStronglyMeasurable (fun ω => quarticRelativeBridgeWeight a t x (B ω)) μ)
    (a : ℝ) (D : ℝ → ℝ)
    (hxmeas : ∀ᶠ t : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (quarticRelativeBridgeExpectation μ B a t)
        ((volume : Measure ℝ).restrict (Ioi 0)))
    (hrep : ∀ᶠ t : ℝ in 𝓝[>] 0, t ^ (3 / 8 : ℝ) * D t =
      (Real.sqrt (4 * Real.pi))⁻¹ * ∫ x in Ioi 0, quarticRelativeBridgeExpectation μ B a t x) :
    Tendsto (fun t : ℝ => t ^ (3 / 8 : ℝ) * D t) (𝓝[>] 0)
      (𝓝 (quarticHolonomyConstant a)) := by
  obtain ⟨Cg, Cs, hCg, hCs, hdom⟩ := quarticRelativeBridgeExpectation_envelope μ B M hM
    (hpaths.mono fun _ h => h.2) htail hm
  let G (x : ℝ) := Cg * Real.exp 4 * Real.exp (-(1 : ℝ) * x ^ 2) +
    Cs * Real.exp (-(Real.pi ^ 2 / 1024) * x ^ 2) +
    (Cg * A) * Real.exp (-(c / 4) * x ^ 2)
  have hi : Integrable G :=
    (((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul _).add
      ((integrable_exp_neg_mul_sq (by positivity : 0 < Real.pi ^ 2 / 1024)).const_mul _)).add
      ((integrable_exp_neg_mul_sq (by positivity : 0 < c / 4)).const_mul _)
  refine quarticRelativeTrace_limit_of_radial_profile hrep hxmeas ?_ hi.integrableOn ?_
  · have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
    have hone : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
    filter_upwards [hpos, hone] with t ht ht1
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    obtain ⟨h0, hg, hs⟩ := hdom a t x ht ht1.le
    rw [Real.norm_of_nonneg h0]
    by_cases hx2 : 2 ≤ x
    · apply (hs hx2).trans
      have hp : x ^ (2 : ℕ) ≤ x ^ (8 : ℕ) :=
        pow_le_pow_right₀ (by linarith) (by norm_num)
      have he : Real.exp (-(Real.pi ^ 2 * (x / 2) ^ (8 : ℕ) / 4)) ≤
          Real.exp (-(Real.pi ^ 2 / 1024) * x ^ (2 : ℕ)) := by
        apply Real.exp_le_exp.mpr
        rw [show -(Real.pi ^ 2 * (x / 2) ^ (8 : ℕ) / 4) =
          -(Real.pi ^ 2 / 1024) * x ^ (8 : ℕ) by ring]
        exact mul_le_mul_of_nonpos_left hp (neg_nonpos.mpr (by positivity))
      have hscalar : -(c * (x / 2) ^ (2 : ℕ)) = -(c / 4) * x ^ (2 : ℕ) := by ring
      rw [hscalar]
      unfold G
      linarith [mul_le_mul_of_nonneg_left he hCs,
        show 0 ≤ Cg * Real.exp 4 * Real.exp (-(1 : ℝ) * x ^ 2) by positivity]
    · have hxs : x ^ (2 : ℕ) ≤ 4 := by
        have hx0 : 0 < x := hx
        nlinarith
      have he : 1 ≤ Real.exp 4 * Real.exp (-(1 : ℝ) * x ^ 2) := by
        rw [← Real.exp_add, Real.one_le_exp_iff]
        linarith
      apply hg.trans
      unfold G
      have hbig := mul_le_mul_of_nonneg_left he hCg
      rw [mul_one, ← mul_assoc] at hbig
      linarith [show 0 ≤ Cs * Real.exp (-(Real.pi ^ 2 / 1024) * x ^ 2) by positivity,
        show 0 ≤ (Cg * A) * Real.exp (-(c / 4) * x ^ 2) by positivity]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    apply quarticRelativeBridgeExpectation_tendsto μ B a hx _ (Eventually.of_forall fun t => hm a t x)
    exact hpaths.mono fun ω h => ⟨h.1, M ω, h.2⟩

end UV.ContinueNormalHolonomy
