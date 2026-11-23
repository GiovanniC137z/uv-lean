import UV.ContinueOSGaussianVariance

/-! A jointly measurable modification of the positive-depth Euclidean
point field. The spatial approximation uses the variogram of the actual
massive covariance and the separability of the oriented four-plane. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace UV

private theorem osAe_square_error_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ℕ → Ω → ℝ) (hi : ∀ n, Integrable (fun z => f n z ^ 2) μ)
    (hb : ∀ n, ∫ z, f n z ^ 2 ∂μ ≤ (1/2 : ℝ)^n) :
    ∀ᵐ z ∂μ, Tendsto (fun n => f n z) atTop (𝓝 0) := by
  let g (n : ℕ) (z : Ω) : ℝ≥0 := ⟨f n z ^ 2,sq_nonneg _⟩
  have hcoe (n : ℕ) (z : Ω) : (g n z : ℝ≥0∞) = ENNReal.ofReal (f n z^2) := by
    rw [ENNReal.ofReal,ENNReal.coe_inj]
    ext
    simp [g,Real.toNNReal_of_nonneg (sq_nonneg _)]
  have hme (n : ℕ) : AEMeasurable (fun z => (g n z : ℝ≥0∞)) μ := by
    simp_rw [hcoe]
    exact (hi n).aemeasurable.ennreal_ofReal
  have hl (n : ℕ) : (∫⁻ z, (g n z : ℝ≥0∞) ∂μ) ≤ ((1/2 : ℝ≥0) : ℝ≥0∞)^n := by
    simp_rw [hcoe]
    rw [←ofReal_integral_eq_lintegral_ofReal (hi n) (Eventually.of_forall fun _ => sq_nonneg _)]
    calc
      _ ≤ ENNReal.ofReal ((1/2 : ℝ)^n) := ENNReal.ofReal_le_ofReal (hb n)
      _ = _ := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        congr 1
        exact ENNReal.ofReal_coe_nnreal (p := (1/2 : ℝ≥0))
  have hsum : (∑' n, ((1/2 : ℝ≥0) : ℝ≥0∞)^n) ≠ ∞ := by
    simp only [←ENNReal.coe_pow]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_geometric (by norm_num))
  have htotal : (∫⁻ z, ∑' n, (g n z : ℝ≥0∞) ∂μ) ≠ ∞ := by
    rw [lintegral_tsum hme]
    exact ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hl)
  filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum hme) htotal] with z hz
  have hs : Summable (fun n => (g n z : ℝ)) := ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hz.ne
  have hsq : Tendsto (fun n => f n z ^ 2) atTop (𝓝 0) := hs.tendsto_atTop_zero
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  simpa only [Real.sqrt_sq_eq_abs,Real.sqrt_zero] using hsq.sqrt

/-- The canonical cylinder process admits an everywhere jointly measurable
representative of the transferred point field. Each fixed point agrees
almost surely with the corresponding Gaussian coordinate. -/
theorem osQuarticGaussian_joint_modification {m r : ℝ} (hm : 0 < m) (hr : 0 < r)
    (μ : Measure (OSQuarticSlot → ℝ)) (hμ : IsProjectiveLimit (α := fun _ => ℝ) μ (osGaussianFamily hm hr)) :
    ∃ Z : OSFourSpace → (OSQuarticSlot → ℝ) → ℝ,
      Measurable (fun p : OSFourSpace × (OSQuarticSlot → ℝ) => Z p.1 p.2) ∧
      ∀ x, Z x =ᵐ[μ] (fun z => z (.inr x)) := by
  classical
  let C := stableCoordinateCovariance (2*r) m
  let V (u : OSFourSpace) := 2*C 0 - C u - C (-u)
  have hc : Continuous C := stableCoordinateCovariance_continuous (by positivity) hm
  have hv : Continuous V := ((continuous_const.sub hc).sub (hc.comp continuous_neg))
  have hv0 : V 0 = 0 := by simp [V]; ring
  have hdelta (n : ℕ) : ∃ δ : ℝ, 0 < δ ∧ ∀ u : OSFourSpace, ‖u‖ < δ → V u ≤ (1/2 : ℝ)^n := by
    obtain ⟨δ,hδ,hu⟩ := Metric.continuousAt_iff.mp (hv.continuousAt (x := 0)) ((1/2 : ℝ)^n) (by positivity)
    refine ⟨δ,hδ,fun u h => ?_⟩
    specialize hu (show dist u 0 < δ by simpa using h)
    rw [hv0,Real.dist_0_eq_abs] at hu
    exact (le_abs_self _).trans hu.le
  choose δ hδ hbound using hdelta
  let d := TopologicalSpace.denseSeq OSFourSpace
  have hclose (n : ℕ) (x : OSFourSpace) : ∃ j, dist (d j) x < δ n := by
    obtain ⟨j,hj⟩ := (Metric.denseRange_iff.mp (TopologicalSpace.denseRange_denseSeq OSFourSpace)) x _ (hδ n)
    exact ⟨j,(dist_comm _ _).trans_lt hj⟩
  let q (n : ℕ) (x : OSFourSpace) := d (Nat.find (hclose n x))
  let A (n : ℕ) (p : OSFourSpace × (OSQuarticSlot → ℝ)) := p.2 (.inr (q n p.1))
  have hA (n : ℕ) : Measurable (A n) :=
    Measurable.find (f := fun j (p : OSFourSpace × (OSQuarticSlot → ℝ)) => p.2 (.inr (d j)))
      (p := fun j (p : OSFourSpace × (OSQuarticSlot → ℝ)) => dist (d j) p.1 < δ n) (fun j => (measurable_pi_apply (.inr (d j) : OSQuarticSlot)).comp measurable_snd)
      (fun j => measurableSet_lt (measurable_const.dist measurable_fst) measurable_const)
      (fun p => hclose n p.1)
  let Z (x : OSFourSpace) (z : OSQuarticSlot → ℝ) := limsup (fun n => A n (x,z)) atTop
  refine ⟨Z,Measurable.limsup hA,?_⟩
  intro x
  let f (n : ℕ) (z : OSQuarticSlot → ℝ) := z (.inr (q n x)) - z (.inr x)
  have hf (n : ℕ) := osQuarticProcess_difference hm hr μ hμ (.inr (q n x)) (.inr x)
  have hb (n : ℕ) : (∫ z, f n z^2 ∂μ) ≤ (1/2 : ℝ)^n := by
    rw [show (∫ z, f n z ^2 ∂μ) = _ from (hf n).2]
    simp only [osQuarticCovariance,sub_self]
    have hle := hbound n (q n x-x) (show ‖q n x-x‖ < δ n by
      simpa only [←dist_eq_norm] using Nat.find_spec (hclose n x))
    dsimp [V,C] at hle
    rw [neg_sub] at hle
    linarith
  filter_upwards [osAe_square_error_zero μ f (fun n => (hf n).1) hb] with z hz
  have ht := hz.add_const (z (.inr x))
  have hconv : Tendsto (fun n => A n (x,z)) atTop (𝓝 (z (.inr x))) := by simpa [A,f] using ht
  exact hconv.limsup_eq

end UV
