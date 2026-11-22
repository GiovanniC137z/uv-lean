import UV.RevisionOpeningSpectrum

/-! The subcritical limit and the exact dispersion-tail threshold for the
inclusive Poisson channel sum. The parameter `S` in the physical statement
is the invariant on the selected Lorentzian plane. -/

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology NNReal Nat

namespace UV

theorem openingWeight_continuous : Continuous openingWeight := by
  unfold openingWeight
  fun_prop

theorem openingWeight_pos_of_subcritical {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hlt : ℓ < 1) :
    0 < openingWeight ℓ := by
  rw [openingWeight_eq_of_nonneg hℓ]
  exact mul_pos (Real.sqrt_pos.mpr (sub_pos.mpr hlt)) (by positivity)

lemma openingPairDensity_summable (ℓ a₀ M : ℝ) :
    Summable (fun n : ℕ ↦ poissonPMFReal (ℓ * M).toNNReal n * openingWeight ((n + a₀) / M)) :=
  Summable.of_nonneg_of_le
    (fun _ ↦ mul_nonneg poissonPMFReal_nonneg (openingWeight_nonneg _))
    (fun _ ↦ mul_le_mul_of_nonneg_left (openingWeight_le _) poissonPMFReal_nonneg)
    ((poissonPMFRealSum _).summable.mul_right (3 / 2 : ℝ))

/-- The exact second moment of the shifted normalized count about `ℓ`. -/
theorem openingPoisson_hasSum_offset_square {ℓ M : ℝ} (hℓ : 0 ≤ ℓ) (hM : 0 < M)
    (a₀ : ℝ) :
    HasSum (fun n : ℕ ↦ poissonPMFReal (ℓ * M).toNNReal n * (((n : ℝ) + a₀) / M - ℓ) ^ 2)
      (ℓ / M + (a₀ / M) ^ 2) := by
  let r : ℝ≥0 := (ℓ * M).toNNReal
  have hr : (r : ℝ) = ℓ * M := Real.coe_toNNReal _ (mul_nonneg hℓ hM.le)
  have hc : HasSum (fun n : ℕ ↦ poissonPMFReal r n * ((n : ℝ) - r)) 0 := by
    have h := (openingPoisson_hasSum_first r).sub ((poissonPMFRealSum r).mul_right (r : ℝ))
    rw [one_mul, sub_self] at h
    convert h using 1
    ext n
    ring
  have hh := ((openingPoisson_hasSum_variance r).add (hc.mul_left (2 * a₀))).add
    ((poissonPMFRealSum r).mul_right (a₀ ^ 2))
  have h := hh.div_const (M ^ 2)
  convert h using 1
  · ext n
    change poissonPMFReal r n * (((n : ℝ) + a₀) / M - ℓ) ^ 2 = _
    rw [hr]
    field_simp
    ring
  · rw [hr]
    field_simp
    ring

/-- The normalized count concentrates by its exact variance. The argument
applies the bounded continuous threshold weight to the full channel law. -/
theorem openingPairDensity_tendsto_weight {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (a₀ : ℝ) :
    Tendsto (openingPairDensity ℓ a₀) atTop (𝓝 (openingWeight ℓ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp
    (openingWeight_continuous.continuousAt (x := ℓ)) (ε / 2) (by positivity)
  let C : ℝ := (3 / 2) / δ ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (x : ℝ) :
      |openingWeight x - openingWeight ℓ| ≤ ε / 2 + C * (x - ℓ) ^ 2 := by
    by_cases h : dist x ℓ < δ
    · have hc := hcont h
      rw [Real.dist_eq] at hc
      exact hc.le.trans (le_add_of_nonneg_right (mul_nonneg hC (sq_nonneg _)))
    · have hdist : δ ≤ |x - ℓ| := by simpa only [Real.dist_eq] using le_of_not_gt h
      have hsq : δ ^ 2 ≤ (x - ℓ) ^ 2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ hδ.le hdist 2
      have hp : (3 / 2 : ℝ) ≤ C * (x - ℓ) ^ 2 := by
        calc
          _ = C * δ ^ 2 := by dsimp [C]; field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hsq hC
      have hB : |openingWeight x - openingWeight ℓ| ≤ 3 / 2 := abs_le.mpr
        ⟨by linarith [openingWeight_nonneg x, openingWeight_le ℓ],
         by linarith [openingWeight_le x, openingWeight_nonneg ℓ]⟩
      exact hB.trans (hp.trans (le_add_of_nonneg_left (by positivity)))
  have hsmall : Tendsto (fun M : ℝ ↦ C * (ℓ / M + (a₀ / M) ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℝ ↦ ℓ / M) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Tendsto (fun M : ℝ ↦ a₀ / M) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using (h1.add (h2.pow 2)).const_mul C
  filter_upwards [eventually_gt_atTop (0 : ℝ), hsmall.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))]
    with M hM hMε
  let p (n : ℕ) := poissonPMFReal (ℓ * M).toNNReal n
  let D (n : ℕ) := ((n : ℝ) + a₀) / M - ℓ
  let B (n : ℕ) := (ε / 2) * p n + C * (p n * D n ^ 2)
  let W (n : ℕ) := p n * (openingWeight ((n + a₀) / M) - openingWeight ℓ)
  let small := C * (ℓ / M + (a₀ / M) ^ 2)
  have hp : HasSum p 1 := poissonPMFRealSum _
  have hB : HasSum B (ε / 2 + small) := by
    simpa only [B, small, mul_one] using (hp.mul_left (ε / 2)).add
      ((openingPoisson_hasSum_offset_square hℓ hM a₀).mul_left C)
  have hW : HasSum W (openingPairDensity ℓ a₀ M - openingWeight ℓ) := by
    have h := (openingPairDensity_summable ℓ a₀ M).hasSum.sub (hp.mul_right (openingWeight ℓ))
    simpa only [openingPairDensity, W, mul_sub, one_mul] using h
  have hW_le (n : ℕ) : |W n| ≤ B n := by
    have hpn : 0 ≤ p n := poissonPMFReal_nonneg
    dsimp only [W]
    rw [abs_mul, abs_of_nonneg hpn]
    calc
      _ ≤ p n * (ε / 2 + C * D n ^ 2) := mul_le_mul_of_nonneg_left (hpoint _) hpn
      _ = _ := by dsimp [B]; ring
  have hlo := Summable.tsum_le_tsum (fun n ↦ (abs_le.mp (hW_le n)).1) hB.neg.summable hW.summable
  have hhi := Summable.tsum_le_tsum (fun n ↦ (abs_le.mp (hW_le n)).2) hW.summable hB.summable
  rw [hB.neg.tsum_eq, hW.tsum_eq] at hlo
  rw [hW.tsum_eq, hB.tsum_eq] at hhi
  rw [Real.dist_eq]
  have hh := abs_le.mpr ⟨hlo, hhi⟩
  have hsε : small < ε / 2 := hMε
  exact hh.trans_lt (by linarith)

/-- The physical invariant is rescaled by `S / (4Δ)`. The prefactor
is the Dirac-pair normalization of the selected plane. -/
theorem openingOscillatorPairDensity_subcritical_limit {e m Δ b : ℝ} (hΔ : 0 < Δ)
    (hb : 0 ≤ b) (hlt : 4 * Δ * b < 1) (he : e ≠ 0) :
    0 < (e ^ 2 / (12 * Real.pi ^ 2)) * openingWeight (4 * Δ * b) ∧
    Tendsto (openingOscillatorPairDensity e m Δ b) atTop
      (𝓝 ((e ^ 2 / (12 * Real.pi ^ 2)) * openingWeight (4 * Δ * b))) := by
  have hb0 : 0 ≤ 4 * Δ * b := by positivity
  constructor
  · exact mul_pos (by positivity) (openingWeight_pos_of_subcritical hb0 hlt)
  have ht : Tendsto (fun S : ℝ ↦ S / (4 * Δ)) atTop atTop := by
    simp only [div_eq_mul_inv]
    exact tendsto_id.atTop_mul_const (by positivity)
  exact ((openingPairDensity_tendsto_weight hb0 (m ^ 2 / Δ)).comp ht).const_mul _

private theorem opening_tail_not_integrable_of_positive_limit {f : ℝ → ℝ} {L S₀ : ℝ}
    (hL : 0 < L) (hf : Tendsto f atTop (𝓝 L)) :
    ¬IntegrableOn (fun S ↦ f S / S) (Ioi S₀) := by
  have hp : ∀ᶠ S in atTop, L / 2 < f S := hf.eventually (lt_mem_nhds (by linarith))
  obtain ⟨B, hB⟩ := eventually_atTop.mp hp
  let T := max S₀ (max B 1)
  have hT1 : 1 ≤ T := (le_max_right B 1).trans (le_max_right _ _)
  have hT : 0 < T := zero_lt_one.trans_le hT1
  intro hi
  have hi' := hi.mono_set (Ioi_subset_Ioi (le_max_left S₀ (max B 1)))
  have hir : IntegrableOn (fun S : ℝ ↦ (L / 2) * S ^ (-1 : ℝ)) (Ioi T) := by
    apply hi'.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with S hS
    have hS0 : 0 < S := hT.trans hS
    have hS' : B ≤ S := ((le_max_left B 1).trans (le_max_right S₀ _)).trans hS.le
    have hlower := div_le_div_of_nonneg_right (hB S hS').le hS0.le
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, Real.norm_of_nonneg (by positivity)]
    exact hlower
  have hr : IntegrableOn (fun S : ℝ ↦ S ^ (-1 : ℝ)) (Ioi T) := by
    have hL0 : (L / 2 : ℝ) ≠ 0 := by positivity
    have hres : IntegrableOn (fun S : ℝ ↦ (L / 2)⁻¹ * ((L / 2) * S ^ (-1 : ℝ))) (Ioi T) :=
      hir.const_mul _
    simpa only [← mul_assoc, inv_mul_cancel₀ hL0, one_mul] using hres
  exact (lt_irrefl (-1 : ℝ)) ((integrableOn_Ioi_rpow_iff hT).mp hr)

theorem openingOscillatorPairDensity_subcritical_divergence {e m Δ b S₀ : ℝ} (hΔ : 0 < Δ)
    (hb : 0 ≤ b) (hlt : 4 * Δ * b < 1) (he : e ≠ 0) :
    ¬IntegrableOn (fun S ↦ openingOscillatorPairDensity e m Δ b S / S) (Ioi S₀) := by
  obtain ⟨hp, hlim⟩ := openingOscillatorPairDensity_subcritical_limit (m := m) hΔ hb hlt he
  exact opening_tail_not_integrable_of_positive_limit hp hlim

/-- Exact ultraviolet threshold of the full positive Poisson channel law. -/
theorem openingOscillatorPairDensity_tail_iff {e m Δ b : ℝ} (hΔ : 0 < Δ)
    (hb : 0 ≤ b) (he : e ≠ 0) :
    IntegrableOn (fun S ↦ openingOscillatorPairDensity e m Δ b S / S) (Ioi (4 * Δ)) ↔
      1 ≤ 4 * Δ * b := by
  constructor
  · intro hi
    exact le_of_not_gt fun hlt ↦ openingOscillatorPairDensity_subcritical_divergence hΔ hb hlt he hi
  · exact openingOscillatorPairDensity_tail_of_critical_or_above hΔ

end UV
