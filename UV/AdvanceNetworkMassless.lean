import UV.ContinueNetworkCriterion

/-! The zero-mass endpoint of the independent-probe marked network.
Positive marks keep the same five-dimensional heat and Lebesgue
normalizations through the massless limit. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace UV

/-- The positive-mark duration identity extends to zero mass by domination
by the actual massless edge kernel. -/
theorem networkHeatFive_integral_nonnegative_mass {m z : ℝ} (hm : 0 ≤ m) (hz : 0 < z) :
    (∫ s in Ioi (0 : ℝ), networkHeatFive m z s) = networkEdgeGreen m z := by
  obtain he | hm := hm.eq_or_lt
  · subst m
    let u (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
    have hu : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hpos (j : ℕ) : 0 < u j := by dsimp [u]; positivity
    have hh (j : ℕ) : AEStronglyMeasurable (networkHeatFive (u j) z)
        (volume.restrict (Ioi (0 : ℝ))) := by
      apply Measurable.aestronglyMeasurable
      unfold networkHeatFive
      fun_prop
    have hD : Tendsto (fun j : ℕ => ∫ s in Ioi (0 : ℝ), networkHeatFive (u j) z s)
        atTop (𝓝 (∫ s in Ioi (0 : ℝ), networkHeatFive 0 z s)) := by
      apply tendsto_integral_of_dominated_convergence (networkHeatFive 0 z) hh
        (networkHeatFive_integrable hz)
      · intro j
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hvol : 0 < s := hs
        rw [Real.norm_of_nonneg (networkHeatFive_nonneg hvol.le _ _)]
        unfold networkHeatFive
        rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, neg_zero]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        linarith only [mul_nonneg (sq_nonneg (u j)) hvol.le]
      · exact Eventually.of_forall fun s => by
          have h : Continuous (fun m : ℝ => networkHeatFive m z s) := by
            unfold networkHeatFive
            fun_prop
          exact (h.continuousAt (x := 0)).tendsto.comp hu
    have hEq (j : ℕ) := networkHeatFive_integral (hpos j) hz
    simp_rw [hEq] at hD
    have hcont : Continuous (fun m : ℝ => networkEdgeGreen m z) := by
      unfold networkEdgeGreen
      fun_prop
    exact tendsto_nhds_unique hD ((hcont.continuousAt (x := 0)).tendsto.comp hu)
  · exact networkHeatFive_integral hm hz

theorem networkEdgeCost_extended_nonnegative_mass {m z : ℝ} (hm : 0 ≤ m) (hz : 0 ≤ z) :
    networkEdgeCost m z = networkExtendedGreen m z := by
  unfold networkExtendedGreen
  split_ifs with h
  · rw [h, networkEdgeCost_zero]
  · have hz' : 0 < z := lt_of_le_of_ne hz (Ne.symm h)
    unfold networkEdgeCost
    rw [← ofReal_integral_eq_lintegral_ofReal (networkHeatFive_integrable hz')
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
          exact networkHeatFive_nonneg hs.le m z),
      networkHeatFive_integral_nonnegative_mass hm hz']

theorem networkDurationCost_extended_nonnegative_mass {E : Type*} [Fintype E]
    (m z : E → ℝ) (hm : ∀ e, 0 ≤ m e) (hz : ∀ e, 0 ≤ z e) :
    networkDurationCost m z = ∏ e, networkExtendedGreen (m e) (z e) := by
  rw [networkDurationCost_product]
  exact Finset.prod_congr rfl (fun e _ => networkEdgeCost_extended_nonnegative_mass (hm e) (hz e))

theorem integrated_marked_normal_network_nonnegative_mass {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m z : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst)
    (hm : ∀ e, 0 ≤ m e) (hz : ∀ e, 0 ≤ z e) :
    networkIndependentCost src dst m z = ∏ e, networkExtendedGreen (m e) (z e) := by
  rw [networkIndependentCost_eq_duration G src dst m z hG hcover,
    networkDurationCost_extended_nonnegative_mass m z hm hz]

theorem integrated_marked_normal_network_common_law_nonnegative_mass
    {E X : Type*} [Fintype E] [MeasurableSpace X] {n : ℕ} (μ : Measure X)
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m : E → ℝ)
    (y : X → Option (Fin n) → ℝ) (hG : G.Connected)
    (hcover : NetworkOrientationCovers G src dst) (hm : ∀ e, 0 ≤ m e) :
    (∫⁻ x, networkIndependentCost src dst m (networkPositionMarks src dst (y x)) ∂μ) =
      ∫⁻ x, ∏ e, networkExtendedGreen (m e) (networkPositionMarks src dst (y x) e) ∂μ := by
  apply lintegral_congr
  intro x
  exact integrated_marked_normal_network_nonnegative_mass G src dst m _ hG hcover hm
    (fun _ => abs_nonneg _)

theorem networkEdgeGreen_bounds_nonnegative_mass {m r : ℝ} (hm : 0 ≤ m)
    (hr : r ∈ Ioc (0 : ℝ) 1) :
    (Real.exp (-m) / (8 * Real.pi ^ 2)) / r ^ 3 ≤ networkEdgeGreen m r ∧
      networkEdgeGreen m r ≤ ((1 + m) / (8 * Real.pi ^ 2)) / r ^ 3 := by
  obtain h | h := hm.eq_or_lt
  · subst m
    simp only [networkEdgeGreen, neg_zero, Real.exp_zero, zero_mul, add_zero, mul_one]
    have hh : (1 : ℝ) / (8 * Real.pi ^ 2) / r ^ 3 =
        1 / (8 * Real.pi ^ 2 * r ^ 3) := by
      field_simp [Real.pi_ne_zero, hr.1.ne']
    exact ⟨hh.le, hh.ge⟩
  · exact networkEdgeGreen_bounds h hr

private theorem networkDurationCost_positive_marks_nonnegative_mass {E : Type*} [Fintype E]
    (m z : E → ℝ) (hm : ∀ e, 0 ≤ m e) (hz : ∀ e, 0 < z e) :
    networkDurationCost m z = ENNReal.ofReal (∏ e, networkEdgeGreen (m e) (z e)) := by
  rw [networkDurationCost_extended_nonnegative_mass m z hm (fun e => (hz e).le)]
  have h (e : E) : networkExtendedGreen (m e) (z e) = ENNReal.ofReal (networkEdgeGreen (m e) (z e)) := by
    simp only [networkExtendedGreen, if_neg (hz e).ne']
  simp_rw [h]
  exact (ENNReal.ofReal_prod_of_nonneg (fun e _ => by
    have hm' := hm e
    have hz' := hz e
    unfold networkEdgeGreen
    positivity)).symm

theorem networkGreen_product_bounds_nonnegative_mass {E : Type*} [Fintype E]
    (m : E → ℝ) (hm : ∀ e, 0 ≤ m e) {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    networkLowerConstant m / r ^ (3 * Fintype.card E) ≤ ∏ e, networkEdgeGreen (m e) r ∧
      (∏ e, networkEdgeGreen (m e) r) ≤ networkUpperConstant m / r ^ (3 * Fintype.card E) := by
  have hr0 := hr.1
  have hLo := Finset.prod_le_prod
    (fun e (_ : e ∈ Finset.univ) => by positivity :
      ∀ e ∈ Finset.univ, 0 ≤ (Real.exp (-(m e)) / (8 * Real.pi ^ 2)) / r ^ 3)
    (fun e (_ : e ∈ Finset.univ) => (networkEdgeGreen_bounds_nonnegative_mass (hm e) hr).1)
  have hHi := Finset.prod_le_prod
    (fun e (_ : e ∈ Finset.univ) => by
      have hme := hm e
      unfold networkEdgeGreen
      positivity :
      ∀ e ∈ Finset.univ, 0 ≤ networkEdgeGreen (m e) r)
    (fun e (_ : e ∈ Finset.univ) => (networkEdgeGreen_bounds_nonnegative_mass (hm e) hr).2)
  constructor
  · simpa only [networkLowerConstant, Finset.prod_div_distrib, Finset.prod_const,
      Finset.card_univ, ← pow_mul] using hLo
  · simpa only [networkUpperConstant, Finset.prod_div_distrib, Finset.prod_const,
      Finset.card_univ, ← pow_mul] using hHi

/-- The exact finite-edge proper-time cost has precisely the source's
inverse third moment per edge on a common collapsing positive width. -/
theorem networkDurationCost_inverse_moment_iff_nonnegative_mass {E : Type*} [Fintype E]
    (μ : Measure ℝ) (m : E → ℝ) (hm : ∀ e, 0 ≤ m e)
    (hr : ∀ᵐ r ∂μ, r ∈ Ioc (0 : ℝ) 1) :
    (∫⁻ r, networkDurationCost m (fun _ => r) ∂μ) < ⊤ ↔
      inverseMoment μ ((3 * Fintype.card E : ℕ) : ℝ) < ⊤ := by
  have hL : 0 < networkLowerConstant m := Finset.prod_pos (fun _ _ => by positivity)
  have hU : 0 < networkUpperConstant m := Finset.prod_pos (fun e _ => by exact div_pos (by linarith [hm e]) (by positivity))
  let R : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal ((r ^ (3 * Fintype.card E))⁻¹)
  have hRm : Measurable R := by dsimp [R]; fun_prop
  have hmoment : inverseMoment μ ((3 * Fintype.card E : ℕ) : ℝ) = ∫⁻ r, R r ∂μ := by
    unfold inverseMoment
    have hpos : ∀ᵐ r ∂μ, r ∈ Ioi (0 : ℝ) := hr.mono fun r hh => hh.1
    have hrestrict : μ.restrict (Ioi (0 : ℝ)) = μ := Measure.restrict_eq_self_of_ae_mem hpos
    rw [hrestrict]
    apply lintegral_congr_ae
    filter_upwards [hr] with r hh
    rw [Real.rpow_neg hh.1.le, Real.rpow_natCast]
  have hLo : ENNReal.ofReal (networkLowerConstant m) * (∫⁻ r, R r ∂μ) ≤
      ∫⁻ r, networkDurationCost m (fun _ => r) ∂μ := by
    rw [← lintegral_const_mul _ hRm]
    apply lintegral_mono_ae
    filter_upwards [hr] with r hh
    rw [networkDurationCost_positive_marks_nonnegative_mass _ _ hm (fun _ => hh.1),
      ← ENNReal.ofReal_mul hL.le]
    exact ENNReal.ofReal_le_ofReal (by simpa only [R, div_eq_mul_inv] using (networkGreen_product_bounds_nonnegative_mass m hm hh).1)
  have hHi : (∫⁻ r, networkDurationCost m (fun _ => r) ∂μ) ≤
      ENNReal.ofReal (networkUpperConstant m) * (∫⁻ r, R r ∂μ) := by
    rw [← lintegral_const_mul _ hRm]
    apply lintegral_mono_ae
    filter_upwards [hr] with r hh
    rw [networkDurationCost_positive_marks_nonnegative_mass _ _ hm (fun _ => hh.1),
      ← ENNReal.ofReal_mul hU.le]
    exact ENNReal.ofReal_le_ofReal (by simpa only [R, div_eq_mul_inv] using (networkGreen_product_bounds_nonnegative_mass m hm hh).2)
  rw [hmoment]
  constructor
  · intro h
    exact ENNReal.lt_top_of_mul_ne_top_right (hLo.trans_lt h).ne
      (ne_of_gt (ENNReal.ofReal_pos.mpr hL))
  · intro h
    exact hHi.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h)

/-- The alternating polygon has the same inverse moment criterion even
when some or all edges use the massless kernel. -/
theorem integrated_alternating_polygon_inverse_moment_iff_nonnegative_mass (N : ℕ) {n : ℕ}
    (chart : (Fin (N + 1) × Bool) ≃ Option (Fin n)) (μ : Measure ℝ)
    (G : SimpleGraph (Option (Fin n))) (m : (Fin (N + 1) × Bool) → ℝ)
    (hG : G.Connected)
    (hcover : NetworkOrientationCovers G chart (fun e => chart (alternatingNetworkNext e)))
    (hm : ∀ e, 0 ≤ m e) (hr : ∀ᵐ r ∂μ, r ∈ Ioc (0 : ℝ) 1) :
    (∫⁻ r, networkIndependentCost chart (fun e => chart (alternatingNetworkNext e)) m
      (networkPositionMarks chart (fun e => chart (alternatingNetworkNext e))
        (fun v => alternatingNetworkHeight r (chart.symm v))) ∂μ) < ⊤ ↔
      inverseMoment μ ((6 * (N + 1) : ℕ) : ℝ) < ⊤ := by
  simp_rw [networkIndependentCost_eq_duration G chart
    (fun e => chart (alternatingNetworkNext e)) m _ hG hcover]
  have hmarks (r : ℝ) (hr0 : 0 ≤ r) :
      networkPositionMarks chart (fun e => chart (alternatingNetworkNext e))
        (fun v => alternatingNetworkHeight r (chart.symm v)) = fun _ => r := by
    funext v
    simpa only [networkPositionMarks, alternatingNetworkDisplacement, Equiv.symm_apply_apply] using
      alternatingNetwork_mark hr0 v
  have hcost :
      (∫⁻ r, networkDurationCost m
        (networkPositionMarks chart (fun e => chart (alternatingNetworkNext e))
          (fun v => alternatingNetworkHeight r (chart.symm v))) ∂μ) =
      ∫⁻ r, networkDurationCost m (fun _ => r) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hr] with r hh
    rw [hmarks r hh.1.le]
  rw [hcost, networkDurationCost_inverse_moment_iff_nonnegative_mass μ m hm hr]
  have hcard : 3 * Fintype.card (Fin (N + 1) × Bool) = 6 * (N + 1) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    ring
  rw [hcard]

end UV
