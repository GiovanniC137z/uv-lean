import UV.RevisionBoundaryHardy

/-! Nodal and positive mixed boundary preparations for the positive midpoint
observable. The claims concern the marked return, with no zero-visit term. -/

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal Topology

namespace UV.RevisionBoundary

def densityReturn (T : ℝ) (n : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ x, n x * returnCost T x

private theorem returnCost_measurable (T : ℝ) : Measurable (returnCost T) := by
  unfold returnCost
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

theorem densityReturn_eq_marked {T : ℝ} (hT : 0 < T) {n : ℝ → ℝ≥0∞}
    (hn : Measurable n) :
    densityReturn T n = integratedNormalReturn T (volume.withDensity n) := by
  rw [integratedNormalReturn_eq hT,
    lintegral_withDensity_eq_lintegral_mul _ hn (returnCost_measurable T)]
  rfl

def bornDensity (φ : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (‖φ x‖ ^ 2)

/-- Marked magnetic ultraviolet cost bound of Proposition
`prop:uvpeP-Dirac-Hardy`. The right-hand side is two over pi times the squared
normal derivative norm in the integral-representative formulation of H¹. -/
theorem nodal_state_return_bound {T : ℝ} (hT : 0 < T)
    {φ g : ℝ → ℂ} (hφc : Continuous φ) (hg : MemLp g 2 volume)
    (hφ : ∀ x, φ x = ∫ t in (0 : ℝ)..x, g t) :
    densityReturn T (bornDensity φ) ≤
      ENNReal.ofReal (2 / Real.pi) * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) := by
  unfold densityReturn
  calc
    _ ≤ ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ x, ENNReal.ofReal (‖φ x‖ ^ 2 / x ^ 2) := by
      apply mul_le_mul_left'
      apply lintegral_mono_ae
      have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (0 : ℝ) := by
        simp [ae_iff, measure_singleton]
      filter_upwards [hae] with x hx
      rw [returnCost, if_neg hx, bornDensity, ← ENNReal.ofReal_mul (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have he : Real.exp (-(x ^ 2) / T) ≤ 1 :=
        Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) hT.le)
      calc
        _ ≤ ‖φ x‖ ^ 2 * (1 / x ^ 2) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right he (sq_nonneg _)) (sq_nonneg _)
        _ = _ := by ring
    _ ≤ ENNReal.ofReal (1 / (2 * Real.pi)) *
        (4 * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2)) :=
      mul_le_mul_left' (normal_hardy hφc hg hφ) _
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_ofNat (n := 4),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

private theorem normal_reciprocal_ne_top_false {d : ℝ} (hd : 0 < d)
    (h : (∫⁻ x in Ioo (0 : ℝ) d, ENNReal.ofReal (1 / x ^ 2)) ≠ ∞) : False := by
  have hi : IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Ioo 0 d) :=
    (lintegral_ofReal_ne_top_iff_integrable
    (by fun_prop : Measurable fun x : ℝ => 1 / x ^ 2).aestronglyMeasurable
    (Eventually.of_forall fun x => div_nonneg zero_le_one (sq_nonneg x))).mp h
  have hp : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioo 0 d) := by
    apply hi.congr_fun
    · intro x hx
      simp [Real.rpow_neg hx.1.le, one_div]
    · exact measurableSet_Ioo
  exact (by norm_num : ¬ (-1 : ℝ) < -2)
    ((intervalIntegral.integrableOn_Ioo_rpow_iff hd).mp hp)

/-- A continuous nonzero value at the midpoint makes the marked return
diverge, irrespective of the energy of the rest of the state. -/
theorem nonnodal_state_return_diverges {T : ℝ} (hT : 0 < T)
    {φ : ℝ → ℂ} (hφ : Continuous φ) (hn : φ 0 ≠ 0) :
    densityReturn T (bornDensity φ) = ∞ := by
  have hp : 0 < ‖φ 0‖ := norm_pos_iff.mpr hn
  have hnear : ∀ᶠ x in 𝓝 (0 : ℝ), ‖φ 0‖ / 2 < ‖φ x‖ :=
    (isOpen_lt continuous_const hφ.norm).mem_nhds (show ‖φ 0‖ / 2 < ‖φ 0‖ by linarith)
  rcases Metric.mem_nhds_iff.mp hnear with ⟨r, hr, hsub⟩
  let d := min r 1
  have hd : 0 < d := lt_min hr zero_lt_one
  let c := (‖φ 0‖ / 2) ^ 2 * Real.exp (-1 / T)
  have hc : 0 < c := mul_pos (sq_pos_of_pos (by positivity)) (Real.exp_pos _)
  have hlo :
      ENNReal.ofReal c * (∫⁻ x in Ioo (0 : ℝ) d, ENNReal.ofReal (1 / x ^ 2)) ≤
        ∫⁻ x, bornDensity φ x * returnCost T x := by
    rw [← lintegral_const_mul _ (by fun_prop)]
    calc
      _ ≤ ∫⁻ x in Ioo (0 : ℝ) d, bornDensity φ x * returnCost T x := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        have hx1 : x ≤ 1 := hx.2.le.trans (min_le_right _ _)
        have hnorm := hsub (show x ∈ Metric.ball (0 : ℝ) r by
          simpa [Real.dist_eq, abs_of_pos hx.1] using hx.2.trans_le (min_le_left r 1))
        have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ ‖φ 0‖ / 2) hnorm.le 2
        have he : Real.exp (-1 / T) ≤ Real.exp (-(x ^ 2) / T) := by
          apply Real.exp_le_exp.mpr
          apply div_le_div_of_nonneg_right _ hT.le
          have hx2 : x ^ 2 ≤ 1 := by nlinarith [mul_nonneg hx.1.le (sub_nonneg.mpr hx1)]
          linarith
        rw [bornDensity, returnCost, if_neg hx.1.ne',
          ← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_mul (sq_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        calc
          _ = ((‖φ 0‖ / 2) ^ 2 * Real.exp (-1 / T)) / x ^ 2 := by unfold c; ring
          _ ≤ (‖φ x‖ ^ 2 * Real.exp (-(x ^ 2) / T)) / x ^ 2 :=
            div_le_div_of_nonneg_right (mul_le_mul hpow he (Real.exp_nonneg _) (sq_nonneg _))
              (sq_nonneg _)
          _ = _ := by ring
      _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl
  have htop : (∫⁻ x in Ioo (0 : ℝ) d, ENNReal.ofReal (1 / x ^ 2)) = ∞ :=
    not_ne_iff.mp (normal_reciprocal_ne_top_false hd)
  rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne', top_le_iff] at hlo
  rw [densityReturn, hlo, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity)).ne']

def mixedBornDensity {ι : Type*} (p : ι → ℝ≥0∞)
    (φ : ι → ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ∑' j, p j * bornDensity (φ j) x

theorem mixed_densityReturn_eq {ι : Type*} [Countable ι] (T : ℝ) (p : ι → ℝ≥0∞)
    (φ : ι → ℝ → ℂ) (hφ : ∀ j, Continuous (φ j)) :
    densityReturn T (mixedBornDensity p φ) = ∑' j, p j * densityReturn T (bornDensity (φ j)) := by
  unfold densityReturn mixedBornDensity
  simp_rw [← ENNReal.tsum_mul_right]
  rw [lintegral_tsum]
  · rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro j
    have hb : Measurable (bornDensity (φ j)) :=
      ((hφ j).norm.pow 2).measurable.ennreal_ofReal
    simp_rw [mul_assoc]
    rw [lintegral_const_mul _ (hb.mul (returnCost_measurable T)), mul_left_comm]
  · intro j
    exact (((((hφ j).norm.pow 2).measurable.ennreal_ofReal).const_mul (p j)).mul
      (returnCost_measurable T)).aemeasurable

/-- The positive mixed-preparation test of Proposition `prop:g5I-mixed`.
The integral representation of the one-dimensional H¹ states uses their
actual occupied derivatives, with square-integrable derivative norm. -/
theorem mixed_preparation_return_criterion {ι : Type*} [Countable ι] {T : ℝ}
    (hT : 0 < T) (p : ι → ℝ≥0∞) (φ g : ι → ℝ → ℂ)
    (hφ : ∀ j, Continuous (φ j)) (hg : ∀ j, MemLp (g j) 2 volume)
    (hprimitive : ∀ j x, φ j x = φ j 0 + ∫ t in (0 : ℝ)..x, g j t)
    (hp : ∀ j, p j ≠ 0)
    (henergy : (∑' j, p j * ∫⁻ x, ENNReal.ofReal (‖g j x‖ ^ 2)) ≠ ∞) :
    (densityReturn T (mixedBornDensity p φ) ≠ ∞ ↔ ∀ j, φ j 0 = 0) ∧
    ((∀ j, φ j 0 = 0) → densityReturn T (mixedBornDensity p φ) ≤
      ENNReal.ofReal (2 / Real.pi) * ∑' j, p j * ∫⁻ x, ENNReal.ofReal (‖g j x‖ ^ 2)) := by
  have hsum := mixed_densityReturn_eq T p φ hφ
  have hbound (hnode : ∀ j, φ j 0 = 0) :
      densityReturn T (mixedBornDensity p φ) ≤
        ENNReal.ofReal (2 / Real.pi) * ∑' j, p j * ∫⁻ x, ENNReal.ofReal (‖g j x‖ ^ 2) := by
    rw [hsum, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro j
    rw [mul_left_comm]
    exact mul_le_mul_left' (nodal_state_return_bound hT (hφ j) (hg j) (by
      intro x
      simpa [hnode j] using hprimitive j x)) _
  refine ⟨⟨?_, ?_⟩, hbound⟩
  · intro hn j
    by_contra hj
    have hle : p j * densityReturn T (bornDensity (φ j)) ≤ densityReturn T (mixedBornDensity p φ) := by
      rw [hsum]
      exact ENNReal.le_tsum j
    rw [nonnodal_state_return_diverges hT (hφ j) hj, ENNReal.mul_top (hp j)] at hle
    exact hn (top_le_iff.mp hle)
  · intro hn
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top henergy) (hbound hn)


theorem mass_weighted_nodal_state_return_bound (m : ℝ) {T : ℝ} (hT : 0 < T)
    {φ g : ℝ → ℂ} (hφc : Continuous φ) (hg : MemLp g 2 volume)
    (hφ : ∀ x, φ x = ∫ t in (0 : ℝ)..x, g t) :
    massWeightedNormalReturn m T (volume.withDensity (bornDensity φ)) ≤
      ENNReal.ofReal (2 / Real.pi) * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) := by
  apply (mass_weighted_return_comparison m T _).2.trans
  rw [← densityReturn_eq_marked hT (show Measurable (bornDensity φ) from
    (hφc.norm.pow 2).measurable.ennreal_ofReal)]
  exact nodal_state_return_bound hT hφc hg hφ


end UV.RevisionBoundary
