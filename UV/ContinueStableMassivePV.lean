import UV.ContinueStableMassiveChart

/-! The full principal-value shell distribution for positive mass.
Both axial sheets are retained in the normal chart. Away from the pole
the height limit is taken against the ordinary inverse. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology NNReal

abbrev MassiveMomentum := ℝ × Spatial

def massiveD (m : ℝ) (q : MassiveMomentum) : ℝ := shellSquare q.1 q.2 - m ^ 2

theorem massiveD_continuous (m : ℝ) : Continuous (massiveD m) :=
  shellSquare_continuous.sub continuous_const

def massiveCoareaTest (b m : ℝ) (f : MassiveMomentum → ℝ) (D : ℝ) : ℝ :=
  ∫ p, massiveChartTest b m f (D, p)

theorem compact_transverse_support_bound {f : MassiveMomentum → ℝ}
    (hs : HasCompactSupport f) : ∃ R, ∀ t p, p ∉ Metric.closedBall (0 : Spatial) R → f (t, p) = 0 := by
  obtain ⟨R, hR⟩ := hs.exists_bound_of_continuousOn
    (continuous_snd : Continuous (Prod.snd : MassiveMomentum → Spatial)).continuousOn
  refine ⟨R, fun t p hp => ?_⟩
  by_contra h
  have hnorm := hR (t, p) (subset_tsupport f h)
  exact hp (by simpa using hnorm)

private theorem chart_test_of_transverse_vanishes {b m : ℝ} {f : MassiveMomentum → ℝ}
    {p : Spatial} (hf : ∀ t, f (t, p) = 0) (D : ℝ) : massiveChartTest b m f (D, p) = 0 := by
  simp [massiveChartTest, hf]

private theorem chart_test_of_normal_far {b m D : ℝ} (hb : 0 < b)
    (hD : b ≤ |D|) (f : MassiveMomentum → ℝ) (p : Spatial) : massiveChartTest b m f (D, p) = 0 := by
  rw [massiveChartTest, massive_normal_cutoff_zero hb hD, zero_mul, zero_mul]

private theorem massive_chart_axial_change {b m : ℝ} (hb : 0 < b) (hm : 2 * b ≤ m ^ 2)
    (f : MassiveMomentum → ℝ) (k : ℝ → ℝ) (p : Spatial) :
    (∫ r in Ioi (0 : ℝ), k (r ^ 2 - shellFrequency m p ^ 2) *
      (massiveNormalCutoff b (r ^ 2 - shellFrequency m p ^ 2) * (f (r, p) + f (-r, p)))) =
      ∫ D, k D * massiveChartTest b m f (D, p) := by
  let κ := shellFrequency m p
  have hκ : 2 * b ≤ κ ^ 2 := by
    dsimp [κ]
    rw [shell_frequency_square]
    linarith [sq_nonneg ‖p‖]
  calc
    _ = ∫ r in Ioi (0 : ℝ), 2 * r *
        (k (r ^ 2 - κ ^ 2) * massiveChartTest b m f (r ^ 2 - κ ^ 2, p)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hp : 0 < r := hr
      have hκr : shellFrequency m p = κ := rfl
      have H : k (r ^ 2 - κ ^ 2) *
          (massiveNormalCutoff b (r ^ 2 - κ ^ 2) * (f (r, p) + f (-r, p))) =
          2 * r * (k (r ^ 2 - κ ^ 2) * massiveChartTest b m f (r ^ 2 - κ ^ 2, p)) := by
        by_cases h : b ≤ |r ^ 2 - κ ^ 2|
        · rw [massive_normal_cutoff_zero hb h, chart_test_of_normal_far hb h]
          ring
        · have hB : b ≤ r ^ 2 := by
            have hD := abs_lt.mp (lt_of_not_ge h)
            linarith
          have hRoot : massiveChartRoot b m (r ^ 2 - κ ^ 2) p = r := by
            rw [massiveChartRoot, hκr, sub_add_cancel, max_eq_right hB, Real.sqrt_sq_eq_abs, abs_of_pos hp]
          simp only [massiveChartTest, massiveChartWeight, hRoot]
          field_simp [hp.ne']
      exact H
    _ = ∫ D in Ioi (-(κ ^ 2)), k D * massiveChartTest b m f (D, p) :=
      positive_ray_shell_change κ (fun D => k D * massiveChartTest b m f (D, p))
    _ = ∫ D, k D * massiveChartTest b m f (D, p) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro D hD
      have hneg : D ≤ -(κ ^ 2) := not_lt.mp hD
      have hDb : b ≤ |D| := by
        have hDneg : D < 0 := by linarith
        rw [abs_of_neg hDneg]
        linarith
      simp [chart_test_of_normal_far hb hDb]

/-- Exact local coarea for the massive shell. The positive and negative
roots enter together, without a physical cut selector. -/
theorem massive_local_coarea {b m : ℝ} (hb : 0 < b) (hm : 2 * b ≤ m ^ 2)
    {f : MassiveMomentum → ℝ} (hf : Continuous f) (hs : HasCompactSupport f)
    {k : ℝ → ℝ} (hk : Continuous k) :
    (∫ q : MassiveMomentum, k (massiveD m q) * (massiveNormalCutoff b (massiveD m q) * f q)) =
      ∫ D, k D * massiveCoareaTest b m f D := by
  obtain ⟨R, hR⟩ := compact_transverse_support_bound hs
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hs
  let B := Metric.closedBall (0 : Spatial) R
  let ν := (volume : Measure Spatial).restrict B
  have hν : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr
    ((isCompact_closedBall (0 : Spatial) R).measure_lt_top.ne)
  let G (q : MassiveMomentum) := k (massiveD m q) * (massiveNormalCutoff b (massiveD m q) * f q)
  have hgC : Continuous G := (hk.comp (massiveD_continuous m)).mul
    (((massive_normal_cutoff_lipschitz hb).continuous.comp (massiveD_continuous m)).mul hf)
  have hgI : Integrable G := hgC.integrable_of_hasCompactSupport (by
    have h : G = (fun q => k (massiveD m q) * massiveNormalCutoff b (massiveD m q)) * f := by
      funext q
      simp only [G, Pi.mul_apply, mul_assoc]
    rw [h]
    exact hs.mul_left)
  have hco : massiveCoareaTest b m f = transverseTest ν (massiveChartTest b m f) := by
    funext D
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun p hp => chart_test_of_transverse_vanishes (fun t => hR t p hp) D)).symm
  have hvar : Integrable (fun x : MassiveMomentum => k x.1 * massiveChartTest b m f x) (volume.prod ν) := by
    simpa only [smul_eq_mul] using
      (chart_integrable_smul ν (massive_chart_test_continuous (m := m) hb hf)
        (massive_chart_test_bound hb hC)
        (fun D p h => chart_test_of_normal_far hb h.le f p) hk)
  calc
    _ = ∫ p : Spatial, ∫ t : ℝ, G (t, p) := integral_prod_symm _ hgI
    _ = ∫ p : Spatial, (∫ t : ℝ, G (t, p)) ∂ν := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      simp [G, hR _ p hp]
    _ = ∫ p : Spatial, (∫ D : ℝ, k D * massiveChartTest b m f (D, p)) ∂ν := by
      apply integral_congr_ae
      filter_upwards [(ae_mono Measure.restrict_le_self) hgI.prod_left_ae] with p hp
      rw [← integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hp, compl_Ioi, ← neg_zero,
        ← integral_comp_neg_Ioi, neg_zero]
      rw [← integral_add hp.integrableOn hp.comp_neg.integrableOn]
      refine Eq.trans ?_ (massive_chart_axial_change hb hm f k p)
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r _
      dsimp only [G, massiveD, shellSquare]
      rw [neg_sq, shell_frequency_square]
      ring
    _ = ∫ D, k D * massiveCoareaTest b m f D := by
      rw [← integral_prod_symm _ hvar, hco]
      simpa only [smul_eq_mul] using chart_integral_smul ν
        (massive_chart_test_continuous hb hf) (massive_chart_test_bound hb hC)
        (fun D p h => chart_test_of_normal_far hb h.le f p) hk

/-- The full normal principal value, with the exterior ordinary inverse
included in the intrinsic four-dimensional measure. -/
def massiveShellPV (b m : ℝ) (f : MassiveMomentum → ℝ) : ℝ :=
  (∫ D in Ioi (0 : ℝ), symmetricTest (massiveCoareaTest b m f) D) +
    ∫ q : MassiveMomentum, ((1 - massiveNormalCutoff b (massiveD m q)) * (massiveD m q)⁻¹) * f q

private theorem normal_cutoff_compl_le {b : ℝ} (hb : 0 < b) (D : ℝ) :
    0 ≤ 1 - massiveNormalCutoff b D ∧
    1 - massiveNormalCutoff b D ≤ |D| * b⁻¹ := by
  refine ⟨sub_nonneg.mpr (massive_normal_cutoff_le_one hb D), ?_⟩
  unfold massiveNormalCutoff
  linarith [le_max_right (0 : ℝ) (1 - |D| * b⁻¹)]

private theorem polePV_norm_le_inv_abs (h D : ℝ) : ‖polePV h D‖ ≤ |D|⁻¹ := by
  by_cases hD : D = 0
  · simp [hD, polePV]
  rw [polePV, Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : 0 ≤ D ^ 2 + h ^ 2)]
  have hn : 0 < |D| := abs_pos.mpr hD
  rw [← one_div, div_le_div_iff₀ (by positivity) hn, one_mul, ← sq, sq_abs]
  exact le_add_of_nonneg_right (sq_nonneg _)

private theorem pole_pv_shell_exterior_limit {b m : ℝ} (hb : 0 < b)
    {f : MassiveMomentum → ℝ} (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun h : ℝ => ∫ q : MassiveMomentum, polePV h (massiveD m q) *
      ((1 - massiveNormalCutoff b (massiveD m q)) * f q)) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ q : MassiveMomentum,
        ((1 - massiveNormalCutoff b (massiveD m q)) * (massiveD m q)⁻¹) * f q)) := by
  let g (q : MassiveMomentum) := 1 - massiveNormalCutoff b (massiveD m q)
  have hgC : Continuous g :=
    continuous_const.sub ((massive_normal_cutoff_lipschitz hb).continuous.comp (massiveD_continuous m))
  refine tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
    (μ := volume) (F := fun h q => polePV h (massiveD m q) * (g q * f q))
    (f := fun q => (g q * (massiveD m q)⁻¹) * f q)
    (fun q => b⁻¹ * ‖f q‖) ?_ ?_ ((hf.integrable_of_hasCompactSupport hs).norm.const_mul _) ?_
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hp : 0 < h := hh
    have hnorm : Continuous (polePV h) := continuous_iff_continuousAt.mpr
      fun D => (polePV_hasDerivAt hp D).continuousAt
    exact ((hnorm.comp (massiveD_continuous m)).mul (hgC.mul hf)).aestronglyMeasurable
  · refine Eventually.of_forall fun h => Eventually.of_forall fun q => ?_
    let D := massiveD m q
    by_cases hD : D = 0
    · change ‖polePV h D * (g q * f q)‖ ≤ _
      rw [hD]
      simpa [polePV] using mul_nonneg (inv_nonneg.mpr hb.le) (norm_nonneg (f q))
    · have hg := normal_cutoff_compl_le hb D
      change ‖polePV h D * (g q * f q)‖ ≤ _
      rw [← mul_assoc, norm_mul, norm_mul, Real.norm_of_nonneg hg.1]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have ha : 0 < |D| := abs_pos.mpr hD
      calc
        _ ≤ |D|⁻¹ * (|D| * b⁻¹) :=
          mul_le_mul (polePV_norm_le_inv_abs h D) hg.2 hg.1 (inv_nonneg.mpr ha.le)
        _ = b⁻¹ := by rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
  · refine Eventually.of_forall fun q => ?_
    let D := massiveD m q
    by_cases hD : D = 0
    · change Tendsto (fun h => polePV h D * (g q * f q)) _ (𝓝 ((g q * D⁻¹) * f q))
      simp [hD, polePV]
    · have hc : ContinuousAt (fun h : ℝ => D / (D ^ 2 + h ^ 2)) 0 :=
        ContinuousAt.div continuousAt_const (by fun_prop)
          (by simpa using (sq_pos_of_ne_zero hD).ne')
      have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      have he : D / (D ^ 2 + (0 : ℝ) ^ 2) = D⁻¹ := by field_simp [hD]; ring
      change Tendsto _ _ (𝓝 (D / (D ^ 2 + (0 : ℝ) ^ 2))) at ht
      rw [he] at ht
      have H := ht.mul_const (g q * f q)
      convert H using 2
      ring

/-- On compact Lipschitz tests the unweighted finite-height principal
value converges on the full massive momentum shell. -/
theorem pole_pv_full_massive_shell_limit {b m : ℝ} (hb : 0 < b) (hm : 2 * b ≤ m ^ 2)
    {f : MassiveMomentum → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    Tendsto (fun h : ℝ => ∫ q : MassiveMomentum, polePV h (massiveD m q) * f q)
      (𝓝[>] (0 : ℝ)) (𝓝 (massiveShellPV b m f)) := by
  obtain ⟨R, hR⟩ := compact_transverse_support_bound hs
  obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hs
  have hC₀ := (norm_nonneg (f 0)).trans (hC 0)
  let ν := (volume : Measure Spatial).restrict (Metric.closedBall 0 R)
  have hν : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr
    ((isCompact_closedBall (0 : Spatial) R).measure_lt_top.ne)
  have he : massiveCoareaTest b m f = transverseTest ν (massiveChartTest b m f) := by
    funext D
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun p hp => chart_test_of_transverse_vanishes (fun t => hR t p hp) D)).symm
  obtain ⟨K, hK⟩ := massive_chart_test_norm_lipschitz (m := m) hb hf
    (C := ⟨C, hC₀⟩) hC
  have hL : LipschitzWith (⟨ν.real univ, measureReal_nonneg⟩ * K) (massiveCoareaTest b m f) := by
    rw [he]
    exact transverse_test_lipschitz ν (massive_chart_test_continuous hb hf.continuous)
      (massive_chart_test_bound hb hC) hK
  have hSf : HasCompactSupport (massiveCoareaTest b m f) := by
    rw [he]
    exact transverse_test_support ν (fun D p h => chart_test_of_normal_far hb h.le f p)
  have h₁ := pole_pv_test_limit hL (hL.continuous.integrable_of_hasCompactSupport hSf)
  have h₂ := pole_pv_shell_exterior_limit (b := b) (m := m) hb hf.continuous hs
  have H := h₁.add h₂
  unfold massiveShellPV
  refine H.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : 0 < h := hh
  have hc : Continuous (polePV h) := continuous_iff_continuousAt.mpr
    fun D => (polePV_hasDerivAt hh' D).continuousAt
  rw [← massive_local_coarea hb hm hf.continuous hs hc]
  have hI {u : MassiveMomentum → ℝ} (hu : Continuous u) :
      Integrable (fun q => u q * f q) :=
    (hu.mul hf.continuous).integrable_of_hasCompactSupport (hs.mul_left (f := u))
  have h₃ := hI ((hc.comp (massiveD_continuous m)).mul
    ((massive_normal_cutoff_lipschitz hb).continuous.comp (massiveD_continuous m)))
  have h₄ := hI ((hc.comp (massiveD_continuous m)).mul
    ((continuous_const (y := (1 : ℝ))).sub
      ((massive_normal_cutoff_lipschitz hb).continuous.comp (massiveD_continuous m))))
  have h₃' : Integrable (fun q : MassiveMomentum => polePV h (massiveD m q) *
      (massiveNormalCutoff b (massiveD m q) * f q)) := by simpa only [mul_assoc] using h₃
  have h₄' : Integrable (fun q : MassiveMomentum => polePV h (massiveD m q) *
      ((1 - massiveNormalCutoff b (massiveD m q)) * f q)) := by simpa only [mul_assoc] using h₄
  rw [← integral_add h₃' h₄']
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  ring

end UV.SectorPlane
