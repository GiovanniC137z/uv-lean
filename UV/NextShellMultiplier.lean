import UV.NextShellJump

/-! Uniform control of the multiplier error on a compact shell chart.
The odd and positive regularizers are tested before the height limit. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology NNReal

theorem compact_shell_pv_norm_bound {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {r h : ℝ} (hr : 0 < r) (hh : 0 < h)
    (hs : ∀ D, r < |D| → f D = 0) :
    ‖∫ D, polePV h D * f D‖ ≤ 2 * (L : ℝ) * r := by
  have hfs : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact
    isCompact_Icc fun D hD => abs_le.mp (le_of_not_gt fun h => hD (hs D h))
  rw [pole_pv_test_symmetrize (hf.continuous.integrable_of_hasCompactSupport hfs) hh,
    setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
      (show Ioc 0 r ⊆ Ioi 0 from fun _ hD => hD.1) ?_]
  · have hi : IntegrableOn (fun _ : ℝ => 2 * (L : ℝ)) (Ioc (0 : ℝ) r) :=
      continuous_const.continuousOn.integrableOn_compact (μ := volume) isCompact_Icc
        |>.mono_set Ioc_subset_Icc_self
    have hb : ‖∫ D in Ioc (0 : ℝ) r, polePV h D * (f D - f (-D))‖ ≤
        ∫ _ in Ioc (0 : ℝ) r, 2 * (L : ℝ) :=
      norm_integral_le_of_norm_le hi ?_
    · simpa [integral_const, Real.volume_real_Ioc_of_le hr.le, mul_comm] using hb
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun D hD => ?_
      have hp : 0 < D := hD.1
      have hd : 0 < D ^ 2 + h ^ 2 := by positivity
      have hLip := hf.norm_sub_le D (-D)
      rw [show D - -D = 2 * D by ring, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * D)] at hLip
      rw [norm_mul, Real.norm_of_nonneg (by unfold polePV; positivity)]
      calc
        _ ≤ polePV h D * ((L : ℝ) * (2 * D)) :=
          mul_le_mul_of_nonneg_left hLip (by unfold polePV; positivity)
        _ = (2 * (L : ℝ)) * (D ^ 2 / (D ^ 2 + h ^ 2)) := by unfold polePV; ring
        _ ≤ 2 * (L : ℝ) := mul_le_of_le_one_right (by positivity)
          ((div_le_one hd).mpr (le_add_of_nonneg_right (sq_nonneg _)))
  · intro D hD
    have hpos : 0 < D := hD.1
    have hfar : r < D := lt_of_not_ge fun he => hD.2 ⟨hpos, he⟩
    simp [hs D (by simpa [abs_of_pos hpos] using hfar),
      hs (-D) (by simpa [abs_of_pos hpos] using hfar)]

private theorem complex_pv_bound {f : ℝ → ℂ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {r h : ℝ} (hr : 0 < r) (hh : 0 < h) (hs : ∀ D, r < |D| → f D = 0) :
    ‖∫ D, polePV h D • f D‖ ≤ 4 * (L : ℝ) * r := by
  have hfs : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact
    isCompact_Icc fun D hD => abs_le.mp (le_of_not_gt fun h => hD (hs D h))
  have hpc : Continuous (polePV h) := (continuous_id.div
    ((continuous_id.pow 2).add continuous_const) (fun D => by positivity))
  have hI : Integrable (fun D => polePV h D • f D) :=
    (hpc.smul hf.continuous).integrable_of_hasCompactSupport (hfs.smul_left (f := polePV h))
  have bR := compact_shell_pv_norm_bound (shell_re_lipschitz hf) hr hh
    (fun D hD => by simp [hs D hD])
  have bI := compact_shell_pv_norm_bound (shell_im_lipschitz hf) hr hh
    (fun D hD => by simp [hs D hD])
  rw [complex_shell_integral_split hI]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
  linarith

private theorem complex_poisson_bound {f : ℝ → ℂ} {C h : ℝ} (hh : 0 < h)
    (hC : ∀ D, ‖f D‖ ≤ C) :
    ‖∫ D, polePoisson h D • f D‖ ≤ Real.pi * C := by
  have hK := (opposite_shell_kernel_integrable hh).const_mul (C * h)
  have hbound : ‖∫ D, polePoisson h D • f D‖ ≤
      ∫ D, (C * h) * oppositeShellKernel h D := by
    apply norm_integral_le_of_norm_le hK
    refine Eventually.of_forall fun D => ?_
    rw [norm_smul, Real.norm_of_nonneg (pole_poisson_nonneg hh.le _)]
    exact (mul_le_mul_of_nonneg_left (hC D) (pole_poisson_nonneg hh.le _)).trans_eq
      (by unfold polePoisson oppositeShellKernel; ring)
  rw [integral_const_mul, opposite_shell_kernel_mass hh] at hbound
  convert hbound using 1
  field_simp

variable {E : Type*} [NormedAddCommGroup E]

/-- Smooth tested multiplier errors with vanishing sup norm and first
derivative bound pair to zero. The proof uses uniform bounds in the
positive height, separately for the principal value and delta parts. -/
theorem Plane.tested_pole_multiplier_error_limit (diamond : Plane E) (ε : Evolution)
    {e e' : ℝ → ℝ → ℂ} {L : ℝ → ℝ≥0} {C : ℝ → ℝ}
    {r : ℝ} (hr : 0 < r)
    (hder : ∀ h > 0, ∀ D, HasDerivAt (e h) (e' h D) D)
    (hL : ∀ h > 0, ∀ D, ‖e' h D‖ ≤ (L h : ℝ))
    (hC : ∀ h > 0, ∀ D, ‖e h D‖ ≤ C h)
    (hs : ∀ h > 0, ∀ D, r < |D| → e h D = 0)
    (hLt : Tendsto (fun h => (L h : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hCt : Tendsto C (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun h : ℝ => if hh : 0 < h then
      ∫ D, diamond.poleCoefficient ε ⟨h, hh⟩ D * e h D else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hb : Tendsto (fun h => 4 * (L h : ℝ) * r + Real.pi * C h)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ((hLt.const_mul (4 : ℝ)).mul_const r).add (hCt.const_mul Real.pi)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (Eventually.of_forall fun _ => norm_nonneg _)
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hp : 0 < h := hh
  rw [dif_pos hp]
  have hel : LipschitzWith (L h) (e h) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun D _ => (hder h hp D).hasDerivWithinAt) (fun D _ => hL h hp D)
      convex_univ (mem_univ x) (mem_univ y)
  have hfs : HasCompactSupport (e h) := HasCompactSupport.of_support_subset_isCompact
    isCompact_Icc fun D hD => abs_le.mp (le_of_not_gt fun hfar => hD (hs h hp D hfar))
  have hpc : Continuous (polePV h) :=
    continuous_id.div ((continuous_id.pow 2).add continuous_const) (fun D => by positivity)
  have hqc : Continuous (polePoisson h) :=
    continuous_const.div ((continuous_id.pow 2).add continuous_const) (fun D => by positivity)
  have hPI : Integrable (fun D => polePV h D • e h D) :=
    (hpc.smul hel.continuous).integrable_of_hasCompactSupport (hfs.smul_left (f := polePV h))
  have hQI : Integrable (fun D => polePoisson h D • e h D) :=
    (hqc.smul hel.continuous).integrable_of_hasCompactSupport (hfs.smul_left (f := polePoisson h))
  let z : ℂ := Complex.I * (diamond.eta ε : ℂ)
  have he : (∫ D, diamond.poleCoefficient ε ⟨h, hp⟩ D * e h D) =
      (∫ D, polePV h D • e h D) - z * ∫ D, polePoisson h D • e h D := by
    rw [← integral_const_mul, ← integral_sub hPI (hQI.const_mul z)]
    apply integral_congr_ae
    refine Eventually.of_forall fun D => ?_
    dsimp [z]
    rw [diamond.pole_coefficient_split]
    push_cast
    ring
  have hz : ‖z‖ = 1 := by
    simp [z, Plane.eta, Real.norm_eq_abs]
  rw [he]
  apply (norm_sub_le _ _).trans
  rw [norm_mul, hz, one_mul]
  exact add_le_add (complex_pv_bound hel hr hp (hs h hp)) (complex_poisson_bound hp (hC h hp))

/-- Adding the compact C¹ multiplier error to a fixed admitted
numerator leaves its tested boundary value unchanged. -/
theorem Plane.tested_pole_varying_numerator_limit (diamond : Plane E) (ε : Evolution)
    {g : ℝ → ℂ} {K : ℝ≥0} (hg : LipschitzWith K g) (hgs : HasCompactSupport g)
    {e e' : ℝ → ℝ → ℂ} {L : ℝ → ℝ≥0} {C : ℝ → ℝ}
    {r : ℝ} (hr : 0 < r)
    (hder : ∀ h > 0, ∀ D, HasDerivAt (e h) (e' h D) D)
    (hL : ∀ h > 0, ∀ D, ‖e' h D‖ ≤ (L h : ℝ))
    (hC : ∀ h > 0, ∀ D, ‖e h D‖ ≤ C h)
    (hs : ∀ h > 0, ∀ D, r < |D| → e h D = 0)
    (hLt : Tendsto (fun h => (L h : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hCt : Tendsto C (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun h : ℝ => if hh : 0 < h then
      ∫ D, diamond.poleCoefficient ε ⟨h, hh⟩ D * (g D + e h D) else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 (complexShellPV g -
        Complex.I * (diamond.eta ε : ℂ) * ((Real.pi : ℂ) * g 0))) := by
  have h := (diamond.tested_pole_coefficient_limit ε hg hgs).add
    (diamond.tested_pole_multiplier_error_limit ε hr hder hL hC hs hLt hCt)
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hpos : 0 < h := hh
  have hc : Continuous (diamond.poleCoefficient ε ⟨h, hpos⟩) := by
    rw [show diamond.poleCoefficient ε ⟨h, hpos⟩ =
      (fun D => (polePV h D : ℂ) -
        Complex.I * ((diamond.eta ε * polePoisson h D : ℝ) : ℂ)) from
      funext (diamond.pole_coefficient_split ε ⟨h, hpos⟩)]
    have hp : Continuous (polePV h) :=
      continuous_id.div ((continuous_id.pow 2).add continuous_const) (fun D => by positivity)
    have hq : Continuous (polePoisson h) :=
      continuous_const.div ((continuous_id.pow 2).add continuous_const) (fun D => by positivity)
    exact (Complex.continuous_ofReal.comp hp).sub
      (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul hq)))
  have he : Continuous (e h) :=
    continuous_iff_continuousAt.mpr fun D => (hder h hpos D).continuousAt
  have hes : HasCompactSupport (e h) := HasCompactSupport.of_support_subset_isCompact
    isCompact_Icc fun D hD => abs_le.mp (le_of_not_gt fun hfar => hD (hs h hpos D hfar))
  simp only [dif_pos hpos, mul_add]
  rw [integral_add
    ((hc.mul hg.continuous).integrable_of_hasCompactSupport (hgs.mul_left (f := _)))
    ((hc.mul he).integrable_of_hasCompactSupport (hes.mul_left (f := _)))]

end UV.SectorPlane
