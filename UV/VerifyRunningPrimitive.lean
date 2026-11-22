import UV.VerifyRunningCalculus

/-! Dominated limits for literal running-sign tests and for the trace
of the inverse branch root on zero axial momentum. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology

def runningAxialTest (g : ℝ × Spatial → ℂ) (q : ℝ × Spatial) : ℂ :=
  (axialSign q.1 : ℂ) * g q

theorem running_axial_test_measurable {g : ℝ × Spatial → ℂ} (hg : Measurable g) :
    Measurable (runningAxialTest g) :=
  (Complex.continuous_ofReal.measurable.comp
    (runningAxialSign_measurable.comp measurable_fst)).mul hg

theorem running_axial_test_compact {g : ℝ × Spatial → ℂ} (hs : HasCompactSupport g) :
    HasCompactSupport (runningAxialTest g) :=
  hs.mul_left

theorem running_axial_test_norm_le (g : ℝ × Spatial → ℂ) (q : ℝ × Spatial) :
    ‖runningAxialTest g q‖ ≤ ‖g q‖ := by
  unfold runningAxialTest
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (runningAxialSign_norm_le q.1)

theorem cone_running_test_limit_of_inverse_root_bound
    {K : Height → ℝ → ℂ} {L : ℝ → ℂ} {C : ℝ}
    (hK : ∀ h, Measurable (K h)) (hL : Measurable L)
    (hBoundK : ∀ h w, w ≠ 0 → ‖K h w‖ ≤ C * inverseRootAbs w)
    (hBoundL : ∀ w, w ≠ 0 → ‖L w‖ ≤ C * inverseRootAbs w)
    (hLim : ∀ w, w ≠ 0 → Tendsto (fun h : Height => K h w)
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))) (𝓝 (L w)))
    {g : ℝ × Spatial → ℂ} (hg : Continuous g) (hs : HasCompactSupport g) :
    Integrable (fun q : ℝ × Spatial => runningAxialTest g q * L (shellSquare q.1 q.2)) ∧
    Tendsto (fun h : Height =>
      ∫ q : ℝ × Spatial, runningAxialTest g q * K h (shellSquare q.1 q.2))
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 (∫ q : ℝ × Spatial, runningAxialTest g q * L (shellSquare q.1 q.2))) := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hs
  exact cone_bounded_test_limit_of_inverse_root_bound hK hL hBoundK hBoundL hLim
    (running_axial_test_measurable hg.measurable) (running_axial_test_compact hs)
    (fun q => (running_axial_test_norm_le _ q).trans (hM q))

variable {E : Type*} [NormedAddCommGroup E]

theorem Plane.running_inverse_root_full_momentum (diamond : Plane E) (ε : Evolution)
    {g : ℝ × Spatial → ℂ} (hg : Continuous g) (hs : HasCompactSupport g) :
    Tendsto (fun h : Height => ∫ q : ℝ × Spatial, runningAxialTest g q *
      (diamond.stableShellRoot ε h (shellSquare q.1 q.2))⁻¹)
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 (∫ q : ℝ × Spatial, runningAxialTest g q *
        (stableShellBoundaryRoot (diamond.eta ε) (shellSquare q.1 q.2))⁻¹)) := by
  refine (cone_running_test_limit_of_inverse_root_bound
    (K := fun h w => (diamond.stableShellRoot ε h w)⁻¹)
    (L := fun w => (stableShellBoundaryRoot (diamond.eta ε) w)⁻¹)
    (C := 1) ?_ ?_ ?_ ?_ ?_ hg hs).2
  · intro h
    exact (continuous_iff_continuousAt.mpr fun w =>
      (diamond.stable_shell_inverse_root_hasDerivAt ε h w).continuousAt).measurable
  · unfold stableShellBoundaryRoot
    fun_prop
  · intro h w hw
    rw [one_mul]
    exact diamond.stable_shell_inverse_root_norm_le ε h hw
  · intro w _
    rw [norm_inv, stable_shell_boundary_root_norm _ (diamond.eta_sq ε), one_mul, inverseRootAbs]
  · intro w hw
    exact diamond.stable_shell_inverse_root_tendsto ε hw

theorem Plane.running_square_residual_full_momentum (diamond : Plane E) (ε : Evolution)
    {a : ℝ} (ha : 0 ≤ a) {g : ℝ × Spatial → ℂ} (hg : Continuous g) (hs : HasCompactSupport g) :
    Tendsto (fun h : Height => ∫ q : ℝ × Spatial, runningAxialTest g q *
      stableSquareResidual a (diamond.shiftedShellCoefficient ε h (shellSquare q.1 q.2)))
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 (∫ q : ℝ × Spatial, runningAxialTest g q *
        stableSquareBoundaryResidual (diamond.eta ε) a (shellSquare q.1 q.2))) :=
  (cone_running_test_limit_of_inverse_root_bound (C := a ^ 3 / 2)
    (fun h => diamond.stable_square_residual_measurable ε h a)
    (stable_square_boundary_residual_measurable (diamond.eta ε) a)
    (fun h _ hw => diamond.stable_square_residual_inverse_root_bound ε h ha hw)
    (fun w _ => stable_square_boundary_residual_norm_le (diamond.eta_sq ε) ha w)
    (fun _ hw => diamond.stable_square_residual_tendsto ε a hw) hg hs).2

theorem stable_shell_boundary_on_axial_zero (η : ℝ) (p : Spatial) :
    stableShellBoundaryRoot η (shellSquare 0 p) = (‖p‖ : ℂ) := by
  simp [stableShellBoundaryRoot, shellSquare, Real.sqrt_sq (norm_nonneg p),
    Real.sqrt_eq_zero_of_nonpos (neg_nonpos.mpr (sq_nonneg ‖p‖))]

/-- The equatorial trace of the same-height inverse root has an ordinary
three-dimensional integral limit. The spatial origin is integrable. -/
theorem Plane.stable_inverse_root_axial_trace_limit (diamond : Plane E) (ε : Evolution)
    {f : Spatial → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => ∫ p : Spatial, f p *
      (diamond.stableShellRoot ε h (shellSquare 0 p))⁻¹)
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 (∫ p : Spatial, f p * (‖p‖ : ℂ)⁻¹)) := by
  obtain ⟨R, hR⟩ := hs.exists_bound_of_continuousOn continuous_id.continuousOn
  let S := Metric.closedBall (0 : Spatial) R
  let μ := (volume : Measure Spatial).restrict S
  have hzero (p : Spatial) (hp : p ∉ S) : f p = 0 := by
    by_contra hn
    have hb := hR p (subset_tsupport f hn)
    exact hp (by simpa [S, Metric.mem_closedBall, dist_zero_right])
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hs
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  let F (h : Height) (p : Spatial) := f p *
    (diamond.stableShellRoot ε h (shellSquare 0 p))⁻¹
  let G (p : Spatial) := f p * (‖p‖ : ℂ)⁻¹
  have hB : Integrable (fun p : Spatial => M * ‖p‖⁻¹) μ :=
    (integrableOn_inv_norm_closedBall_spatial R).const_mul M
  have hF (h : Height) : ∀ p ∉ S, F h p = 0 := fun p hp => by simp [F, hzero p hp]
  have hG : ∀ p ∉ S, G p = 0 := fun p hp => by simp [G, hzero p hp]
  have hneVol : ∀ᵐ p : Spatial ∂(volume : Measure Spatial), p ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_eq_eq_singleton] using
      (measure_singleton (0 : Spatial) : (volume : Measure Spatial) {0} = 0)
  have hne : ∀ᵐ p : Spatial ∂μ, p ≠ 0 :=
    (ae_mono Measure.restrict_le_self) hneVol
  have hshell (p : Spatial) (hp : p ≠ 0) : shellSquare 0 p ≠ 0 := by
    simp [shellSquare, norm_ne_zero_iff.mpr hp]
  have hRootNorm (h : Height) (p : Spatial) (hp : p ≠ 0) :
      ‖(diamond.stableShellRoot ε h (shellSquare 0 p))⁻¹‖ ≤ ‖p‖⁻¹ := by
    have h := diamond.stable_shell_inverse_root_norm_le ε h (hshell p hp)
    simpa [inverseRootAbs, shellSquare, abs_of_nonneg, Real.sqrt_sq (norm_nonneg p)] using h
  let H := (𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))
  have hL := tendsto_integral_filter_of_dominated_convergence
    (l := H) (μ := μ) (F := F) (f := G) _ ?_ ?_ hB ?_
  · rw [show (∫ p, G p ∂μ) = ∫ p, G p from
      setIntegral_eq_integral_of_forall_compl_eq_zero hG] at hL
    exact hL.congr (fun h => setIntegral_eq_integral_of_forall_compl_eq_zero (hF h))
  · refine Eventually.of_forall fun h => ?_
    have hC : Continuous (fun w => (diamond.stableShellRoot ε h w)⁻¹) :=
      continuous_iff_continuousAt.mpr fun w =>
        (diamond.stable_shell_inverse_root_hasDerivAt ε h w).continuousAt
    exact (hf.mul (hC.comp (shellSquare_continuous.comp
      (continuous_const.prodMk continuous_id)))).aestronglyMeasurable
  · refine Eventually.of_forall fun h => ?_
    filter_upwards [hne] with p hp
    rw [show ‖F h p‖ = ‖f p‖ * ‖(diamond.stableShellRoot ε h (shellSquare 0 p))⁻¹‖ from norm_mul _ _]
    exact mul_le_mul (hM p) (hRootNorm h p hp) (norm_nonneg _) hM₀
  · filter_upwards [hne] with p hp
    have h := (diamond.stable_shell_inverse_root_tendsto ε (hshell p hp)).const_mul (f p)
    simpa only [F, G, stable_shell_boundary_on_axial_zero] using h

end UV.SectorPlane
