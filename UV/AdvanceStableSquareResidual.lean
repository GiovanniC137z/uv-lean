import UV.AdvanceStableRoot
import UV.ResumeStableCone

/-! The remaining inverse-root singularity is absolutely integrable
on compact four-momentum tests through both sheets and the cone tip. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology

def stableSquareBoundaryResidual (η a w : ℝ) : ℂ :=
  stableSquareResidualFromRoot a (stableShellBoundaryRoot η w) (w : ℂ)

theorem stable_square_boundary_residual_norm_le {η a : ℝ} (hη : η ^ 2 = 1)
    (ha : 0 ≤ a) (w : ℝ) :
    ‖stableSquareBoundaryResidual η a w‖ ≤ (a ^ 3 / 2) * inverseRootAbs w := by
  by_cases hw : w = 0
  · simp [hw, stableSquareBoundaryResidual, stableSquareResidualFromRoot,
      stableShellBoundaryRoot, inverseRootAbs]
  · have hs : 0 ≤ (stableShellBoundaryRoot η w).re := by
      simp [stableShellBoundaryRoot, Complex.mul_re, Complex.mul_im]
    have hnorm : ‖stableShellBoundaryRoot η w‖ = Real.sqrt ‖(w : ℂ)‖ := by
      rw [stable_shell_boundary_root_norm _ hη, Complex.norm_real, Real.norm_eq_abs]
    apply (stable_square_residual_from_root_norm_le ha (Complex.ofReal_ne_zero.mpr hw) hnorm hs).trans_eq
    rw [Complex.norm_real, Real.norm_eq_abs, inverseRootAbs, div_mul_eq_div_div,
      div_eq_mul_inv (a ^ 3 / 2)]

variable {E : Type*} [NormedAddCommGroup E]

theorem Plane.stable_square_residual_tendsto (diamond : Plane E) (ε : Evolution)
    (a : ℝ) {w : ℝ} (hw : w ≠ 0) :
    Tendsto (fun h : Height => stableSquareResidual a (diamond.shiftedShellCoefficient ε h w))
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 (stableSquareBoundaryResidual (diamond.eta ε) a w)) := by
  let H := (𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))
  let x (h : Height) := -(a : ℂ) * diamond.stableShellRoot ε h w
  let X := -(a : ℂ) * stableShellBoundaryRoot (diamond.eta ε) w
  have hX : Tendsto x H (𝓝 X) := (diamond.stable_shell_root_tendsto ε w).const_mul _
  have hCoe : Tendsto (fun h : Height => (h : ℝ)) H (𝓝 (0 : ℝ)) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have hZ : Tendsto (fun h : Height => diamond.shiftedShellCoefficient ε h w) H (𝓝 (w : ℂ)) := by
    let Z (t : ℝ) : ℂ := (w : ℂ) + Complex.I * ((diamond.eta ε * t : ℝ) : ℂ)
    have hc : Continuous Z := by dsimp [Z]; fun_prop
    have ht := (hc.continuousAt (x := 0)).tendsto.comp hCoe
    simpa [Z, Function.comp_def, Plane.shiftedShellCoefficient] using ht
  have hG : Continuous (fun y : ℂ => Complex.exp y - 1 - y - y ^ 2 / 2) := by fun_prop
  exact (hG.continuousAt.tendsto.comp hX).div (hZ.pow 2)
    (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hw))

private theorem stable_square_boundary_residual_measurable (η a : ℝ) :
    Measurable (stableSquareBoundaryResidual η a) := by
  unfold stableSquareBoundaryResidual stableSquareResidualFromRoot stableShellBoundaryRoot
  fun_prop

private theorem Plane.stable_square_residual_measurable (diamond : Plane E) (ε : Evolution)
    (h : Height) (a : ℝ) :
    Measurable (fun w : ℝ => stableSquareResidual a (diamond.shiftedShellCoefficient ε h w)) := by
  unfold stableSquareResidual stableSquareResidualFromRoot Plane.shiftedShellCoefficient
  fun_prop

/-- Local integrability and dominated convergence for an actual normal
coefficient with an inverse-root bound on the four-momentum cone. -/
theorem cone_test_limit_of_inverse_root_bound {K : Height → ℝ → ℂ} {L : ℝ → ℂ} {C : ℝ}
    (hK : ∀ h, Measurable (K h)) (hL : Measurable L)
    (hBoundK : ∀ h w, w ≠ 0 → ‖K h w‖ ≤ C * inverseRootAbs w)
    (hBoundL : ∀ w, w ≠ 0 → ‖L w‖ ≤ C * inverseRootAbs w)
    (hLim : ∀ w, w ≠ 0 → Tendsto (fun h : Height => K h w)
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))) (𝓝 (L w)))
    {g : ℝ × Spatial → ℂ} (hg : Continuous g) (hs : HasCompactSupport g) :
    Integrable (fun q : ℝ × Spatial => g q * L (shellSquare q.1 q.2)) ∧
    Tendsto (fun h : Height => ∫ q : ℝ × Spatial, g q * K h (shellSquare q.1 q.2))
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 (∫ q : ℝ × Spatial, g q * L (shellSquare q.1 q.2))) := by
  obtain ⟨R₀, hR₀⟩ := hs.exists_bound_of_continuousOn continuous_id.continuousOn
  let R := max 1 R₀
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  let S := Icc (-R) R ×ˢ Metric.closedBall (0 : Spatial) R
  let μ := (volume : Measure (ℝ × Spatial)).restrict S
  have hzero (q : ℝ × Spatial) (hq : q ∉ S) : g q = 0 := by
    by_contra hn
    have hN : ‖q‖ ≤ R := (hR₀ q (subset_tsupport g hn)).trans (le_max_right _ _)
    rw [Prod.norm_def, max_le_iff] at hN
    exact hq ⟨abs_le.mp (by simpa only [Real.norm_eq_abs] using hN.1),
      by simpa only [Metric.mem_closedBall, dist_zero_right] using hN.2⟩
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hs
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  let F (h : Height) (q : ℝ × Spatial) :=
    g q * K h (shellSquare q.1 q.2)
  let G (q : ℝ × Spatial) :=
    g q * L (shellSquare q.1 q.2)
  have hBound : Integrable (fun q : ℝ × Spatial =>
      (M * C) * inverseRootAbs (shellSquare q.1 q.2)) μ :=
    (integrableOn_inverse_root_shell_box hR).const_mul _
  have hGc : Measurable G :=
    hg.measurable.mul (hL.comp shellSquare_continuous.measurable)
  have hw : ∀ᵐ q ∂μ, shellSquare q.1 q.2 ≠ 0 :=
    (ae_mono Measure.restrict_le_self) massless_shell_nonzero_ae
  have hGi : Integrable G μ := by
    apply hBound.mono' hGc.aestronglyMeasurable
    filter_upwards [hw] with q hn
    dsimp only [G]
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (hM q)
      (hBoundL _ hn)
      (norm_nonneg _) hM₀
  have hSg : ∀ q ∉ S, G q = 0 := fun q hq => by simp [G, hzero q hq]
  have hSf (h : Height) : ∀ q ∉ S, F h q = 0 := fun q hq => by simp [F, hzero q hq]
  constructor
  · have hZ : IntegrableOn G S := hGi
    exact hZ.integrable_of_forall_notMem_eq_zero hSg
  · let H := (𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))
    have hT := tendsto_integral_filter_of_dominated_convergence
      (l := H) (μ := μ) (F := F) (f := G) _ ?_ ?_ hBound ?_
    · rw [show (∫ q, G q ∂μ) = ∫ q, G q from
        setIntegral_eq_integral_of_forall_compl_eq_zero hSg] at hT
      exact hT.congr (fun h => setIntegral_eq_integral_of_forall_compl_eq_zero (hSf h))
    · exact Eventually.of_forall fun h =>
        (hg.measurable.mul ((hK h).comp shellSquare_continuous.measurable)).aestronglyMeasurable
    · refine Eventually.of_forall fun h => ?_
      filter_upwards [hw] with q hn
      dsimp only [F]
      rw [norm_mul, mul_assoc]
      exact mul_le_mul (hM q) (hBoundK h _ hn)
        (norm_nonneg _) hM₀
    · filter_upwards [hw] with q hn
      exact (hLim _ hn).const_mul (g q)

theorem Plane.stable_square_residual_full_momentum (diamond : Plane E) (ε : Evolution)
    {a : ℝ} (ha : 0 ≤ a) {g : ℝ × Spatial → ℂ} (hg : Continuous g) (hs : HasCompactSupport g) :
    Integrable (fun q : ℝ × Spatial =>
      g q * stableSquareBoundaryResidual (diamond.eta ε) a (shellSquare q.1 q.2)) ∧
    Tendsto (fun h : Height => ∫ q : ℝ × Spatial,
      g q * stableSquareResidual a (diamond.shiftedShellCoefficient ε h (shellSquare q.1 q.2)))
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 (∫ q : ℝ × Spatial,
        g q * stableSquareBoundaryResidual (diamond.eta ε) a (shellSquare q.1 q.2))) := by
  exact cone_test_limit_of_inverse_root_bound (C := a ^ 3 / 2)
    (fun h => diamond.stable_square_residual_measurable ε h a)
    (stable_square_boundary_residual_measurable (diamond.eta ε) a)
    (fun h _ hw => diamond.stable_square_residual_inverse_root_bound ε h ha hw)
    (fun w _ => stable_square_boundary_residual_norm_le (diamond.eta_sq ε) ha w)
    (fun _ hw => diamond.stable_square_residual_tendsto ε a hw) hg hs

end UV.SectorPlane
