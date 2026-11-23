import UV.SectorPlaneFractionalAngle
import UV.ContinueConeSquareProbe

/-! Uniform four-momentum bound for the uncontracted fractional branch
term on compact radial tests, including tests through the cone tip. -/

noncomputable section

namespace UV.SectorPlane

open Filter Set MeasureTheory Real
open scoped Topology Interval

/-- Radial test of a continuous function of the Lorentzian invariant,
with the normalized pushforward of the actual four-dimensional angles. -/
theorem radial_invariant_integral {φ : ℝ → ℝ} (hc : Continuous φ) {R : ℝ} (hs : ∀ r > R, φ r = 0)
    (B : ℝ → ℂ) (hB : Continuous B) :
    (∫ q : ℝ × Spatial, φ (coneEuclideanRadius q) • B (shellSquare q.1 q.2)) =
      (2*π^2 : ℝ) • ∫ r in Ioi (0:ℝ), φ r • ∫ u in Ioo (-1:ℝ) 1,
        coneInvariantDensity u • ((r:ℂ)^3 * B (r^2*u)) := by
  let G (p : ℝ × ℝ) := φ (sqrt (p.1^2+p.2^2)) • B (p.1^2-p.2^2)
  have hG : Continuous G := (hc.comp (continuous_sqrt.comp ((continuous_fst.pow 2).add (continuous_snd.pow 2)))).smul
    (hB.comp ((continuous_fst.pow 2).sub (continuous_snd.pow 2)))
  have hcompact : HasCompactSupport (fun q : ℝ × Spatial => G (q.1, ‖q.2‖)) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0:ℝ × Spatial) R)
    intro q hq
    have hr : R < ‖q‖ := lt_of_not_ge (by simpa only [Metric.mem_closedBall, dist_zero_right] using hq)
    change φ (coneEuclideanRadius q) • _ = 0
    rw [hs _ (hr.trans_le (norm_le_coneEuclideanRadius q)),zero_smul]
  have hi := (hG.comp (continuous_fst.prodMk (continuous_norm.comp continuous_snd))).integrable_of_hasCompactSupport
    (μ := volume) hcompact
  change (∫ q : ℝ × Spatial, G (q.1, ‖q.2‖)) = _
  rw [cone_polar_integral G hG.aestronglyMeasurable hi]
  have he (r : ℝ) (hr : r ∈ Ioi 0) :
      (∫ θ in Ioo (0:ℝ) π, (r^3 * sin θ^2) • G (r*cos θ,r*sin θ)) =
        (π/2) • (φ r • ∫ u in Ioo (-1:ℝ) 1, coneInvariantDensity u • ((r:ℂ)^3*B (r^2*u))) := by
    let F (u : ℝ) := (r:ℂ)^3 * B (r^2*u)
    have hF : Continuous F := continuous_const.mul (hB.comp (continuous_const.mul continuous_id))
    have hpoint (θ : ℝ) : (r^3*sin θ^2) • G (r*cos θ,r*sin θ) =
        φ r • (sin θ^2 • F (cos θ^2-sin θ^2)) := by
      have hnorm : sqrt ((r*cos θ)^2+(r*sin θ)^2) = r := by
        rw [show (r*cos θ)^2+(r*sin θ)^2=r^2 by linear_combination r^2 * sin_sq_add_cos_sq θ]
        exact sqrt_sq hr.le
      have hw : (r*cos θ)^2-(r*sin θ)^2 = r^2*(cos θ^2-sin θ^2) := by ring
      simp only [G,F,hnorm,hw,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_pow]; ring
    simp_rw [hpoint]
    rw [integral_smul,cone_polar_angular_integral hF,cone_angular_density_integral,smul_comm (φ r)]
    rfl
  rw [setIntegral_congr_fun measurableSet_Ioi he,integral_smul,smul_smul]
  congr 1
  ring

variable {E : Type*} [NormedAddCommGroup E]

theorem Plane.radial_fractional_uniform (diamond : Plane E) (ε : Evolution) {φ : ℝ → ℝ} (hc : Continuous φ)
    {R : ℝ} (hs : ∀ r > R, φ r = 0) :
    ∃ C ≥ (0:ℝ), ∀ h : Height, ‖∫ q : ℝ × Spatial, φ (coneEuclideanRadius q) •
      ((diamond.stableShellRoot ε h (shellSquare q.1 q.2))⁻¹)^3‖ ≤ C := by
  obtain ⟨L,hL,hbound⟩ := diamond.uncontracted_fractional_angle_bound ε
  let M := ∫ r in Ioc (0:ℝ) R, |φ r| * L
  have hM : 0 ≤ M := integral_nonneg (fun r => mul_nonneg (abs_nonneg _) hL)
  refine ⟨2*π^2*M,by positivity,?_⟩
  intro h
  let B (w : ℝ) := ((diamond.stableShellRoot ε h w)⁻¹)^3
  have hcB : Continuous B := (continuous_iff_continuousAt.mpr (fun w => (diamond.stable_shell_inverse_root_hasDerivAt ε h w).continuousAt)).pow 3
  rw [radial_invariant_integral hc hs B hcB,norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ 2*π^2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  let A (r : ℝ) := ∫ u in Ioo (-1:ℝ) 1, coneInvariantDensity u • ((r:ℂ)^3 * B (r^2*u))
  change ‖∫ r in Ioi (0:ℝ), φ r • A r‖ ≤ M
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi (Ioc_subset_Ioi_self (a := 0) (b := R))
    (f := fun r => φ r • A r) (fun r hr => by
      have hR : R < r := lt_of_not_ge fun h => hr.2 ⟨hr.1,h⟩
      change φ r • A r = 0
      rw [hs r hR,zero_smul])]
  apply norm_integral_le_of_norm_le ((hc.abs.mul continuous_const).continuousOn.integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self)
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := 0) (b := R))] with r hr
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hbound h hr.1) (abs_nonneg _)

end UV.SectorPlane
