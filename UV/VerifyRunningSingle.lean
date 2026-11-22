import UV.VerifyRunningPrimitive
import UV.ExtendRunningAngularBoundary
import UV.ContinueStableMassiveRemainder

/-! The compact-test boundary of the running stable-half simple pole
in the actual four-momentum variables. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology

def stableSingleBoundaryResidual (η a w : ℝ) : ℂ :=
  (Complex.exp (-(a : ℂ) * stableShellBoundaryRoot η w) - 1) * (w : ℂ)⁻¹

theorem stable_single_boundary_residual_norm_le {η a : ℝ} (hη : η ^ 2 = 1)
    (ha : 0 ≤ a) {w : ℝ} (hw : w ≠ 0) :
    ‖stableSingleBoundaryResidual η a w‖ ≤ a * inverseRootAbs w := by
  let S := stableShellBoundaryRoot η w
  have hre : 0 ≤ S.re := by
    simp [S, stableShellBoundaryRoot, Complex.mul_re, Complex.mul_im]
  have hx : (-(a : ℂ) * S).re ≤ 0 := by
    simpa [Complex.mul_re] using mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) hre
  have hs : 0 < Real.sqrt |w| := Real.sqrt_pos.mpr (abs_pos.mpr hw)
  have hn := exp_sub_one_norm_le_of_re_nonpos hx
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg ha,
    stable_shell_boundary_root_norm _ hη] at hn
  change ‖(Complex.exp (-(a : ℂ) * S) - 1) * (w : ℂ)⁻¹‖ ≤ _
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, inverseRootAbs]
  refine (mul_le_mul_of_nonneg_right hn (inv_nonneg.mpr (abs_nonneg w))).trans_eq ?_
  field_simp [hs.ne', (abs_pos.mpr hw).ne']
  linear_combination a * Real.sq_sqrt (abs_nonneg w)

variable {E : Type*} [NormedAddCommGroup E]

theorem Plane.stable_single_residual_tendsto (diamond : Plane E) (ε : Evolution)
    (a : ℝ) {w : ℝ} (hw : w ≠ 0) :
    Tendsto (fun h : Height => diamond.stableHalfRegular ε a w h)
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 (stableSingleBoundaryResidual (diamond.eta ε) a w)) := by
  let H := (𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))
  let Z (t : ℝ) : ℂ := (w : ℂ) + Complex.I * ((diamond.eta ε * t : ℝ) : ℂ)
  have hc : Continuous Z := by dsimp [Z]; fun_prop
  have hCoe : Tendsto (fun h : Height => (h : ℝ)) H (𝓝 (0 : ℝ)) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have hZ : Tendsto (fun h : Height => diamond.shiftedShellCoefficient ε h w) H (𝓝 (w : ℂ)) := by
    simpa [Z, Function.comp_def, Plane.shiftedShellCoefficient] using
      (hc.continuousAt (x := 0)).tendsto.comp hCoe
  have hX := (diamond.stable_shell_root_tendsto ε w).const_mul (-(a : ℂ))
  have hG : Continuous (fun x : ℂ => Complex.exp x - 1) := Complex.continuous_exp.sub continuous_const
  refine ((hG.continuousAt.tendsto.comp hX).mul (hZ.inv₀ (Complex.ofReal_ne_zero.mpr hw))).congr ?_
  intro h
  simp only [Function.comp_apply, Plane.stableHalfRegular, h.property, dite_true,
    Plane.stableHalfCoefficient, diamond.stable_half_numerator_characters,
    diamond.pole_coefficient_eq_inv, Plane.stableShellRoot]

theorem Plane.running_single_residual_full_momentum (diamond : Plane E) (ε : Evolution)
    {a : ℝ} (ha : 0 ≤ a) {g : ℝ × Spatial → ℂ} (hg : Continuous g) (hs : HasCompactSupport g) :
    Tendsto (fun h : Height => ∫ q : ℝ × Spatial, runningAxialTest g q *
      diamond.stableHalfRegular ε a (shellSquare q.1 q.2) h)
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 (∫ q : ℝ × Spatial, runningAxialTest g q *
        stableSingleBoundaryResidual (diamond.eta ε) a (shellSquare q.1 q.2))) := by
  have hL : Measurable (stableSingleBoundaryResidual (diamond.eta ε) a) := by
    unfold stableSingleBoundaryResidual stableShellBoundaryRoot
    fun_prop
  exact (cone_running_test_limit_of_inverse_root_bound
    (fun h => diamond.stable_half_regular_measurable ε a h) hL
    (fun h _ hw => diamond.stable_half_regular_norm_bound ε ha hw h.property)
    (fun _ hw => stable_single_boundary_residual_norm_le (diamond.eta_sq ε) ha hw)
    (fun _ hw => diamond.stable_single_residual_tendsto ε a hw) hg hs).2

def Plane.masslessRunningStableSinglePair (diamond : Plane E) (ε : Evolution) (h : Height)
    (a : ℝ) (g : ℝ × Spatial → ℂ) : ℂ :=
  ∫ q : ℝ × Spatial, runningAxialTest g q *
    (diamond.stableHalfCoefficient ε a (shellSquare q.1 q.2) h *
      diamond.poleCoefficient ε h (shellSquare q.1 q.2))

theorem Plane.massless_running_stable_single_pair_split (diamond : Plane E) (ε : Evolution)
    (h : Height) (a : ℝ) {g : ℝ × Spatial → ℂ} (hg : Continuous g) (hs : HasCompactSupport g) :
    diamond.masslessRunningStableSinglePair ε h a g =
      (∫ q : ℝ × Spatial, runningAxialTest g q *
        diamond.poleCoefficient ε h (shellSquare q.1 q.2)) +
      ∫ q : ℝ × Spatial, runningAxialTest g q *
        diamond.stableHalfRegular ε a (shellSquare q.1 q.2) h := by
  let P (q : ℝ × Spatial) := diamond.poleCoefficient ε h (shellSquare q.1 q.2)
  let K (q : ℝ × Spatial) := diamond.stableHalfCoefficient ε a (shellSquare q.1 q.2) h
  have hp : Continuous P := (diamond.pole_coefficient_continuous ε h).comp shellSquare_continuous
  have hK : Continuous K :=
    (diamond.stable_half_coefficient_continuous ε a h).comp shellSquare_continuous
  have hi {L : ℝ × Spatial → ℂ} (hL : Continuous L) :
      Integrable (fun q => runningAxialTest g q * L q) := by
    simpa only [runningAxialTest, mul_assoc] using integrable_runningAxialSign_mul measurable_fst
      ((hg.mul hL).integrable_of_hasCompactSupport hs.mul_right)
  have h₁ := hi hp
  have h₁const : Continuous (fun _ : ℝ × Spatial => (1 : ℂ)) := continuous_const
  have h₂ := hi ((hK.sub h₁const).mul hp)
  change diamond.masslessRunningStableSinglePair ε h a g =
    (∫ q, runningAxialTest g q * P q) + ∫ q, runningAxialTest g q *
      diamond.stableHalfRegular ε a (shellSquare q.1 q.2) h
  simp only [Plane.stableHalfRegular, h.property, dite_true]
  rw [← integral_add h₁ h₂]
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  change runningAxialTest g q * (K q * P q) =
    runningAxialTest g q * P q + runningAxialTest g q * ((K q - 1) * P q)
  ring

theorem Plane.massless_running_stable_single_limit (diamond : Plane E) (ε : Evolution)
    {a : ℝ} (ha : 0 ≤ a) {g : ℝ × Spatial → ℂ} (hg : ContDiff ℝ 2 g) (hs : HasCompactSupport g) :
    ∃ R > (0 : ℝ),
      Tendsto (fun h : Height => diamond.masslessRunningStableSinglePair ε h a g)
        ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
        (𝓝 (((2 * Real.pi ^ 2 : ℝ) • (∫ r in Ioc (0 : ℝ) R, r •
          coneAngularSingleBoundary (diamond.eta ε) (coneRunningAngularAmplitude g r))) +
          (∫ q : ℝ × Spatial, runningAxialTest g q *
            stableSingleBoundaryResidual (diamond.eta ε) a (shellSquare q.1 q.2)))) := by
  obtain ⟨R, hR, hP⟩ := diamond.cone_running_smooth_single_limit ε hg hs
  have hL := diamond.running_single_residual_full_momentum ε ha hg.continuous hs
  refine ⟨R, hR, (hP.add hL).congr (fun h => ?_)⟩
  rw [diamond.massless_running_stable_single_pair_split ε h a hg.continuous hs]
  simp only [Complex.real_smul, runningAxialTest, mul_assoc]

end UV.SectorPlane
