import UV.ContinueRestThresholdSeparation
import UV.AdvanceConeAngularGeometry
import UV.MassiveRunningPole
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The degenerate intersection and the compensating intrinsic radial
measure. The direction used in angular averaging remains norm one. -/

noncomputable section

namespace UV.SectorPlane

open Set Filter MeasureTheory
open scoped Topology UV.SectorPlane

variable {E : Type*} [NormedAddCommGroup E]

theorem symmetric_rest_threshold_intersection {m : ℝ} (hm : 0 < m) (q : MassiveMomentum) :
    symmetricRestNormals m (2 * m) q = 0 ↔ q = 0 := by
  have hk : ((2 : ℝ) * m) / 2 = m := by ring
  constructor
  · intro h
    have he := (symmetric_rest_shell_intersection m (2 * m) (by positivity) q).mp
      ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    rw [hk, sub_self] at he
    exact Prod.ext he.1 (norm_eq_zero.mp (pow_eq_zero he.2))
  · rintro rfl
    simp [symmetric_rest_normals_eval, hk]

theorem symmetric_rest_threshold_jacobian_zero (m : ℝ) :
    (fderiv ℝ (restAxialRadialNormals m (2 * m)) (0 : ℝ × ℝ)).det = 0 := by
  rw [rest_axial_radial_fderiv_det]
  simp

theorem threshold_axial_signs {m x : ℝ} (hm : 0 < m) (hx : |x| ≤ m / 2) :
    0 < x + m ∧ x - m < 0 := by
  constructor
  · linarith only [(abs_le.mp hx).1, hm]
  · linarith only [(abs_le.mp hx).2, hm]

theorem Plane.rest_threshold_running_units [NormedSpace ℝ E] (diamond : Plane E)
    {m x : ℝ} (hm : 0 < m) (hx : |x| ≤ m / 2) :
    (diamond.runningUnit (x + m) (threshold_axial_signs hm hx).1.ne' : E) =
        (diamond.poleUnit : E) ∧
    (diamond.runningUnit (x - m) (threshold_axial_signs hm hx).2.ne : E) =
        -(diamond.poleUnit : E) := by
  have H := threshold_axial_signs hm hx
  simp [Plane.runningUnit, axialSign, H.1, H.2, H.2.not_gt]

/-- Radial Jacobian divided by the actual finite-height near-pole gap. -/
def Plane.restThresholdRadialCoefficient (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) (m r : ℝ) : ℂ :=
  (↑(r ^ 2) : ℂ) * (diamond.restThresholdNearPlus ε₁ h m r -
    diamond.restThresholdNearMinus ε₂ h m r)⁻¹

theorem Plane.rest_threshold_radial_coefficient_continuous (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) {m : ℝ} (hm : 0 < m) :
    Continuous (diamond.restThresholdRadialCoefficient ε₁ ε₂ h m) := by
  have hc (ε : Evolution) : Continuous (diamond.restThresholdRoot ε h m) := by
    let w : ℝ → ℂ := fun r => (↑(m ^ 2 + r ^ 2) : ℂ) -
      Complex.I * ↑(diamond.eta ε * (h : ℝ))
    have hw : Continuous w := by unfold w; fun_prop
    apply continuous_iff_continuousAt.mpr
    intro r
    have hRe : 0 < (w r).re := by
      unfold w
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
      positivity
    exact (principalSqrt_differentiableAt hRe).continuousAt.comp hw.continuousAt
  have H : Continuous (fun r =>
      diamond.restThresholdNearPlus ε₁ h m r - diamond.restThresholdNearMinus ε₂ h m r) :=
    ((hc ε₁).sub continuous_const).sub (continuous_const.sub (hc ε₂))
  exact (Complex.continuous_ofReal.comp (continuous_id.pow 2)).mul
    (H.inv₀ (diamond.rest_threshold_near_separation_ne_zero ε₁ ε₂ h hm))

theorem Plane.rest_threshold_radial_coefficient_bound (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) {m : ℝ} (hm : 0 < m) (r : ℝ) :
    ‖diamond.restThresholdRadialCoefficient ε₁ ε₂ h m r‖ ≤
      (Real.sqrt (m ^ 2 + r ^ 2) + m) / 2 := by
  rw [Plane.restThresholdRadialCoefficient, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg r)]
  exact diamond.rest_threshold_radial_separation ε₁ ε₂ h hm r

theorem Plane.rest_threshold_radial_coefficient_tendsto (diamond : Plane E) (ε₁ ε₂ : Evolution)
    {m r : ℝ} (hm : 0 < m) (hr : r ≠ 0) :
    Tendsto (fun h => diamond.restThresholdRadialCoefficient ε₁ ε₂ h m r)
      poleBoundaryHeights (𝓝 (↑((Real.sqrt (m ^ 2 + r ^ 2) + m) / 2) : ℂ)) := by
  set R := Real.sqrt (m ^ 2 + r ^ 2)
  have hF : poleBoundaryHeights ≤ Filter.comap Subtype.val (𝓝 (0 : ℝ)) :=
    Filter.comap_mono nhdsWithin_le_nhds
  have hplus := (diamond.rest_threshold_root_tendsto ε₁ hm r).mono_left hF
  have hminus := (diamond.rest_threshold_root_tendsto ε₂ hm r).mono_left hF
  have hs : R ^ 2 = m ^ 2 + r ^ 2 := Real.sq_sqrt (by positivity)
  have hR : m < R := lt_of_le_of_ne (rest_threshold_mass_le_radius_root hm r) (fun h => by
    rw [← h] at hs
    exact hr (pow_eq_zero (by linarith only [hs] : r ^ 2 = 0)))
  have hd : ((R : ℂ) - (m : ℂ)) - ((m : ℂ) - (R : ℂ)) ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at he
    linarith only [hR, he]
  have H := (((hplus.sub_const (m : ℂ)).sub (hminus.const_sub (m : ℂ))).inv₀ hd).const_mul
    (↑(r ^ 2) : ℂ)
  convert H using 1
  rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, ← Complex.ofReal_sub, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul]
  apply congrArg (fun x : ℝ => 𝓝 (x : ℂ))
  rw [← div_eq_mul_inv]
  apply Eq.symm
  apply (div_eq_iff (by linarith only [hR])).2
  nlinarith only [hs]

/-- The compensation factor has a bounded, integrable majorant on every
bounded interval of the intrinsic positive spatial radius. -/
theorem rest_threshold_radial_majorant_integrable (m R : ℝ) :
    IntegrableOn (fun r : ℝ => (Real.sqrt (m ^ 2 + r ^ 2) + m) / 2) (Icc 0 R) := by
  exact ContinuousOn.integrableOn_compact isCompact_Icc (by fun_prop)

/-- The compensated near-pole coefficient may be tested through the
degenerate boundary radius against compact radial data. -/
theorem Plane.rest_threshold_radial_coefficient_test (diamond : Plane E) (ε₁ ε₂ : Evolution)
    {m R B : ℝ} (hm : 0 < m) {f : ℝ → ℂ} (hf : Measurable f)
    (hB : ∀ r ∈ Icc 0 R, ‖f r‖ ≤ B) :
    Tendsto (fun h => ∫ r in Icc 0 R, diamond.restThresholdRadialCoefficient ε₁ ε₂ h m r * f r)
      poleBoundaryHeights
      (𝓝 (∫ r in Icc 0 R, (↑((Real.sqrt (m ^ 2 + r ^ 2) + m) / 2) : ℂ) * f r)) := by
  have hM := (rest_threshold_radial_majorant_integrable m R).mul_const B
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hM ?_
  · exact Eventually.of_forall fun h =>
      ((diamond.rest_threshold_radial_coefficient_continuous ε₁ ε₂ h hm).measurable.mul hf).aestronglyMeasurable
  · refine Eventually.of_forall fun h => (ae_restrict_mem measurableSet_Icc).mono fun r hr => ?_
    rw [norm_mul]
    exact mul_le_mul (diamond.rest_threshold_radial_coefficient_bound ε₁ ε₂ h hm r) (hB r hr)
      (norm_nonneg _) (by positivity)
  · have hn : ∀ᵐ r : ℝ ∂volume, r ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [ae_restrict_of_ae hn] with r hr
    exact (diamond.rest_threshold_radial_coefficient_tendsto ε₁ ε₂ hm hr).mul_const (f r)

end UV.SectorPlane
