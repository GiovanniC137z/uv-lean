import UV.AdvanceStableRoot
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The fractional contribution to the squared stable-half boundary
on the regular angular shell. Integration by parts uses the
actual inverse principal root and the same positive height. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology Interval

variable {E : Type*} [NormedAddCommGroup E]

def Plane.stableAngularFractionalPair (diamond : Plane E) (ε : Evolution)
    (h : Height) (a r b : ℝ) (g : ℝ → ℂ) : ℂ :=
  ∫ u in (-b)..b, g u * (-(a : ℂ) / (diamond.stableShellRoot ε h (r ^ 2 * u)) ^ 3)

theorem Plane.stable_angular_fractional_pair_parts (diamond : Plane E) (ε : Evolution)
    (h : Height) (a : ℝ) {r b : ℝ} (hr : 0 < r) {g g' : ℝ → ℂ}
    (hg : ∀ u, HasDerivAt g (g' u) u) (hg' : Continuous g')
    (hLeft : g (-b) = 0) (hRight : g b = 0) :
    diamond.stableAngularFractionalPair ε h a r b g =
      ((2 * a / r ^ 2 : ℝ) : ℂ) *
        ∫ u in (-b)..b, g' u * (diamond.stableShellRoot ε h (r ^ 2 * u))⁻¹ := by
  let v (u : ℝ) := (diamond.stableShellRoot ε h (r ^ 2 * u))⁻¹
  let v' (u : ℝ) := (((r ^ 2 / 2 : ℝ) : ℂ) *
    ((diamond.stableShellRoot ε h (r ^ 2 * u)) ^ 3)⁻¹)
  have hv (u : ℝ) : HasDerivAt v (v' u) u :=
    diamond.stable_shell_inverse_root_angular_derivative ε h r u
  have hvc : Continuous v := continuous_iff_continuousAt.mpr fun u => (hv u).continuousAt
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun u => (hg u).continuousAt
  have hv'c : Continuous v' := by
    have he : v' = fun u => ((r ^ 2 / 2 : ℝ) : ℂ) * v u ^ 3 := by
      funext u
      simp only [v, v', inv_pow]
    rw [he]
    exact continuous_const.mul (hvc.pow 3)
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := -b) (b := b) hgc.continuousOn hvc.continuousOn
    (fun u _ => hg u) (fun u _ => hv u)
    (hg'.intervalIntegrable _ _) (hv'c.intervalIntegrable _ _)
  simp only [hLeft, hRight, zero_mul, sub_self, zero_sub] at hIBP
  have hEq (u : ℝ) : g u * (-(a : ℂ) / (diamond.stableShellRoot ε h (r ^ 2 * u)) ^ 3) =
      (-((2 * a / r ^ 2 : ℝ) : ℂ)) * (g u * v' u) := by
    have hScale : ((2 * a / r ^ 2 : ℝ) : ℂ) * ((r ^ 2 / 2 : ℝ) : ℂ) = (a : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      field_simp [hr.ne']
    unfold v'
    rw [div_eq_mul_inv]
    linear_combination g u * ((diamond.stableShellRoot ε h (r ^ 2 * u)) ^ 3)⁻¹ * hScale
  unfold Plane.stableAngularFractionalPair
  simp_rw [hEq]
  rw [intervalIntegral.integral_const_mul, hIBP]
  ring

/-- Integrate the inverse-root primitive directly across the angular
shell. The test against the primitive may be any continuous function. -/
theorem Plane.stable_angular_inverse_root_test_limit (diamond : Plane E) (ε : Evolution)
    {r b : ℝ} (hr : 0 < r) (hb : 0 < b) {g : ℝ → ℂ} (hg : Continuous g) :
    Tendsto (fun h : Height => ∫ u in (-b)..b,
      g u * (diamond.stableShellRoot ε h (r ^ 2 * u))⁻¹)
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 (∫ u in (-b)..b, g u * (stableShellBoundaryRoot (diamond.eta ε) (r ^ 2 * u))⁻¹)) := by
  let μ := (volume : Measure ℝ).restrict (Ioc (-b) b)
  have hb' : -b ≤ b := (neg_nonpos.mpr hb.le).trans hb.le
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-b) b) hg.continuousOn
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM b ⟨hb', le_rfl⟩)
  have hi : Integrable (fun u => (M * r⁻¹) * inverseRootAbs u) μ :=
    ((integrableOn_inverseRootAbs_Icc hb).mono_set Ioc_subset_Icc_self).const_mul _
  have hme : ∀ᵐ u ∂μ, u ∈ Ioc (-b) b := ae_restrict_mem measurableSet_Ioc
  have hzero : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by simp [ae_iff]
  have hz : ∀ᵐ u : ℝ ∂μ, u ≠ 0 := (ae_mono Measure.restrict_le_self) hzero
  let H := (𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))
  simp only [intervalIntegral.integral_of_le hb']
  refine tendsto_integral_filter_of_dominated_convergence (l := H) (μ := μ) _ ?_ ?_ hi ?_
  · refine Eventually.of_forall fun (h : Height) => ?_
    have hc : Continuous (fun u => (diamond.stableShellRoot ε h (r ^ 2 * u))⁻¹) :=
      continuous_iff_continuousAt.mpr fun u =>
        (diamond.stable_shell_inverse_root_angular_derivative ε h r u).continuousAt
    exact (hg.mul hc).aestronglyMeasurable
  · refine Eventually.of_forall fun h => ?_
    filter_upwards [hme, hz] with u hu hne
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (hM u (Ioc_subset_Icc_self hu))
      (diamond.stable_shell_inverse_root_angular_norm_le ε h hr hne)
      (norm_nonneg _) hM₀
  · filter_upwards [hz] with u hu
    exact (diamond.stable_shell_inverse_root_tendsto ε
      (mul_ne_zero (pow_ne_zero _ hr.ne') hu)).const_mul (g u)

theorem Plane.stable_angular_fractional_pair_limit (diamond : Plane E) (ε : Evolution) (a : ℝ)
    {r b : ℝ} (hr : 0 < r) (hb : 0 < b) {g g' : ℝ → ℂ}
    (hg : ∀ u, HasDerivAt g (g' u) u) (hg' : Continuous g')
    (hLeft : g (-b) = 0) (hRight : g b = 0) :
    Tendsto (fun h : Height => diamond.stableAngularFractionalPair ε h a r b g)
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 (((2 * a / r ^ 2 : ℝ) : ℂ) *
        ∫ u in (-b)..b, g' u * (stableShellBoundaryRoot (diamond.eta ε) (r ^ 2 * u))⁻¹)) := by
  refine ((diamond.stable_angular_inverse_root_test_limit ε hr hb hg').const_mul
    (((2 * a / r ^ 2 : ℝ) : ℂ))).congr fun h => ?_
  exact (diamond.stable_angular_fractional_pair_parts ε h a hr hg hg' hLeft hRight).symm

/-- After the physical quadratic numerator and the four-momentum
Jacobian, the regular angular fractional term costs two powers of r. -/
theorem Plane.stable_angular_fractional_radial_bound (diamond : Plane E) (ε : Evolution)
    (h : Height) {a r b M : ℝ} (ha : 0 ≤ a) (hr : 0 < r) (hb : 0 < b)
    {g g' : ℝ → ℂ} (hg : ∀ u, HasDerivAt g (g' u) u) (hg' : Continuous g')
    (hLeft : g (-b) = 0) (hRight : g b = 0) (hM : ∀ u ∈ Icc (-b) b, ‖g' u‖ ≤ M) :
    ‖(r : ℂ) ^ 5 * diamond.stableAngularFractionalPair ε h a r b g‖ ≤
      (2 * a * M * ∫ u in (-b)..b, inverseRootAbs u) * r ^ 2 := by
  have hab : -b ≤ b := (neg_nonpos.mpr hb.le).trans hb.le
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM b ⟨hab, le_rfl⟩)
  let F (u : ℝ) := g' u * (diamond.stableShellRoot ε h (r ^ 2 * u))⁻¹
  have hFc : Continuous F :=
    hg'.mul (continuous_iff_continuousAt.mpr fun u =>
      (diamond.stable_shell_inverse_root_angular_derivative ε h r u).continuousAt)
  have hi : IntervalIntegrable (fun u => (M * r⁻¹) * inverseRootAbs u) volume (-b) b := by
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact (integrableOn_inverseRootAbs_Icc hb).const_mul _
  have hzero : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by simp [ae_iff]
  have hBound : ‖∫ u in (-b)..b, F u‖ ≤ (M * r⁻¹) * ∫ u in (-b)..b, inverseRootAbs u := by
    calc
      _ ≤ ∫ u in (-b)..b, ‖F u‖ := intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ u in (-b)..b, (M * r⁻¹) * inverseRootAbs u := by
        apply intervalIntegral.integral_mono_ae_restrict hab (hFc.norm.intervalIntegrable _ _) hi
        filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc (a := -b) (b := b)),
          (ae_mono Measure.restrict_le_self hzero)] with u hu hne
        dsimp only [F]
        rw [norm_mul, mul_assoc]
        exact mul_le_mul (hM u hu)
          (diamond.stable_shell_inverse_root_angular_norm_le ε h hr hne)
          (norm_nonneg _) hM₀
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [diamond.stable_angular_fractional_pair_parts ε h a hr hg hg' hLeft hRight,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * a / r ^ 2)]
  change r ^ 5 * (2 * a / r ^ 2 * ‖∫ u in (-b)..b, F u‖) ≤ _
  calc
    _ ≤ r ^ 5 * (2 * a / r ^ 2 * ((M * r⁻¹) * ∫ u in (-b)..b, inverseRootAbs u)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBound (by positivity)) (by positivity)
    _ = _ := by
      field_simp [hr.ne']

end UV.SectorPlane
