import UV.AdvanceStableAngularFractional
import UV.ContinueConeAngularLaw

/-! The uncontracted inverse-cube root on the massless cone. After the
four-dimensional polar Jacobian its angular integral is bounded uniformly
in the positive radius and in the prescribed common height. -/

noncomputable section

namespace UV.SectorPlane

open Filter Set MeasureTheory Real
open scoped Topology Interval

def coneInvariantDensity (u : ℝ) := (1-u)/(π*sqrt (1-u^2))
private def angleCost (u : ℝ) := |coneInvariantDensity u - π⁻¹| * (inverseRootAbs u)^3

private theorem density_near_zero {u : ℝ} (hu : |u| ≤ 1/2) :
    |coneInvariantDensity u - π⁻¹| ≤ (4/π) * |u| := by
  let s := sqrt (1-u^2)
  have hu' := abs_le.mp hu
  have hsq : 0 ≤ 1-u^2 := by nlinarith [sq_nonneg (u+1/2),mul_nonneg (sub_nonneg.mpr hu'.2) (by linarith : 0 ≤ u+1/2)]
  have hse : s^2 = 1-u^2 := Real.sq_sqrt hsq
  have hspos : 1/2 ≤ s := by nlinarith [Real.sqrt_nonneg (1-u^2),mul_nonneg (sub_nonneg.mpr hu'.2) (by linarith : 0 ≤ u+1/2)]
  have hsp : 0 < s := by linarith
  have hsmall : |1-s| ≤ |u| := by
    have hsle : s ≤ 1 := by nlinarith [sq_nonneg u]
    rw [abs_of_nonneg (sub_nonneg.mpr hsle)]
    nlinarith [sq_abs u,abs_nonneg u,mul_nonneg (sub_nonneg.mpr hsle) hsp.le,mul_nonneg (abs_nonneg u) (show 0 ≤ 1-|u| by linarith)]
  have H : coneInvariantDensity u - π⁻¹ = ((1-s)-u)/(π*s) := by
    change (1-u)/(π*s)-π⁻¹ = _
    field_simp; ring
  rw [H,abs_div,abs_of_pos (mul_pos pi_pos hsp),div_le_iff₀ (mul_pos pi_pos hsp)]
  have hb := (abs_sub (1-s) u).trans (add_le_add_right hsmall |u|)
  have hπ : 4/π * |u| * (π*s) = 4 * |u| * s := by field_simp
  rw [hπ]
  nlinarith [mul_nonneg (abs_nonneg u) (sub_nonneg.mpr hspos)]

private theorem angle_cost_integrable : IntegrableOn angleCost (Ioo (-1:ℝ) 1) := by
  let μ := volume.restrict (Ioo (-1:ℝ) 1)
  have hW : Integrable coneInvariantDensity μ := by
    by_contra hn
    have hmass : (∫ u, coneInvariantDensity u ∂μ) = 1 := cone_angular_density_mass_one
    rw [integral_undef hn] at hmass
    exact zero_ne_one hmass
  have hI : Integrable inverseRootAbs μ := (integrableOn_inverseRootAbs_Icc zero_lt_one).mono_set Ioo_subset_Icc_self
  haveI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hM := (hI.const_mul (4/π)).add ((hW.add (integrable_const π⁻¹)).const_mul 8)
  apply hM.mono'
  · have H : Measurable angleCost := by unfold angleCost coneInvariantDensity inverseRootAbs; fun_prop
    exact H.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioo (a := (-1:ℝ)) (b := 1))] with u hu
    have hi : 0 ≤ inverseRootAbs u := inv_nonneg.mpr (sqrt_nonneg _)
    have hW₀ : 0 ≤ coneInvariantDensity u := div_nonneg (sub_nonneg.mpr hu.2.le) (by positivity)
    have hπ : 0 < π⁻¹ := inv_pos.mpr pi_pos
    change ‖|coneInvariantDensity u - π⁻¹| * (inverseRootAbs u)^3‖ ≤ 4/π*inverseRootAbs u + 8*(coneInvariantDensity u+π⁻¹)
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hi _))]
    by_cases hz : u = 0
    · subst u; simp [inverseRootAbs]; positivity
    have hs := sqrt_pos.mpr (abs_pos.mpr hz)
    have he : |u| * (inverseRootAbs u)^3 = inverseRootAbs u := by
      unfold inverseRootAbs
      nth_rw 1 [← Real.sq_sqrt (abs_nonneg u)]
      field_simp [hs.ne']
    by_cases hn : |u| ≤ 1/2
    · have hb := mul_le_mul_of_nonneg_right (density_near_zero hn) (pow_nonneg hi 3)
      rw [mul_assoc,he] at hb
      exact hb.trans (le_add_of_nonneg_right (mul_nonneg (by norm_num) (add_nonneg hW₀ hπ.le)))
    · have hh : 1/2 ≤ sqrt |u| := by nlinarith [Real.sq_sqrt (abs_nonneg u),hs.le]
      have ht : inverseRootAbs u ≤ 2 := by
        change (sqrt |u|)⁻¹ ≤ 2
        rw [inv_le_comm₀ hs (by norm_num : (0:ℝ)<2)]; norm_num; linarith
      have hpow : (inverseRootAbs u)^3 ≤ 8 := by simpa only [show (2:ℝ)^3 = 8 by norm_num] using pow_le_pow_left₀ hi ht 3
      have hdiff : |coneInvariantDensity u - π⁻¹| ≤ coneInvariantDensity u + π⁻¹ := by
        simpa only [abs_of_nonneg hW₀,abs_of_pos hπ] using abs_sub (coneInvariantDensity u) π⁻¹
      have H := mul_le_mul hdiff hpow (pow_nonneg hi _) (add_nonneg hW₀ hπ.le)
      rw [mul_comm _ 8] at H
      exact H.trans (le_add_of_nonneg_left (mul_nonneg (by positivity) hi))

variable {E : Type*} [NormedAddCommGroup E]

theorem Plane.uncontracted_fractional_angle_bound (diamond : Plane E) (ε : Evolution) :
    ∃ C ≥ (0:ℝ), ∀ (h : Height) {r : ℝ}, 0 < r →
      ‖∫ u in Ioo (-1:ℝ) 1, coneInvariantDensity u •
        ((r:ℂ)^3 * ((diamond.stableShellRoot ε h (r^2*u))⁻¹)^3)‖ ≤ C := by
  let I := Ioo (-1:ℝ) 1
  refine ⟨4/π + ∫ u in I, angleCost u, add_nonneg (by positivity) (integral_nonneg (fun u => mul_nonneg (abs_nonneg _) (pow_nonneg (inv_nonneg.mpr (sqrt_nonneg _)) 3))),?_⟩
  intro h r hr
  let V (u : ℝ) := (diamond.stableShellRoot ε h (r^2*u))⁻¹
  let B (u : ℝ) := (r:ℂ)^3*(V u)^3
  have hV : Continuous V := continuous_iff_continuousAt.mpr fun u =>
    (diamond.stable_shell_inverse_root_angular_derivative ε h r u).continuousAt
  have hB : Continuous B := continuous_const.mul (hV.pow 3)
  have hVb (u : ℝ) (hu : u ≠ 0) : ‖V u‖ ≤ r⁻¹*inverseRootAbs u :=
    diamond.stable_shell_inverse_root_angular_norm_le ε h hr hu
  have hbb (u : ℝ) (hu : u ≠ 0) : ‖B u‖ ≤ (inverseRootAbs u)^3 := by
    change ‖(r:ℂ)^3 * (V u)^3‖ ≤ _
    rw [norm_mul,norm_pow,norm_pow,Complex.norm_real,Real.norm_of_nonneg hr.le]
    calc
      _ ≤ r^3*(r⁻¹*inverseRootAbs u)^3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hVb u hu) 3) (by positivity)
      _ = _ := by field_simp
  have hder (u : ℝ) : HasDerivAt (fun u => (2*(r:ℂ))*V u) (B u) u := by
    convert (diamond.stable_shell_inverse_root_angular_derivative ε h r u).const_mul (2*(r:ℂ)) using 1
    dsimp only [B,V]; push_cast; rw [inv_pow]; ring
  have h0 : ‖∫ u in I, B u‖ ≤ 4 := by
    change ‖∫ u in Ioo (-1:ℝ) 1, B u‖ ≤ _
    rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hder u) (hB.intervalIntegrable _ _)]
    have hplus : ‖V 1‖ ≤ r⁻¹ := by simpa [inverseRootAbs] using hVb 1 one_ne_zero
    have hminus : ‖V (-1)‖ ≤ r⁻¹ := by simpa [inverseRootAbs] using hVb (-1) (by norm_num)
    apply (norm_sub_le _ _).trans
    simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg hr.le,show ‖(2:ℂ)‖ = 2 by norm_num]
    have he : 2*r*r⁻¹ = 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hplus (by positivity : 0 ≤ 2*r),mul_le_mul_of_nonneg_left hminus (by positivity : 0 ≤ 2*r)]
  let R (u : ℝ) := (coneInvariantDensity u - π⁻¹) • B u
  have hrmeas : Measurable R := by unfold R coneInvariantDensity; fun_prop
  have hn₀ : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by simp [ae_iff]
  have hnonzero := hn₀.filter_mono (ae_mono (Measure.restrict_le_self (μ := (volume : Measure ℝ)) (s := I)))
  have hbound : ∀ᵐ u ∂volume.restrict I, ‖R u‖ ≤ angleCost u := hnonzero.mono fun u hu => by
    rw [show ‖R u‖ = |coneInvariantDensity u-π⁻¹| * ‖B u‖ from norm_smul _ _]
    exact mul_le_mul_of_nonneg_left (hbb u hu) (abs_nonneg _)
  have hR := angle_cost_integrable.mono' hrmeas.aestronglyMeasurable hbound
  have hBi : IntegrableOn B I := (hB.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  change ‖∫ u in I, coneInvariantDensity u • B u‖ ≤ _
  have he (u : ℝ) : coneInvariantDensity u • B u = π⁻¹ • B u + R u := by simp [R,sub_smul]
  simp_rw [he]
  have hi₀ : IntegrableOn (fun u => π⁻¹ • B u) I := hBi.smul _
  rw [integral_add hi₀ hR,integral_smul]
  apply (norm_add_le _ _).trans (add_le_add _ ((norm_integral_le_integral_norm _).trans (integral_mono_ae hR.norm angle_cost_integrable hbound)))
  rw [norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ π⁻¹),div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left h0 (by positivity)

end UV.SectorPlane
