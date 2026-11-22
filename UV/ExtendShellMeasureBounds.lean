import UV.FurtherCoincidentShell
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! Uniform positive-ray shell bounds for transverse integration. The
bound retains only one inverse power of the positive-shell frequency,
so the massless threshold is locally integrable in three spatial dimensions. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Filter Set
open scoped ENNReal Topology

theorem pole_poisson_integrable_pos_height {h : ℝ} (hh : 0 < h) :
    Integrable (polePoisson h) := by
  simpa only [polePoisson, oppositeShellKernel, div_eq_mul_inv] using
    (opposite_shell_kernel_integrable hh).const_mul h

theorem pole_poisson_integral_pi {h : ℝ} (hh : 0 < h) : (∫ D, polePoisson h D) = Real.pi := by
  simpa only [mul_one, integral_univ_inv_one_add_sq] using pole_poisson_scaling (fun _ => 1) hh

private theorem pole_poisson_le_inv_abs {h : ℝ} (hh : 0 < h) {D : ℝ} (hD : D ≠ 0) :
    polePoisson h D ≤ (2 * |D|)⁻¹ := by
  have hp : 0 < 2 * |D| := mul_pos two_pos (abs_pos.mpr hD)
  rw [polePoisson, ← one_div, div_le_div_iff₀ (by positivity) hp, one_mul]
  nlinarith [sq_nonneg (|D| - h), sq_abs D]

private theorem weighted_positive_ray_poisson_integrable {h : ℝ} (hh : 0 < h) (κ : ℝ) :
    IntegrableOn (fun r : ℝ => 2 * r * polePoisson h (r ^ 2 - κ ^ 2)) (Ioi 0) := by
  let D : ℝ → ℝ := fun r => r ^ 2 - κ ^ 2
  have hder (r : ℝ) (_ : r ∈ Ioi (0 : ℝ)) :
      HasDerivWithinAt D (2 * r) (Ioi 0) r := by
    simpa [D] using (((hasDerivAt_id r).pow 2).sub_const (κ ^ 2)).hasDerivWithinAt
  have hinj : InjOn D (Ioi 0) := by
    apply StrictMonoOn.injOn
    intro a ha b hb hab
    exact sub_lt_sub_right ((sq_lt_sq₀ ha.le hb.le).2 hab) _
  have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    hder hinj (polePoisson h)).mp (pole_poisson_integrable_pos_height hh).integrableOn
  apply hi.congr_fun (fun r hr => ?_) measurableSet_Ioi
  have hr' : 0 < r := hr
  dsimp [D]
  rw [abs_of_pos (by positivity : 0 < 2 * r)]

private theorem weighted_positive_ray_poisson_bound {h : ℝ} (hh : 0 < h) (κ : ℝ) :
    (∫ r in Ioi (0 : ℝ), 2 * r * polePoisson h (r ^ 2 - κ ^ 2)) ≤ Real.pi := by
  rw [positive_ray_shell_change κ (polePoisson h), ← pole_poisson_integral_pi hh]
  exact setIntegral_le_integral (pole_poisson_integrable_pos_height hh)
    (Eventually.of_forall fun D => pole_poisson_nonneg hh.le D)

private theorem ray_poisson_integrable_with_test {h : ℝ} (hh : 0 < h) (κ : ℝ)
    {f : ℝ → ℝ} (hi : IntegrableOn f (Ioi (0 : ℝ))) :
    IntegrableOn (fun r => polePoisson h (r ^ 2 - κ ^ 2) * f r) (Ioi (0 : ℝ)) := by
  have hc : Continuous (fun r : ℝ => polePoisson h (r ^ 2 - κ ^ 2)) :=
    continuous_const.div
      ((((continuous_id.pow 2).sub continuous_const).pow 2).add continuous_const)
      (fun _ => by positivity)
  exact hi.bdd_mul hc.aestronglyMeasurable ⟨h⁻¹, fun r => by
    rw [Real.norm_of_nonneg (pole_poisson_nonneg hh.le _)]
    exact pole_poisson_le_inv_height hh _⟩

/-- Uniform axial mass bound for every positive height. Separating the
low axial ray before coarea avoids the artificial singularity of the
inverse derivative at the ray's endpoint. -/
theorem positive_ray_poisson_test_norm_le {κ h : ℝ} (hκ : 0 < κ) (hh : 0 < h)
    {f : ℝ → ℝ} (hi : IntegrableOn f (Ioi (0 : ℝ)))
    (C : ℝ) (hC : ∀ r, ‖f r‖ ≤ C) :
    ‖∫ r in Ioi (0 : ℝ), polePoisson h (r ^ 2 - κ ^ 2) * f r‖ ≤
      (Real.pi + 1 / 3) * C / κ := by
  have hC₀ : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  let s := Ioc (0 : ℝ) (κ / 2)
  let t := Ioi (κ / 2)
  let F (r : ℝ) := polePoisson h (r ^ 2 - κ ^ 2) * f r
  let G (r : ℝ) := (C / κ) * (2 * r * polePoisson h (r ^ 2 - κ ^ 2))
  have hs : MeasurableSet s := measurableSet_Ioc
  have ht : MeasurableSet t := measurableSet_Ioi
  have hsub : t ⊆ Ioi (0 : ℝ) := fun _ hr => (half_pos hκ).trans hr
  have hFi := ray_poisson_integrable_with_test hh κ hi
  have hsi : IntegrableOn F s := hFi.mono_set Ioc_subset_Ioi_self
  have hti : IntegrableOn F t := hFi.mono_set hsub
  have hGi : IntegrableOn G (Ioi (0 : ℝ)) :=
    (weighted_positive_ray_poisson_integrable hh κ).const_mul _
  have hun : s ∪ t = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi (half_pos hκ).le
  have hdis : Disjoint s t := disjoint_left.mpr fun r hr hr' => not_lt_of_ge hr.2 hr'
  have hlow : ‖∫ r in s, F r‖ ≤ C / (3 * κ) := by
    have hb : ‖∫ r in s, F r‖ ≤ ∫ r in s, 2 * C / (3 * κ ^ 2) := by
      apply norm_integral_le_of_norm_le (integrable_const _)
      rw [ae_restrict_iff' hs]
      refine Eventually.of_forall fun r hr => ?_
      have hrs : 0 < r ∧ r ≤ κ / 2 := hr
      have hk2 : 0 < κ ^ 2 := sq_pos_of_pos hκ
      have hsq := (sq_le_sq₀ hrs.1.le (half_pos hκ).le).2 hrs.2
      have hD₀ : 0 < κ ^ 2 - r ^ 2 := by nlinarith
      have hD : r ^ 2 - κ ^ 2 ≠ 0 := (sub_neg_of_lt (sub_pos.mp hD₀)).ne
      have hP : polePoisson h (r ^ 2 - κ ^ 2) ≤ 2 / (3 * κ ^ 2) := by
        apply (pole_poisson_le_inv_abs hh hD).trans
        rw [← one_div, abs_of_neg (sub_neg_of_lt (sub_pos.mp hD₀)),
          div_le_div_iff₀ (by linarith) (by positivity)]
        nlinarith
      dsimp [F]
      rw [abs_mul, abs_of_nonneg (pole_poisson_nonneg hh.le _)]
      exact (mul_le_mul hP (hC r) (norm_nonneg _) (by positivity)).trans_eq (by ring)
    rw [integral_const, measureReal_def, Measure.restrict_apply_univ,
      ← measureReal_def] at hb
    dsimp [s] at hb
    rw [Real.volume_real_Ioc_of_le (half_pos hκ).le, sub_zero] at hb
    convert hb using 1
    field_simp
  have hhigh : ‖∫ r in t, F r‖ ≤ Real.pi * C / κ := by
    have hb : ‖∫ r in t, F r‖ ≤ ∫ r in t, G r := by
      apply norm_integral_le_of_norm_le (hGi.mono_set hsub)
      rw [ae_restrict_iff' ht]
      refine Eventually.of_forall fun r hr => ?_
      have hr' : κ / 2 < r := hr
      dsimp [F, G]
      rw [abs_mul, abs_of_nonneg (pole_poisson_nonneg hh.le _)]
      have ha : C ≤ (C / κ) * (2 * r) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
        exact mul_le_mul_of_nonneg_left (by linarith) hC₀
      calc
        _ ≤ polePoisson h (r ^ 2 - κ ^ 2) * C :=
          mul_le_mul_of_nonneg_left (hC r) (pole_poisson_nonneg hh.le _)
        _ ≤ polePoisson h (r ^ 2 - κ ^ 2) * ((C / κ) * (2 * r)) :=
          mul_le_mul_of_nonneg_left ha (pole_poisson_nonneg hh.le _)
        _ = _ := by ring
    calc
      _ ≤ ∫ r in t, G r := hb
      _ ≤ ∫ r in Ioi (0 : ℝ), G r := by
        apply setIntegral_mono_set hGi ?_ (Eventually.of_forall hsub)
        change ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ G r
        rw [ae_restrict_iff' measurableSet_Ioi]
        refine Eventually.of_forall fun r hr => ?_
        have hr' : 0 < r := hr
        dsimp [G]
        exact mul_nonneg (div_nonneg hC₀ hκ.le)
          (mul_nonneg (by positivity) (pole_poisson_nonneg hh.le _))
      _ ≤ Real.pi * C / κ := by
        dsimp [G]
        rw [integral_const_mul, mul_comm Real.pi, div_mul_eq_mul_div]
        simpa only [div_mul_eq_mul_div] using
          mul_le_mul_of_nonneg_left (weighted_positive_ray_poisson_bound hh κ)
            (div_nonneg hC₀ hκ.le)
  change ‖∫ r in Ioi (0 : ℝ), F r‖ ≤ _
  rw [← hun, setIntegral_union hdis ht hsi hti]
  exact (norm_add_le _ _).trans ((add_le_add hlow hhigh).trans_eq (by field_simp; ring))

/-- The inverse-momentum majorant for regular positive axial shells is
locally integrable in all three transverse spatial components. -/
theorem integrableOn_inv_norm_closedBall_spatial (R : ℝ) :
    IntegrableOn (fun p : Spatial => ‖p‖⁻¹) (Metric.closedBall 0 R) := by
  rw [← integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
  let F (r : ℝ) := (Iic R).indicator (fun r : ℝ => r⁻¹) r
  have he : (Metric.closedBall (0 : Spatial) R).indicator
      (fun p : Spatial => ‖p‖⁻¹) = fun p : Spatial => F ‖p‖ := by
    funext p
    by_cases hp : ‖p‖ ≤ R <;> simp [F, hp]
  rw [he]
  apply (integrable_fun_norm_addHaar (E := Spatial) volume).mpr
  rw [finrank_euclideanSpace, Fintype.card_fin]
  have hmeq : (fun r : ℝ => r ^ (3 - 1) • F r) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun r : ℝ => (Iic R).indicator id r) := by
    change ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      r ^ (3 - 1) • F r = (Iic R).indicator id r
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun r hr => ?_
    have hr' : 0 < r := hr
    by_cases hR : r ≤ R
    · simp [F, hR, smul_eq_mul, pow_two, hr'.ne']
    · simp [F, hR]
  refine (integrable_congr hmeq).mpr ?_
  change Integrable ((Iic R).indicator id) (volume.restrict (Ioi (0 : ℝ)))
  rw [integrable_indicator_iff measurableSet_Iic]
  change Integrable id ((volume.restrict (Ioi (0 : ℝ))).restrict (Iic R))
  rw [Measure.restrict_restrict measurableSet_Iic, inter_comm, Ioi_inter_Iic]
  exact continuous_id.integrableOn_Ioc

end UV.SectorPlane
