import UV.ContinueNormalHolonomyMagnetic
import UV.ContinueNormalHolonomyGamma
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! Transfer of scalar normal heat asymptotics to the bare proper-time
integral, with the positive short-duration coefficient explicit. -/

noncomputable section

open Real Set Filter MeasureTheory
open scoped Topology

namespace UV.ContinueNormalHolonomy

/-- A positive scaled limit with nonnegative exponent implies divergence
of the bare proper-time integral at zero. -/
theorem normalProperTime_not_integrable_of_positive_limit {F : ℝ → ℝ} {α c T : ℝ}
    (hα : 0 ≤ α) (hc : 0 < c) (hT : 0 < T)
    (hlim : Tendsto (fun t : ℝ => t ^ α * F t) (𝓝[>] 0) (𝓝 c)) :
    ¬ IntegrableOn (fun t : ℝ => F t / t) (Ioc 0 T) := by
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, c / 2 < t ^ α * F t :=
    hlim.eventually (Ioi_mem_nhds (by linarith))
  obtain ⟨η, hη, hnear⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  let ε := min η (min 1 T)
  have hε : 0 < ε := lt_min hη (lt_min zero_lt_one hT)
  intro hi
  have hi' : IntegrableOn (fun t : ℝ => F t / t) (Ioo 0 ε) := by
    apply hi.mono_set
    intro t ht
    exact ⟨ht.1, ht.2.le.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hcomp : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Ioo 0 ε) := by
    apply (hi'.const_mul (2 / c)).mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have htin : t ∈ Ioo 0 η := ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
    have hlt : c / 2 < t ^ α * F t := hnear htin
    have hpos : 0 < F t := by
      by_contra! hn
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg ht.1.le _) hn))
        ((half_pos hc).trans hlt)
    have hpow : t ^ α ≤ 1 := by
      have ht1 := ht.2.le.trans ((min_le_right _ _).trans (min_le_left _ _))
      simpa only [Real.one_rpow] using Real.rpow_le_rpow ht.1.le ht1 hα
    have hF : c / 2 ≤ F t :=
      hlt.le.trans (mul_le_of_le_one_left hpos.le hpow)
    rw [Real.rpow_neg_one, Real.norm_of_nonneg (inv_nonneg.mpr ht.1.le)]
    rw [← mul_div_assoc, ← one_div t]
    apply div_le_div_of_nonneg_right _ ht.1.le
    have h := mul_le_mul_of_nonneg_left hF (by positivity : 0 ≤ (2 : ℝ) / c)
    convert h using 1
    field_simp [hc.ne']
  exact (lt_irrefl (-1 : ℝ)) ((intervalIntegral.integrableOn_Ioo_rpow_iff hε).mp hcomp)

/-- The exact positive winding coefficient yields the logarithmic-determinant
obstruction whenever the relative radial heat trace has the asserted limit. -/
theorem quarticRelativeProperTime_not_integrable {D : ℝ → ℝ} {a T : ℝ}
    (ha : ∀ m : ℤ, a ≠ (m : ℝ)) (hT : 0 < T)
    (hlim : Tendsto (fun t : ℝ => t ^ (3 / 8 : ℝ) * D t) (𝓝[>] 0)
      (𝓝 (quarticHolonomyConstant a))) :
    ¬IntegrableOn (fun t : ℝ => D t / t) (Ioc 0 T) :=
  normalProperTime_not_integrable_of_positive_limit (by norm_num)
    (quarticHolonomyConstant_positive ha) hT hlim

/-- The prepared scalar magnetic coefficient diverges if the prepared
normal trace tends to its positive zero-duration normalization. -/
theorem preparedMagneticProperTime_not_integrable {P : ℝ → ℝ} {m T : ℝ}
    (hm : 0 < m) (hT : 0 < T) (hlim : Tendsto P (𝓝[>] 0) (𝓝 m)) :
    ¬ IntegrableOn (fun t : ℝ => scalarMagneticQuadratic * P t / t) (Ioc 0 T) := by
  have hq : 0 < scalarMagneticQuadratic := by unfold scalarMagneticQuadratic; positivity
  apply normalProperTime_not_integrable_of_positive_limit
    (F := fun t => scalarMagneticQuadratic * P t) (α := 0)
    (show 0 ≤ (0 : ℝ) by norm_num) (mul_pos hq hm) hT
  simpa only [Real.rpow_zero, one_mul] using hlim.const_mul scalarMagneticQuadratic

/-- The normal counting factor (O(t^{-1})) and the path coefficient
factor (O(t^{2n-2})) suffice for each higher magnetic order. -/
theorem higherMagneticProperTime_integrable {F : ℝ → ℝ} {C T : ℝ}
    {n : ℕ} (hn : 2 ≤ n) (hT : 0 < T) (hF : Measurable F)
    (hb : ∀ t ∈ Ioo 0 T, |F t| ≤ C * t ^ ((2 : ℝ) * n - 3)) :
    IntegrableOn (fun t : ℝ => F t / t) (Ioo 0 T) := by
  have hβ : -1 < (2 : ℝ) * n - 4 := by exact_mod_cast (show (-1 : ℤ) < 2 * n - 4 by omega)
  have hi := (intervalIntegral.integrableOn_Ioo_rpow_iff hT).mpr hβ
  apply (hi.const_mul C).mono' (hF.div measurable_id).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  change ‖F t / t‖ ≤ C * t ^ ((2 : ℝ) * n - 4)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos ht.1]
  apply (div_le_div_of_nonneg_right (hb t ht) ht.1.le).trans_eq
  rw [mul_div_assoc]
  congr 1
  calc
    _ = t ^ ((2 : ℝ) * n - 3) / t ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_sub ht.1]; congr 1; ring

/-- The rescaled radial profile yields the exact relative heat trace
coefficient once the bridge representation has its pointwise limit
and an integrable domination. -/
theorem quarticRelativeTrace_limit_of_radial_profile {a : ℝ} {D : ℝ → ℝ}
    {F : ℝ → ℝ → ℝ} {bound : ℝ → ℝ}
    (hrepresentation : ∀ᶠ t : ℝ in 𝓝[>] 0,
      t ^ (3 / 8 : ℝ) * D t =
        (Real.sqrt (4 * Real.pi))⁻¹ * ∫ x in Ioi 0, F t x)
    (hF : ∀ᶠ t : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (F t) ((volume : Measure ℝ).restrict (Ioi 0)))
    (hbound : ∀ᶠ t : ℝ in 𝓝[>] 0,
      ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioi 0)), ‖F t x‖ ≤ bound x)
    (hi : IntegrableOn bound (Ioi 0))
    (hpoint : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioi 0)),
      Tendsto (fun t => F t x) (𝓝[>] 0) (𝓝 (relativeNormalTheta (x ^ (8 : ℕ))⁻¹ a))) :
    Tendsto (fun t : ℝ => t ^ (3 / 8 : ℝ) * D t) (𝓝[>] 0)
      (𝓝 (quarticHolonomyConstant a)) := by
  have h := (tendsto_integral_filter_of_dominated_convergence bound hF hbound hi hpoint).const_mul
    (Real.sqrt (4 * Real.pi))⁻¹
  rw [← integral_const_mul, quarticHolonomyProfile_integral] at h
  exact h.congr' (hrepresentation.mono fun _ ht => ht.symm)

end UV.ContinueNormalHolonomy
