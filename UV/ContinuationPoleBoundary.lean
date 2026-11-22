import UV.ContinuationSectorPlane
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Boundary tests in the real invariant denominator of a single
fixed virtual-carrier line. The variable here is (D), with the positive
height left in place until after integration. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Filter Set
open scoped Topology NNReal

def polePoisson (height D : ℝ) : ℝ := height / (D ^ 2 + height ^ 2)

def polePV (height D : ℝ) : ℝ := D / (D ^ 2 + height ^ 2)

/-- Keep the exact unnormalized Poisson mass π in the invariant D variable. -/
theorem pole_poisson_scaling (f : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ D : ℝ, polePoisson ε D * f D) =
      ∫ t : ℝ, (1 + t ^ 2)⁻¹ * f (ε * t) := by
  have hs := Measure.integral_comp_mul_left (fun D => polePoisson ε D * f D) ε
  rw [abs_of_pos (inv_pos.mpr hε), smul_eq_mul] at hs
  have hp (t : ℝ) : polePoisson ε (ε * t) = (1 + t ^ 2)⁻¹ * ε⁻¹ := by
    unfold polePoisson
    have h₁ : 1 + t ^ 2 ≠ 0 := by positivity
    have h₂ : (ε * t) ^ 2 + ε ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  change (∫ t : ℝ, polePoisson ε (ε * t) * f (ε * t)) =
    ε⁻¹ * ∫ D : ℝ, polePoisson ε D * f D at hs
  simp only [hp] at hs
  simp_rw [mul_comm ((1 + _ ^ 2)⁻¹) ε⁻¹, mul_assoc] at hs
  rw [integral_const_mul] at hs
  exact (mul_left_cancel₀ (inv_ne_zero hε.ne') hs).symm

theorem pole_poisson_test_limit {f : ℝ → ℝ}
    (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun ε : ℝ => ∫ D : ℝ, polePoisson ε D * f D)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi * f 0)) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ)) (μ := volume)
    (F := fun ε t : ℝ => (1 + t ^ 2)⁻¹ * f (ε * t))
    (f := fun t : ℝ => (1 + t ^ 2)⁻¹ * f 0)
    (fun t => C * (1 + t ^ 2)⁻¹) ?_ ?_
    (integrable_inv_one_add_sq.const_mul C) ?_
  · rw [integral_mul_const, integral_univ_inv_one_add_sq] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (pole_poisson_scaling f hε).symm
  · exact Eventually.of_forall fun ε =>
      (((measurable_const.add (measurable_id.pow_const 2)).inv).mul
        (hf.measurable.comp (measurable_const.mul measurable_id))).aestronglyMeasurable
  · exact Eventually.of_forall fun _ => Eventually.of_forall fun t => by
      change ‖(1 + t ^ 2)⁻¹ * f (_ * t)‖ ≤ C * (1 + t ^ 2)⁻¹
      rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ (1 + t ^ 2)⁻¹), mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC _) (by positivity)
  · exact Eventually.of_forall fun t => by
      have ht : Tendsto (fun ε : ℝ => ε * t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have ht0 := (continuous_id.mul (continuous_const (y := t))).continuousAt
          (x := (0 : ℝ))
        simpa using ht0.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa only [mul_comm] using (hf.continuousAt.tendsto.comp ht).const_mul (1 + t ^ 2)⁻¹

/-- Symmetric differentiation of a test at the pole gives an absolutely
integrable representative of the principal value under the stated test bounds. -/
def symmetricTest (f : ℝ → ℝ) (D : ℝ) : ℝ := (f D - f (-D)) / D

theorem symmetric_test_integrable {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hi : Integrable f) :
    IntegrableOn (symmetricTest f) (Ioi (0 : ℝ)) := by
  have hmeas : Measurable (symmetricTest f) := by
    unfold symmetricTest
    exact (hf.continuous.measurable.sub (hf.continuous.measurable.comp measurable_neg)).div
      measurable_id
  have ha : IntegrableOn (symmetricTest f) (Ioc (0 : ℝ) 1) := by
    apply (integrableOn_const (C := (2 * (L : ℝ))) (by simp)).mono' hmeas.aestronglyMeasurable
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun D hD => ?_
    have hDp : 0 < D := hD.1
    have hLip := hf.norm_sub_le D (-D)
    rw [show D - -D = 2 * D by ring, norm_mul, Real.norm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)),
      Real.norm_of_nonneg hDp.le] at hLip
    unfold symmetricTest
    rw [norm_div, Real.norm_of_nonneg hDp.le, div_le_iff₀ hDp]
    linarith
  have hb : IntegrableOn (symmetricTest f) (Ioi (1 : ℝ)) := by
    have hi' := hi.comp_neg
    refine ((hi.norm.add hi'.norm).integrableOn (s := Ioi 1)).mono'
      hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun D hD => ?_
    have hD₀ : 0 < D := zero_lt_one.trans hD
    unfold symmetricTest
    rw [norm_div, Real.norm_of_nonneg hD₀.le]
    exact ((div_le_self (norm_nonneg _) hD.le).trans (norm_sub_le _ _))
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact ha.union hb

theorem pole_pv_symmetric_test_limit {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hi : Integrable f) :
    Tendsto (fun ε : ℝ => ∫ D in Ioi (0 : ℝ), polePV ε D * (f D - f (-D)))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ D in Ioi (0 : ℝ), symmetricTest f D)) := by
  have hY : Measurable (symmetricTest f) := by
    unfold symmetricTest
    exact (hf.continuous.measurable.sub (hf.continuous.measurable.comp measurable_neg)).div
      measurable_id
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ)) (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun ε D : ℝ => (D ^ 2 / (D ^ 2 + ε ^ 2)) * symmetricTest f D)
    (f := symmetricTest f) (fun D => ‖symmetricTest f D‖) ?_ ?_
    (symmetric_test_integrable hf hi).norm ?_
  · refine h.congr' (Eventually.of_forall fun ε => integral_congr_ae ?_)
    change ∀ᵐ D ∂volume.restrict (Ioi (0 : ℝ)),
      (D ^ 2 / (D ^ 2 + ε ^ 2)) * symmetricTest f D = polePV ε D * (f D - f (-D))
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun D hD => ?_
    have hDp : 0 < D := hD
    have hden : D ^ 2 + ε ^ 2 ≠ 0 := by positivity
    unfold polePV symmetricTest
    field_simp
  · exact Eventually.of_forall fun ε =>
      (((measurable_id.pow_const 2).div ((measurable_id.pow_const 2).add measurable_const)).mul
        hY).aestronglyMeasurable
  · refine Eventually.of_forall fun ε => ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun D hD => ?_
    have hDp : 0 < D := hD
    have hden : 0 < D ^ 2 + ε ^ 2 := by positivity
    rw [norm_mul, Real.norm_of_nonneg (div_nonneg (sq_nonneg _) hden.le)]
    exact mul_le_of_le_one_left (norm_nonneg _) ((div_le_one hden).2 (le_add_of_nonneg_right (sq_nonneg _)))
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun D hD => ?_
    have hDp : 0 < D := hD
    have h := ((continuous_const (y := D ^ 2)).div (by fun_prop :
      Continuous (fun ε : ℝ => D ^ 2 + ε ^ 2)) (fun ε => by positivity :
      ∀ ε : ℝ, D ^ 2 + ε ^ 2 ≠ 0)).continuousAt (x := (0 : ℝ))
    change ContinuousAt (fun ε : ℝ => D ^ 2 / (D ^ 2 + ε ^ 2)) 0 at h
    have ht : Tendsto (fun ε : ℝ => D ^ 2 / (D ^ 2 + ε ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      simpa [hDp.ne'] using h.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using ht.mul_const (symmetricTest f D)

/-- At positive height, the complete absolute integral of the odd
regularizer is equal to its symmetric test expression. -/
theorem pole_pv_test_symmetrize {f : ℝ → ℝ} (hi : Integrable f)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ D : ℝ, polePV ε D * f D) =
      ∫ D in Ioi (0 : ℝ), polePV ε D * (f D - f (-D)) := by
  have hnorm (D : ℝ) : ‖polePV ε D‖ ≤ (2 * ε)⁻¹ := by
    have hden : 0 < D ^ 2 + ε ^ 2 := by positivity
    have hε2 : 0 < 2 * ε := by positivity
    unfold polePV
    rw [norm_div, Real.norm_of_nonneg hden.le, Real.norm_eq_abs, ← one_div,
      div_le_div_iff₀ hden hε2, one_mul]
    nlinarith [sq_nonneg (|D| - ε), sq_abs D]
  have hm : Measurable (polePV ε) :=
    measurable_id.div ((measurable_id.pow_const 2).add measurable_const)
  have hprod : Integrable (fun D => polePV ε D * f D) :=
    (hi.norm.const_mul (2 * ε)⁻¹).mono' (hm.aestronglyMeasurable.mul hi.aestronglyMeasurable)
      (Eventually.of_forall fun D => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hnorm D) (norm_nonneg _))
  have hprod' : Integrable (fun D => polePV ε D * f (-D)) :=
    (hi.comp_neg.norm.const_mul (2 * ε)⁻¹).mono'
      (hm.aestronglyMeasurable.mul hi.comp_neg.aestronglyMeasurable)
      (Eventually.of_forall fun D => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hnorm D) (norm_nonneg _))
  rw [← integral_add_compl measurableSet_Ioi hprod, compl_Ioi, ← neg_zero,
    ← integral_comp_neg_Ioi, neg_zero]
  simp_rw [polePV, neg_sq, neg_div, neg_mul, integral_neg]
  change (∫ D in Ioi (0 : ℝ), polePV ε D * f D) -
      (∫ D in Ioi (0 : ℝ), polePV ε D * f (-D)) = _
  rw [← integral_sub hprod.integrableOn hprod'.integrableOn]
  exact integral_congr_ae (Eventually.of_forall fun D => by unfold polePV; ring)

theorem pole_pv_test_limit {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hi : Integrable f) :
    Tendsto (fun ε : ℝ => ∫ D : ℝ, polePV ε D * f D)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ D in Ioi (0 : ℝ), symmetricTest f D)) := by
  refine (pole_pv_symmetric_test_limit hf hi).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (pole_pv_test_symmetrize hi hε).symm

/-- The two scalar factors in the fixed-carrier boundary converge with
their distinct sector and evolution signs on the same locked diamond. -/
theorem Plane.fixed_pole_test_limits {E : Type*} [NormedAddCommGroup E]
    (diamond : Plane E) (ε : Evolution) {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hi : Integrable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun height : ℝ =>
      (sectorSign diamond.s * ∫ D, polePoisson height D * f D,
        evolutionSign ε * ∫ D, polePV height D * f D))
      (𝓝[>] (0 : ℝ))
      (𝓝 (sectorSign diamond.s * (Real.pi * f 0),
        evolutionSign ε * ∫ D in Ioi (0 : ℝ), symmetricTest f D)) :=
  ((pole_poisson_test_limit hf.continuous C hC).const_mul (sectorSign diamond.s)).prodMk_nhds
    ((pole_pv_test_limit hf hi).const_mul (evolutionSign ε))

end UV.SectorPlane
