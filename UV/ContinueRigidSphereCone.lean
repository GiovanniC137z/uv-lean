import UV.ContinueRigidSphereSupport
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact Cartesian slices of the axial unit-ball cone. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Real Filter
open scoped ENNReal Interval Pointwise RealInnerProductSpace

namespace UV.ContinueRigidLaw

open UV.SectorPlane

private abbrev Cart := ℝ × (Fin 2 → ℝ)

private def splitCoord : Spatial ≃ᵐ Cart :=
  (EuclideanSpace.measurableEquiv (Fin 3)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0)

private theorem splitCoord_preserving : MeasurePreserving splitCoord :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).comp
    (EuclideanSpace.volume_preserving_measurableEquiv (Fin 3))

private def tailNorm (p : Fin 2 → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 2))‖

private theorem measurable_tailNorm : Measurable tailNorm :=
  continuous_norm.measurable.comp (PiLp.volume_preserving_toLp (Fin 2)).measurable

private theorem splitCoord_fst (x : Spatial) : (splitCoord x).1 = x 0 := rfl

private theorem splitCoord_norm (x : Spatial) :
    ‖x‖^2 = (splitCoord x).1^2 + tailNorm (splitCoord x).2^2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ, tailNorm, EuclideanSpace.norm_sq_eq,
    splitCoord_fst]
  simp only [Real.norm_eq_abs, sq_abs]
  rfl

private theorem basis_along_axis (a : Direction) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ Spatial, b 0 = (a : Spatial) := by
  have ho : Orthonormal ℝ ((({0} : Set (Fin 3))).restrict (fun _ ↦ (a : Spatial))) := by
    rw [orthonormal_iff_ite]
    intro i j
    have he : i = j := Subtype.ext (i.property.trans j.property.symm)
    simp [he, real_inner_self_eq_norm_sq, a.property]
  obtain ⟨b,hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq (by simp)
  exact ⟨b, hb 0 (mem_singleton _)⟩

/-- Angular coordinate along a spatial unit vector. -/
def axialProjection (a n : Direction) : ℝ := ⟪(a : Spatial), (n : Spatial)⟫

theorem continuous_axialProjection (a : Direction) : Continuous (axialProjection a) :=
  continuous_const.inner continuous_subtype_val

def axisCone (a : Direction) (t : ℝ) : Set Spatial :=
  {x | ‖x‖ < 1 ∧ t*‖x‖ < ⟪(a : Spatial), x⟫}

private theorem measurableSet_axisCone (a : Direction) (t : ℝ) :
    MeasurableSet (axisCone a t) :=
  (isOpen_lt continuous_norm continuous_const).measurableSet.inter
    (isOpen_lt (continuous_const.mul continuous_norm) (continuous_const.inner continuous_id)).measurableSet

private def cutOf (t : ℝ) (p : Cart) : Prop :=
  0 < p.1 ∧ p.1 < 1 ∧
    tailNorm p.2 < sqrt (min (1-p.1^2) ((1/t^2-1)*p.1^2))

private theorem measurableSet_cutOf (t : ℝ) : MeasurableSet {p | cutOf t p} := by
  have hz : Measurable (fun p : Cart ↦ p.1) := measurable_fst
  apply MeasurableSet.inter (measurableSet_lt measurable_const hz)
  apply MeasurableSet.inter (measurableSet_lt hz measurable_const)
  exact measurableSet_lt (measurable_tailNorm.comp measurable_snd)
    (continuous_sqrt.measurable.comp ((measurable_const.sub (hz.pow_const 2)).min
      ((hz.pow_const 2).const_mul _)))

private theorem cutOf_iff (t x r : ℝ) (ht : 0 < t)
    (hr : 0 ≤ r) (hR : 0 ≤ x) {z : ℝ} (h : x^2 = z^2+r^2) :
    (x < 1 ∧ t*x < z) ↔
      0 < z ∧ z < 1 ∧ r < sqrt (min (1-z^2) ((1/t^2-1)*z^2)) := by
  have ht₂ : 0 < t^2 := sq_pos_of_pos ht
  have he : (1/t^2-1)*z^2 = (z^2-t^2*z^2)/t^2 := by
    field_simp
  constructor
  · rintro ⟨hx, hz⟩
    have hzp : 0 < z := (mul_nonneg ht.le hR).trans_lt hz
    have hzx : z ≤ x := by
      apply (sq_le_sq₀ hzp.le hR).1
      nlinarith [sq_nonneg r]
    have h1 : r^2 < 1-z^2 := by
      have := (sq_lt_sq₀ hR zero_le_one).2 hx
      nlinarith
    have h2 : r^2 < (1/t^2-1)*z^2 := by
      rw [he, lt_div_iff₀ ht₂]
      have hh := (sq_lt_sq₀ (mul_nonneg ht.le hR) hzp.le).2 hz
      rw [mul_pow, h] at hh
      nlinarith
    have hm : r^2 < min (1-z^2) ((1/t^2-1)*z^2) := lt_min h1 h2
    exact ⟨hzp,hzx.trans_lt hx, (lt_sqrt hr).2 hm⟩
  · rintro ⟨hz,hz₁,hh⟩
    obtain ⟨h1,h2⟩ := lt_min_iff.mp ((lt_sqrt hr).1 hh)
    rw [he, lt_div_iff₀ ht₂] at h2
    refine ⟨(sq_lt_sq₀ hR zero_le_one).1 (by nlinarith), ?_⟩
    apply (sq_lt_sq₀ (mul_nonneg ht.le hR) hz.le).1
    rw [mul_pow, h]
    nlinarith

private theorem axisCone_volume_eq_cartesian (a : Direction) {t : ℝ} (ht : 0 < t) :
    volume (axisCone a t) = (volume : Measure Cart) {p | cutOf t p} := by
  obtain ⟨b,hb⟩ := basis_along_axis a
  have hbpres := b.measurePreserving_repr
  have hp := splitCoord_preserving.comp hbpres
  have he : (splitCoord ∘ b.repr) ⁻¹' {p | cutOf t p} = axisCone a t := by
    ext x
    have hi : (splitCoord (b.repr x)).1 = ⟪(a : Spatial), x⟫ := by
      rw [splitCoord_fst, b.repr_apply_apply, hb]
    have hn : ‖x‖^2 = (splitCoord (b.repr x)).1^2 + tailNorm (splitCoord (b.repr x)).2^2 := by
      rw [← splitCoord_norm, b.repr.norm_map]
    change cutOf t (splitCoord (b.repr x)) ↔ _
    rw [axisCone, mem_setOf_eq, ← hi, cutOf]
    exact (cutOf_iff t ‖x‖ _ ht (norm_nonneg _) (norm_nonneg _) hn).symm
  rw [← he, hp.measure_preimage (measurableSet_cutOf t).nullMeasurableSet]

private theorem capSlice_volume {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) (z : ℝ) :
    (volume : Measure (Fin 2 → ℝ)) ((Prod.mk z) ⁻¹' {p | cutOf t p}) =
      if 0 < z ∧ z < 1 then ENNReal.ofReal (π * min (1-z^2) ((1/t^2-1)*z^2))
        else 0 := by
  by_cases hz : 0 < z ∧ z < 1
  · rw [if_pos hz]
    let m := min (1-z^2) ((1/t^2-1)*z^2)
    have he : (Prod.mk z) ⁻¹' {p | cutOf t p} =
        (WithLp.toLp 2 : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2)) ⁻¹' Metric.ball 0 (sqrt m) := by
      ext x
      simp only [mem_preimage, mem_setOf_eq, cutOf, hz.1, hz.2, true_and, Metric.mem_ball,
        dist_zero_right, tailNorm, m]
    rw [he, (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
      Metric.isOpen_ball.measurableSet.nullMeasurableSet, EuclideanSpace.volume_ball_fin_two]
    have hnn : 0 ≤ m := by
      have ht₂ : t^2 ≤ 1 := by nlinarith [mul_nonneg ht.le (sub_nonneg.mpr ht₁.le)]
      have hz₂ : z^2 ≤ 1 := by nlinarith [mul_nonneg hz.1.le (sub_nonneg.mpr hz.2.le)]
      have hD : 0 ≤ 1/t^2-1 :=
        sub_nonneg.mpr ((le_div_iff₀ (sq_pos_of_pos ht)).2 (by simpa only [one_mul] using ht₂))
      exact le_min (sub_nonneg.mpr hz₂) (mul_nonneg hD (sq_nonneg z))
    change ENNReal.ofReal (sqrt m)^2 * ENNReal.ofReal π = ENNReal.ofReal (π*m)
    rw [← ENNReal.ofReal_pow (sqrt_nonneg _) 2, sq_sqrt hnn,
      ← ENNReal.ofReal_mul hnn, mul_comm m π]
  · rw [if_neg hz]
    have he : (Prod.mk z) ⁻¹' {p | cutOf t p} = ∅ := by
      ext x
      exact ⟨fun h ↦ False.elim (hz ⟨h.1,h.2.1⟩), fun h ↦ False.elim h⟩
    rw [he, measure_empty]

private theorem split_height (t : ℝ) (ht : 0 < t) {z : ℝ} (hz : 0 < z) :
    (1/t^2-1)*z^2 ≤ 1-z^2 ↔ z ≤ t := by
  have h : (1/t^2-1)*z^2 = (z^2-t^2*z^2)/t^2 := by field_simp
  rw [h, div_le_iff₀ (sq_pos_of_pos ht), ← sq_le_sq₀ hz.le ht.le]
  constructor <;> intro hc <;> linarith

private theorem cartesianCap_volume {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    (volume : Measure Cart) {p | cutOf t p} = ENNReal.ofReal ((2*π/3)*(1-t)) := by
  change ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) {p | cutOf t p} = _
  rw [Measure.prod_apply (measurableSet_cutOf t)]
  let F := fun z : ℝ ↦ π*((1/t^2-1)*z^2)
  let G := fun z : ℝ ↦ π*(1-z^2)
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hG : Continuous G := by dsimp [G]; fun_prop
  have htnn : 0 ≤ 1/t^2-1 := by
    have hs : t^2 ≤ 1 := by nlinarith [mul_nonneg ht.le (sub_nonneg.mpr ht₁.le)]
    apply sub_nonneg.mpr
    exact (le_div_iff₀ (sq_pos_of_pos ht)).2 (by simpa only [one_mul] using hs)
  have hFnn : ∀ z, 0 ≤ F z := fun z ↦ mul_nonneg pi_nonneg (mul_nonneg htnn (sq_nonneg z))
  have hGnn {z : ℝ} (hz : z ∈ Ioc t 1) : 0 ≤ G z := by
    have hp : 0 ≤ z := ht.le.trans hz.1.le
    have hs := (sq_le_sq₀ hp zero_le_one).2 hz.2
    exact mul_nonneg pi_nonneg (sub_nonneg.mpr (by simpa only [one_pow] using hs))
  have he (z : ℝ) :
      (volume : Measure (Fin 2 → ℝ)) (Prod.mk z ⁻¹' {p | cutOf t p}) =
      (Ioc 0 t).indicator (fun z ↦ ENNReal.ofReal (F z)) z +
        (Ioc t 1).indicator (fun z ↦ ENNReal.ofReal (G z)) z := by
    rw [capSlice_volume ht ht₁]
    by_cases h₀ : 0 < z
    · by_cases h₁ : z < 1
      · rw [if_pos ⟨h₀,h₁⟩]
        by_cases ht' : z ≤ t
        · have hn : z ∉ Ioc t 1 := fun hx ↦ (not_lt.mpr ht') hx.1
          rw [indicator_of_mem (show z ∈ Ioc 0 t from ⟨h₀,ht'⟩), indicator_of_notMem hn,
            add_zero, min_eq_right ((split_height t ht h₀).2 ht')]
        · have hn : z ∉ Ioc 0 t := fun hx ↦ ht' hx.2
          rw [indicator_of_notMem hn, indicator_of_mem
            (show z ∈ Ioc t 1 from ⟨lt_of_not_ge ht',h₁.le⟩), zero_add,
            min_eq_left (le_of_not_ge (fun h ↦ ht' ((split_height t ht h₀).1 h)))]
      · rw [if_neg (fun h ↦ h₁ h.2)]
        have hₙ : z ∉ Ioc 0 t := fun hz ↦ h₁ (hz.2.trans_lt ht₁)
        rw [indicator_of_notMem hₙ, zero_add]
        by_cases h₁' : z ≤ 1
        · have heq : z = 1 := h₁'.antisymm (le_of_not_gt h₁)
          subst z
          rw [indicator_of_mem (show (1:ℝ) ∈ Ioc t 1 from ⟨ht₁,le_rfl⟩)]
          simp [G]
        · rw [indicator_of_notMem (fun hz : z ∈ Ioc t 1 ↦ h₁' hz.2)]
    · rw [if_neg (fun h ↦ h₀ h.1), indicator_of_notMem (fun hz : z ∈ Ioc 0 t ↦ h₀ hz.1),
        indicator_of_notMem (fun hz : z ∈ Ioc t 1 ↦ h₀ (ht.trans hz.1)), add_zero]
  simp_rw [he]
  rw [lintegral_add_left (hF.measurable.ennreal_ofReal.indicator measurableSet_Ioc),
    lintegral_indicator measurableSet_Ioc, lintegral_indicator measurableSet_Ioc]
  have hFi := (hF.intervalIntegrable (μ := volume) 0 t).1
  have hGi := (hG.intervalIntegrable (μ := volume) t 1).1
  rw [← ofReal_integral_eq_lintegral_ofReal hFi (ae_of_all _ hFnn),
    ← ofReal_integral_eq_lintegral_ofReal hGi ((ae_restrict_iff' measurableSet_Ioc).2
      (ae_of_all _ fun _ hz ↦ hGnn hz)),
    ← ENNReal.ofReal_add (integral_nonneg hFnn)
      (integral_nonneg_of_ae ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun _ hz ↦ hGnn hz))),
    ← intervalIntegral.integral_of_le ht.le, ← intervalIntegral.integral_of_le ht₁.le]
  congr 1
  have hpow : Continuous (fun z : ℝ ↦ z^2) := by fun_prop
  dsimp [F,G]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) (hpow.intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_pow, integral_pow]
  simp only [Nat.reduceAdd, Nat.cast_ofNat, zero_pow (by decide : 3 ≠ 0), sub_zero, one_pow, smul_eq_mul]
  field_simp [ht.ne']
  ring

/-- The Cartesian cone cut has exact volume `2π(1-t)/3`. -/
theorem axisCone_volume (a : Direction) {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    volume (axisCone a t) = ENNReal.ofReal ((2*π/3)*(1-t)) := by
  rw [axisCone_volume_eq_cartesian a ht, cartesianCap_volume ht ht₁]

end UV.ContinueRigidLaw
