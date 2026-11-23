import UV.VerifyVisitCodimension
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Positive angular measure and the radial power test in the actual
normal Euclidean space. The angular variables are unit vectors. -/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace UV.ContinueVisitNormalPolar

open UV.VerifyVisitCodimension

abbrev NormalUnit (n : ℕ) := sphere (0 : NormalCoordinates n) 1
abbrev PositiveRadius := Ioi (0 : ℝ)

def normalSphereMeasure (n : ℕ) : Measure (NormalUnit n) :=
  (volume : Measure (NormalCoordinates n)).toSphere

instance (n : ℕ) : IsFiniteMeasure (normalSphereMeasure n) := by
  unfold normalSphereMeasure
  infer_instance

/-- Every nonempty open patch of genuine unit directions has positive
angular measure. The punctured-space polar homeomorphism lifts the
patch to a nonempty open set of positive Lebesgue measure. -/
theorem normal_sphere_open_ne_zero (n : ℕ) {U : Set (NormalUnit n)}
    (hU : IsOpen U) (hne : U.Nonempty) : normalSphereMeasure n U ≠ 0 := by
  let E := NormalCoordinates n
  let e := homeomorphUnitSphereProd E
  let V : Set (NormalUnit n × PositiveRadius) := U ×ˢ (univ : Set PositiveRadius)
  let W := e ⁻¹' V
  let C := Subtype.val '' W
  have hV : IsOpen V := hU.prod isOpen_univ
  have hW : IsOpen W := hV.preimage e.continuous
  have hC : IsOpen C := (isOpen_compl_singleton : IsOpen ({(0 : E)} : Set E)ᶜ)
    |>.isOpenMap_subtype_val _ hW
  obtain ⟨u, hu⟩ := hne
  let r : PositiveRadius := ⟨1, mem_Ioi.mpr one_pos⟩
  have hv : (u, r) ∈ V := ⟨hu, mem_univ _⟩
  have hCW : C.Nonempty := ⟨(e.symm (u, r)).val, e.symm (u, r),
    by simpa only [W, mem_preimage, e.apply_symm_apply] using hv, rfl⟩
  have hC0 : (volume : Measure E) C ≠ 0 := (hC.measure_pos volume hCW).ne'
  have hm := (volume : Measure E).measurePreserving_homeomorphUnitSphereProd
  have hdim : Module.finrank ℝ E - 1 = n := by simp [E, NormalCoordinates]
  have hrad := congrArg Measure.volumeIoiPow hdim
  have hmap := hm.map_eq.trans (congrArg (Measure.prod (volume : Measure E).toSphere) hrad)
  have hEq : (normalSphereMeasure n).prod (Measure.volumeIoiPow n) V = volume C := by
    unfold normalSphereMeasure
    rw [← hmap, Measure.map_apply hm.measurable hV.measurableSet]
    exact (MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : E)).compl)
      |>.comap_apply _ _
  unfold V at hEq
  rw [Measure.prod_prod] at hEq
  intro hzero
  exact hC0 (by simpa only [hzero, zero_mul] using hEq.symm)

/-- Pull back a local integral to the product of the unit directions
and the actual polar radial measure. -/
theorem normal_polar_integrable_iff (n : ℕ) (R : ℝ) (f : NormalCoordinates n → ℝ) :
    IntegrableOn f (ball 0 R) ↔
      Integrable (fun p : NormalUnit n × PositiveRadius =>
        if (p.2 : ℝ) < R then f ((p.2 : ℝ) • (p.1 : NormalCoordinates n)) else 0)
        ((normalSphereMeasure n).prod (Measure.volumeIoiPow n)) := by
  let E := NormalCoordinates n
  let e := homeomorphUnitSphereProd E
  let g : NormalUnit n × PositiveRadius → ℝ := fun p =>
    if (p.2 : ℝ) < R then f ((p.2 : ℝ) • (p.1 : E)) else 0
  have he : (ball 0 R).indicator f ∘ (Subtype.val : ↥(({(0 : E)} : Set E)ᶜ) → E) = g ∘ e := by
    funext x
    have hnorm := norm_ne_zero_iff.mpr x.property
    simp [g, e, dist_zero_right, indicator, smul_inv_smul₀ hnorm]
  rw [← integrable_indicator_iff isOpen_ball.measurableSet]
  nth_rw 1 [← restrict_compl_singleton (μ := (volume : Measure E)) 0]
  rw [← IntegrableOn, integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl, he]
  have hm := (volume : Measure E).measurePreserving_homeomorphUnitSphereProd
  have hdim : Module.finrank ℝ E - 1 = n := by simp [E, NormalCoordinates]
  have hiff := hm.integrable_comp_emb (g := g) (Homeomorph.measurableEmbedding _)
  rw [hdim] at hiff
  exact hiff

def radialPower (R α : ℝ) (r : PositiveRadius) : ℝ :=
  if (r : ℝ) < R then (r : ℝ) ^ α else 0

theorem radial_power_measurable (R α : ℝ) : Measurable (radialPower R α) := by
  unfold radialPower
  exact Measurable.ite (measurableSet_lt measurable_subtype_coe measurable_const)
    (by fun_prop) measurable_const

theorem radial_power_nonneg (R α : ℝ) (r : PositiveRadius) : 0 ≤ radialPower R α r := by
  unfold radialPower
  split
  · exact Real.rpow_nonneg r.property.le _
  · exact le_rfl

theorem radial_power_integrable_iff (n : ℕ) {R : ℝ} (hR : 0 < R) (α : ℝ) :
    Integrable (radialPower R α) (Measure.volumeIoiPow n) ↔ -1 < (n : ℝ) + α := by
  rw [Measure.volumeIoiPow, integrable_withDensity_iff_integrable_smul']
  · have he : (fun x : PositiveRadius =>
        (ENNReal.ofReal ((x : ℝ) ^ n)).toReal • radialPower R α x) =
        fun x : PositiveRadius => (Iio R).indicator (fun r : ℝ => r ^ ((n : ℝ) + α)) x.val := by
      funext x
      rw [ENNReal.toReal_ofReal (pow_nonneg x.property.le _), smul_eq_mul]
      simp only [radialPower, Set.indicator, mem_Iio]
      split
      · rw [Real.rpow_add x.property, Real.rpow_natCast]
      · exact mul_zero _
    rw [he]
    change Integrable ((Iio R).indicator (fun r : ℝ => r ^ ((n : ℝ) + α)) ∘ Subtype.val)
      ((volume : Measure ℝ).comap (Subtype.val : PositiveRadius → ℝ)) ↔ _
    rw [← integrableOn_iff_comap_subtypeVal measurableSet_Ioi, IntegrableOn,
      integrable_indicator_iff measurableSet_Iio, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]
    exact intervalIntegral.integrableOn_Ioo_rpow_iff hR
  · fun_prop
  · exact Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

/-- At equality of twice the Taylor degree and the normal dimension
the radial power is exactly the reciprocal, with logarithmic primitive. -/
theorem critical_radial_power_integral (n j : ℕ) {δ R : ℝ}
    (hδ : 0 < δ) (hR : 0 < R) (hJR : 2 * j = n + 1) :
    (∫ r in δ..R, r ^ ((n : ℝ) + (2 * (j : ℝ) - 2 * ((n : ℝ) + 1)))) =
      Real.log (R / δ) := by
  have hj : (2 : ℝ) * (j : ℝ) = (n : ℝ) + 1 := by exact_mod_cast hJR
  have he : (n : ℝ) + (2 * (j : ℝ) - 2 * ((n : ℝ) + 1)) = -1 := by linarith
  simp_rw [he, Real.rpow_neg_one]
  exact integral_inv_of_pos hδ hR

end UV.ContinueVisitNormalPolar
