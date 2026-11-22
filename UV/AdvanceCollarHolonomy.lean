import UV.FurtherBoundaryCollar
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! The translation and nonzero integer charge on the flat holonomy
circle preserve its normalized probability measure. The positive
angular representative reads the same holonomy before the collar heat
operator is applied. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace UV.AdvanceCollarHolonomy

private def positiveTurn (x : UnitAddCircle) : ℝ :=
  (AddCircle.measurableEquivIoc 1 0 x).1

def holonomyGap (q : ℤ) (shift x : UnitAddCircle) : ℝ :=
  positiveTurn (shift + (-q) • x)

private theorem positive_turn_measure :
    MeasurePreserving positiveTurn (volume : Measure UnitAddCircle)
      (volume.restrict (Ioc 0 1)) := by
  have hm : Measurable positiveTurn :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIoc 1 0).measurable
  refine ⟨hm, ?_⟩
  have hcover : MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
      (volume.restrict (Ioc 0 1)) (volume : Measure UnitAddCircle) := by
    simpa only [zero_add] using UnitAddCircle.measurePreserving_mk 0
  rw [← hcover.map_eq, Measure.map_map hm hcover.measurable]
  refine (Measure.map_congr ?_).trans Measure.map_id
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  change positiveTurn (x : UnitAddCircle) = x
  have hx' : x ∈ Ioc 0 ((0 : ℝ) + 1) := by simpa only [zero_add] using hx
  change AddCircle.liftIoc 1 0 id (x : UnitAddCircle) = x
  rw [AddCircle.liftIoc_coe_apply hx']
  rfl

/-- In turn coordinates, the source's normal angular number
η⊥ − q a₀ is read modulo its integer mode index. Its positive local
representative has density one in the normalized Haar preparation. -/
theorem charged_holonomy_gap_measure {q : ℤ} (hq : q ≠ 0) (shift : UnitAddCircle) :
    MeasurePreserving (holonomyGap q shift) (volume : Measure UnitAddCircle)
      (volume.restrict (Ioc 0 1)) := by
  have hcharge := Measure.measurePreserving_zsmul (volume : Measure UnitAddCircle) (neg_ne_zero.mpr hq)
  have hshift := measurePreserving_add_left (volume : Measure UnitAddCircle) shift
  exact positive_turn_measure.comp (hshift.comp hcharge)

theorem charged_holonomy_gap_interval_mass {q : ℤ} (hq : q ≠ 0) (shift : UnitAddCircle)
    {b : ℝ} (hb1 : b ≤ 1) :
    (volume : Measure UnitAddCircle) (holonomyGap q shift ⁻¹' Ioc 0 b) =
      ENNReal.ofReal b := by
  let h := charged_holonomy_gap_measure hq shift
  rw [← Measure.map_apply h.measurable measurableSet_Ioc,
    h.map_eq, Measure.restrict_apply measurableSet_Ioc,
    inter_eq_left.mpr (Ioc_subset_Ioc_right hb1), Real.volume_Ioc]
  simp only [sub_zero]

/-- The checked lower vacuum estimate implies divergence for the
actual affine pushforward of normalized circle Haar measure. -/
theorem charged_holonomy_vacuum_not_integrable {q : ℤ} (hq : q ≠ 0) (shift : UnitAddCircle)
    {V : ℝ → ℝ} (hVmeas : Measurable V) {d : ℝ} (hd : 0 < d)
    (hV : ∀ᶠ ν in 𝓝[>] (0 : ℝ),
      Real.exp (d * ν ^ (-2 / 3 : ℝ) * (1 + |Real.log ν|) ^ (4 : ℕ)) ≤ V ν) :
    ¬ Integrable (fun x => V (holonomyGap q shift x)) (volume : Measure UnitAddCircle) := by
  intro hI
  have h := charged_holonomy_gap_measure hq shift
  have hmap := (integrable_map_measure hVmeas.aestronglyMeasurable h.measurable.aemeasurable).mpr hI
  rw [h.map_eq] at hmap
  obtain ⟨T, hT, hbound⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hV
  let s := min T 1
  have hs : 0 < s := lt_min hT zero_lt_one
  have hsmall : IntegrableOn V (Ioc 0 s) :=
    IntegrableOn.mono_set hmap (Ioc_subset_Ioc_right (min_le_right _ _))
  have hn := UV.FurtherBoundaryCollar.averaged_spin_vacuum_not_integrableOn
    (ρ := fun _ => 1) (V := V) (m := 1) hd zero_lt_one hs 0
    (fun ν _ => by simp)
    (fun ν hν => hbound (Ioc_subset_Ioc_right (min_le_left _ _) hν))
  apply hn
  simpa only [one_mul] using hsmall

/-- The averaged vacuum is infinite as a nonnegative extended
integral, without a pointwise finiteness assumption at positive gap. -/
theorem charged_holonomy_vacuum_lintegral_eq_top {q : ℤ} (hq : q ≠ 0) (shift : UnitAddCircle)
    {V : ℝ → ℝ≥0∞} (hVmeas : Measurable V) {d : ℝ} (hd : 0 < d)
    (hV : ∀ᶠ ν in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (Real.exp (d * ν ^ (-2 / 3 : ℝ) * (1 + |Real.log ν|) ^ (4 : ℕ))) ≤ V ν) :
    (∫⁻ x : UnitAddCircle, V (holonomyGap q shift x)) = ⊤ := by
  let h := charged_holonomy_gap_measure hq shift
  let G := fun ν : ℝ => Real.exp (d * ν ^ (-2 / 3 : ℝ) * (1 + |Real.log ν|) ^ (4 : ℕ))
  obtain ⟨T, hT, hbound⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hV
  let s := min T 1
  have hs : 0 < s := lt_min hT zero_lt_one
  have hbad : ¬ IntegrableOn G (Ioc 0 s) := by
    intro hI
    have hn := UV.FurtherBoundaryCollar.averaged_spin_vacuum_not_integrableOn
      (ρ := fun _ => 1) (V := G) (m := 1) hd zero_lt_one hs 0
      (fun ν _ => by simp) (fun _ _ => le_rfl)
    exact hn (by simpa only [one_mul] using hI)
  have hGm : Measurable G := by unfold G; fun_prop
  have htop : (∫⁻ ν in Ioc 0 s, ENNReal.ofReal (G ν)) = ⊤ := by
    by_contra hf
    exact hbad ((lintegral_ofReal_ne_top_iff_integrable hGm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)).mp hf)
  have hge : (∫⁻ ν in Ioc 0 s, ENNReal.ofReal (G ν)) ≤ ∫⁻ ν in Ioc 0 s, V ν := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with ν hν
    exact hbound (Ioc_subset_Ioc_right (min_le_left _ _) hν)
  calc
    _ = ∫⁻ ν in Ioc 0 1, V ν := by
      rw [← h.map_eq, lintegral_map hVmeas h.measurable]
    _ = ⊤ := top_unique (htop ▸ hge.trans (lintegral_mono_set (Ioc_subset_Ioc_right (min_le_right _ _))))

end UV.AdvanceCollarHolonomy
