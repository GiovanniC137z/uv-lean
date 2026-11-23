import UV.ContinueRigidSphereCaps

/-! Exact uniform law of the axial projection of spatial solid angle. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Real Filter
open scoped ENNReal Interval RealInnerProductSpace Topology

namespace UV.ContinueRigidLaw

open UV.SectorPlane UV.ContinueRigidThreshold

/-- The unnormalized uniform measure, with solid-angle mass `4π`. -/
def axialSolidAngle : Measure ℝ :=
  ENNReal.ofReal (2*π) • volume.restrict (Icc (-1 : ℝ) 1)

private def axialLaw (a : Direction) : Measure ℝ :=
  solidAngle.map (axialProjection a)

private instance (a : Direction) : IsFiniteMeasure (axialLaw a) :=
  Measure.isFiniteMeasure_map _ _

private theorem axialSolidAngle_mass : axialSolidAngle univ = ENNReal.ofReal (4*π) := by
  rw [axialSolidAngle, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Icc, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*π)]
  congr 1
  ring

private instance : IsFiniteMeasure axialSolidAngle :=
  ⟨by rw [axialSolidAngle_mass]; exact ENNReal.ofReal_lt_top⟩

private theorem axialLaw_mass (a : Direction) : axialLaw a univ = ENNReal.ofReal (4*π) := by
  rw [axialLaw, Measure.map_apply (continuous_axialProjection a).measurable MeasurableSet.univ,
    preimage_univ, solidAngle_mass]

private theorem axialProjection_le_one (a n : Direction) : axialProjection a n ≤ 1 := by
  have hh := real_inner_le_norm (a : Spatial) (n : Spatial)
  rw [a.property, n.property, mul_one] at hh
  exact hh

private theorem law_Ioi_pos (a : Direction) {t : ℝ} (ht : 0 < t) :
    axialLaw a (Ioi t) = axialSolidAngle (Ioi t) := by
  rw [axialLaw, Measure.map_apply (continuous_axialProjection a).measurable measurableSet_Ioi,
    axialSolidAngle, Measure.smul_apply, Measure.restrict_apply measurableSet_Ioi]
  by_cases h₁ : t < 1
  · have h : Ioi t ∩ Icc (-1 : ℝ) 1 = Ioc t 1 := by
      ext z
      simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
      constructor
      · exact fun hz ↦ ⟨hz.1,hz.2.2⟩
      · exact fun hz ↦ ⟨hz.1, by linarith [hz.1], hz.2⟩
    rw [solidAngle_axial_cap a ht h₁, h, Real.volume_Ioc, smul_eq_mul,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*π)]
  · have h : Ioi t ∩ Icc (-1 : ℝ) 1 = ∅ := by
      ext z
      constructor
      · rintro ⟨hz,hz₁⟩
        exact False.elim (h₁ (hz.trans_le hz₁.2))
      · exact False.elim
    have h' : axialProjection a ⁻¹' Ioi t = ∅ := by
      ext n
      constructor
      · intro hn
        exact False.elim (h₁ (hn.trans_le (axialProjection_le_one a n)))
      · exact False.elim
    simp [h,h']

private def positiveSequence (n : ℕ) : ℝ := 1/((n:ℝ)+1)

private theorem sequence_pos (n : ℕ) : 0 < positiveSequence n := by
  unfold positiveSequence
  positivity

private theorem sequence_antitone : Antitone positiveSequence := by
  intro n m h
  unfold positiveSequence
  exact one_div_le_one_div_of_le (by positivity)
    (by exact_mod_cast (Nat.add_le_add_right h 1))

private theorem sequence_tendsto : Tendsto positiveSequence atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

private theorem law_Ioi_zero (a : Direction) :
    axialLaw a (Ioi 0) = axialSolidAngle (Ioi 0) := by
  have hu : (⋃ n, Ioi (positiveSequence n)) = Ioi (0:ℝ) := by
    ext x
    constructor
    · intro h
      obtain ⟨n,hn⟩ := mem_iUnion.1 h
      exact (sequence_pos n).trans hn
    · intro hx
      have he := sequence_tendsto.eventually (Iio_mem_nhds hx)
      obtain ⟨n,hn⟩ := he.exists
      exact mem_iUnion.2 ⟨n,hn⟩
  have hmono : Monotone (fun n ↦ Ioi (positiveSequence n)) :=
    fun _ _ h ↦ Ioi_subset_Ioi (sequence_antitone h)
  rw [← hu, hmono.measure_iUnion (μ := axialLaw a),
    hmono.measure_iUnion (μ := axialSolidAngle)]
  simp only [law_Ioi_pos a (sequence_pos _)]

private theorem law_Ici_pos (a : Direction) {t : ℝ} (ht : 0 < t) :
    axialLaw a (Ici t) = axialSolidAngle (Ici t) := by
  let s (n : ℕ) := t - (t/2)*positiveSequence n
  have hs : ∀ n, 0 < s n := by
    intro n
    have hl := sequence_antitone (Nat.zero_le n)
    have h0 : positiveSequence 0 = 1 := by norm_num [positiveSequence]
    rw [h0] at hl
    dsimp [s]
    nlinarith [mul_le_mul_of_nonneg_left hl (show 0 ≤ t/2 by positivity)]
  have hsm : Monotone s := by
    intro n m h
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left (sequence_antitone h) (by positivity)) _
  have hlim : Tendsto s atTop (𝓝 t) := by
    simp only [s]
    simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub (sequence_tendsto.const_mul (t/2))
  have he : (⋂ n, Ioi (s n)) = Ici t := by
    ext x
    constructor
    · intro h
      apply le_of_tendsto hlim
      exact Eventually.of_forall fun n ↦ (show s n < x from mem_iInter.1 h n).le
    · intro hx
      exact mem_iInter.2 fun n ↦ (sub_lt_self _ (mul_pos (by positivity) (sequence_pos n))).trans_le hx
  have hanti : Antitone (fun n ↦ Ioi (s n)) := antitone_Ioi.comp_monotone hsm
  rw [← he, hanti.measure_iInter (μ := axialLaw a)
    (fun _ ↦ measurableSet_Ioi.nullMeasurableSet) ⟨0, measure_ne_top _ _⟩,
    hanti.measure_iInter (μ := axialSolidAngle)
    (fun _ ↦ measurableSet_Ioi.nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
  simp only [law_Ioi_pos a (hs _)]

private def negDirection (a : Direction) : Direction := ⟨-(a : Spatial), by simp [a.property]⟩

private theorem law_neg (a : Direction) (t : ℝ) :
    axialLaw a (Iic t) = axialLaw (negDirection a) (Ici (-t)) := by
  rw [axialLaw, axialLaw,
    Measure.map_apply (continuous_axialProjection a).measurable measurableSet_Iic,
    Measure.map_apply (continuous_axialProjection (negDirection a)).measurable measurableSet_Ici]
  congr 1
  ext n
  simp [axialProjection, negDirection]

private theorem uniform_neg (t : ℝ) :
    axialSolidAngle (Iic t) = axialSolidAngle (Ici (-t)) := by
  rw [axialSolidAngle, Measure.smul_apply, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Iic, Measure.restrict_apply measurableSet_Ici]
  have hS : (fun x : ℝ ↦ -x) ⁻¹' (Ici (-t) ∩ Icc (-1) 1) = Iic t ∩ Icc (-1) 1 := by
    ext x
    simp only [mem_preimage, mem_inter_iff, mem_Ici, mem_Icc, mem_Iic]
    constructor <;> rintro ⟨h₁,h₂,h₃⟩ <;>
      exact ⟨by linarith, by linarith, by linarith⟩
  rw [← hS, (Measure.measurePreserving_neg (volume : Measure ℝ)).measure_preimage
    (measurableSet_Ici.inter measurableSet_Icc).nullMeasurableSet]

/-- The axial coordinate of the actual solid-angle measure is uniform. -/
theorem map_axialProjection_solidAngle (a : Direction) :
    solidAngle.map (axialProjection a) = axialSolidAngle := by
  change axialLaw a = axialSolidAngle
  apply Measure.ext_of_Iic
  intro t
  by_cases ht : t < 0
  · rw [law_neg, uniform_neg, law_Ici_pos _ (neg_pos.mpr ht)]
  · have he : axialLaw a (Ioi t) = axialSolidAngle (Ioi t) := by
      rcases eq_or_lt_of_le (le_of_not_gt ht) with ht' | ht'
      · rw [← ht', law_Ioi_zero]
      · exact law_Ioi_pos a ht'
    rw [← compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top _ _),
      measure_compl measurableSet_Ioi (by rw [← he]; exact measure_ne_top _ _),
      he, axialLaw_mass, axialSolidAngle_mass]

end UV.ContinueRigidLaw
