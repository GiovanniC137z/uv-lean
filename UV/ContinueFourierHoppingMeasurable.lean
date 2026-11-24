import UV.ContinueFourierHoppingLoop

/-! Joint measurability in the original photon transfers, external shifts,
and all charged four-momentum coordinates, including vanishing scalar
frequencies and repeated directions. -/

noncomputable section

open MeasureTheory Set Complex

namespace UV.SectorPlane

variable {Z : Type*} [MeasurableSpace Z]

private theorem measurable_pulse {b u : Z → ℝ} (hb : Measurable b) (hu : Measurable u) :
    Measurable (fun z => hoppingPulse (b z) (u z)) := by
  have he : (fun z => hoppingPulse (b z) (u z)) =
      fun z => if b z=0 then (u z:ℂ) else
        (openingFourierWave (b z) (u z)-1)/(I*(b z:ℂ)) := by
    funext z
    split_ifs with h
    · simp only [h,hopping_pulse_zero]
    · exact hopping_pulse_formula h _
  rw [he]
  unfold openingFourierWave
  apply Measurable.ite (measurableSet_eq_fun hb measurable_const) <;> fun_prop

theorem measurable_carrier_slot {k r : ℕ} {a : ℝ} (ha : a ≠ 0) {b s : Z → ℝ}
    (hb : Measurable b) (hs : Measurable s) (ν : Fin k → Z → ℝ) (hν : ∀ j, Measurable (ν j)) :
    Measurable (fun z => (HoppingCarrierSlot.mk a (b z) (List.ofFn (ν · z)) r).value (s z)) := by
  let L := fun z => List.ofFn (ν · z) ++ List.replicate r 0
  have hPulse : Measurable (fun t : Z × ℝ => ((L t.1).map (fun v => hoppingPulse v t.2)).prod) := by
    simp only [L,List.map_append,List.prod_append,List.map_ofFn,List.prod_ofFn,Function.comp_def,
      List.map_replicate,List.prod_replicate,hopping_pulse_zero]
    exact (Finset.measurable_prod _ fun j _ => measurable_pulse ((hν j).comp measurable_fst) measurable_snd).mul
      ((Complex.continuous_ofReal.measurable.comp measurable_snd).pow_const _)
  have h (sign : ℂ) (U : Set ℝ) : Measurable (fun z => ∫ u in U,
      sign*(Real.exp (-a*u):ℂ)*openingFourierWave (s z+b z) u*
        ((L z).map (fun v => hoppingPulse v u)).prod) := by
    apply StronglyMeasurable.measurable
    apply StronglyMeasurable.integral_prod_right' (f := fun t : Z × ℝ => sign*(Real.exp (-a*t.2):ℂ)*
      openingFourierWave (s t.1+b t.1) t.2*((L t.1).map (fun v => hoppingPulse v t.2)).prod)
    apply Measurable.stronglyMeasurable
    apply Measurable.mul _ hPulse
    unfold openingFourierWave
    fun_prop
  have he (z) := congrFun (hopping_marked_iterated_deriv ha (List.ofFn (ν · z)) (b z) r) (s z)
  change Measurable (fun z => iteratedDeriv r (hoppingMarks _ _) (s z))
  simp_rw [he]
  apply measurable_const.mul
  rcases lt_or_gt_of_ne ha with hn|hp
  · have h' (z) := (hopping_marks_oriented_fourier (neg_pos.mpr hn) (b z) (L z) (s z)).2
    simp only [neg_neg] at h'
    change Measurable (fun z => hoppingMarks (L z) (fun x => hoppingInterval a (x+b z)) (s z))
    simp_rw [h']
    simpa only [neg_mul,one_mul] using h (-1) (Iic 0)
  · simpa only [one_mul,← (hopping_marks_oriented_fourier hp _ _ _).1] using h 1 (Ioi 0)

theorem measurable_spatial_slot {r : ℕ} (σ : ℝ) (u : Fin r → UnitVector Spatial)
    {b k : Z → Spatial} (hb : Measurable b) (hk : Measurable k) (q : Fin r → Z → Spatial)
    (hq : ∀ j, Measurable (q j)) :
    Measurable (fun z => (HoppingSpatialSlot.mk r u (b z) (q · z)).value σ (k z)) := by
  let Φ := fun x : Spatial => iteratedFDeriv ℝ r (twoBandSpatialHop 1 σ) x (fun j => (u j).val)
  have hSmooth : ContDiff ℝ r (twoBandSpatialHop 1 σ) :=
    (twoBand_gaussian_hop_smooth 1 σ).of_le (by exact_mod_cast le_top)
  have hΦ : Continuous Φ :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Spatial) ℝ (fun j => (u j).val)).continuous.comp
      hSmooth.continuous_iteratedFDeriv'
  change Measurable (fun z => ∫ θ, Φ (k z+(b z+∑ j, θ j • q j z)) ∂twoBandPathFractions r)
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right' (f := fun t : Z × (Fin r → ℝ) => Φ (k t.1+(b t.1+∑ j, t.2 j • q j t.1)))
  exact (hΦ.measurable.comp ((hk.comp measurable_fst).add ((hb.comp measurable_fst).add
    (Finset.measurable_sum _ fun j _ => ((measurable_pi_apply j).comp measurable_snd).smul ((hq j).comp measurable_fst))))).stronglyMeasurable

end UV.SectorPlane
