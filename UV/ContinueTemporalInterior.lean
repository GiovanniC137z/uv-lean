import UV.ContinueTemporalWronskian

/-! The response at a retained normal depth, derived through the actual
two-energy Wronskian. -/

noncomputable section

namespace UV.TemporalRay

open MeasureTheory Filter Set
open scoped Topology

def temporalTail (D : NormalChannel) (u v : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in Ioi t, D.temporal s*u s*v s

theorem temporal_tail_sub_right (D : NormalChannel) {u v w : ℝ → ℝ}
    (hu : MemLp u 2 normalRayMeasure) (hv : MemLp v 2 normalRayMeasure)
    (hw : MemLp w 2 normalRayMeasure) {t : ℝ} (ht : 0 ≤ t) :
    temporalTail D u (fun r => w r-v r) t = temporalTail D u w t - temporalTail D u v t := by
  have hi (k : ℝ → ℝ) (hk : MemLp k 2 normalRayMeasure) :
      IntegrableOn (fun r => D.temporal r*u r*k r) (Ioi t) := by
    have h0 := temporal_pairing_integrable D hu hk
    change IntegrableOn (fun r : ℝ => D.temporal r*u r*k r) (Ioi (0:ℝ)) volume at h0
    exact h0.mono_set (Ioi_subset_Ioi ht)
  unfold temporalTail
  rw [← integral_sub (hi w hw) (hi v hv)]
  exact integral_congr_ae (Eventually.of_forall fun r => by ring)

theorem temporal_tail_bound (D : NormalChannel) {u v : ℝ → ℝ}
    (hu : MemLp u 2 normalRayMeasure) (hv : MemLp v 2 normalRayMeasure)
    {t : ℝ} (ht : 0 ≤ t) :
    |temporalTail D u v t| ≤ D.parMax * (rayL2Size u * rayL2Size v) := by
  unfold temporalTail
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ((setIntegral_mono_set
    (temporal_pairing_integrable D hu hv).norm ?_ ?_).trans (temporal_pairing_norm_bound D hu hv))
  · exact Eventually.of_forall fun r => norm_nonneg _
  · exact Eventually.of_forall fun _ hr => Ioi_subset_Ioi ht hr

theorem continuousOn_temporal_tail (D : NormalChannel) {u v : ℝ → ℝ}
    (hu : MemLp u 2 normalRayMeasure) (hv : MemLp v 2 normalRayMeasure) :
    ContinuousOn (temporalTail D u v) (Ici 0) := by
  let f (s : ℝ) := D.temporal s*u s*v s
  have hi : IntegrableOn f (Ioi 0) := temporal_pairing_integrable D hu hv
  have hiv (t : ℝ) (ht : 0 ≤ t) : IntervalIntegrable f volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr (hi.mono_set Ioc_subset_Ioi_self)
  have hcont : ContinuousOn (fun t => ∫ s in (0:ℝ)..t, f s) (Ici 0) := by
    intro t ht
    have hb : 0 ≤ t+1 := by change 0 ≤ t at ht; linarith
    have hc := intervalIntegral.continuousOn_primitive_interval' (hiv (t+1) hb)
      (a := (0:ℝ)) left_mem_uIcc
    rw [uIcc_of_le hb] at hc
    apply (hc t ⟨ht,by linarith⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin (s := Ici (0:ℝ)),
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t < t+1 by linarith))] with q hq hq'
    exact ⟨hq,hq'.le⟩
  have hEq (t : ℝ) (ht : 0 ≤ t) :
      temporalTail D u v t = temporalPairing D u v - ∫ s in (0:ℝ)..t, f s := by
    have hdisj : Disjoint (Ioc (0:ℝ) t) (Ioi t) := Set.disjoint_left.mpr fun _ hs hs' => hs'.not_ge hs.2
    have hUnion : Ioc (0:ℝ) t ∪ Ioi t = Ioi 0 := by
      ext s
      simp only [mem_union,mem_Ioc,mem_Ioi]
      constructor
      · rintro (⟨h,_⟩ | h)
        · exact h
        · exact ht.trans_lt h
      · intro h
        rcases le_or_gt s t with hs | hs
        · exact Or.inl ⟨h,hs⟩
        · exact Or.inr hs
    have h := setIntegral_union hdisj measurableSet_Ioi
      (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi ht))
    rw [hUnion,← intervalIntegral.integral_of_le ht] at h
    change temporalPairing D u v = _ + temporalTail D u v t at h
    linarith
  exact (continuousOn_const.sub hcont).congr (fun t ht => hEq t ht)

def inverseNormalWeight (D : NormalChannel) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  (D.a t*u t^2)⁻¹

theorem inverse_normal_weight_continuousOn (D : NormalChannel) (u : NormalProfile)
    (hu : ∀ r ≥ 0, 0 < u.amplitude r) :
    ContinuousOn (inverseNormalWeight D u.amplitude) (Ici 0) := by
  have hc : ContinuousOn u.amplitude (Ici 0) := fun t ht =>
    (u.has_gradient t ht).continuousAt.continuousWithinAt
  apply (D.continuous_a.continuousOn.mul (hc.pow 2)).inv₀
  intro t ht
  exact mul_ne_zero (D.aMin_pos.trans_le (D.a_bound t ht).1).ne' (pow_ne_zero _ (hu t ht).ne')

theorem transverse_amplitude_exact_difference (D : NormalChannel) {y z : ℝ}
    (u : NormalTransfer D.a (D.potential y)) (v : NormalTransfer D.a (D.potential z))
    (hu : ∀ r ≥ 0, 0 < u.amplitude r) {r : ℝ} (hr : 0 ≤ r) :
    v.amplitude r-u.amplitude r = -(z-y) * u.amplitude r *
      ∫ t in (0:ℝ)..r, inverseNormalWeight D u.amplitude t * temporalTail D u.amplitude v.amplitude t := by
  let g (t : ℝ) := inverseNormalWeight D u.amplitude t * temporalTail D u.amplitude v.amplitude t
  have hc : ContinuousOn g (Ici 0) := (inverse_normal_weight_continuousOn D u.toNormalProfile hu).mul
    (continuousOn_temporal_tail D u.amplitude_L2 v.amplitude_L2)
  have hi : IntervalIntegrable g volume 0 r :=
    (hc.mono (by rw [uIcc_of_le hr]; exact fun _ h => h.1)).intervalIntegrable
  have hd (t : ℝ) (ht : t ∈ uIcc (0:ℝ) r) :
      HasDerivAt (fun s => v.amplitude s/u.amplitude s) (-(z-y)*g t) t := by
    have ht₀ : 0 ≤ t := (uIcc_of_le hr ▸ ht).1
    have h := normal_ratio_hasDerivAt D u v ht₀ (hu t ht₀).ne'
    rw [normal_wronskian_eq_tail D u v ht₀] at h
    convert h using 1
    unfold g inverseNormalWeight temporalTail
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hi.const_mul (-(z-y)))
  rw [intervalIntegral.integral_const_mul,u.boundary_one,v.boundary_one,div_one] at h
  have hh := congrArg (fun s : ℝ => s * u.amplitude r) h
  dsimp only at hh
  rw [sub_mul,div_mul_cancel₀ _ (hu r hr).ne',one_mul] at hh
  rw [← hh]
  change _ = _
  ring

end UV.TemporalRay
