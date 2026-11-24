import UV.ContinueOrderedHopFourierClosure
import UV.ContinueTwoBandSpectralLoop
import UV.ContinueNormalCoverConvolution

/-! The one-sided temporal closure for complete scalar vertices on a loop.
Duration insertions from the soft subtractions differentiate the very same
resolvent. The point at the onsite jump is a null set on the return slice
because an active loop has two or more hops. -/

noncomputable section

open MeasureTheory Filter Set Complex
open scoped Topology BigOperators RealInnerProductSpace

namespace UV.SectorPlane

private theorem pulse_cont (ν : ℝ) : Continuous (hoppingPulse ν) :=
  intervalIntegral.continuous_primitive (fun a b => (opening_fourier_wave_continuous ν).intervalIntegrable a b) 0

private def carrierPulseList (T : HoppingCarrierSlot) := T.marks ++ List.replicate T.derivatives 0

private def carrierRaw (T : HoppingCarrierSlot) (u : ℝ) : ℂ := Complex.I^T.derivatives *
  ((Real.exp (-T.signedMass*u):ℂ) * openingFourierWave T.shift u *
      ((carrierPulseList T).map (fun ν => hoppingPulse ν u)).prod)

def HoppingCarrierSlot.positionDensity (T : HoppingCarrierSlot) : ℝ → ℂ :=
  if 0 < T.signedMass then (Ioi 0).indicator (carrierRaw T)
  else (Iic 0).indicator (fun u => -carrierRaw T u)

private theorem pulse_prod_cont (L : List ℝ) : Continuous (fun u => (L.map (fun ν => hoppingPulse ν u)).prod) := by
  induction L with
  | nil => exact continuous_const
  | cons ν L ih => exact (pulse_cont ν).mul ih

private theorem raw_cont (T : HoppingCarrierSlot) : Continuous (carrierRaw T) := by
  unfold carrierRaw
  exact continuous_const.mul (((Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
    (opening_fourier_wave_continuous _)).mul (pulse_prod_cont _))

theorem HoppingCarrierSlot.position_measurable (T : HoppingCarrierSlot) : Measurable T.positionDensity := by
  unfold positionDensity
  split
  · exact (raw_cont _).measurable.indicator measurableSet_Ioi
  · exact (raw_cont _).measurable.neg.indicator measurableSet_Iic

theorem HoppingCarrierSlot.position_cont_off_zero (T : HoppingCarrierSlot) {u : ℝ} (hu : u ≠ 0) :
    ContinuousAt T.positionDensity u := by
  unfold positionDensity
  split
  · rcases lt_or_gt_of_ne hu with hn | hp
    · have h : (Ioi (0:ℝ)).indicator (carrierRaw T) =ᶠ[𝓝 u] fun _ => 0 :=
        (gt_mem_nhds hn).mono fun x hx => indicator_of_notMem (not_lt.mpr hx.le) _
      exact (continuousAt_congr h).mpr continuousAt_const
    · exact ((raw_cont _).continuousAt).congr ((lt_mem_nhds hp).mono fun x hx => (indicator_of_mem hx _).symm)
  · rcases lt_or_gt_of_ne hu with hn | hp
    · exact ((raw_cont T).neg.continuousAt).congr ((gt_mem_nhds hn).mono fun x hx => (indicator_of_mem (show x ∈ Iic (0:ℝ) from hx.le) (fun v => -carrierRaw T v)).symm)
    · have h : (Iic (0:ℝ)).indicator (fun x => -carrierRaw T x) =ᶠ[𝓝 u] fun _ => 0 :=
        (lt_mem_nhds hp).mono fun x hx => indicator_of_notMem (show x ∉ Iic (0:ℝ) from not_le.mpr hx) _
      exact (continuousAt_congr h).mpr continuousAt_const

private theorem pulse_prod_norm (L : List ℝ) (u : ℝ) :
    ‖(L.map (fun ν => hoppingPulse ν u)).prod‖ ≤ |u|^L.length := by
  induction L with
  | nil => simp
  | cons ν L ih =>
    simp only [List.map_cons,List.prod_cons,norm_mul,List.length_cons,pow_succ']
    exact mul_le_mul (hopping_pulse_norm ν u) ih (norm_nonneg _) (abs_nonneg _)

private theorem raw_bound (T : HoppingCarrierSlot) (u : ℝ) :
    ‖carrierRaw T u‖ ≤ Real.exp (-T.signedMass*u)*|u|^T.degree := by
  unfold carrierRaw
  simp only [norm_mul,norm_pow,norm_I,one_pow,one_mul,opening_fourier_wave_norm,mul_one,
    Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  simpa only [carrierPulseList,HoppingCarrierSlot.degree,List.length_append,List.length_replicate] using
    pulse_prod_norm (carrierPulseList T) u

private theorem oriented_bound (T : HoppingCarrierSlot) (ht : T.signedMass ≠ 0) (u : ℝ) :
    ‖T.positionDensity u‖ ≤ Real.exp (-|T.signedMass| * |u|)*|u|^T.degree := by
  unfold HoppingCarrierSlot.positionDensity
  split
  · rename_i hp
    by_cases hu : 0 < u
    · rw [indicator_of_mem (show u ∈ Ioi (0:ℝ) from hu),abs_of_pos hp,abs_of_pos hu]; simpa only [abs_of_pos hu] using raw_bound T u
    · rw [indicator_of_notMem (show u ∉ Ioi (0:ℝ) from hu),norm_zero]; positivity
  · rename_i hn
    by_cases hu : u ≤ 0
    · rw [indicator_of_mem (show u ∈ Iic (0:ℝ) from hu),norm_neg,abs_of_neg (lt_of_le_of_ne (le_of_not_gt hn) ht),abs_of_nonpos hu,neg_neg,mul_neg]
      simpa only [neg_mul,abs_of_nonpos hu] using raw_bound T u
    · rw [indicator_of_notMem (show u ∉ Iic (0:ℝ) from hu),norm_zero]; positivity

theorem HoppingCarrierSlot.position_envelope (T : HoppingCarrierSlot) (ht : T.signedMass ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      ‖T.positionDensity u‖ ≤ C*Real.exp (-(|T.signedMass|/2)*|u|) := by
  let a := |T.signedMass|/2
  have ha : 0 < a := half_pos (abs_pos.mpr ht)
  refine ⟨orderedHopMomentConstant a T.degree, by unfold orderedHopMomentConstant; positivity, ?_⟩
  intro u
  apply (oriented_bound T ht u).trans
  have hp := (pow_le_pow_left₀ (abs_nonneg u) (show |u| ≤ 1+|u| by linarith) T.degree).trans
    (orderedHop_nonneg_power_bound ha (abs_nonneg u) T.degree)
  apply (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le).trans_eq
  change Real.exp (-|T.signedMass| * |u|)*(orderedHopMomentConstant a T.degree * Real.exp (a*|u|)) = _
  rw [mul_left_comm,←Real.exp_add]
  congr 2; unfold a; ring

theorem HoppingCarrierSlot.position_integrable (T : HoppingCarrierSlot) (ht : T.signedMass ≠ 0) :
    Integrable T.positionDensity := by
  obtain ⟨C,_,hb⟩ := T.position_envelope ht
  let a := |T.signedMass|/2
  have ha : 0 < a := half_pos (abs_pos.mpr ht)
  have hi : Integrable (fun u : ℝ => Real.exp (-a*|u|)) := by
    by_contra h
    have H := orderedHop_time_mass ha
    rw [integral_undef h] at H
    exact (div_pos (by norm_num : 0 < (2:ℝ)) ha).ne H
  exact (hi.const_mul C).mono' T.position_measurable.aestronglyMeasurable (Eventually.of_forall hb)

theorem HoppingCarrierSlot.position_transform (T : HoppingCarrierSlot) (ht : T.signedMass ≠ 0) (s : ℝ) :
    orderedHopFourier T.positionDensity s = T.value s := by
  have hv := hopping_marks_oriented_fourier (abs_pos.mpr ht) T.shift (carrierPulseList T) s
  unfold HoppingCarrierSlot.value
  rw [hopping_marked_iterated_deriv ht]
  change orderedHopFourier T.positionDensity s = I^T.derivatives *
    hoppingMarks (carrierPulseList T) (fun x => hoppingInterval T.signedMass (x+T.shift)) s
  have he (u : ℝ) : orderedHopWave s u = openingFourierWave s u := by
    simp [orderedHopWave,openingFourierWave]
  unfold orderedHopFourier HoppingCarrierSlot.positionDensity
  by_cases hp : 0 < T.signedMass
  · rw [if_pos hp,show hoppingMarks (carrierPulseList T) (fun x => hoppingInterval T.signedMass (x+T.shift)) s = _
      from (abs_of_pos hp) ▸ hv.1,←integral_const_mul]
    simp_rw [he,← indicator_mul_right]
    rw [integral_indicator measurableSet_Ioi]
    apply integral_congr_ae (ae_of_all _ fun u => ?_)
    rw [opening_fourier_wave_add]; unfold carrierRaw; ring
  · have hn := lt_of_le_of_ne (le_of_not_gt hp) ht
    have hvn := hv.2
    rw [abs_of_neg hn,neg_neg] at hvn
    rw [if_neg hp,hvn,←integral_const_mul]
    simp_rw [he,← indicator_mul_right]
    rw [integral_indicator measurableSet_Iic]
    apply integral_congr_ae (ae_of_all _ fun u => ?_)
    rw [opening_fourier_wave_add]; unfold carrierRaw; ring

theorem orderedHop_carrier_closure {n : ℕ} {m : ℝ} (hm : 0 < m)
    (T : Fin (n+1+1) → HoppingCarrierSlot) (hMass : ∀ i, |(T i).signedMass| = m) :
    (2*Real.pi)⁻¹ • (∫ s, ∏ j, (T j).value s) =
      ∫ z : Fin (n+1) → ℝ, (T 0).positionDensity (-(∑ j, z j)) * ∏ j, (T j.succ).positionDensity (z j) := by
  let A := T 0
  let B := T 1
  let rest := List.ofFn (fun j : Fin n => T j.succ.succ)
  let M := A.degree+B.degree+hoppingLoopDegree rest
  have hN (i) : (T i).signedMass ≠ 0 := abs_pos.mp ((hMass i).symm ▸ hm)
  have hrest : ∀ t ∈ rest, |t.signedMass| = m := by simpa [rest] using (fun j : Fin n => hMass j.succ.succ)
  have hi := (hopping_charged_loop_frequency hm A B rest (hMass _) (hMass _) hrest (le_refl M)).1
  have hAbs : Integrable (fun s => (T 0).value s * ∏ j : Fin (n+1), (T j.succ).value s) := by
    change Integrable (fun s => hoppingLoopValue (A::B::rest) s) at hi
    simpa only [hoppingLoopValue,List.map_cons,List.prod_cons,List.map_ofFn,Fin.prod_ofFn,Function.comp_def,
      Fin.prod_univ_succ,rest,A,B,Fin.succ_zero_eq_one] using hi
  obtain ⟨C,hC,hb⟩ := (T 0).position_envelope (hN 0)
  have hmax (u : ℝ) : ‖(T 0).positionDensity u‖ ≤ C :=
    (hb u).trans (mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr (by
      apply mul_nonpos_of_nonpos_of_nonneg _ (abs_nonneg _)
      exact neg_nonpos.mpr (div_nonneg (abs_nonneg _) (by norm_num)))))
  have h := orderedHop_fourier_return (f := (T 0).positionDensity) (h := fun j : Fin (n+1) => (T j.succ).positionDensity)
    (T 0).position_measurable (fun j => (T j.succ).position_measurable) ((T 0).position_integrable (hN 0))
    (fun j => (T j.succ).position_integrable (hN _)) hmax
    ((UV.normal_sum_ne_ae n 0).mono fun z hz => (T 0).position_cont_off_zero (neg_ne_zero.mpr hz)) (by
      simpa only [fun j => (T j).position_transform (hN j)] using hAbs)
  simpa only [Module.finrank_self,pow_one,orderedHopClosure,zero_sub,Fin.prod_univ_succ,
    fun j => (T j).position_transform (hN j)] using h

/-- A phase on this signed interval translates exactly this slot's charged
frequency. -/
theorem HoppingCarrierSlot.position_translate (T : HoppingCarrierSlot) (β u : ℝ) :
    ({ T with shift := T.shift+β } : HoppingCarrierSlot).positionDensity u =
      openingFourierWave β u * T.positionDensity u := by
  have hw : openingFourierWave (T.shift+β) u = openingFourierWave β u * openingFourierWave T.shift u := by
    unfold openingFourierWave; rw [←Complex.exp_add]; push_cast; congr 1; ring
  unfold positionDensity
  split <;> by_cases h : u ∈ Ioi (0:ℝ)
  all_goals simp [h,show (u ∈ Iic (0:ℝ)) ↔ u ∉ Ioi (0:ℝ) by simp]
  all_goals simp only [carrierRaw,carrierPulseList,hw]; ring

/-- A signed duration multiplied by the Fourier factor I is exactly a
derivative of the original resolvent slot, with its original pole intact. -/
theorem HoppingCarrierSlot.position_extra_derivative (T : HoppingCarrierSlot) (u : ℝ) :
    ({ T with derivatives := T.derivatives+1 } : HoppingCarrierSlot).positionDensity u =
      (Complex.I*(u:ℂ))*T.positionDensity u := by
  unfold positionDensity
  split <;> by_cases h : u ∈ Ioi (0:ℝ)
  all_goals simp [h,show (u ∈ Iic (0:ℝ)) ↔ u ∉ Ioi (0:ℝ) by simp]
  all_goals simp only [carrierRaw,carrierPulseList,List.map_append,List.prod_append,List.map_replicate,
    List.prod_replicate,hopping_pulse_zero,pow_succ]; ring

/-- An ordinary scalar source insertion adds its full signed interval pulse
at the specified incident frequency. -/
theorem HoppingCarrierSlot.position_extra_pulse (T : HoppingCarrierSlot) (ν u : ℝ) :
    ({ T with marks := ν :: T.marks } : HoppingCarrierSlot).positionDensity u =
      hoppingPulse ν u*T.positionDensity u := by
  unfold positionDensity
  split <;> by_cases h : u ∈ Ioi (0:ℝ)
  all_goals simp [h,show (u ∈ Iic (0:ℝ)) ↔ u ∉ Ioi (0:ℝ) by simp]
  all_goals simp only [carrierRaw,carrierPulseList,List.cons_append,List.map_cons,List.prod_cons]; ring

end UV.SectorPlane
