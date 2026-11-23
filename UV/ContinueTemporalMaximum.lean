import UV.ContinueTemporalWronskian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! The one-dimensional maximum principle for the finite-energy normal mode. -/

noncomputable section

namespace UV.TemporalRay

open MeasureTheory Filter Set Real
open scoped Topology

theorem normal_amplitude_tendsto_zero (u : NormalProfile) :
    Tendsto u.amplitude atTop (𝓝 0) := by
  have hi := ((memLp_two_iff_integrable_sq u.amplitude_L2.aestronglyMeasurable).mp u.amplitude_L2)
  have hdi : IntegrableOn (fun r => 2*(u.amplitude r*u.gradient r)) (Ioi 0) :=
    (u.amplitude_L2.integrable_mul u.gradient_L2).const_mul _
  have h := ray_derivative_tendsto_zero (a := 0) (fun r hr => by
    convert (u.has_gradient r hr).pow 2 using 1
    norm_num
    ring) hi hdi
  have hS : Tendsto (fun r => √(u.amplitude r^2)) atTop (𝓝 (√0)) :=
    continuous_sqrt.continuousAt.tendsto.comp h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [sqrt_zero,sqrt_sq_eq_abs,Real.norm_eq_abs] using hS

theorem normal_transfer_nonneg (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (u : NormalTransfer D.a (D.potential y)) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ u.amplitude r := by
  by_contra! hneg
  have hR : ∀ᶠ t in atTop, r<t ∧ u.amplitude r < u.amplitude t :=
    (eventually_gt_atTop r).and ((normal_amplitude_tendsto_zero u.toNormalProfile).eventually_const_lt hneg)
  obtain ⟨R,hrR,hRR⟩ := hR.exists
  have hR₀ := hr.trans hrR.le
  have hc : ContinuousOn u.amplitude (Ici 0) := fun t ht =>
    (u.has_gradient t ht).continuousAt.continuousWithinAt
  obtain ⟨x,hx,hmin⟩ := (isCompact_Icc (a := (0:ℝ)) (b := R)).exists_isMinOn
    ⟨r,hr,hrR.le⟩ (hc.mono fun _ ht => ht.1)
  have hxneg : u.amplitude x < 0 := (hmin ⟨hr,hrR.le⟩).trans_lt hneg
  have hx₀ : 0 < x := by
    apply lt_of_le_of_ne hx.1
    intro he
    rw [← he,u.boundary_one] at hxneg
    norm_num at hxneg
  have hxR : x < R := by
    apply lt_of_le_of_ne hx.2
    intro he
    rw [he] at hmin
    exact hRR.not_ge (hmin ⟨hr,hrR.le⟩)
  have hloc := hmin.isLocalMin (Icc_mem_nhds hx₀ hxR)
  have hd0 := hloc.hasDerivAt_eq_zero (u.has_gradient x hx₀.le)
  let F := normalFluxProfile D u
  have hF0 : F x = 0 := by simp [F,normalFluxProfile,hd0]
  have hxevent : {t | u.amplitude t < 0} ∈ 𝓝 x :=
    (u.has_gradient x hx₀.le).continuousAt (Iio_mem_nhds hxneg)
  obtain ⟨ε,hε,hεball⟩ := Metric.mem_nhds_iff.mp hxevent
  let b := min (x+ε/2) R
  have hxb : x < b := lt_min (by linarith) hxR
  have hbR : b ≤ R := min_le_right _ _
  have hbε : b ≤ x+ε/2 := min_le_left _ _
  have htneg (t : ℝ) (ht : t ∈ Icc x b) : u.amplitude t < 0 := by
    apply hεball
    rw [Metric.mem_ball,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  have hFanti : StrictAntiOn F (Icc x b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc x b)
    · exact fun t ht => (u.flux_derivative t (hx₀.le.trans ht.1)).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t ∈ Icc x b := interior_subset ht
      have h0 : 0 ≤ t := hx₀.le.trans ht'.1
      change deriv (fun r => D.a r * u.gradient r) t < 0
      rw [(u.flux_derivative t h0).deriv]
      exact mul_neg_of_pos_of_neg
        ((mul_pos D.spMin_pos (pow_pos D.k_pos 2)).trans_le (D.potential_lower hy h0)) (htneg t ht')
  have hUanti : StrictAntiOn u.amplitude (Icc x b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc x b) (hc.mono fun _ ht => hx₀.le.trans ht.1)
    intro t ht
    rw [interior_Icc] at ht
    have hFx := hFanti ⟨le_rfl,hxb.le⟩ ⟨ht.1.le,ht.2.le⟩ ht.1
    rw [hF0] at hFx
    have h0 : 0 ≤ t := hx₀.le.trans ht.1.le
    rw [(u.has_gradient t h0).deriv]
    by_contra! hg
    exact hFx.not_ge (mul_nonneg (D.aMin_pos.le.trans (D.a_bound t h0).1) hg)
  exact (hUanti ⟨le_rfl,hxb.le⟩ ⟨hxb.le,le_rfl⟩ hxb).not_ge
    (hmin ⟨hx₀.le.trans hxb.le,hbR⟩)

private theorem normal_phase_norm_positive (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (u : NormalTransfer D.a (D.potential y)) {r : ℝ} (hr : 0 ≤ r) :
    0 < u.amplitude r^2 + normalFluxProfile D u r^2 := by
  let F := normalFluxProfile D u
  let G (r : ℝ) := u.amplitude r^2 + F r^2
  let C := D.aMin⁻¹ + (D.spMax*D.k^2+D.parMax*y)
  have hG (s : ℝ) (hs : 0 ≤ s) :
      HasDerivAt G (2*(D.a s)⁻¹ * u.amplitude s * F s +
        2*F s * (D.potential y s * u.amplitude s)) s := by
    have ha : D.a s ≠ 0 := (D.aMin_pos.trans_le (D.a_bound s hs).1).ne'
    have hf : (D.a s)⁻¹ * F s = u.gradient s := by
      rw [show F s = D.a s * u.gradient s by rfl,← mul_assoc,inv_mul_cancel₀ ha,one_mul]
    have hu2 : HasDerivAt (fun t => u.amplitude t^2)
        (2*u.amplitude s*u.gradient s) s := by
      simpa using (u.has_gradient s hs).pow 2
    have hF2 : HasDerivAt (fun t => F t^2) (2*F s*(D.potential y s*u.amplitude s)) s := by
      simpa only [show F s = D.a s*u.gradient s from rfl, Nat.cast_ofNat,
        show (2:ℕ)-1=1 by decide,pow_one] using (u.flux_derivative s hs).pow 2
    convert hu2.add hF2 using 1
    rw [show 2*(D.a s)⁻¹*u.amplitude s*F s = 2*u.amplitude s*((D.a s)⁻¹*F s) by ring,hf]
  have hUp (s : ℝ) (hs : 0 ≤ s) :
      0 ≤ C*G s + (2*(D.a s)⁻¹* u.amplitude s*F s +
        2*F s*(D.potential y s*u.amplitude s)) := by
    have ha : 0 < D.a s := D.aMin_pos.trans_le (D.a_bound s hs).1
    have hP : 0 ≤ D.potential y s :=
      (mul_nonneg D.spMin_pos.le (sq_nonneg D.k)).trans (D.potential_lower hy hs)
    have hU : ((D.a s)⁻¹ + D.potential y s) ≤ C := by
      have h := D.potential_upper hy hs
      rw [abs_of_nonneg hP] at h
      exact add_le_add (inv_anti₀ D.aMin_pos (D.a_bound s hs).1) h
    have h_non := add_nonneg (inv_nonneg.mpr ha.le) hP
    have h1 := mul_nonneg (sub_nonneg.mpr hU) (show 0 ≤ G s by dsimp [G]; positivity)
    have h2 := mul_nonneg h_non (sq_nonneg (u.amplitude s+F s))
    dsimp [G] at h1 ⊢
    nlinarith only [h1,h2]
  let T (s : ℝ) := exp (C*s)*G s
  have hT (s : ℝ) (hs : 0 ≤ s) : HasDerivAt T (exp (C*s) *
      (C*G s + (2*(D.a s)⁻¹ * u.amplitude s * F s +
        2*F s * (D.potential y s * u.amplitude s)))) s := by
    convert (((hasDerivAt_id s).const_mul C).exp).mul (hG s hs) using 1
    simp only [id_eq,mul_one]
    ring
  have hmono : MonotoneOn T (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t ht => (hT t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hT t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht₀ : 0 ≤ t := interior_subset ht
      rw [(hT t ht₀).deriv]
      exact mul_nonneg (exp_pos _).le (hUp t ht₀)
  have h0 : 0 < T 0 := by
    simp only [T,G,mul_zero,exp_zero,one_mul,u.boundary_one,one_pow]
    positivity
  exact pos_of_mul_pos_right (h0.trans_le (hmono left_mem_Ici hr hr)) (exp_pos _).le

theorem normal_transfer_positive (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (u : NormalTransfer D.a (D.potential y)) {r : ℝ} (hr : 0 ≤ r) :
    0 < u.amplitude r := by
  refine lt_of_le_of_ne (normal_transfer_nonneg D hy u hr) ?_
  intro h0
  have hR : 0 < r := lt_of_le_of_ne hr (by intro h; rw [← h,u.boundary_one] at h0; norm_num at h0)
  have hMin : IsLocalMin u.amplitude r := by
    filter_upwards [Ioi_mem_nhds hR] with t ht
    rw [← h0]
    exact normal_transfer_nonneg D hy u (le_of_lt ht)
  have hg := hMin.hasDerivAt_eq_zero (u.has_gradient r hr)
  have hp := normal_phase_norm_positive D hy u hr
  simp [normalFluxProfile,← h0,hg] at hp

end UV.TemporalRay
