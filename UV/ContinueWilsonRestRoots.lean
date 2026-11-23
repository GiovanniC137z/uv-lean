import UV.ContinueWilsonTimeSpin

/-! Real rest energies for the two time-spin blocks of the same Wilson
endpoint. The spin signs do not specify a sector or an evolution order. -/

noncomputable section

open MeasureTheory Set Filter Real
open scoped Topology

namespace UV

theorem WilsonRestLaw.block_deriv_strictMono {L : ℝ} (D : WilsonRestLaw L) {σ : ℝ} (hσ : |σ| ≤ 1) :
    StrictMono (D.block σ 1) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(D.block_derivative σ 1 x).deriv]
  exact D.block_second_pos hσ _

theorem WilsonRestLaw.block_strictConvex {L : ℝ} (D : WilsonRestLaw L) {σ : ℝ} (hσ : |σ| ≤ 1) :
    StrictConvexOn ℝ univ (D.block σ 0) := by
  have hc : Continuous (D.block σ 0) := continuous_iff_continuousAt.mpr
    (fun t => (D.block_derivative σ 0 t).continuousAt)
  apply StrictMono.strictConvexOn_univ_of_deriv hc
  have he : deriv (D.block σ 0) = D.block σ 1 := funext (fun t => (D.block_derivative σ 0 t).deriv)
  rw [he]
  exact D.block_deriv_strictMono hσ

theorem WilsonRestLaw.positive_root_slope {L : ℝ} (D : WilsonRestLaw L) {σ b M : ℝ}
    (hσ : |σ| ≤ 1) (hb : 1 < b) (hM : 0 < M) (hz : D.block σ 0 M = b) :
    0 < D.block σ 1 M := by
  have h := (D.block_strictConvex hσ).convexOn.slope_le_deriv (mem_univ (0:ℝ)) (mem_univ M) hM
    (D.block_derivative σ 0 M).differentiableAt
  rw [slope_def_field, hz, D.block_at_zero, sub_zero, (D.block_derivative σ 0 M).deriv] at h
  exact (div_pos (sub_pos.mpr hb) hM).trans_le h

theorem WilsonRestLaw.positive_root_unique {L : ℝ} (D : WilsonRestLaw L) {σ b : ℝ}
    (hσ : |σ| ≤ 1) (hb : 1 < b) : ∃! M : ℝ, 0 < M ∧ D.block σ 0 M = b := by
  have hc : Continuous (D.block σ 0) := continuous_iff_continuousAt.mpr
    (fun t => (D.block_derivative σ 0 t).continuousAt)
  obtain ⟨B,hB,hv⟩ := ((eventually_gt_atTop (0:ℝ)).and
    ((D.block_atTop hσ).eventually (eventually_gt_atTop b))).exists
  obtain ⟨M,hM,hz⟩ := intermediate_value_Icc hB.le hc.continuousOn
    (show b ∈ Icc (D.block σ 0 0) (D.block σ 0 B) from ⟨D.block_at_zero σ ▸ hb.le,hv.le⟩)
  have hM0 : M ≠ 0 := fun h => hb.ne (by simpa only [h, D.block_at_zero] using hz)
  refine ⟨M, ⟨hM.1.lt_of_ne hM0.symm, hz⟩, ?_⟩
  intro N hN
  have noless (x y : ℝ) (hx : 0 < x) (hxy : x < y)
      (hxz : D.block σ 0 x = b) (hyz : D.block σ 0 y = b) : False := by
    have hh := (D.block_strictConvex hσ).convexOn.deriv_le_slope (mem_univ x) (mem_univ y) hxy
      (D.block_derivative σ 0 x).differentiableAt
    rw [slope_def_field, hxz, hyz, sub_self, zero_div, (D.block_derivative σ 0 x).deriv] at hh
    exact (D.positive_root_slope hσ hb hx hxz).not_ge hh
  exact le_antisymm (le_of_not_gt (fun h => noless M N (hM.1.lt_of_ne hM0.symm) h hz hN.2))
    (le_of_not_gt (fun h => noless N M hN.1 h hN.2 hz))

theorem WilsonRestLaw.symmetric_moment_derivative_pos {L : ℝ} (D : WilsonRestLaw L) {x : ℝ} (hx : 0 < x) :
    0 < D.moment 1 x := by
  have h := D.block_deriv_strictMono (σ := 0) (by norm_num) hx
  simpa only [D.block_moments, zero_div, zero_mul, add_zero, D.mean_zero] using h

theorem WilsonRestLaw.spin_order {L : ℝ} (D : WilsonRestLaw L) {x : ℝ} (hx : 0 < x) :
    D.block (-1) 0 x < D.block 1 0 x := by
  rw [D.block_moments, D.block_moments]
  have hp := D.symmetric_moment_derivative_pos hx
  have hl := D.length_pos
  change _ + -1/(2*L)*D.moment 1 x < _ + 1/(2*L)*D.moment 1 x
  have h : 0 < 1 / (2*L) * D.moment 1 x := by positivity
  rw [neg_div, neg_mul]
  linarith

/-- The rest masses are ordered strictly; the negative root in the opposite
spin block is precisely the reflected positive root. -/
theorem WilsonRestLaw.two_rest_masses {L lam : ℝ} (D : WilsonRestLaw L) (hlam : 0 < lam) (hl : lam < 1) :
    ∃ Mplus Mminus : ℝ, 0 < Mplus ∧ Mplus < Mminus ∧
      (∀ x, D.block 1 0 x = lam⁻¹ ↔ x = Mplus ∨ x = -Mminus) ∧
      (∀ x, D.block (-1) 0 x = lam⁻¹ ↔ x = Mminus ∨ x = -Mplus) ∧
      0 < D.block 1 1 Mplus ∧ 0 < D.block (-1) 1 Mminus := by
  have hb : 1 < lam⁻¹ := (one_lt_inv₀ hlam).mpr hl
  obtain ⟨p,⟨hp,hpz⟩,hpu⟩ := D.positive_root_unique (σ := 1) (by norm_num) hb
  obtain ⟨q,⟨hq,hqz⟩,hqu⟩ := D.positive_root_unique (σ := -1) (by norm_num) hb
  have hi := D.spin_order hq
  rw [hqz] at hi
  have hc : Continuous (D.block 1 0) := continuous_iff_continuousAt.mpr (fun x => (D.block_derivative 1 0 x).continuousAt)
  obtain ⟨t,ht,htz⟩ := intermediate_value_Icc hq.le hc.continuousOn
    (show lam⁻¹ ∈ Icc (D.block 1 0 0) (D.block 1 0 q) from ⟨by simpa only [D.block_at_zero] using hb.le, hi.le⟩)
  have ht₀ := ht.1.lt_of_ne (fun h => hb.ne (by simpa only [← h, D.block_at_zero] using htz))
  have htq := ht.2.lt_of_ne (fun h => hi.ne' (by simpa only [h] using htz))
  have hpq := (hpu t ⟨ht₀,htz⟩) ▸ htq
  have both (σ u v : ℝ) (hu : D.block σ 0 u = lam⁻¹) (hv : D.block (-σ) 0 v = lam⁻¹)
      (uu : ∀ x, (0 < x ∧ D.block σ 0 x = lam⁻¹) → x = u)
      (uv : ∀ x, (0 < x ∧ D.block (-σ) 0 x = lam⁻¹) → x = v) (x : ℝ) :
      D.block σ 0 x = lam⁻¹ ↔ x = u ∨ x = -v := by
    constructor
    · intro hx
      rcases lt_trichotomy 0 x with h | h | h
      · exact Or.inl (uu x ⟨h,hx⟩)
      · subst x
        exact (hb.ne (show 1 = lam⁻¹ from (D.block_at_zero σ).symm.trans hx)).elim
      · have he := D.block_reflect (-σ) x
        rw [neg_neg] at he
        have hh := uv (-x) ⟨neg_pos.mpr h,he.trans hx⟩
        exact Or.inr (by linarith)
    · rintro (rfl | rfl)
      · exact hu
      · rw [D.block_reflect, hv]
  refine ⟨p,q,hp,hpq,both 1 p q hpz hqz hpu hqu, ?_,
    D.positive_root_slope (by norm_num) hb hp hpz, D.positive_root_slope (by norm_num) hb hq hqz⟩
  simpa only [neg_neg] using both (-1) q p hqz (by simpa only [neg_neg] using hpz) hqu
    (by simpa only [neg_neg] using hpu)

theorem WilsonRestLaw.reflected_root_derivative {L : ℝ} (D : WilsonRestLaw L) (σ x : ℝ) :
    D.block σ 1 (-x) = -D.block (-σ) 1 x := by
  have h := (D.block_derivative σ 0 (-x)).comp x (hasDerivAt_neg x)
  have he : D.block σ 0 ∘ Neg.neg = D.block (-σ) 0 := funext (D.block_reflect σ)
  rw [he] at h
  have he' := h.unique (D.block_derivative (-σ) 0 x)
  simpa only [mul_neg_one,neg_eq_iff_eq_neg] using he'

theorem WilsonRestLaw.real_root_derivative_nonzero {L lam σ M : ℝ} (D : WilsonRestLaw L)
    (hσ : |σ| ≤ 1) (hlam : 0 < lam) (hl : lam < 1) (hr : D.block σ 0 M = lam⁻¹) :
    D.block σ 1 M ≠ 0 := by
  have hb : 1 < lam⁻¹ := (one_lt_inv₀ hlam).mpr hl
  rcases lt_trichotomy 0 M with hp | h | hm
  · exact (D.positive_root_slope hσ hb hp hr).ne'
  · exact (hb.ne (by simpa only [← h,D.block_at_zero] using hr)).elim
  · have hn := D.block_reflect (-σ) M
    rw [neg_neg,hr] at hn
    have hd := D.positive_root_slope (σ := -σ) (by simpa only [abs_neg] using hσ) hb (neg_pos.mpr hm) hn
    have he := D.reflected_root_derivative (-σ) M
    rw [neg_neg] at he
    rw [he] at hd
    exact (neg_pos.mp hd).ne

end UV
