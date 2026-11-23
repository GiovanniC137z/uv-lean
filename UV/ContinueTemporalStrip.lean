import UV.ContinueTemporalMaximum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The optical strip estimate for the transverse normal equation in
the expanded manuscript, at the strip discussion following
`prop:closure-native-uv`. -/

noncomputable section

namespace UV.TemporalRay

open Filter MeasureTheory Set Real
open scoped Interval Topology

/-- Optical length measured with the actual longitudinal coefficient of
the normal channel. -/
def NormalChannel.opticalCoordinate (D : NormalChannel) (r : ℝ) : ℝ :=
  ∫ s in 0..r, (D.a s)⁻¹

private theorem NormalChannel.a_pos (D : NormalChannel) {r : ℝ} (hr : 0 ≤ r) :
    0 < D.a r :=
  D.aMin_pos.trans_le (D.a_bound r hr).1

private theorem NormalChannel.optical_integrable (D : NormalChannel) {r₁ r₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (h₁₂ : r₁ ≤ r₂) :
    IntervalIntegrable (fun s => (D.a s)⁻¹) volume r₁ r₂ := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le h₁₂]
  exact D.continuous_a.continuousOn.inv₀ (fun r hr => (D.a_pos (hr₁.trans hr.1)).ne')

theorem NormalChannel.optical_coordinate_hasDerivAt (D : NormalChannel) {r : ℝ} (hr : 0 ≤ r) :
    HasDerivAt D.opticalCoordinate (D.a r)⁻¹ r := by
  have hc : ContinuousAt (fun s => (D.a s)⁻¹) r :=
    D.continuous_a.continuousAt.inv₀ (D.a_pos hr).ne'
  exact intervalIntegral.integral_hasDerivAt_right (D.optical_integrable le_rfl hr)
    (D.continuous_a.measurable.inv.aestronglyMeasurable.stronglyMeasurableAtFilter) hc

/-- Bounded positive normal coefficients give the corresponding lower
bound on the actual optical length, with the manuscript's Jacobian. -/
theorem NormalChannel.optical_length_lower (D : NormalChannel) {r₁ r₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (h₁₂ : r₁ ≤ r₂) :
    (r₂ - r₁) / D.aMax ≤ D.opticalCoordinate r₂ - D.opticalCoordinate r₁ := by
  have hconst : IntervalIntegrable (fun _ : ℝ => D.aMax⁻¹) volume r₁ r₂ := intervalIntegrable_const
  have h := intervalIntegral.integral_mono_on h₁₂ hconst (D.optical_integrable hr₁ h₁₂)
    (fun r hr => inv_anti₀ (D.a_pos (hr₁.trans hr.1)) (D.a_bound r (hr₁.trans hr.1)).2)
  rw [intervalIntegral.integral_const, smul_eq_mul, ← div_eq_mul_inv] at h
  unfold NormalChannel.opticalCoordinate
  have hadd := intervalIntegral.integral_add_adjacent_intervals (D.optical_integrable le_rfl hr₁)
    (D.optical_integrable hr₁ h₁₂)
  linarith only [h, hadd]

theorem normal_transfer_flux_nonpos (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (u : NormalTransfer D.a (D.potential y)) {r : ℝ} (hr : 0 ≤ r) :
    normalFluxProfile D u r ≤ 0 := by
  have hmono : MonotoneOn (normalFluxProfile D u) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun s hs => (u.flux_derivative s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (u.flux_derivative s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs₀ : 0 ≤ s := interior_subset hs
      change 0 ≤ deriv (fun t => D.a t * u.gradient t) s
      rw [(u.flux_derivative s hs₀).deriv]
      exact mul_nonneg ((mul_nonneg D.spMin_pos.le (sq_nonneg D.k)).trans (D.potential_lower hy hs₀))
        (normal_transfer_positive D hy u hs₀).le
  by_contra! hFp
  have hgrad (s : ℝ) (hs : r ≤ s) : 0 ≤ u.gradient s := by
    have hp := hFp.le.trans (hmono hr (hr.trans hs) hs)
    by_contra! hneg
    exact (mul_neg_of_pos_of_neg (D.a_pos (hr.trans hs)) hneg).not_ge hp
  have hu : MonotoneOn u.amplitude (Ici r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici r)
    · exact fun s hs => (u.has_gradient s (hr.trans hs)).continuousAt.continuousWithinAt
    · intro s hs
      exact (u.has_gradient s (hr.trans (interior_subset hs))).differentiableAt.differentiableWithinAt
    · intro s hs
      have hrs : r ≤ s := interior_subset hs
      rw [(u.has_gradient s (hr.trans hrs)).deriv]
      exact hgrad s hrs
  have hsmall := (normal_amplitude_tendsto_zero u.toNormalProfile).eventually_lt_const
    (normal_transfer_positive D hy u hr)
  obtain ⟨s, hs, hus⟩ := ((eventually_ge_atTop r).and hsmall).exists
  exact hus.not_ge (hu (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs) hs)

theorem normal_transfer_antitone_in_radius (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (u : NormalTransfer D.a (D.potential y)) :
    AntitoneOn u.amplitude (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · exact fun r hr => (u.has_gradient r hr).continuousAt.continuousWithinAt
  · intro r hr
    exact (u.has_gradient r (interior_subset hr)).differentiableAt.differentiableWithinAt
  · intro r hr
    have hr₀ : 0 ≤ r := interior_subset hr
    rw [(u.has_gradient r hr₀).deriv]
    by_contra! hp
    exact (mul_pos (D.a_pos hr₀) hp).not_ge (normal_transfer_flux_nonpos D hy u hr₀)

/-- The exact optical-strip comparison for a regular positive
finite-energy channel. The terminal Wronskian has the sign of minus the
outgoing normal flux. The sharper inequality keeps the entrance
amplitude of the actual mode. -/
theorem normal_transfer_optical_strip_sharp (D : NormalChannel) (ω : ℝ)
    (u : NormalTransfer D.a (D.potential (ω ^ 2))) {r₁ r₂ r d : ℝ}
    (hr₁ : 0 ≤ r₁) (h₁₂ : r₁ ≤ r₂) (h₂r : r₂ ≤ r) (hd : 0 < d)
    (hstrip : ∀ s ∈ Icc r₁ r₂, d ≤ D.a s * D.temporal s) :
    u.amplitude r ≤ u.amplitude r₁ /
      cosh (Real.sqrt d * |ω| * (D.opticalCoordinate r₂ - D.opticalCoordinate r₁)) := by
  let q := Real.sqrt d * |ω|
  let z (s : ℝ) := q * (D.opticalCoordinate r₂ - D.opticalCoordinate s)
  let C (s : ℝ) := cosh (z s)
  let S (s : ℝ) := sinh (z s)
  let F := normalFluxProfile D u
  let W (s : ℝ) := -(C s * F s) - q * S s * u.amplitude s
  have hq : q ^ 2 = d * ω ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hd.le, sq_abs]
  have hC (s : ℝ) (hs : 0 ≤ s) :
      HasDerivAt C (sinh (z s) * (-(q * (D.a s)⁻¹))) s := by
    convert (((D.optical_coordinate_hasDerivAt hs).const_sub (D.opticalCoordinate r₂)).const_mul q).cosh using 1
    ring
  have hS (s : ℝ) (hs : 0 ≤ s) :
      HasDerivAt S (cosh (z s) * (-(q * (D.a s)⁻¹))) s := by
    convert (((D.optical_coordinate_hasDerivAt hs).const_sub (D.opticalCoordinate r₂)).const_mul q).sinh using 1
    ring
  have hW (s : ℝ) (hs : 0 ≤ s) :
      HasDerivAt W (-(C s * ((D.potential (ω ^ 2) s) - q ^ 2 * (D.a s)⁻¹) * u.amplitude s)) s := by
    have hD := ((hC s hs).mul (u.flux_derivative s hs)).neg.sub
      (((hS s hs).const_mul q).mul (u.has_gradient s hs))
    convert hD using 1
    dsimp only [C, S, F, normalFluxProfile]
    field_simp [(D.a_pos hs).ne']
    ring
  have hanti : AntitoneOn W (Icc r₁ r₂) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc r₁ r₂)
    · exact fun s hs => (hW s (hr₁.trans hs.1)).continuousAt.continuousWithinAt
    · intro s hs
      exact (hW s (hr₁.trans (interior_subset hs).1)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hsi : s ∈ Icc r₁ r₂ := interior_subset hs
      have h₀ : 0 ≤ s := hr₁.trans hsi.1
      have hP : q ^ 2 * (D.a s)⁻¹ ≤ D.potential (ω ^ 2) s := by
        rw [hq, ← div_eq_mul_inv]
        apply (div_le_iff₀ (D.a_pos h₀)).mpr
        calc
          _ ≤ D.a s * D.temporal s * ω ^ 2 :=
            mul_le_mul_of_nonneg_right (hstrip s hsi) (sq_nonneg ω)
          _ ≤ _ := by
            unfold NormalChannel.potential modePotential
            have hm := mul_nonneg (D.a_pos h₀).le
              (mul_nonneg (D.spMin_pos.le.trans (D.spatial_bound s h₀).1) (sq_nonneg D.k))
            nlinarith only [hm]
      rw [(hW s h₀).deriv]
      exact neg_nonpos.mpr (mul_nonneg (mul_nonneg (cosh_pos _).le (sub_nonneg.mpr hP))
        (normal_transfer_positive D (sq_nonneg ω) u h₀).le)
  have hW₂ : 0 ≤ W r₂ := by
    simpa [W, C, S, z, F] using neg_nonneg.mpr (normal_transfer_flux_nonpos D (sq_nonneg ω) u (hr₁.trans h₁₂))
  let R (s : ℝ) := u.amplitude s / C s
  have hR (s : ℝ) (hs : 0 ≤ s) :
      HasDerivAt R (-W s / (D.a s * C s ^ 2)) s := by
    convert (u.has_gradient s hs).div (hC s hs) (cosh_pos _).ne' using 1
    dsimp only [W, C, S, F, normalFluxProfile]
    field_simp [(D.a_pos hs).ne', (cosh_pos (z s)).ne']
    ring
  have hRanti : AntitoneOn R (Icc r₁ r₂) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc r₁ r₂)
    · exact fun s hs => (hR s (hr₁.trans hs.1)).continuousAt.continuousWithinAt
    · intro s hs
      exact (hR s (hr₁.trans (interior_subset hs).1)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hi : s ∈ Icc r₁ r₂ := interior_subset hs
      have hn := hW₂.trans (hanti hi ⟨h₁₂, le_rfl⟩ hi.2)
      rw [(hR s (hr₁.trans hi.1)).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hn)
        (mul_nonneg (D.a_pos (hr₁.trans hi.1)).le (sq_nonneg _))
  have hlim := hRanti ⟨le_rfl, h₁₂⟩ ⟨h₁₂, le_rfl⟩ h₁₂
  have hread := normal_transfer_antitone_in_radius D (sq_nonneg ω) u (mem_Ici.mpr (hr₁.trans h₁₂))
    (mem_Ici.mpr ((hr₁.trans h₁₂).trans h₂r)) h₂r
  apply hread.trans
  simpa [R, C, z, q] using hlim

/-- The displayed unit-boundary-amplitude bound at and beyond r₂. -/
theorem normal_transfer_optical_strip (D : NormalChannel) (ω : ℝ)
    (u : NormalTransfer D.a (D.potential (ω ^ 2))) {r₁ r₂ r d : ℝ}
    (hr₁ : 0 ≤ r₁) (h₁₂ : r₁ ≤ r₂) (h₂r : r₂ ≤ r) (hd : 0 < d)
    (hstrip : ∀ s ∈ Icc r₁ r₂, d ≤ D.a s * D.temporal s) :
    u.amplitude r ≤ 1 / cosh (Real.sqrt d * |ω| * (D.opticalCoordinate r₂ - D.opticalCoordinate r₁)) := by
  have h₀ := normal_transfer_antitone_in_radius D (sq_nonneg ω) u
    (mem_Ici.mpr (le_rfl : (0 : ℝ) ≤ 0)) (mem_Ici.mpr hr₁) hr₁
  rw [u.boundary_one] at h₀
  exact (normal_transfer_optical_strip_sharp D ω u hr₁ h₁₂ h₂r hd hstrip).trans
    (div_le_div_of_nonneg_right h₀ (cosh_pos _).le)

end UV.TemporalRay
