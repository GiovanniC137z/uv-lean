import UV.ContinueConeAngularLaw
import UV.ContinueCarrierConeBounds

/-! Angular tests of the literal first and second cone poles. Subtraction at
the normal coordinate zero uses the exact constant and affine averages. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Real Set
open scoped Interval Topology

/-- Pairing against the normalized angular law, with test in the normal
coordinate and with the original sign of the pole. -/
def coneAngularPairing (η t : ℝ) (n : ℕ) (g : ℝ → ℂ) : ℂ :=
  ∫ θ in (0 : ℝ)..π, coneAngularWeight θ • (g (cos θ) * coneAngularPole η t θ ^ n)

private theorem coneAngularWeight_continuous : Continuous coneAngularWeight :=
  (continuous_const.sub continuous_cos).div_const π

private theorem coneAngularWeight_nonneg (θ : ℝ) : 0 ≤ coneAngularWeight θ :=
  div_nonneg (sub_nonneg.mpr (cos_le_one θ)) pi_pos.le

private theorem coneAngularWeight_one :
    (∫ θ in (0 : ℝ)..π, coneAngularWeight θ) = 1 := by
  have h := cone_angular_density_integral (fun _ : ℝ => (1 : ℝ))
  simpa only [smul_eq_mul, mul_one, coneAngularWeight, cone_angular_density_mass_one] using h

private theorem cone_angular_pairing_continuous {g : ℝ → ℂ} (hg : Continuous g)
    {η t : ℝ} (hη : η ^ 2 = 1) (ht : 0 < t) (n : ℕ) :
    Continuous fun θ => coneAngularWeight θ • (g (cos θ) * coneAngularPole η t θ ^ n) :=
  coneAngularWeight_continuous.smul
    ((hg.comp continuous_cos).mul ((coneAngularPole_continuous ht hη).pow n))

private theorem cone_angular_pole_scale {η t : ℝ} (hη : η ^ 2 = 1) (ht : 0 < t) (θ : ℝ) :
    |cos θ| * ‖coneAngularPole η t θ‖ ≤ 1 := by
  let z : ℂ := (cos θ : ℂ) + Complex.I * ((η * t : ℝ) : ℂ)
  have hRe : z.re = cos θ := by simp [z, Complex.mul_re, -Complex.ofReal_cos]
  have hZ : z ≠ 0 := by
    intro hz
    have him : η * t = 0 := by
      simpa [z, Complex.mul_im, -Complex.ofReal_cos] using congrArg Complex.im hz
    have hη₀ : η ≠ 0 := by intro hh; simp [hh] at hη
    exact (mul_ne_zero hη₀ ht.ne') him
  change |cos θ| * ‖z⁻¹‖ ≤ 1
  rw [norm_inv, ← div_eq_mul_inv, div_le_one (norm_pos_iff.mpr hZ), ← hRe]
  exact Complex.abs_re_le_norm z

private theorem cone_angular_remainder_bound {g : ℝ → ℂ} {n : ℕ} {M : ℝ}
    (hM : 0 ≤ M) (hg : ∀ u ∈ Icc (-1 : ℝ) 1, ‖g u‖ ≤ M * |u| ^ n)
    {η t : ℝ} (hη : η ^ 2 = 1) (ht : 0 < t) (θ : ℝ) :
    ‖coneAngularWeight θ • (g (cos θ) * coneAngularPole η t θ ^ n)‖ ≤
      M * coneAngularWeight θ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (coneAngularWeight_nonneg θ), norm_mul,
    norm_pow, mul_comm M]
  apply mul_le_mul_of_nonneg_left _ (coneAngularWeight_nonneg θ)
  calc
    _ ≤ (M * |cos θ| ^ n) * ‖coneAngularPole η t θ‖ ^ n :=
      mul_le_mul_of_nonneg_right (hg _ ⟨neg_one_le_cos θ, cos_le_one θ⟩) (by positivity)
    _ = M * (|cos θ| * ‖coneAngularPole η t θ‖) ^ n := by rw [mul_pow, mul_assoc]
    _ ≤ M := mul_le_of_le_one_right hM
      (pow_le_one₀ (by positivity) (cone_angular_pole_scale hη ht θ))

/-- At every positive height, a normal test that vanishes to order n has
pairing bounded by the normal Taylor remainder constant. -/
theorem cone_angular_remainder_pairing_norm_le {g : ℝ → ℂ} (hc : Continuous g)
    {n : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ u ∈ Icc (-1 : ℝ) 1, ‖g u‖ ≤ M * |u| ^ n)
    {η t : ℝ} (hη : η ^ 2 = 1) (ht : 0 < t) :
    ‖coneAngularPairing η t n g‖ ≤ M := by
  have hD := cone_angular_pairing_continuous hc hη ht n
  calc
    _ ≤ ∫ θ in (0 : ℝ)..π, ‖coneAngularWeight θ •
        (g (cos θ) * coneAngularPole η t θ ^ n)‖ :=
      intervalIntegral.norm_integral_le_integral_norm pi_pos.le
    _ ≤ ∫ θ in (0 : ℝ)..π, M * coneAngularWeight θ :=
      intervalIntegral.integral_mono pi_pos.le (hD.norm.intervalIntegrable _ _)
        ((continuous_const.mul coneAngularWeight_continuous).intervalIntegrable _ _)
        (cone_angular_remainder_bound hM hg hη ht)
    _ = _ := by rw [intervalIntegral.integral_const_mul, coneAngularWeight_one, mul_one]

private theorem cone_angular_remainder_point_limit {g : ℝ → ℂ} {n : ℕ} {M : ℝ}
    (hg : ∀ u ∈ Icc (-1 : ℝ) 1, ‖g u‖ ≤ M * |u| ^ n) (η θ : ℝ) :
    Tendsto (fun t => coneAngularWeight θ • (g (cos θ) * coneAngularPole η t θ ^ n))
      (𝓝[>] (0 : ℝ))
      (𝓝 (coneAngularWeight θ • (g (cos θ) * ((cos θ : ℂ)⁻¹) ^ n))) := by
  by_cases hz : cos θ = 0
  · cases n with
    | zero => simp
    | succ n =>
      have h0 : g 0 = 0 := by
        apply norm_eq_zero.mp
        exact le_antisymm (by simpa using hg 0 (by norm_num : (0 : ℝ) ∈ Icc (-1) 1))
          (norm_nonneg _)
      simp [hz, h0]
  · let z (t : ℝ) : ℂ := (cos θ : ℂ) + Complex.I * ((η * t : ℝ) : ℂ)
    have hc : Continuous z := continuous_const.add
      (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))
    have h0 : z 0 = (cos θ : ℂ) := by simp [z, -Complex.ofReal_cos]
    have hn : z 0 ≠ 0 := by rwa [h0, Complex.ofReal_ne_zero]
    have H := ((hc.continuousAt (x := 0)).inv₀ hn).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [h0] at H
    exact ((H.pow n).const_mul (g (cos θ))).const_smul (coneAngularWeight θ)

/-- A vanishing normal remainder may pass to the ordinary inverse power.
The limiting integrand is integrable even at the angular shell. -/
theorem cone_angular_remainder_pairing_tendsto {g : ℝ → ℂ} (hc : Continuous g)
    {n : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ u ∈ Icc (-1 : ℝ) 1, ‖g u‖ ≤ M * |u| ^ n)
    {η : ℝ} (hη : η ^ 2 = 1) :
    Tendsto (fun t => coneAngularPairing η t n g) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ θ in (0 : ℝ)..π, coneAngularWeight θ •
        (g (cos θ) * ((cos θ : ℂ)⁻¹) ^ n))) := by
  simp_rw [coneAngularPairing, intervalIntegral.integral_of_le pi_pos.le]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun θ => M * coneAngularWeight θ)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (cone_angular_pairing_continuous hc hη ht n).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact Eventually.of_forall (cone_angular_remainder_bound hM hg hη ht)
  · exact ((continuous_const.mul coneAngularWeight_continuous).intervalIntegrable 0 π).1
  · exact Eventually.of_forall (cone_angular_remainder_point_limit hg η)

private theorem cone_first_closed_continuous (η : ℝ) : Continuous (coneFirstClosed η) := by
  have hS : Continuous (fun t : ℝ => (sqrt (1 + t ^ 2) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2)))
  have hS₀ (t : ℝ) : (sqrt (1 + t ^ 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sqrt_pos.mpr (by positivity)).ne'
  exact ((Complex.continuous_ofReal.sub continuous_const).div hS hS₀).sub continuous_const

private theorem cone_second_closed_continuous (η : ℝ) : Continuous (coneSecondClosed η) := by
  have hS : Continuous (fun t : ℝ => (sqrt (1 + t ^ 2) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2)))
  have hS₀ (t : ℝ) : (sqrt (1 + t ^ 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sqrt_pos.mpr (by positivity)).ne'
  exact (continuous_const.sub Complex.continuous_ofReal).div (hS.pow 3)
    (fun t => pow_ne_zero _ (hS₀ t))

private theorem cone_angular_first_tendsto {η : ℝ} (hη : η ^ 2 = 1) :
    Tendsto (coneAngularFirst η) (𝓝[>] (0 : ℝ)) (𝓝 (-1 - Complex.I * (η : ℂ))) := by
  have h := (cone_first_closed_continuous η).continuousAt (x := 0)
    |>.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have h0 : coneFirstClosed η 0 = -1 - Complex.I * (η : ℂ) := by
    norm_num [coneFirstClosed]
    ring
  rw [h0] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (coneAngularFirst_eq_closed ht hη).symm

private theorem cone_angular_second_tendsto {η : ℝ} (hη : η ^ 2 = 1) :
    Tendsto (coneAngularSecond η) (𝓝[>] (0 : ℝ)) (𝓝 (Complex.I * (η : ℂ))) := by
  have h := (cone_second_closed_continuous η).continuousAt (x := 0)
    |>.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have h0 : coneSecondClosed η 0 = Complex.I * (η : ℂ) := by norm_num [coneSecondClosed]
  rw [h0] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (coneAngularSecond_eq_closed ht hη).symm

private theorem cone_angular_pairing_one_split {g : ℝ → ℂ} (hc : Continuous g)
    {η t : ℝ} (hη : η ^ 2 = 1) (ht : 0 < t) :
    coneAngularPairing η t 1 g =
      g 0 * coneAngularFirst η t + coneAngularPairing η t 1 (fun u => g u - g 0) := by
  let P := coneAngularPole η t
  have hP : Continuous P := coneAngularPole_continuous ht hη
  unfold coneAngularPairing coneAngularFirst
  simp only [pow_one]
  have hpoint (θ : ℝ) :
      coneAngularWeight θ • (g (cos θ) * P θ) =
        g 0 * (coneAngularWeight θ • P θ) +
          coneAngularWeight θ • ((g (cos θ) - g 0) * P θ) := by
    simp only [Complex.real_smul]
    ring
  change (∫ θ in (0 : ℝ)..π, coneAngularWeight θ • (g (cos θ) * P θ)) = _
  simp_rw [hpoint]
  have h₁ : Continuous (fun θ => g 0 * (coneAngularWeight θ • P θ)) :=
    continuous_const.mul (coneAngularWeight_continuous.smul hP)
  have h₂ : Continuous (fun θ => coneAngularWeight θ • ((g (cos θ) - g 0) * P θ)) :=
    coneAngularWeight_continuous.smul (((hc.comp continuous_cos).sub continuous_const).mul hP)
  rw [intervalIntegral.integral_add (h₁.intervalIntegrable _ _) (h₂.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]

private theorem cone_angular_pairing_square_split {g : ℝ → ℂ} (hc : Continuous g) (d : ℂ)
    {η t : ℝ} (hη : η ^ 2 = 1) (ht : 0 < t) :
    coneAngularPairing η t 2 g =
      g 0 * coneAngularSecond η t +
      d * (coneAngularFirst η t -
        Complex.I * ((η * t : ℝ) : ℂ) * coneAngularSecond η t) +
      coneAngularPairing η t 2 (fun u => g u - g 0 - (u : ℂ) * d) := by
  let P := coneAngularPole η t
  let Z : ℂ := Complex.I * ((η * t : ℝ) : ℂ)
  let W := coneAngularWeight
  let R (u : ℝ) := g u - g 0 - (u : ℂ) * d
  have hP : Continuous P := coneAngularPole_continuous ht hη
  have hw : Continuous W := coneAngularWeight_continuous
  have hR : Continuous R := (hc.sub continuous_const).sub
    (Complex.continuous_ofReal.mul continuous_const)
  have hC₀ : Continuous (fun θ => W θ • P θ ^ 2) := hw.smul (hP.pow 2)
  have hC₁ : Continuous (fun θ => W θ • P θ) := hw.smul hP
  have hpoint (θ : ℝ) :
      W θ • (g (cos θ) * P θ ^ 2) =
        (g 0 * (W θ • P θ ^ 2) +
          d * (W θ • P θ - Z * (W θ • P θ ^ 2))) +
          W θ • (R (cos θ) * P θ ^ 2) := by
    have hId : (cos θ : ℂ) * P θ ^ 2 = P θ - Z * P θ ^ 2 :=
      coneAngularPole_identity ht hη θ
    simp only [Complex.real_smul]
    unfold R
    linear_combination (W θ : ℂ) * d * hId
  change (∫ θ in (0 : ℝ)..π, W θ • (g (cos θ) * P θ ^ 2)) = _
  simp_rw [hpoint]
  rw [intervalIntegral.integral_add
    (((continuous_const.mul hC₀).add
      (continuous_const.mul (hC₁.sub (continuous_const.mul hC₀)))).intervalIntegrable _ _)
    ((cone_angular_pairing_continuous hR hη ht 2).intervalIntegrable _ _),
    intervalIntegral.integral_add
      ((continuous_const.mul hC₀).intervalIntegrable _ _)
      ((continuous_const.mul (hC₁.sub (continuous_const.mul hC₀))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hC₁.intervalIntegrable _ _)
      ((continuous_const.mul hC₀).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]
  rfl

/-- Exact normalized angular first-pole limit for arbitrary complex normal
tests with a controlled linear remainder. -/
theorem cone_angular_single_pairing_tendsto {g : ℝ → ℂ} (hc : Continuous g)
    {M : ℝ} (hM : 0 ≤ M) (hg : ∀ u ∈ Icc (-1 : ℝ) 1, ‖g u - g 0‖ ≤ M * |u|)
    {η : ℝ} (hη : η ^ 2 = 1) :
    Tendsto (fun t => coneAngularPairing η t 1 g) (𝓝[>] (0 : ℝ))
      (𝓝 (g 0 * (-1 - Complex.I * (η : ℂ)) +
        ∫ θ in (0 : ℝ)..π, coneAngularWeight θ •
          ((g (cos θ) - g 0) * (cos θ : ℂ)⁻¹))) := by
  have hR := cone_angular_remainder_pairing_tendsto (hc.sub continuous_const) hM
    (η := η) (n := 1) (by simpa only [pow_one] using hg) hη
  simp only [pow_one] at hR
  apply (((cone_angular_first_tendsto hη).const_mul (g 0)).add hR).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (cone_angular_pairing_one_split hc hη ht).symm

theorem cone_angular_single_pairing_norm_le {g : ℝ → ℂ} (hc : Continuous g)
    {M : ℝ} (hM : 0 ≤ M) (h0 : ‖g 0‖ ≤ M)
    (hg : ∀ u ∈ Icc (-1 : ℝ) 1, ‖g u - g 0‖ ≤ M * |u|)
    {η t : ℝ} (hη : η ^ 2 = 1) (ht : 0 < t) :
    ‖coneAngularPairing η t 1 g‖ ≤ 3 * M := by
  rw [cone_angular_pairing_one_split hc hη ht]
  have hRem := cone_angular_remainder_pairing_norm_le (hc.sub continuous_const) hM
    (n := 1) (by simpa only [pow_one] using hg) hη ht
  have hA : ‖coneAngularFirst η t‖ ≤ 2 := by
    rw [coneAngularFirst_eq_closed ht hη]
    exact coneFirstClosed_norm_le hη t
  have h₀ : ‖g 0 * coneAngularFirst η t‖ ≤ M * 2 := by
    rw [norm_mul]
    exact mul_le_mul h0 hA (norm_nonneg _) hM
  exact (norm_add_le _ _).trans (by linarith only [h₀, hRem])

/-- Exact normalized angular square limit for arbitrary complex normal tests
with a controlled quadratic remainder after subtracting their normal jet. -/
theorem cone_angular_square_pairing_tendsto {g : ℝ → ℂ} (hc : Continuous g)
    (d : ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ u ∈ Icc (-1 : ℝ) 1, ‖g u - g 0 - (u : ℂ) * d‖ ≤ M * |u| ^ 2)
    {η : ℝ} (hη : η ^ 2 = 1) :
    Tendsto (fun t => coneAngularPairing η t 2 g) (𝓝[>] (0 : ℝ))
      (𝓝 (g 0 * (Complex.I * (η : ℂ)) + d * (-1 - Complex.I * (η : ℂ)) +
        ∫ θ in (0 : ℝ)..π, coneAngularWeight θ •
          ((g (cos θ) - g 0 - (cos θ : ℂ) * d) * ((cos θ : ℂ)⁻¹) ^ 2))) := by
  have hR := cone_angular_remainder_pairing_tendsto
    ((hc.sub continuous_const).sub (Complex.continuous_ofReal.mul continuous_const)) hM hg hη
  have h₁ := cone_angular_first_tendsto hη
  have h₂ := cone_angular_second_tendsto hη
  have hZ : Tendsto (fun t : ℝ => Complex.I * ((η * t : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcZ : Continuous (fun t : ℝ => Complex.I * ((η * t : ℝ) : ℂ)) :=
      continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id))
    simpa only [mul_zero, Complex.ofReal_zero] using
      hcZ.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))
  have H := ((h₂.const_mul (g 0)).add
    ((h₁.sub (hZ.mul h₂)).const_mul d)).add hR
  simp only [zero_mul, sub_zero] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (cone_angular_pairing_square_split hc d hη ht).symm

/-- Uniform bound for the same actual finite-height squared pairing. -/
theorem cone_angular_square_pairing_norm_le {g : ℝ → ℂ} (hc : Continuous g)
    (d : ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ u ∈ Icc (-1 : ℝ) 1, ‖g u - g 0 - (u : ℂ) * d‖ ≤ M * |u| ^ 2)
    {η t : ℝ} (hη : η ^ 2 = 1) (ht : 0 < t) :
    ‖coneAngularPairing η t 2 g‖ ≤ ‖g 0‖ + 3 * ‖d‖ + M := by
  rw [cone_angular_pairing_square_split hc d hη ht]
  refine (norm_add_le _ _).trans (add_le_add ?_
    (cone_angular_remainder_pairing_norm_le
      ((hc.sub continuous_const).sub (Complex.continuous_ofReal.mul continuous_const)) hM hg hη ht))
  rw [coneAngularFirst_eq_closed ht hη, coneAngularSecond_eq_closed ht hη]
  have h₁ := coneFirstClosed_norm_le hη t
  have h₂ := coneSecondClosed_norm_le hη t
  have hZ := cone_shift_second_norm_le ht.le hη
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) h₂
  · rw [norm_mul, mul_comm 3]
    exact mul_le_mul_of_nonneg_left
      ((norm_sub_le _ _).trans (by linarith only [h₁, hZ])) (norm_nonneg _)

end UV.SectorPlane
