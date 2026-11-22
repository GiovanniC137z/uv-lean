import UV.ExtendTransverseJump
import UV.EvenDescent
import UV.RevisionSpectrumCross

/-! Stable-half kernel on the original sector-plane directed pole.
The branch is fixed before coefficient extraction. The timelike
boundary and the massless remainder use the same principal root. -/

noncomputable section

namespace UV.SectorPlane

open Filter Set UV.Carrier UV.RevisionSpectrum
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

private theorem spectralRootUpper_re_pos (p : ℝ) {h : ℝ} (hh : 0 < h) :
    0 < (spectralRootUpper p h).re := by
  have hs : (Real.sqrt (p ^ 2 + h ^ 2)) ^ 2 = p ^ 2 + h ^ 2 := Real.sq_sqrt (by positivity)
  have hp : |p| < Real.sqrt (p ^ 2 + h ^ 2) :=
    (sq_lt_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp (by
      rw [sq_abs, hs]
      exact lt_add_of_pos_right _ (sq_pos_of_pos hh))
  simp only [spectralRootUpper, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  exact Real.sqrt_pos.mpr (by linarith [neg_abs_le p])

theorem principalSqrt_upper_eq (p : ℝ) {h : ℝ} (hh : 0 < h) :
    principalSqrt ((p : ℂ) + (h : ℂ) * Complex.I) = spectralRootUpper p h := by
  let z := (p : ℂ) + (h : ℂ) * Complex.I
  rcases eq_or_eq_neg_of_sq_eq_sq (principalSqrt z) (spectralRootUpper p h)
      ((principalSqrt_sq z).trans (spectralRootUpper_sq p hh.le).symm) with H | H
  · exact H
  · have hr := congrArg Complex.re H
    rw [Complex.neg_re] at hr
    linarith [principalSqrt_re_nonneg z, spectralRootUpper_re_pos p hh]

theorem principalSqrt_lower_eq (p : ℝ) {h : ℝ} (hh : 0 < h) :
    principalSqrt ((p : ℂ) - (h : ℂ) * Complex.I) = star (spectralRootUpper p h) := by
  let z := (p : ℂ) - (h : ℂ) * Complex.I
  have hs : (star (spectralRootUpper p h) : ℂ) ^ 2 = z := by
    rw [← star_pow, spectralRootUpper_sq p hh.le]
    simp [z, sub_eq_add_neg]
  rcases eq_or_eq_neg_of_sq_eq_sq (principalSqrt z) (star (spectralRootUpper p h))
      ((principalSqrt_sq z).trans hs.symm) with H | H
  · exact H
  · have hr := congrArg Complex.re H
    change (principalSqrt z).re = -(spectralRootUpper p h).re at hr
    linarith [principalSqrt_re_nonneg z, spectralRootUpper_re_pos p hh]

private theorem spectralRootUpper_lower_cut_swap (w h : ℝ) :
    star (spectralRootUpper (-w) h) = -Complex.I * spectralRootUpper w h := by
  apply Complex.ext <;> simp [spectralRootUpper, sub_eq_add_neg]

private theorem spectralRootUpper_upper_cut_swap (w h : ℝ) :
    spectralRootUpper (-w) h = Complex.I * star (spectralRootUpper w h) := by
  apply Complex.ext <;> simp [spectralRootUpper, sub_eq_add_neg]

def Plane.shiftedShellCoefficient (diamond : Plane E) (ε : Evolution) (h : Height) (w : ℝ) : ℂ :=
  (w : ℂ) + Complex.I * ((diamond.eta ε * (h : ℝ) : ℝ) : ℂ)

def Plane.stableHalfNumerator (diamond : Plane E) (ε : Evolution) (h : Height)
    (a w : ℝ) : QuotientCarrier :=
  directed (Complex.exp (-(a : ℂ) * principalSqrt (-(diamond.shiftedShellCoefficient ε h w))))

theorem Plane.stable_half_argument_is_directed (diamond : Plane E) (ε : Evolution) (h : Height)
    (kParallel : ℝ) (k : Spatial) :
    directed (-(diamond.shiftedShellCoefficient ε h (shellSquare kParallel k))) =
      -diamond.poleDenominator ε h (shellSquare kParallel k) := by
  rw [directed_neg]
  rfl

theorem Plane.stable_half_numerator_characters (diamond : Plane E) (ε : Evolution) (h : Height)
    (a w : ℝ) :
    quotientCharacterEquiv (diamond.stableHalfNumerator ε h a w) =
      let z := Complex.exp (-(a : ℂ) * principalSqrt (-(diamond.shiftedShellCoefficient ε h w)))
      (z, star z) := by
  simp [Plane.stableHalfNumerator, directed]

/-- The regulated analytic coefficient, totalized only outside the
positive-height domain. -/
def Plane.stableHalfCoefficient (diamond : Plane E) (ε : Evolution) (a w h : ℝ) : ℂ :=
  if hh : 0 < h then (quotientCharacterEquiv (diamond.stableHalfNumerator ε ⟨h, hh⟩ a w)).1 else 0

theorem Plane.stable_half_analytic_form (diamond : Plane E) (ε : Evolution) (h : Height)
    (a w : ℝ) :
    diamond.stableHalfCoefficient ε a w (h : ℝ) =
      Complex.exp ((Complex.I * ((diamond.eta ε * a : ℝ) : ℂ)) *
        principalSqrt (diamond.shiftedShellCoefficient ε h w)) := by
  have hη : diamond.eta ε = 1 ∨ diamond.eta ε = -1 := by
    rcases diamond with ⟨s, b, G⟩
    cases s <;> cases ε <;> norm_num [Plane.eta, sectorSign, evolutionSign]
  rw [Plane.stableHalfCoefficient, dif_pos h.property, diamond.stable_half_numerator_characters]
  rcases hη with he | he
  · have hz : diamond.shiftedShellCoefficient ε h w = (w : ℂ) + (h : ℝ) * Complex.I := by
      simp [Plane.shiftedShellCoefficient, he, mul_comm Complex.I]
    have hn : -diamond.shiftedShellCoefficient ε h w = ((-w : ℝ) : ℂ) - (h : ℝ) * Complex.I := by
      rw [hz]
      push_cast
      ring
    dsimp only
    rw [hn, hz, principalSqrt_lower_eq (-w) h.property, principalSqrt_upper_eq w h.property,
      spectralRootUpper_lower_cut_swap, he]
    push_cast
    congr 1
    ring
  · have hz : diamond.shiftedShellCoefficient ε h w = (w : ℂ) - (h : ℝ) * Complex.I := by
      simp [Plane.shiftedShellCoefficient, he]
      ring
    have hn : -diamond.shiftedShellCoefficient ε h w = ((-w : ℝ) : ℂ) + (h : ℝ) * Complex.I := by
      rw [hz]
      push_cast
      ring
    dsimp only
    rw [hn, hz, principalSqrt_upper_eq (-w) h.property, principalSqrt_lower_eq w h.property,
      spectralRootUpper_upper_cut_swap, he]
    push_cast
    congr 1
    ring

/-- The actual regular-timelike calibrated numerator and its derivative
extend through zero height on the right half-plane in the shifted
shell argument. -/
theorem stable_half_analyticOn_timed (a η : ℝ) :
    AnalyticOnNhd ℂ (fun z : ℂ =>
      Complex.exp ((Complex.I * ((η * a : ℝ) : ℂ)) * principalSqrt z))
      {z : ℂ | 0 < z.re} := by
  intro z hz
  exact ((analyticAt_const.mul (principalSqrt_analyticOnNhd_rightHalfPlane z hz)).cexp)

theorem stable_half_boundary_phase_difference (a w : ℝ) :
    Complex.exp (((a * Real.sqrt w : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((-(a * Real.sqrt w) : ℝ) : ℂ) * Complex.I) =
      2 * Complex.I * (Real.sin (a * Real.sqrt w) : ℂ) := by
  simp only [Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg,
    Complex.ofReal_sin]
  ring

theorem stable_half_boundary_phase_sum (a m : ℝ) (hm : 0 ≤ m) :
    Complex.exp (((a * Real.sqrt (m ^ 2) : ℝ) : ℂ) * Complex.I) +
        Complex.exp (((-(a * Real.sqrt (m ^ 2)) : ℝ) : ℂ) * Complex.I) =
      2 * (Real.cos (a * m) : ℂ) := by
  rw [Real.sqrt_sq hm]
  simp only [Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg,
    Complex.ofReal_cos]
  ring

theorem Plane.stable_half_timed_coefficient_limit (diamond : Plane E) (ε : Evolution)
    (a : ℝ) {w : ℝ} (hw : 0 < w) :
    Tendsto (diamond.stableHalfCoefficient ε a w) (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.exp (((diamond.eta ε * a * Real.sqrt w : ℝ) : ℂ) * Complex.I))) := by
  have hη : diamond.eta ε = 1 ∨ diamond.eta ε = -1 := by
    rcases diamond with ⟨s, b, G⟩
    cases s <;> cases ε <;> norm_num [Plane.eta, sectorSign, evolutionSign]
  rcases hη with he | he
  · let q (h : ℝ) := Complex.exp (-(a : ℂ) * star (spectralRootUpper (-w) h))
    have hq : Continuous q := Complex.continuous_exp.comp
      (continuous_const.mul ((spectralRootUpper_continuous _).star))
    have hz : q 0 = Complex.exp (((diamond.eta ε * a * Real.sqrt w : ℝ) : ℂ) * Complex.I) := by
      unfold q
      rw [spectralRootUpper_at_cut (by linarith : -w ≤ 0), he, neg_neg]
      simp [mul_assoc]
    rw [← hz]
    refine (hq.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    have heq : -(diamond.shiftedShellCoefficient ε ⟨h, hh'⟩ w) =
        ((-w : ℝ) : ℂ) - (h : ℂ) * Complex.I := by
      simp [Plane.shiftedShellCoefficient, he]
      ring
    change q h = diamond.stableHalfCoefficient ε a w h
    rw [Plane.stableHalfCoefficient, dif_pos hh', diamond.stable_half_numerator_characters ε,
      heq, principalSqrt_lower_eq (-w) hh']
  · let q (h : ℝ) := Complex.exp (-(a : ℂ) * spectralRootUpper (-w) h)
    have hq : Continuous q := Complex.continuous_exp.comp
      (continuous_const.mul (spectralRootUpper_continuous _))
    have hz : q 0 = Complex.exp (((diamond.eta ε * a * Real.sqrt w : ℝ) : ℂ) * Complex.I) := by
      unfold q
      rw [spectralRootUpper_at_cut (by linarith : -w ≤ 0), he, neg_neg]
      push_cast
      congr 1
      ring
    rw [← hz]
    refine (hq.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    have heq : -(diamond.shiftedShellCoefficient ε ⟨h, hh'⟩ w) =
        ((-w : ℝ) : ℂ) + (h : ℂ) * Complex.I := by
      simp [Plane.shiftedShellCoefficient, he]
      ring
    change q h = diamond.stableHalfCoefficient ε a w h
    rw [Plane.stableHalfCoefficient, dif_pos hh', diamond.stable_half_numerator_characters ε,
      heq, principalSqrt_upper_eq (-w) hh']

theorem Plane.stable_half_timed_directed_limit (diamond : Plane E) (ε : Evolution)
    (a kParallel : ℝ) (k : Spatial) (hw : 0 < shellSquare kParallel k) :
    let w := shellSquare kParallel k
    Tendsto (fun h : ℝ => if hh : 0 < h then diamond.stableHalfNumerator ε ⟨h, hh⟩ a w else 0)
      (𝓝[>] (0 : ℝ))
      (𝓝 (algebraMap ℂ QuotientCarrier (Real.cos (a * Real.sqrt w)) +
        algebraMap ℂ QuotientCarrier
          ((diamond.eta ε * Real.sin (a * Real.sqrt w) : ℝ) : ℂ) * directedUnit)) := by
  let w := shellSquare kParallel k
  have h := directed_shell_readout_continuous.continuousAt.tendsto.comp
    (diamond.stable_half_timed_coefficient_limit ε a hw)
  have hη : diamond.eta ε = 1 ∨ diamond.eta ε = -1 := by
    rcases diamond with ⟨s, b, G⟩
    cases s <;> cases ε <;> norm_num [Plane.eta, sectorSign, evolutionSign]
  have hz : directed (Complex.exp (((diamond.eta ε * a * Real.sqrt w : ℝ) : ℂ) * Complex.I)) =
      algebraMap ℂ QuotientCarrier (Real.cos (a * Real.sqrt w)) +
        algebraMap ℂ QuotientCarrier
          ((diamond.eta ε * Real.sin (a * Real.sqrt w) : ℝ) : ℂ) * directedUnit := by
    rw [directed_as_real_plus_root, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    rcases hη with hE | hE <;>
      simp [hE, directedUnit, mul_assoc, mul_comm Complex.I]
  change Tendsto _ _ (𝓝 _) at h
  rw [hz] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with height hmem
  have hPos : 0 < height := hmem
  simp [Plane.stableHalfCoefficient, hPos, Plane.stableHalfNumerator, directed]

/-- Quantitative massless expansion, with a uniform O(1) remainder
as the finite-height shifted coefficient tends to zero. -/
theorem stable_half_massless_remainder {a : ℝ} {z : ℂ} (hz : z ≠ 0)
    (ha : |a| * Real.sqrt ‖z‖ ≤ 1) :
    ‖Complex.exp (-(a : ℂ) * principalSqrt (-z)) / z -
      z⁻¹ - (a : ℂ) / principalSqrt (-z)‖ ≤ a ^ 2 := by
  let s := principalSqrt (-z)
  let x := -(a : ℂ) * s
  have hs : s ^ 2 = -z := principalSqrt_sq (-z)
  have hs₀ : s ≠ 0 := by
    intro he
    have h := hs
    rw [he, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h
    exact hz (neg_eq_zero.mp h.symm)
  have hx : ‖x‖ = |a| * Real.sqrt ‖z‖ := by
    simp [x, s, principalSqrt_norm, Complex.norm_real]
  have hsq : ‖x‖ ^ 2 = a ^ 2 * ‖z‖ := by
    rw [hx, mul_pow, sq_abs, Real.sq_sqrt (norm_nonneg _)]
  have heq : Complex.exp x / z - z⁻¹ - (a : ℂ) / s = (Complex.exp x - 1 - x) / z := by
    rw [show z = -(s ^ 2) from (neg_eq_iff_eq_neg.mpr hs).symm]
    field_simp [hs₀, x]
    ring
  change ‖Complex.exp x / z - z⁻¹ - (a : ℂ) / s‖ ≤ a ^ 2
  rw [heq, norm_div, div_le_iff₀ (norm_pos_iff.mpr hz), ← hsq]
  exact Complex.norm_exp_sub_one_sub_id_le (hx.trans_le ha)

theorem Plane.massless_shifted_coefficient_nonzero (diamond : Plane E) (ε : Evolution)
    (h : Height) (w : ℝ) : diamond.shiftedShellCoefficient ε h w ≠ 0 :=
  diamond.shifted_denominator_ne_zero ε h w

/-- The quantitative massless expansion in the literal carrier
quotient. All terms use the same shifted shell coefficient. -/
theorem Plane.stable_half_massless_directed_remainder (diamond : Plane E) (ε : Evolution)
    (h : Height) (a kParallel : ℝ) (k : Spatial)
    (ha : |a| * Real.sqrt ‖diamond.shiftedShellCoefficient ε h (shellSquare kParallel k)‖ ≤ 1) :
    let w := shellSquare kParallel k
    let z := diamond.shiftedShellCoefficient ε h w
    ‖diamond.stableHalfNumerator ε h a w * diamond.poleInverse ε h w -
      diamond.poleInverse ε h w - directed ((a : ℂ) / principalSqrt (-z))‖ ≤ a ^ 2 := by
  let w := shellSquare kParallel k
  let z := diamond.shiftedShellCoefficient ε h w
  have hz : z ≠ 0 := diamond.massless_shifted_coefficient_nonzero ε h w
  have hInv : diamond.poleInverse ε h w = directed z⁻¹ :=
    diamond.pole_inverse_complex ε h w
  have hd (x y : ℂ) : directed (x - y) = directed x - directed y := by
    apply quotientCharacterEquiv.injective
    simp [directed]
  have hn (x : ℂ) : ‖directed x‖ = ‖x‖ := by
    simp [quotient_character_norm, directed]
  change ‖diamond.stableHalfNumerator ε h a w * diamond.poleInverse ε h w -
    diamond.poleInverse ε h w - directed ((a : ℂ) / principalSqrt (-z))‖ ≤ a ^ 2
  rw [Plane.stableHalfNumerator, hInv, ← directed_mul, ← hd, ← hd, hn, ← div_eq_mul_inv]
  exact stable_half_massless_remainder hz ha

end UV.SectorPlane
