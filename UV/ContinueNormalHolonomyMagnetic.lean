import UV.RootMagneticResponse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! The charged scalar horizontal Landau trace before normal sewing.
The dimension-four heat factor uses the full two magnetic and two free
horizontal coordinates. -/

noncomputable section

open Real Set Filter MeasureTheory
open scoped Topology

namespace UV.ContinueNormalHolonomy

private def cardinalTerm (x : ℝ) (n : ℕ) : ℝ := x ^ (2 * n) / ((2 * n + 1).factorial : ℝ)

private theorem cardinal_summable (x : ℝ) : Summable (cardinalTerm x) := by
  by_cases hx : x = 0
  · subst x
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    have hn' : n ≠ 0 := by simpa using hn
    simp [cardinalTerm, hn']
  · convert (Real.hasSum_sinh x).summable.div_const x using 1
    ext n
    simp only [cardinalTerm, pow_succ]
    field_simp [hx]

/-- The continuously filled cardinal hyperbolic sine. -/
def scalarSinhCardinal (x : ℝ) : ℝ := ∑' n, cardinalTerm x n

private def cardinalRemainder (x : ℝ) : ℝ :=
  ∑' n : ℕ, x ^ (2 * n) / ((2 * n + 5).factorial : ℝ)

private theorem cardinal_remainder_summable (x : ℝ) :
    Summable (fun n : ℕ => x ^ (2 * n) / ((2 * n + 5).factorial : ℝ)) := by
  by_cases hx : x = 0
  · subst x
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    have hn' : n ≠ 0 := by simpa using hn
    simp [hn']
  · have h := (summable_nat_add_iff 2).mpr (cardinal_summable x)
    convert h.div_const (x ^ 4) using 1
    ext n
    have he : 2 * (n + 2) = 2 * n + 4 := by omega
    have he' : 2 * n + 4 + 1 = 2 * n + 5 := by omega
    simp only [cardinalTerm, he, he', pow_add]
    field_simp [hx]

private theorem scalarSinhCardinal_eq (x : ℝ) (hx : x ≠ 0) :
    scalarSinhCardinal x = Real.sinh x / x := by
  rw [Real.sinh_eq_tsum, ← tsum_div_const]
  apply tsum_congr
  intro n
  simp only [cardinalTerm, pow_succ]
  field_simp [hx]

private theorem scalarSinhCardinal_expand (x : ℝ) :
    scalarSinhCardinal x = 1 + x ^ 2 / 6 + x ^ 4 * cardinalRemainder x := by
  rw [scalarSinhCardinal, ← (cardinal_summable x).sum_add_tsum_nat_add 2]
  rw [Finset.sum_range_succ, Finset.sum_range_one, cardinalRemainder, ← tsum_mul_left]
  congr 1
  · norm_num [cardinalTerm]
  · apply tsum_congr
    intro n
    have he : 2 * (n + 2) = 2 * n + 4 := by omega
    have he' : 2 * n + 4 + 1 = 2 * n + 5 := by omega
    simp only [cardinalTerm, he, he', pow_add, mul_div_assoc']
    rw [mul_comm (x ^ (2 * n))]

private theorem cardinal_remainder_nonneg (x : ℝ) : 0 ≤ cardinalRemainder x := by
  apply tsum_nonneg
  intro n
  exact div_nonneg (by rw [pow_mul]; positivity) (Nat.cast_nonneg _)

private theorem cardinal_remainder_le {x : ℝ} (hx : |x| ≤ 1) :
    cardinalRemainder x ≤ cardinalRemainder 1 := by
  apply (cardinal_remainder_summable x).tsum_le_tsum _ (cardinal_remainder_summable 1)
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hp : x ^ (2 * n) = |x| ^ (2 * n) := by rw [pow_mul, pow_mul, sq_abs]
  rw [hp]
  exact pow_le_pow_left₀ (abs_nonneg x) hx _

/-- Scalar Landau diagonal per unit horizontal four-volume, with the
zero-field value included. -/
def scalarMagneticDiagonal (b S : ℝ) : ℝ :=
  (scalarSinhCardinal (b * S))⁻¹ / (4 * Real.pi * S) ^ 2

theorem scalarMagneticDiagonal_zero (S : ℝ) :
    scalarMagneticDiagonal 0 S = 1 / (4 * Real.pi * S) ^ 2 := by
  rw [scalarMagneticDiagonal, zero_mul, scalarSinhCardinal_expand]
  norm_num

theorem scalarMagneticDiagonal_landau {b S : ℝ} (hb : b ≠ 0) (hS : 0 < S) :
    scalarMagneticDiagonal b S =
      ((|b| / (2 * Real.pi)) * ∑' n : ℕ, exp (-((2 * (n : ℝ) + 1) * (|b| * S)))) /
        (4 * Real.pi * S) := by
  have hx : 0 < |b| * S := mul_pos (abs_pos.mpr hb) hS
  have he (x : ℝ) : scalarSinhCardinal x = scalarSinhCardinal |x| := by
    unfold scalarSinhCardinal
    apply tsum_congr
    intro n
    simp only [cardinalTerm, pow_mul, sq_abs]
  have hsum := (eq_div_iff (show 2 * (|b| * S) ≠ 0 by positivity)).mpr
    (by simpa only [mul_comm (2 * (|b| * S))] using UV.RootMagnetic.landau_level_sum hx)
  rw [scalarMagneticDiagonal, he, abs_mul, abs_of_pos hS, scalarSinhCardinal_eq _ hx.ne', hsum]
  field_simp [pi_ne_zero, hb, hS.ne', abs_ne_zero.mpr hb, sinh_ne_zero.mpr hx.ne']
  ring

/-- Horizontal heat loss at one integrated diffusion time. -/
def scalarMagneticLoss (b S : ℝ) : ℝ :=
  scalarMagneticDiagonal 0 S - scalarMagneticDiagonal b S

/-- The pathwise quadratic coefficient in actual horizontal units. -/
def scalarMagneticQuadratic : ℝ := 1 / (6 * (4 * Real.pi) ^ 2)

private def magneticTailBound : ℝ := cardinalRemainder 1 +
  (1 / 6 : ℝ) * (1 / 6 + cardinalRemainder 1)

theorem scalarMagneticLoss_uniform {b S : ℝ} (hS : 0 < S) (hsmall : |b * S| ≤ 1) :
    |scalarMagneticLoss b S - scalarMagneticQuadratic * b ^ 2| ≤
      (magneticTailBound / (4 * Real.pi) ^ 2) * b ^ 4 * S ^ 2 := by
  let x := b * S
  let d := scalarSinhCardinal x
  let c := cardinalRemainder 1
  let e := cardinalRemainder x
  have hc : 0 ≤ c := cardinal_remainder_nonneg _
  have he : 0 ≤ e := cardinal_remainder_nonneg _
  have hec : e ≤ c := cardinal_remainder_le hsmall
  have hx2 : x ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact (pow_le_pow_left₀ (abs_nonneg _) hsmall 2).trans_eq (one_pow _)
  have hde : d = 1 + x ^ 2 / 6 + x ^ 4 * e := scalarSinhCardinal_expand x
  have hd : 1 ≤ d := by
    rw [hde]
    linarith [show 0 ≤ x ^ 2 / 6 by positivity, show 0 ≤ x ^ 4 * e by positivity]
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have habs : |e - (1 / 6 : ℝ) * (1 / 6 + x ^ 2 * e)| ≤ magneticTailBound := by
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg he, abs_of_nonneg (by positivity :
      0 ≤ (1 / 6 : ℝ) * (1 / 6 + x ^ 2 * e))]
    unfold magneticTailBound
    dsimp [c] at hc hec
    have hs : x ^ 2 * e ≤ cardinalRemainder 1 :=
      (mul_le_of_le_one_left he hx2).trans hec
    linarith
  have hi : |1 - d⁻¹ - x ^ 2 / 6| ≤ magneticTailBound * x ^ 4 := by
    have hfield : 1 - d⁻¹ - x ^ 2 / 6 =
        x ^ 4 / d * (e - (1 / 6 : ℝ) * (1 / 6 + x ^ 2 * e)) := by
      field_simp [hd0.ne']
      rw [hde]
      ring
    rw [hfield, abs_mul, abs_of_nonneg (by positivity : 0 ≤ x ^ 4 / d)]
    apply (mul_le_mul_of_nonneg_left habs (by positivity)).trans
    rw [mul_comm (x ^ 4 / d)]
    apply mul_le_mul_of_nonneg_left (div_le_self (by positivity) hd)
    unfold magneticTailBound
    positivity
  have hscale : scalarMagneticLoss b S - scalarMagneticQuadratic * b ^ 2 =
      (1 - d⁻¹ - x ^ 2 / 6) / (4 * Real.pi * S) ^ 2 := by
    rw [scalarMagneticLoss, scalarMagneticDiagonal_zero, scalarMagneticDiagonal,
      scalarMagneticQuadratic]
    dsimp [d, x]
    field_simp [hS.ne', pi_ne_zero]
  rw [hscale, abs_div, abs_of_nonneg (sq_nonneg (4 * Real.pi * S))]
  apply (div_le_div_of_nonneg_right hi (sq_nonneg _)).trans_eq
  dsimp [x]
  field_simp [hS.ne', pi_ne_zero]

@[fun_prop]
theorem scalarSinhCardinal_measurable : Measurable scalarSinhCardinal := by
  have he (x : ℝ) : scalarSinhCardinal x =
      if x = 0 then 1 else Real.sinh x / x := by
    split_ifs with hx
    · rw [hx, scalarSinhCardinal_expand]
      norm_num
    · exact scalarSinhCardinal_eq x hx
  have hmeas := Measurable.ite (p := fun x : ℝ => x = 0) (measurableSet_singleton 0)
    (measurable_const (a := (1 : ℝ))) (Real.continuous_sinh.measurable.div measurable_id)
  convert hmeas using 1
  funext x
  exact he x

theorem scalarMagneticLoss_measurable (b : ℝ) : Measurable (scalarMagneticLoss b) := by
  unfold scalarMagneticLoss scalarMagneticDiagonal
  fun_prop

/-- The unsewn normal kernel is the mass of the positive endpoint path law.
This estimate retains both endpoints and any bounded positive time change. -/
theorem scalarMagnetic_endpoint_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    {b U : ℝ} (hsmall : |b| * U ≤ 1)
    (hpath : ∀ᵐ ω ∂μ, 0 < S ω ∧ S ω ≤ U) :
    |(∫ ω, scalarMagneticLoss b (S ω) ∂μ) -
        scalarMagneticQuadratic * b ^ 2 * μ.real univ| ≤
      (magneticTailBound / (4 * Real.pi) ^ 2) * b ^ 4 * U ^ 2 * μ.real univ := by
  let K := (magneticTailBound / (4 * Real.pi) ^ 2) * b ^ 4
  let q := scalarMagneticQuadratic * b ^ 2
  have hK : 0 ≤ K := by
    dsimp [K, magneticTailBound]
    have := cardinal_remainder_nonneg 1
    positivity
  have hω : ∀ᵐ ω ∂μ, ‖scalarMagneticLoss b (S ω) - q‖ ≤ K * U ^ 2 := by
    filter_upwards [hpath] with ω hω
    rw [Real.norm_eq_abs]
    have hbs : |b * S ω| ≤ 1 := by
      rw [abs_mul, abs_of_pos hω.1]
      exact (mul_le_mul_of_nonneg_left hω.2 (abs_nonneg _)).trans hsmall
    exact (scalarMagneticLoss_uniform hω.1 hbs).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hω.1.le hω.2 2) hK)
  have hi : Integrable (fun ω => scalarMagneticLoss b (S ω) - q) μ :=
    (integrable_const (K * U ^ 2)).mono'
      (((scalarMagneticLoss_measurable b).comp hS).sub measurable_const).aestronglyMeasurable hω
  have hbase : Integrable (fun ω => scalarMagneticLoss b (S ω)) μ := by
    convert hi.add (integrable_const q) using 1
    funext ω
    exact (sub_add_cancel _ _).symm
  have hI := norm_integral_le_of_norm_le_const hω
  rw [Real.norm_eq_abs, integral_sub hbase (integrable_const q),
    integral_const, smul_eq_mul, mul_comm (μ.real univ)] at hI
  exact hI

/-- Extracting (b^2) after the horizontal trace and before integrating either
normal endpoint gives exactly the zero-field endpoint mass times the coefficient. -/
theorem scalarMagnetic_endpoint_quadratic {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S) {U : ℝ}
    (hpath : ∀ᵐ ω ∂μ, 0 < S ω ∧ S ω ≤ U) :
    Tendsto (fun b : ℝ => (∫ ω, scalarMagneticLoss b (S ω) ∂μ) / b ^ 2)
      (𝓝[≠] 0) (𝓝 (scalarMagneticQuadratic * μ.real univ)) := by
  let D := (magneticTailBound / (4 * Real.pi) ^ 2) * U ^ 2 * μ.real univ
  have hbound : Tendsto (fun b : ℝ => D * b ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have hc : Continuous (fun b : ℝ => D * b ^ 2) := by fun_prop
    have hh := (hc.continuousAt (x := (0 : ℝ))).tendsto
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using
      hh.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
  have hsmall : ∀ᶠ b : ℝ in 𝓝[≠] 0, |b| * U < 1 := by
    have hh : Tendsto (fun b : ℝ => |b| * U) (𝓝[≠] 0) (𝓝 (0 : ℝ)) := by
      simpa only [abs_zero, zero_mul] using
        ((continuous_abs.mul continuous_const).continuousAt (x := (0 : ℝ))).tendsto.mono_left
          (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
    exact hh.eventually (Iio_mem_nhds zero_lt_one)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero_norm' _ hbound
  filter_upwards [hsmall, self_mem_nhdsWithin] with b hbsmall hb
  have hb' : b ≠ 0 := hb
  have hi := scalarMagnetic_endpoint_bound μ S hS hbsmall.le hpath
  have hr :
      (∫ ω, scalarMagneticLoss b (S ω) ∂μ) / b ^ 2 -
          scalarMagneticQuadratic * μ.real univ =
        ((∫ ω, scalarMagneticLoss b (S ω) ∂μ) -
          scalarMagneticQuadratic * b ^ 2 * μ.real univ) / b ^ 2 := by
    field_simp [hb']
  rw [norm_of_nonneg (norm_nonneg _), Real.norm_eq_abs, hr, abs_div, abs_of_nonneg (sq_nonneg b)]
  apply (div_le_div_of_nonneg_right hi (sq_nonneg b)).trans_eq
  dsimp [D]
  field_simp [hb']

/-- Integrated horizontal diffusion time along the normal radial path. -/
def scalarHorizontalClock (κ R : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in Icc 0 t, κ (R s)

/-- A bounded positive horizontal diffusion rate gives the precise
duration-dependent bound used before normal sewing. -/
theorem scalarHorizontalClock_bounds (κ R : ℝ → ℝ) (hκ : Measurable κ) (hR : Measurable R)
    {t κmin κmax : ℝ} (ht : 0 < t) (hκmin : 0 < κmin)
    (hκb : ∀ s ∈ Icc 0 t, κmin ≤ κ (R s) ∧ κ (R s) ≤ κmax) :
    κmin * t ≤ scalarHorizontalClock κ R t ∧ scalarHorizontalClock κ R t ≤ κmax * t := by
  let ν := (volume : Measure ℝ).restrict (Icc 0 t)
  letI : IsFiniteMeasure ν := ⟨by simp [ν, Real.volume_Icc]⟩
  have hi : Integrable (fun s => κ (R s)) ν := by
    apply (integrable_const κmax).mono' (hκ.comp hR).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    change ‖κ (R s)‖ ≤ κmax
    rw [Real.norm_of_nonneg (hκmin.le.trans (hκb s hs).1)]
    exact (hκb s hs).2
  have hc (k : ℝ) : (∫ _ : ℝ, k ∂ν) = k * t := by
    rw [integral_const]
    simp [ν, measureReal_def, Real.volume_Icc, ht.le, smul_eq_mul, mul_comm]
  constructor
  · rw [← hc κmin]
    apply integral_mono_ae (integrable_const _) hi
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact (hκb s hs).1
  · rw [← hc κmax]
    apply integral_mono_ae hi (integrable_const _)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact (hκb s hs).2

end UV.ContinueNormalHolonomy
