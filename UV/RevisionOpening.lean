import Mathlib.Probability.Distributions.Poisson
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! The inclusive oscillator comparison with the manuscript's Poisson
channel weights. The exponential bound is for the complete positive sum
of accessible channels, including their phase-space factors. -/

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology NNReal Nat

namespace UV

def openingWeight (x : ℝ) : ℝ := Real.sqrt (1 - max x 0) * (1 + max x 0 / 2)

theorem openingWeight_eq_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    openingWeight x = Real.sqrt (1 - x) * (1 + x / 2) := by
  rw [openingWeight, max_eq_left hx]

theorem openingWeight_nonneg (x : ℝ) : 0 ≤ openingWeight x := by
  unfold openingWeight
  have h : 0 ≤ max x 0 := le_max_right _ _
  positivity

theorem openingWeight_eq_zero {x : ℝ} (hx : 1 ≤ x) : openingWeight x = 0 := by
  rw [openingWeight_eq_of_nonneg (zero_le_one.trans hx),
    Real.sqrt_eq_zero_of_nonpos (sub_nonpos.mpr hx), zero_mul]

theorem openingWeight_le (x : ℝ) : openingWeight x ≤ 3 / 2 := by
  by_cases h : 1 ≤ x
  · rw [openingWeight_eq_zero h]
    norm_num
  · have hv : 0 ≤ max x 0 := le_max_right _ _
    have hv' : max x 0 ≤ 1 := max_le (le_of_not_ge h) zero_le_one
    have hs : Real.sqrt (1 - max x 0) ≤ 1 := by
      calc
        _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
        _ = 1 := Real.sqrt_one
    unfold openingWeight
    calc
      _ ≤ 1 * (1 + max x 0 / 2) := mul_le_mul_of_nonneg_right hs (by positivity)
      _ ≤ _ := by linarith

/-- Normalized pair spectral density before the common factor `e²/(12π²)`.
`ℓ M` is the Poisson mean and `a₀` is the offset of the lowest threshold. -/
def openingPairDensity (ℓ a₀ M : ℝ) : ℝ :=
  ∑' n : ℕ, poissonPMFReal (ℓ * M).toNNReal n * openingWeight ((n + a₀) / M)

theorem openingPairDensity_nonneg (ℓ a₀ M : ℝ) :
    0 ≤ openingPairDensity ℓ a₀ M := by
  apply tsum_nonneg
  intro n
  exact mul_nonneg poissonPMFReal_nonneg (openingWeight_nonneg _)

theorem openingPairDensity_measurable (ℓ a₀ : ℝ) :
    Measurable (openingPairDensity ℓ a₀) := by
  let f (n : ℕ) (M : ℝ) := poissonPMFReal (ℓ * M).toNNReal n * openingWeight ((n + a₀) / M)
  have h₀ (n : ℕ) (M : ℝ) : 0 ≤ f n M :=
    mul_nonneg poissonPMFReal_nonneg (openingWeight_nonneg _)
  have h (n : ℕ) : Measurable (f n) := by
    dsimp [f, poissonPMFReal, openingWeight]
    fun_prop
  have ht : Measurable (fun M ↦ ((∑' n : ℕ, (f n M).toNNReal : ℝ≥0) : ℝ)) := by
    exact (Measurable.nnreal_tsum fun n ↦ (h n).real_toNNReal).coe_nnreal_real
  convert ht using 1
  ext M
  simp only [openingPairDensity, NNReal.coe_tsum, Real.coe_toNNReal _ (h₀ _ _)]
  rfl

/-- The Poisson exponential moment is an equality of convergent series. -/
theorem openingPoisson_hasSum_exp_moment (rate : ℝ≥0) (t : ℝ) :
    HasSum (fun n : ℕ ↦ poissonPMFReal rate n * Real.exp (t * n))
      (Real.exp ((rate : ℝ) * (Real.exp t - 1))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp ℝ ((rate : ℝ) * Real.exp t)).mul_left
    (Real.exp (- (rate : ℝ)))
  rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add] at h
  have he : -(rate : ℝ) + (rate : ℝ) * Real.exp t = (rate : ℝ) * (Real.exp t - 1) := by ring
  rw [he] at h
  convert h using 1
  ext n
  rw [poissonPMFReal, mul_pow, ← Real.exp_nat_mul, mul_comm (n : ℝ) t]
  ring

/-- Chernoff at the optimal negative tilt. The finite mass offset improves
accessibility, so dropping it gives the same upper bound as in the paper. -/
theorem openingPairDensity_supercritical {ℓ a₀ M : ℝ} (hℓ : 1 < ℓ)
    (ha : 0 ≤ a₀) (hM : 0 < M) :
    openingPairDensity ℓ a₀ M ≤ (3 / 2) * Real.exp (-M * (ℓ - 1 - Real.log ℓ)) := by
  let rate : ℝ≥0 := (ℓ * M).toNNReal
  let t : ℝ := -Real.log ℓ
  have hℓ0 : 0 < ℓ := by linarith
  have ht : t < 0 := neg_neg_of_pos (Real.log_pos hℓ)
  have hrate : (rate : ℝ) = ℓ * M := Real.coe_toNNReal _ (mul_nonneg hℓ0.le hM.le)
  have hnom := openingPoisson_hasSum_exp_moment rate t
  have hsum := hnom.mul_left ((3 / 2) * Real.exp (-t * M))
  have hpoint (n : ℕ) :
      poissonPMFReal rate n * openingWeight ((n + a₀) / M) ≤
        ((3 / 2) * Real.exp (-t * M)) * (poissonPMFReal rate n * Real.exp (t * n)) := by
    have hp : 0 ≤ poissonPMFReal rate n := poissonPMFReal_nonneg
    by_cases hc : 1 ≤ (n + a₀) / M
    · rw [openingWeight_eq_zero hc, mul_zero]
      positivity
    · have hn : (n : ℝ) ≤ M := by
        have h := (div_lt_iff₀ hM).mp (lt_of_not_ge hc)
        linarith
      have hExp : 1 ≤ Real.exp (-t * M) * Real.exp (t * n) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp_iff.mpr (by nlinarith [mul_nonneg (neg_nonneg.mpr ht.le) (sub_nonneg.mpr hn)])
      have hw := openingWeight_le ((n + a₀) / M)
      calc
        _ ≤ poissonPMFReal rate n * (3 / 2) := mul_le_mul_of_nonneg_left hw hp
        _ ≤ (poissonPMFReal rate n * (3 / 2)) *
            (Real.exp (-t * M) * Real.exp (t * n)) := by
              simpa only [mul_one] using mul_le_mul_of_nonneg_left hExp
                (show 0 ≤ poissonPMFReal rate n * (3 / 2) by positivity)
        _ = _ := by ring
  have hs : Summable (fun n : ℕ ↦ poissonPMFReal rate n * openingWeight ((n + a₀) / M)) :=
    Summable.of_nonneg_of_le (fun n ↦ mul_nonneg poissonPMFReal_nonneg
      (openingWeight_nonneg _)) hpoint hsum.summable
  calc
    openingPairDensity ℓ a₀ M ≤ ∑' n : ℕ, ((3 / 2) * Real.exp (-t * M)) *
        (poissonPMFReal rate n * Real.exp (t * n)) :=
      Summable.tsum_le_tsum hpoint hs hsum.summable
    _ = _ := by
      rw [hsum.tsum_eq, mul_assoc, ← Real.exp_add, hrate]
      dsimp [t]
      rw [Real.exp_neg, Real.exp_log hℓ0]
      congr 2
      field_simp
      ring

/-- For `ℓ > 1`, the actual unsubtracted dispersion tail is integrable. -/
theorem openingPairDensity_supercritical_tail {ℓ a₀ : ℝ} (hℓ : 1 < ℓ)
    (ha : 0 ≤ a₀) : IntegrableOn (fun M ↦ openingPairDensity ℓ a₀ M / M) (Ioi 1) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hr : 0 < ℓ - 1 - Real.log ℓ := by
    linarith [Real.log_lt_sub_one_of_pos hℓ0 (ne_of_gt hℓ)]
  have hi := (integrableOn_exp_mul_Ioi (neg_neg_of_pos hr) 1).const_mul (3 / 2 : ℝ)
  apply hi.mono' (((openingPairDensity_measurable ℓ a₀).div measurable_id).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with M hM
  have hM0 : 0 < M := zero_lt_one.trans hM
  change ‖openingPairDensity ℓ a₀ M / M‖ ≤ (3 / 2) * Real.exp (-(ℓ - 1 - Real.log ℓ) * M)
  rw [Real.norm_of_nonneg (div_nonneg (openingPairDensity_nonneg ℓ a₀ M) hM0.le)]
  calc
    _ ≤ openingPairDensity ℓ a₀ M := div_le_self (openingPairDensity_nonneg ℓ a₀ M) hM.le
    _ ≤ _ := by
      rw [show -(ℓ - 1 - Real.log ℓ) * M = -M * (ℓ - 1 - Real.log ℓ) by ring]
      exact openingPairDensity_supercritical hℓ ha hM0

end UV
