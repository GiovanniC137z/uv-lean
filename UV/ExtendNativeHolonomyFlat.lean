import UV.ExtendNativeHolonomyResponse
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Complete flat holonomy winding sum and its absolute derivative budgets.
Winding number is a normal-circle variable and does not select a carrier ray. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace UV.ExtendNativeHolonomy

variable {E : Type} [NormedAddCommGroup E]

def holonomyEnergy (C : NormalCircle E) (p : UV.ScalarMomentum) : ℝ :=
  Real.sqrt (‖p‖ ^ 2 + C.mass ^ 2)

private theorem holonomyEnergy_lower (C : NormalCircle E) (p : UV.ScalarMomentum) :
    (C.mass + ‖p‖) / 2 ≤ holonomyEnergy C p := by
  have h : 0 ≤ (C.mass + ‖p‖) / 2 := by linarith [C.mass_pos, norm_nonneg p]
  apply (Real.le_sqrt h (by positivity)).2
  nlinarith [sq_nonneg (C.mass - ‖p‖), sq_nonneg C.mass, sq_nonneg ‖p‖]

def windingIndex (n : ℕ) : ℝ := (n : ℝ) + 1

private theorem windingIndex_one_le (n : ℕ) : 1 ≤ windingIndex n := by
  unfold windingIndex
  linarith [Nat.cast_nonneg (α := ℝ) n]

def windingProfile (n j : ℕ) (θ : ℝ) : ℝ :=
  if j = 0 then 1 - Real.cos (windingIndex n * θ)
  else -(windingIndex n) ^ j *
    Real.cos (windingIndex n * θ + (j : ℝ) * (Real.pi / 2))

theorem windingProfile_hasDerivAt (n j : ℕ) (θ : ℝ) :
    HasDerivAt (windingProfile n j) (windingProfile n (j + 1) θ) θ := by
  have hθ : HasDerivAt (fun x : ℝ => windingIndex n * x) (windingIndex n) θ := by
    simpa only [mul_one] using (hasDerivAt_id θ).const_mul (windingIndex n)
  by_cases hj : j = 0
  · subst j
    convert ((hasDerivAt_const θ (1 : ℝ)).sub hθ.cos) using 1
    simp [windingProfile, Real.cos_add_pi_div_two]
    ring
  · have ht := (hθ.add_const ((j : ℝ) * (Real.pi / 2))).cos.const_mul (-(windingIndex n) ^ j)
    convert ht using 1
    · funext y
      simp [windingProfile, hj]
    · simp only [windingProfile, Nat.succ_ne_zero, if_false, Nat.cast_add, Nat.cast_one]
      rw [show windingIndex n * θ + ((j : ℝ) + 1) * (Real.pi / 2) =
        (windingIndex n * θ + (j : ℝ) * (Real.pi / 2)) + Real.pi / 2 by ring,
        Real.cos_add_pi_div_two, pow_succ]
      ring

private theorem windingProfile_bound (n j : ℕ) (θ : ℝ) :
    ‖windingProfile n j θ‖ ≤ 2 * windingIndex n ^ j := by
  have hn : 0 ≤ windingIndex n := zero_le_one.trans (windingIndex_one_le n)
  by_cases hj : j = 0
  · subst j
    simp only [windingProfile, if_true, pow_zero, mul_one, Real.norm_eq_abs]
    exact abs_le.mpr (by constructor <;> linarith [Real.cos_le_one (windingIndex n * θ),
      Real.neg_one_le_cos (windingIndex n * θ)])
  · simp only [windingProfile, if_neg hj, norm_mul, norm_neg, norm_pow,
      Real.norm_of_nonneg hn, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (pow_nonneg hn _)).trans
      (by linarith [pow_nonneg hn j])

def windingDecay (C : NormalCircle E) (n : ℕ) (p : UV.ScalarMomentum) : ℝ :=
  Real.exp (-(windingIndex n * C.length * holonomyEnergy C p))

def angularVolume : ℝ := (2 * Real.pi) ^ 4

def flatIntegrand (C : NormalCircle E) (n j : ℕ) (θ : ℝ) (p : UV.ScalarMomentum) : ℝ :=
  (2 / (windingIndex n * angularVolume)) * windingDecay C n p * windingProfile n j θ

def flatLogDet (C : NormalCircle E) (θ : ℝ) : ℝ :=
  ∫ p, ∑' n : ℕ, flatIntegrand C n 0 θ p

private def radialEnvelope (C : NormalCircle E) (p : UV.ScalarMomentum) : ℝ :=
  Real.exp (-((C.length / 2) * ‖p‖))

private def modeEnvelope (C : NormalCircle E) (j n : ℕ) : ℝ :=
  (4 / angularVolume) * windingIndex n ^ j *
    Real.exp (-(C.length * C.mass / 2 * windingIndex n))

private theorem angularVolume_pos : 0 < angularVolume := by
  unfold angularVolume
  positivity

private theorem radialEnvelope_integrable (C : NormalCircle E) :
    Integrable (radialEnvelope C) := by
  change Integrable (fun p : UV.ScalarMomentum => Real.exp (-((C.length / 2) * ‖p‖)))
  simpa only [pow_zero, one_mul] using (UV.integrable_norm_pow_exp (μ := volume)
    (E := UV.ScalarMomentum) (half_pos C.length_pos) 0)

private theorem modeEnvelope_nonneg (C : NormalCircle E) (j n : ℕ) :
    0 ≤ modeEnvelope C j n := by
  have h : 0 ≤ windingIndex n := zero_le_one.trans (windingIndex_one_le n)
  unfold modeEnvelope
  have hp := angularVolume_pos
  positivity

private theorem modeEnvelope_summable (C : NormalCircle E) (j : ℕ) :
    Summable (modeEnvelope C j) := by
  have hpos : 0 < C.length * C.mass / 2 := half_pos (mul_pos C.length_pos C.mass_pos)
  have h := (summable_nat_add_iff 1).2 (Real.summable_pow_mul_exp_neg_nat_mul j hpos)
  unfold modeEnvelope
  have he (n : ℕ) : (4 / angularVolume) * windingIndex n ^ j *
      Real.exp (-(C.length * C.mass / 2 * windingIndex n)) =
      (4 / angularVolume) * ((n + 1 : ℕ) ^ j *
        Real.exp (-(C.length * C.mass / 2) * (↑(n + 1) : ℝ))) := by
    push_cast
    unfold windingIndex
    simp only [neg_mul, mul_assoc]
  simp_rw [he]
  exact h.mul_left _

private theorem windingDecay_le (C : NormalCircle E) (n : ℕ) (p : UV.ScalarMomentum) :
    windingDecay C n p ≤
      Real.exp (-(C.length * C.mass / 2 * windingIndex n)) * radialEnvelope C p := by
  unfold windingDecay radialEnvelope
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hw := windingIndex_one_le n
  have hL : 0 ≤ C.length := C.length_pos.le
  have h1 := mul_le_mul_of_nonneg_left (holonomyEnergy_lower C p)
    (mul_nonneg (zero_le_one.trans hw) hL)
  have h2 := mul_le_mul_of_nonneg_right hw (mul_nonneg (half_pos C.length_pos).le (norm_nonneg p))
  linarith [show windingIndex n * C.length * ((C.mass + ‖p‖) / 2) =
    C.length * C.mass / 2 * windingIndex n + windingIndex n * (C.length / 2 * ‖p‖) by ring]

theorem flatIntegrand_bound (C : NormalCircle E) (n j : ℕ) (θ : ℝ) (p : UV.ScalarMomentum) :
    ‖flatIntegrand C n j θ p‖ ≤ modeEnvelope C j n * radialEnvelope C p := by
  have hn : 0 < windingIndex n := zero_lt_one.trans_le (windingIndex_one_le n)
  have hvol := angularVolume_pos
  have hwd : 0 ≤ windingDecay C n p := Real.exp_nonneg _
  unfold flatIntegrand
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ 2 / (windingIndex n * angularVolume)),
    Real.norm_of_nonneg hwd]
  have hden : 2 / (windingIndex n * angularVolume) ≤ 2 / angularVolume := by
    exact div_le_div_of_nonneg_left (by norm_num) hvol
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (windingIndex_one_le n) hvol.le)
  have hmode := windingProfile_bound n j θ
  calc
    _ ≤ (2 / angularVolume * (Real.exp (-(C.length * C.mass / 2 * windingIndex n)) *
          radialEnvelope C p)) * (2 * windingIndex n ^ j) := by
      apply mul_le_mul
      · exact mul_le_mul hden (windingDecay_le C n p) hwd (by positivity)
      · exact hmode
      · exact norm_nonneg _
      · unfold radialEnvelope
        positivity
    _ = _ := by unfold modeEnvelope; ring

private theorem flatIntegrand_integrable (C : NormalCircle E) (n j : ℕ) (θ : ℝ) :
    Integrable (flatIntegrand C n j θ) := by
  apply ((radialEnvelope_integrable C).const_mul (modeEnvelope C j n)).mono'
  · unfold flatIntegrand windingDecay holonomyEnergy
    exact (by fun_prop : Measurable _).aestronglyMeasurable
  · exact Eventually.of_forall (flatIntegrand_bound C n j θ)

theorem flatIntegrand_summable (C : NormalCircle E) (j : ℕ) (θ : ℝ) (p : UV.ScalarMomentum) :
    Summable (fun n => flatIntegrand C n j θ p) :=
  ((modeEnvelope_summable C j).mul_right (radialEnvelope C p)).of_norm_bounded
    (fun n => flatIntegrand_bound C n j θ p)

theorem flat_winding_sum_integrable (C : NormalCircle E) (j : ℕ) (θ : ℝ) :
    Integrable (fun p => ∑' n : ℕ, flatIntegrand C n j θ p) := by
  have hmeas : AEStronglyMeasurable (fun p =>
      ∑' n : ℕ, flatIntegrand C n j θ p) volume := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N p => ∑ n ∈ Finset.range N, flatIntegrand C n j θ p) ?_ ?_
    · exact fun N => (Finset.range N).aestronglyMeasurable_fun_sum
        (fun n _ => (flatIntegrand_integrable C n j θ).1)
    · exact Eventually.of_forall fun p =>
        (flatIntegrand_summable C j θ p).hasSum.tendsto_sum_nat
  apply ((radialEnvelope_integrable C).const_mul (∑' n, modeEnvelope C j n)).mono' hmeas
  refine Eventually.of_forall fun p => ?_
  have hs := (modeEnvelope_summable C j).mul_right (radialEnvelope C p)
  have hnorm := hs.of_nonneg_of_le (fun n => norm_nonneg (flatIntegrand C n j θ p))
    (fun n => flatIntegrand_bound C n j θ p)
  rw [← tsum_mul_right]
  exact (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum
    (fun n => flatIntegrand_bound C n j θ p) hs)

/-- Absolute convergence across the full winding sum and carrier integral
after every finite number of holonomy derivatives. -/
theorem flat_integral_norm_summable (C : NormalCircle E) (j : ℕ) (θ : ℝ) :
    Summable (fun n : ℕ => ∫ p, ‖flatIntegrand C n j θ p‖) := by
  let I : ℝ := ∫ p, radialEnvelope C p
  apply ((modeEnvelope_summable C j).mul_right I).of_nonneg_of_le
  · exact fun n => integral_nonneg (fun p => norm_nonneg _)
  · intro n
    simp only [I, ← integral_const_mul]
    exact integral_mono_of_nonneg (Eventually.of_forall (fun _ => norm_nonneg _))
      ((radialEnvelope_integrable C).const_mul _) (Eventually.of_forall (flatIntegrand_bound C n j θ))

def integratedWinding (C : NormalCircle E) (n j : ℕ) (θ : ℝ) : ℝ :=
  (2 / (windingIndex n * angularVolume) * ∫ p, windingDecay C n p) * windingProfile n j θ

theorem integratedWinding_eq (C : NormalCircle E) (n j : ℕ) (θ : ℝ) :
    integratedWinding C n j θ = ∫ p, flatIntegrand C n j θ p := by
  unfold integratedWinding flatIntegrand
  rw [integral_mul_const, integral_const_mul]

private theorem integratedWinding_bound (C : NormalCircle E) (n j : ℕ) (θ : ℝ) :
    ‖integratedWinding C n j θ‖ ≤ modeEnvelope C j n * ∫ p, radialEnvelope C p := by
  rw [integratedWinding_eq, ← integral_const_mul]
  exact norm_integral_le_of_norm_le ((radialEnvelope_integrable C).const_mul _)
    (Eventually.of_forall (flatIntegrand_bound C n j θ))

def windingDerivative (C : NormalCircle E) (j : ℕ) (θ : ℝ) : ℝ :=
  ∑' n : ℕ, integratedWinding C n j θ

/-- Exact exchange of every absolutely controlled winding series with the
carrier momentum integration. -/
theorem windingDerivative_eq_integral (C : NormalCircle E) (j : ℕ) (θ : ℝ) :
    windingDerivative C j θ = ∫ p, ∑' n : ℕ, flatIntegrand C n j θ p := by
  unfold windingDerivative
  simp_rw [integratedWinding_eq]
  exact (integral_tsum_of_summable_integral_norm (fun n => flatIntegrand_integrable C n j θ)
    (flat_integral_norm_summable C j θ))

theorem windingDerivative_hasDerivAt (C : NormalCircle E) (j : ℕ) (θ : ℝ) :
    HasDerivAt (windingDerivative C j) (windingDerivative C (j + 1) θ) θ := by
  let I : ℝ := ∫ p, radialEnvelope C p
  have hsum : Summable (fun n => modeEnvelope C (j + 1) n * I) :=
    (modeEnvelope_summable C (j + 1)).mul_right I
  have h0 : Summable (fun n => integratedWinding C n j (0 : ℝ)) := by
    apply Summable.of_norm_bounded ((modeEnvelope_summable C j).mul_right I)
    exact fun n => integratedWinding_bound C n j 0
  unfold windingDerivative
  exact hasDerivAt_tsum hsum
    (fun n y => (windingProfile_hasDerivAt n j y).const_mul _)
    (fun n y => integratedWinding_bound C n (j+1) y) h0 θ

/-- The complete flat determinant admits all derivatives, each on the
full summation and integration domain. -/
theorem flatLogDet_iteratedDeriv (C : NormalCircle E) (j : ℕ) :
    iteratedDeriv j (flatLogDet C) = windingDerivative C j := by
  induction j with
  | zero =>
    funext θ
    simp only [iteratedDeriv_zero, flatLogDet, windingDerivative_eq_integral]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext θ
    exact (windingDerivative_hasDerivAt C j θ).deriv

end UV.ExtendNativeHolonomy
