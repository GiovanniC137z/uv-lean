import UV.MatrixPole
import UV.RevisionSpectrumRigidity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Real pole, local complex residues and the positive-measure obstruction
for the free heat-link vector coefficient in the expanded manuscript. -/

noncomputable section

namespace UV.HeatMaxwell

open Filter Set MeasureTheory
open scoped Topology

def heatVectorDenominator (m a : ℝ) (z : ℂ) : ℂ :=
  (m:ℂ)^2 + z*Complex.exp (-(2*(a:ℂ)^2)*z)

def heatVectorNumerator (a : ℝ) (z : ℂ) : ℂ := Complex.exp (-(a:ℂ)^2*z)

def heatFreeVector (m a : ℝ) (z : ℂ) : ℂ := heatVectorNumerator a z / heatVectorDenominator m a z

/-- The change of variables in the manuscript's Lambert equation is
bijective at positive width and preserves all complex denominator zeros. -/
theorem heatVector_zero_iff_lambert {m a : ℝ} (ha : 0 < a) (z : ℂ) :
    heatVectorDenominator m a z = 0 ↔
      (-(2*(a:ℂ)^2)*z)*Complex.exp (-(2*(a:ℂ)^2)*z) = ((2*a^2*m^2 : ℝ):ℂ) := by
  have hne : 2*(a:ℂ)^2 ≠ 0 := by exact_mod_cast (show 2*a^2 ≠ 0 by positivity)
  unfold heatVectorDenominator
  push_cast
  constructor
  · intro h
    linear_combination -(2*(a:ℂ)^2)*h
  · intro h
    apply (mul_eq_zero.mp (show (2*(a:ℂ)^2)*((m:ℂ)^2 + z*Complex.exp (-(2*(a:ℂ)^2)*z)) = 0 by
      linear_combination -h)).resolve_left hne

theorem heatVectorDenominator_derivative (m a : ℝ) (z : ℂ) :
    HasDerivAt (heatVectorDenominator m a)
      (Complex.exp (-(2*(a:ℂ)^2)*z)*(1-2*(a:ℂ)^2*z)) z := by
  have h := ((hasDerivAt_id z).mul (((hasDerivAt_id z).const_mul (-(2*(a:ℂ)^2))).cexp)).const_add ((m:ℂ)^2)
  convert h using 1
  dsimp [id]
  ring

theorem heatVector_zero_simple {m a : ℝ} (hm : 0 < m) (ha : 0 < a) {z : ℂ}
    (hz : heatVectorDenominator m a z = 0) : 1-2*(a:ℂ)^2*z ≠ 0 := by
  intro hc
  have hw := (heatVector_zero_iff_lambert ha z).mp hz
  have harg : -(2*(a:ℂ)^2)*z = -1 := by linear_combination hc
  rw [harg] at hw
  have hreal := congrArg Complex.re hw
  rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by simp, ← Complex.ofReal_exp, ← Complex.ofReal_mul] at hreal
  change -1*Real.exp (-1) = 2*a^2*m^2 at hreal
  linarith only [Real.exp_pos (-1),show 0 < 2*a^2*m^2 by positivity,hreal]

/-- Actual punctured-limit coefficient. The exponential numerator is
nonzero at every zero, so no simple denominator pole is removable. -/
theorem heatFreeVector_residue_limit {m a : ℝ} (hm : 0 < m) (ha : 0 < a) {p : ℂ}
    (hp : heatVectorDenominator m a p = 0) :
    Tendsto (fun z => (z-p)*heatFreeVector m a z) (𝓝[≠] p)
      (𝓝 (Complex.exp ((a:ℂ)^2*p)/(1-2*(a:ℂ)^2*p))) := by
  let d := Complex.exp (-(2*(a:ℂ)^2)*p)*(1-2*(a:ℂ)^2*p)
  have hd : d ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (heatVector_zero_simple hm ha hp)
  have hs := (hasDerivAt_iff_tendsto_slope.mp (heatVectorDenominator_derivative m a p))
  have hn : Continuous (heatVectorNumerator a) := Complex.continuous_exp.comp (continuous_const.mul continuous_id)
  have hlim := (hn.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {p}ᶜ))).div hs hd
  have he : heatVectorNumerator a p / d = Complex.exp ((a:ℂ)^2*p)/(1-2*(a:ℂ)^2*p) := by
    unfold heatVectorNumerator d
    rw [← div_div, ← Complex.exp_sub, show -(a:ℂ)^2*p - -(2*(a:ℂ)^2)*p = (a:ℂ)^2*p by ring]
  rw [← he]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin (s := {p}ᶜ)] with z hz
  have hnz : z-p ≠ 0 := sub_ne_zero.mpr hz
  change heatVectorNumerator a z / slope (heatVectorDenominator m a) p z = _
  rw [slope_def_field,hp,sub_zero]
  unfold heatFreeVector
  rw [div_div_eq_mul_div]
  ring

theorem heatFreeVector_residue {m a : ℝ} (hm : 0 < m) (ha : 0 < a) {z : ℂ}
    (hz : heatVectorDenominator m a z = 0) :
    UV.simplePoleResidue (heatFreeVector m a) z = Complex.exp ((a:ℂ)^2*z)/(1-2*(a:ℂ)^2*z) :=
  (heatFreeVector_residue_limit hm ha hz).limUnder_eq

theorem heatFreeVector_residue_ne_zero {m a : ℝ} (hm : 0 < m) (ha : 0 < a) {z : ℂ}
    (hz : heatVectorDenominator m a z = 0) : UV.simplePoleResidue (heatFreeVector m a) z ≠ 0 := by
  rw [heatFreeVector_residue hm ha hz]
  exact div_ne_zero (Complex.exp_ne_zero _) (heatVector_zero_simple hm ha hz)

private theorem heatVector_real_zero_iff (m a s : ℝ) :
    heatVectorDenominator m a (-(s:ℂ)) = 0 ↔ s*Real.exp (2*a^2*s) = m^2 := by
  unfold heatVectorDenominator
  rw [show -(2*(a:ℂ)^2) * -(s:ℂ) = ((2*a^2*s : ℝ):ℂ) by push_cast; ring,
    ← Complex.ofReal_exp]
  constructor
  · intro h
    exact_mod_cast (show (s:ℂ)*(Real.exp (2*a^2*s):ℂ) = (m:ℂ)^2 by linear_combination -h)
  · intro h
    have hh : (s:ℂ)*(Real.exp (2*a^2*s):ℂ) = (m:ℂ)^2 := by exact_mod_cast h
    linear_combination -hh

theorem heatFreeVector_unique_real_pole {m a : ℝ} (hm : 0 < m) (ha : 0 < a) :
    ∃ s : ℝ, 0 < s ∧ (∀ x : ℝ, heatVectorDenominator m a (x:ℂ) = 0 ↔ x = -s) ∧
      UV.simplePoleResidue (heatFreeVector m a) (-(s:ℂ)) =
        ((Real.exp (-a^2*s)/(1+2*a^2*s) : ℝ) : ℂ) ∧ 0 < Real.exp (-a^2*s)/(1+2*a^2*s) := by
  let f := fun s : ℝ => s*Real.exp (2*a^2*s)
  have hcont : Continuous f := continuous_id.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hm₂ := sq_pos_of_pos hm
  have hhi : m^2 ≤ f (m^2) := le_mul_of_one_le_right hm₂.le (Real.one_le_exp (by positivity))
  obtain ⟨s,hs,hf⟩ := intermediate_value_Icc hm₂.le hcont.continuousOn
    (show m^2 ∈ Icc (f 0) (f (m^2)) from ⟨by simpa [f] using hm₂.le,hhi⟩)
  have hp : 0 < s := by
    refine lt_of_le_of_ne hs.1 ?_
    rintro rfl
    simp [f] at hf
    linarith
  have hz := (heatVector_real_zero_iff m a s).mpr hf
  refine ⟨s,hp,?_,?_,by positivity⟩
  · intro x
    have h := heatVector_real_zero_iff m a (-x)
    simp only [Complex.ofReal_neg,neg_neg] at h
    rw [h]
    constructor
    · intro hx
      have hx' : 0 < -x := pos_of_mul_pos_left (hx.symm ▸ hm₂) (Real.exp_pos _).le
      have hmon : StrictMonoOn f (Ici 0) := by
        intro i hi j hj hij
        apply mul_lt_mul_of_lt_of_le_of_nonneg_of_pos hij
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hij.le (by positivity))) (by exact hi) (Real.exp_pos _)
      have he := hmon.injOn hx'.le hp.le (hx.trans hf.symm)
      linarith
    · rintro rfl
      simpa only [neg_neg] using hf
  · rw [heatFreeVector_residue hm ha hz]
    push_cast
    simp only [mul_neg,neg_mul,sub_neg_eq_add]

def heatFreeVectorReal (m a x : ℝ) : ℝ :=
  Real.exp (-a^2*x)/(m^2 + x*Real.exp (-(2*a^2)*x))

theorem heatFreeVector_ofReal (m a x : ℝ) : heatFreeVector m a (x:ℂ) = (heatFreeVectorReal m a x : ℂ) := by
  simp [heatFreeVector,heatVectorNumerator,heatVectorDenominator,heatFreeVectorReal,Complex.ofReal_exp]

theorem heatFreeVector_scaled_tendsto_zero {m a : ℝ} (hm : 0 < m) (ha : 0 < a) :
    Tendsto (fun x => x*heatFreeVectorReal m a x) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => x*Real.exp (-a^2*x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (a^2) (sq_pos_of_pos ha)
  apply squeeze_zero' _ _ (by simpa only [zero_div] using h.div_const (m^2))
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    unfold heatFreeVectorReal
    positivity
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    unfold heatFreeVectorReal
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hm)
      (le_add_of_nonneg_right (by positivity))

/-- A nonzero unsubtracted positive vector spectrum on nonnegative squared
masses is impossible even on the positive Euclidean axis. -/
theorem heatFreeVector_no_positive_spectrum {m a : ℝ} (hm : 0 < m) (ha : 0 < a)
    (ρ : Measure ℝ) (hne : ρ ≠ 0) (hs : ∀ᵐ s ∂ρ, 0 ≤ s)
    (hi : ∀ x > 0, Integrable (fun s : ℝ => (x+s)⁻¹) ρ) :
    ¬ ∀ x > 0, heatFreeVectorReal m a x = ∫ s, (x+s)⁻¹ ∂ρ := by
  intro h
  let x := fun n : ℕ => (n:ℝ)+1
  have hx (n : ℕ) : 0 < x n := by dsimp [x]; positivity
  have hmono : Monotone x := fun i j hij => add_le_add_right (Nat.cast_le.mpr hij) _
  have htop : Tendsto x atTop atTop := tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hi' (n : ℕ) : Integrable (fun s => x n/(x n+s)*(1:ℝ)) ρ := by
    simpa only [mul_one,div_eq_mul_inv] using (hi (x n) (hx n)).const_mul (x n)
  have hlim : Tendsto (fun n => ∫ s, x n/(x n+s)*(1:ℝ) ∂ρ) atTop (𝓝 0) := by
    apply ((heatFreeVector_scaled_tendsto_zero hm ha).comp htop).congr
    intro n
    simp only [Function.comp_apply,h (x n) (hx n),mul_one,div_eq_mul_inv,integral_const_mul]
  have hz := UV.RevisionSpectrum.normalizedMoment_lintegral hx hmono htop hs
    (f := fun _ => 1) (Eventually.of_forall fun _ => zero_le_one) hi' hlim
  exact hne (Measure.measure_univ_eq_zero.mp (by simpa using hz))

end UV.HeatMaxwell
