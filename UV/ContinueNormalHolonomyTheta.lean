import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Real.Pi.Bounds

/-! The angular trace of the periodic normal circle and its relative winding
series. The winding here belongs to the normal circle. -/

noncomputable section

open Real Filter Asymptotics Set
open scoped FourierTransform Topology

namespace UV.ContinueNormalHolonomy

/-- The full periodic scalar angular trace at heat width (v) and shift (a). -/
def normalTheta (v a : ℝ) : ℝ :=
  ∑' j : ℤ, Real.exp (-v * ((j : ℝ) - a) ^ 2)

/-- Zero-holonomy angular trace minus the trace at the given holonomy. -/
def relativeNormalTheta (v a : ℝ) : ℝ :=
  normalTheta v 0 - normalTheta v a

theorem normalTheta_integer_shift (v : ℝ) (m : ℤ) :
    normalTheta v m = normalTheta v 0 := by
  unfold normalTheta
  rw [← (Equiv.addRight m).tsum_eq (f := fun j : ℤ => Real.exp (-v * ((j : ℝ) - (m : ℝ)) ^ 2))]
  simp

private theorem normal_gaussian_fourier {v : ℝ} (hv : 0 < v) :
    (𝓕 fun x : ℝ => Complex.exp (-(v : ℂ) * (x : ℂ) ^ 2)) =
      fun x : ℝ => (Real.sqrt (Real.pi / v) : ℂ) *
        Complex.exp (-((Real.pi ^ 2 / v : ℝ) : ℂ) * (x : ℂ) ^ 2) := by
  let q : ℝ := v / Real.pi
  have hq : 0 < q := div_pos hv Real.pi_pos
  have h₀ : (↑Real.pi : ℂ) * (q : ℂ) = (v : ℂ) := by
    dsimp [q]
    push_cast
    field_simp [Real.pi_ne_zero]
  have h₁ : (↑Real.pi : ℂ) / (q : ℂ) = (↑(Real.pi ^ 2 / v) : ℂ) := by
    dsimp [q]
    push_cast
    field_simp [Real.pi_ne_zero, hv.ne']
  have hp : 1 / (q : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt (Real.pi / v) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hq.le, ← Real.sqrt_eq_rpow, ← Complex.ofReal_one, ← Complex.ofReal_div,
      one_div, ← Real.sqrt_inv]
    dsimp [q]
    rw [inv_div]
  have h := fourierIntegral_gaussian_pi (b := (q : ℂ)) (by simpa using hq)
  convert h using 1
  · congr 1
    funext x
    rw [show -(↑Real.pi : ℂ) * (q : ℂ) = -(v : ℂ) by rw [neg_mul, h₀]]
  · funext x
    rw [hp, neg_div, h₁]

private theorem normal_gaussian_decay {v : ℝ} (hv : 0 < v) :
    (fun x : ℝ => Complex.exp (-(v : ℂ) * (x : ℂ) ^ 2)) =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (-2 : ℝ)) :=
  (isLittleO_exp_neg_mul_sq_cocompact (by simpa using hv : 0 < (v : ℂ).re) _).isBigO

/-- Poisson summation for the actual shifted integer angular spectrum. -/
theorem normalTheta_poisson {v : ℝ} (hv : 0 < v) (a : ℝ) :
    normalTheta v a = Real.sqrt (Real.pi / v) *
      ∑' j : ℤ, Real.exp (-Real.pi ^ 2 / v * (j : ℝ) ^ 2) *
        Real.cos (2 * Real.pi * (j : ℝ) * a) := by
  let f (x : ℝ) := Complex.exp (-(v : ℂ) * (x : ℂ) ^ 2)
  have hF := normal_gaussian_fourier hv
  have hc : Continuous f := by unfold f; fun_prop
  have hb : 0 < Real.pi ^ 2 / v := by positivity
  have hFdec : (𝓕 f) =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
    rw [show 𝓕 f = _ from hF]
    exact (normal_gaussian_decay hb).const_mul_left _
  have hFs : Summable fun j : ℤ => 𝓕 f (j : ℝ) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hFdec.comp_tendsto Int.tendsto_coe_cofinite)
  have hmod : Summable fun j : ℤ => 𝓕 f (j : ℝ) * fourier j ((-a : ℝ) : UnitAddCircle) := by
    apply (summable_norm_iff.mpr hFs).of_norm_bounded
    intro j
    rw [norm_mul, fourier_coe_apply, show (2 * ↑Real.pi * Complex.I * (j : ℂ) * ↑(-a) /
      (1 : ℝ) : ℂ) = ((-(2 * Real.pi * (j : ℝ) * a) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have h := Real.tsum_eq_tsum_fourierIntegral_of_rpow_decay_of_summable hc one_lt_two
    (normal_gaussian_decay hv) hFs (-a)
  have h' := congrArg Complex.re h
  have hleft (j : ℤ) : f (-a + (j : ℝ)) =
      (Real.exp (-v * ((j : ℝ) - a) ^ 2) : ℂ) := by
    rw [show -a + (j : ℝ) = (j : ℝ) - a by ring]
    simp [f, Complex.ofReal_exp]
  rw [Complex.re_tsum hmod] at h'
  simp_rw [hleft, ← Complex.ofReal_tsum, Complex.ofReal_re] at h'
  have hright (j : ℤ) :
      (𝓕 f (j : ℝ) * fourier j ((-a : ℝ) : UnitAddCircle)).re =
        Real.sqrt (Real.pi / v) * (Real.exp (-Real.pi ^ 2 / v * (j : ℝ) ^ 2) *
          Real.cos (2 * Real.pi * (j : ℝ) * a)) := by
    rw [show 𝓕 f = _ from hF, fourier_coe_apply,
      show (2 * ↑Real.pi * Complex.I * (j : ℂ) * ↑(-a) / (1 : ℝ) : ℂ) =
        ((-(2 * Real.pi * (j : ℝ) * a) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    simp only [neg_div, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      ← Complex.ofReal_neg, ← Complex.ofReal_exp, mul_assoc, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  simp_rw [hright, tsum_mul_left] at h'
  exact h'

/-- Nonnegative contribution of one winding to the relative trace. -/
def relativeNormalWinding (v a : ℝ) (w : ℤ) : ℝ :=
  Real.exp (-(Real.pi ^ 2 / v) * (w : ℝ) ^ 2) *
    (1 - Real.cos (2 * Real.pi * (w : ℝ) * a))

private theorem normalGauss_int_summable {c : ℝ} (hc : 0 < c) :
    Summable (fun j : ℤ => Real.exp (-c * (j : ℝ) ^ 2)) := by
  have h := summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    ((normal_gaussian_decay hc).comp_tendsto Int.tendsto_coe_cofinite)
  convert h.norm using 1
  funext j
  rw [Function.comp_apply, Complex.norm_exp]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_neg,
    ← Complex.ofReal_mul, Complex.ofReal_re]

private theorem normalGauss_cos_summable {v : ℝ} (hv : 0 < v) (a : ℝ) :
    Summable (fun j : ℤ => Real.exp (-(Real.pi ^ 2 / v) * (j : ℝ) ^ 2) *
      Real.cos (2 * Real.pi * (j : ℝ) * a)) := by
  apply (normalGauss_int_summable (by positivity : 0 < Real.pi ^ 2 / v)).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

theorem relativeNormalWinding_nonnegative (v a : ℝ) (w : ℤ) :
    0 ≤ relativeNormalWinding v a w :=
  mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (Real.cos_le_one _))

theorem relativeNormalWinding_summable {v : ℝ} (hv : 0 < v) (a : ℝ) :
    Summable (relativeNormalWinding v a) := by
  convert (normalGauss_int_summable (by positivity : 0 < Real.pi ^ 2 / v)).sub
    (normalGauss_cos_summable hv a) using 1
  funext j
  simp only [relativeNormalWinding, mul_sub, mul_one]

/-- The zero mode cancels, and the two signs of each nonzero winding agree. -/
theorem relativeNormalTheta_poisson {v : ℝ} (hv : 0 < v) (a : ℝ) :
    relativeNormalTheta v a = 2 * Real.sqrt (Real.pi / v) *
      ∑' w : ℕ+, relativeNormalWinding v a (w : ℤ) := by
  rw [relativeNormalTheta, normalTheta_poisson hv 0, normalTheta_poisson hv a, ← mul_sub]
  simp only [mul_zero, Real.cos_zero, mul_one, neg_div]
  rw [← (normalGauss_int_summable (by positivity : 0 < Real.pi ^ 2 / v)).tsum_sub
    (normalGauss_cos_summable hv a)]
  have he (w : ℤ) : relativeNormalWinding v a (-w) = relativeNormalWinding v a w := by
    unfold relativeNormalWinding
    push_cast
    rw [neg_sq, mul_neg, neg_mul, neg_mul, Real.cos_neg]
  have h (w : ℤ) : Real.exp (-(Real.pi ^ 2 / v) * (w : ℝ) ^ 2) -
      Real.exp (-(Real.pi ^ 2 / v) * (w : ℝ) ^ 2) *
        Real.cos (2 * Real.pi * (w : ℝ) * a) = relativeNormalWinding v a w := by
    rw [relativeNormalWinding, mul_sub, mul_one]
  simp_rw [h]
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat he (relativeNormalWinding_summable hv a)]
  have hz : relativeNormalWinding v a 0 = 0 := by norm_num [relativeNormalWinding]
  rw [hz, zero_add]
  ring

theorem relativeNormalTheta_nonnegative {v : ℝ} (hv : 0 < v) (a : ℝ) :
    0 ≤ relativeNormalTheta v a := by
  rw [relativeNormalTheta_poisson hv]
  exact mul_nonneg (by positivity) (tsum_nonneg fun _ => relativeNormalWinding_nonnegative _ _ _)

theorem relativeNormalTheta_integer (v : ℝ) (m : ℤ) :
    relativeNormalTheta v m = 0 := by
  rw [relativeNormalTheta, normalTheta_integer_shift, sub_self]

private theorem relativeNormalWinding_one_positive {v a : ℝ}
    (ha : ∀ m : ℤ, a ≠ (m : ℝ)) : 0 < relativeNormalWinding v a 1 := by
  apply mul_pos (Real.exp_pos _)
  simp only [Int.cast_one, mul_one]
  apply sub_pos.mpr
  apply lt_of_le_of_ne (Real.cos_le_one _)
  intro h
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff _).mp h
  exact ha m (mul_left_cancel₀ (show 2 * Real.pi ≠ 0 by positivity)
    (by linarith))

theorem relativeNormalTheta_positive {v a : ℝ} (hv : 0 < v)
    (ha : ∀ m : ℤ, a ≠ (m : ℝ)) : 0 < relativeNormalTheta v a := by
  rw [relativeNormalTheta_poisson hv]
  apply mul_pos (by positivity)
  have hs := (relativeNormalWinding_summable hv a).comp_injective
    (show Function.Injective (fun w : ℕ+ => (w : ℤ)) by
      intro x y h
      apply Subtype.ext
      change ((x : ℕ) : ℤ) = ((y : ℕ) : ℤ) at h
      exact Int.ofNat_inj.mp h)
  apply (relativeNormalWinding_one_positive ha).trans_le
  exact hs.le_tsum (1 : ℕ+) (fun i _ => relativeNormalWinding_nonnegative v a i)

theorem normalTheta_continuousAt {v : ℝ} (hv : 0 < v) (a : ℝ) :
    ContinuousAt (fun s => normalTheta s a) v := by
  let f (s : ℝ) (j : ℤ) := Real.exp (-(Real.pi ^ 2 / s) * (j : ℝ) ^ 2) *
    Real.cos (2 * Real.pi * (j : ℝ) * a)
  have hsum : ContinuousAt (fun s => ∑' j, f s j) v := by
    apply tendsto_tsum_of_dominated_convergence
      (bound := fun j : ℤ => Real.exp (-(Real.pi ^ 2 / (2 * v)) * (j : ℝ) ^ 2))
      (normalGauss_int_summable (by positivity))
    · intro j
      have h : ContinuousAt (fun s => f s j) v := by unfold f; fun_prop (disch := positivity)
      exact h.tendsto
    · filter_upwards [Ioo_mem_nhds (half_lt_self hv) (by linarith : v < 2 * v)] with s hs j
      have hs0 : 0 < s := (half_pos hv).trans hs.1
      unfold f
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
      apply (mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)).trans
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg _) hs0 hs.2.le)
  have hroot : ContinuousAt (fun s => Real.sqrt (Real.pi / s)) v := by
    fun_prop (disch := positivity)
  apply (hroot.mul hsum).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hv] with s hs
  simpa only [neg_div, f] using normalTheta_poisson hs a

theorem relativeNormalTheta_continuousAt {v : ℝ} (hv : 0 < v) (a : ℝ) :
    ContinuousAt (fun s => relativeNormalTheta s a) v :=
  (normalTheta_continuousAt hv 0).sub (normalTheta_continuousAt hv a)

private theorem pnat_int_injective : Function.Injective (fun w : ℕ+ => (w : ℤ)) := by
  intro x y h
  apply Subtype.ext
  change ((x : ℕ) : ℤ) = ((y : ℕ) : ℤ) at h
  exact Int.ofNat_inj.mp h

/-- Uniform small-width estimate for a relative normal-circle trace. -/
theorem relativeNormalTheta_small_width :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v a : ℝ), 0 < v → v ≤ 1 →
      relativeNormalTheta v a ≤ C * Real.exp (-(Real.pi ^ 2 / (4 * v))) := by
  let G := ∑' w : ℕ+, Real.exp (-(Real.pi ^ 2 / 2) * ((w : ℤ) : ℝ) ^ 2)
  let C := 4 * Real.sqrt Real.pi * G
  have hG : 0 ≤ G := tsum_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨C, by positivity, ?_⟩
  intro v a hv hv1
  have hs := (normalGauss_int_summable (by positivity : 0 < Real.pi ^ 2 / 2)).comp_injective
    pnat_int_injective
  let E := Real.exp (-(Real.pi ^ 2 / (2 * v)))
  have hterm (w : ℕ+) :
      relativeNormalWinding v a (w : ℤ) ≤
        (2 * E) * Real.exp (-(Real.pi ^ 2 / 2) * ((w : ℤ) : ℝ) ^ 2) := by
    have hw : 1 ≤ ((w : ℤ) : ℝ) := by
      have hn : 1 ≤ (w : ℕ) := Nat.one_le_iff_ne_zero.mpr (PNat.ne_zero w)
      exact_mod_cast hn
    have hw2 : 1 ≤ (((w : ℤ) : ℝ) ^ 2) := by nlinarith
    have hp : (1 : ℝ) ≤ 1 / v := (le_div_iff₀ hv).mpr (by simpa using hv1)
    have hcost : -(Real.pi ^ 2 / v) * ((w : ℤ) : ℝ) ^ 2 ≤
        -(Real.pi ^ 2 / (2 * v)) + -(Real.pi ^ 2 / 2) * ((w : ℤ) : ℝ) ^ 2 := by
      have hm1 := mul_le_mul_of_nonneg_left hw2 (show 0 ≤ 1 / v by positivity)
      have hm2 := mul_le_mul_of_nonneg_right hp (sq_nonneg ((w : ℤ) : ℝ))
      have hh : 1 / v + ((w : ℤ) : ℝ) ^ 2 ≤ 2 * ((1 / v) * ((w : ℤ) : ℝ) ^ 2) := by
        linarith
      have hk := mul_le_mul_of_nonneg_left hh (show 0 ≤ Real.pi ^ 2 / 2 by positivity)
      convert neg_le_neg hk using 1 <;> ring
    unfold relativeNormalWinding E
    rw [show (2 * Real.exp (-(Real.pi ^ 2 / (2 * v)))) *
        Real.exp (-(Real.pi ^ 2 / 2) * ((w : ℤ) : ℝ) ^ 2) =
      Real.exp (-(Real.pi ^ 2 / (2 * v)) + -(Real.pi ^ 2 / 2) * ((w : ℤ) : ℝ) ^ 2) * 2 by
      rw [Real.exp_add]
      ring]
    refine mul_le_mul (Real.exp_le_exp.mpr hcost) ?_ (sub_nonneg.mpr (Real.cos_le_one _))
      (Real.exp_pos _).le
    linarith [Real.neg_one_le_cos (2 * Real.pi * ((w : ℤ) : ℝ) * a)]
  have hs' := (relativeNormalWinding_summable hv a).comp_injective pnat_int_injective
  have hsum := hs'.tsum_le_tsum hterm (hs.mul_left (2 * E))
  rw [tsum_mul_left] at hsum
  have hy : 1 ≤ v⁻¹ := by
    simpa only [one_div] using (le_div_iff₀ hv).mpr (by simpa using hv1 : 1 * v ≤ 1)
  have hyr : (Real.sqrt v⁻¹) ≤ v⁻¹ := by
    have hys := Real.sq_sqrt (show 0 ≤ v⁻¹ by positivity)
    nlinarith [Real.sqrt_nonneg v⁻¹, sq_nonneg (Real.sqrt v⁻¹ - v⁻¹),
      mul_nonneg (sub_nonneg.mpr hy) (show 0 ≤ v⁻¹ by positivity)]
  have hexp : Real.sqrt v⁻¹ ≤ Real.exp (Real.pi ^ 2 / (4 * v)) := by
    apply hyr.trans
    have hpi : 1 ≤ Real.pi ^ 2 / 4 := by nlinarith [Real.pi_gt_three]
    have hyc := mul_le_mul_of_nonneg_right hpi (show 0 ≤ v⁻¹ by positivity)
    have hxy : v⁻¹ ≤ Real.pi ^ 2 / (4 * v) := by
      simpa only [one_mul, div_eq_mul_inv, mul_inv, mul_assoc, mul_comm v⁻¹] using hyc
    exact (by linarith [Real.add_one_le_exp (v⁻¹)] : v⁻¹ ≤ Real.exp (v⁻¹)).trans
      (Real.exp_le_exp.mpr hxy)
  rw [relativeNormalTheta_poisson hv]
  apply (mul_le_mul_of_nonneg_left hsum (by positivity)).trans
  have hbig : Real.sqrt (Real.pi / v) ≤
      Real.sqrt Real.pi * Real.exp (Real.pi ^ 2 / (4 * v)) := by
    rw [div_eq_mul_inv, Real.sqrt_mul Real.pi_pos.le]
    exact mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _)
  have hbig' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbig (by norm_num : (0 : ℝ) ≤ 2))
    (show 0 ≤ (2 * E) * G by dsimp [E]; positivity)
  apply hbig'.trans_eq
  dsimp [E, C, G]
  rw [show 2 * (Real.sqrt Real.pi * Real.exp (Real.pi ^ 2 / (4 * v))) *
      (2 * Real.exp (-(Real.pi ^ 2 / (2 * v))) * _) =
      4 * Real.sqrt Real.pi * (∑' w : ℕ+, Real.exp (-(Real.pi ^ 2 / 2) * ((w : ℤ) : ℝ) ^ 2)) *
        (Real.exp (Real.pi ^ 2 / (4 * v)) * Real.exp (-(Real.pi ^ 2 / (2 * v)))) by ring,
    ← Real.exp_add]
  congr 2
  ring

theorem relativeNormalTheta_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v a : ℝ), 0 < v → relativeNormalTheta v a ≤ C := by
  obtain ⟨C, hC, hsmall⟩ := relativeNormalTheta_small_width
  refine ⟨max C (normalTheta 1 0), hC.trans (le_max_left _ _), ?_⟩
  intro v a hv
  by_cases h : v ≤ 1
  · exact (hsmall v a hv h).trans ((mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (by positivity)))).trans (le_max_left _ _))
  · apply le_trans _ (le_max_right _ _)
    have hna : 0 ≤ normalTheta v a := tsum_nonneg fun _ => (Real.exp_pos _).le
    apply (sub_le_self _ hna).trans
    simp only [normalTheta, sub_zero]
    apply (normalGauss_int_summable hv).tsum_le_tsum _ (normalGauss_int_summable zero_lt_one)
    intro j
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))

end UV.ContinueNormalHolonomy
