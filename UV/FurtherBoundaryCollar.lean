import UV.RevisionBoundaryHeat
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.MeasureTheory.Integral.Prod

/-! Scalar estimates for the jointly short normal collar and the angular gap. -/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace UV.FurtherBoundaryCollar

private theorem fifth_power_rpow {r : ℝ} (hr : 0 ≤ r) :
    (r ^ (5 : ℕ)) ^ (-3 / 5 : ℝ) = (r ^ (3 : ℕ))⁻¹ := by
  rw [← Real.rpow_natCast r 5, ← Real.rpow_mul hr]
  change r ^ ((5 : ℝ) * (-3 / 5)) = _
  rw [show (5 : ℝ) * (-3 / 5) = -((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg hr, Real.rpow_natCast]

private theorem small_radius_rate {r t : ℝ} (hr : 0 < r) (hrt : r ^ (5 : ℕ) ≤ t) :
    t ^ (-3 / 5 : ℝ) ≤ (r ^ (3 : ℕ))⁻¹ := by
  rw [← fifth_power_rpow hr.le]
  exact Real.rpow_le_rpow_of_exponent_nonpos (pow_pos hr _) hrt (by norm_num)

private theorem short_duration_rate {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hrt : t ≤ r ^ (5 : ℕ)) :
    (r ^ (3 : ℕ))⁻¹ ≤ t ^ (-3 / 5 : ℝ) ∧
      t ^ (-3 / 5 : ℝ) ≤ r ^ (2 : ℕ) / t := by
  constructor
  · rw [← fifth_power_rpow hr.le]
    exact Real.rpow_le_rpow_of_exponent_nonpos ht hrt (by norm_num)
  · apply (le_div_iff₀ ht).mpr
    rw [← Real.rpow_add_one ht.ne']
    convert Real.rpow_le_rpow ht.le hrt (show (0 : ℝ) ≤ 2 / 5 by norm_num) using 1
    · norm_num
    · rw [← Real.rpow_natCast r 5, ← Real.rpow_mul hr.le]
      norm_num

/-- The shared radial readout retains both the angular barrier and the bridge. -/
theorem joint_collar_pointwise_bound {F : ℝ → ℝ} {K : ℝ → ℝ → ℝ}
    {C M k t r : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hk : 0 < k)
    (hr : 0 < r) (ht : 0 < t)
    (hF0 : 0 ≤ F r)
    (hF : F r ≤ M * Real.exp (min (k / 2) (1 / 2) / r ^ (3 : ℕ)))
    (hK₀ : K t r ≤ C * t ^ (-1 / 2 : ℝ))
    (hK₁ : r ^ (5 : ℕ) ≤ t →
      K t r ≤ C * t ^ (-1 / 2 : ℝ) * Real.exp (-k / r ^ (3 : ℕ))) :
    F r * Real.exp (-(r ^ (2 : ℕ)) / t) * K t r ≤
      M * C * t ^ (-1 / 2 : ℝ) * Real.exp (-min (k / 2) (1 / 2) * t ^ (-3 / 5 : ℝ)) := by
  let c : ℝ := min (k / 2) (1 / 2)
  have hc : 0 ≤ c := le_min (by linarith) (by norm_num)
  have hx : 0 < r ^ (3 : ℕ) := pow_pos hr _
  have hy : 0 ≤ r ^ (2 : ℕ) / t := div_nonneg (sq_nonneg r) ht.le
  have hp : 0 ≤ C * t ^ (-1 / 2 : ℝ) := mul_nonneg hC (Real.rpow_nonneg ht.le _)
  change F r ≤ M * Real.exp (c / r ^ (3 : ℕ)) at hF
  have hmain {w : ℝ} (hKw : K t r ≤ C * t ^ (-1 / 2 : ℝ) * Real.exp w)
      (hexp : c / r ^ (3 : ℕ) + -(r ^ (2 : ℕ)) / t + w ≤ -c * t ^ (-3 / 5 : ℝ)) :
      F r * Real.exp (-(r ^ (2 : ℕ)) / t) * K t r ≤
        M * C * t ^ (-1 / 2 : ℝ) * Real.exp (-c * t ^ (-3 / 5 : ℝ)) := by
    calc
      _ ≤ F r * Real.exp (-(r ^ (2 : ℕ)) / t) *
          (C * t ^ (-1 / 2 : ℝ) * Real.exp w) :=
        mul_le_mul_of_nonneg_left hKw (mul_nonneg hF0 (Real.exp_nonneg _))
      _ ≤ (M * Real.exp (c / r ^ (3 : ℕ))) * Real.exp (-(r ^ (2 : ℕ)) / t) *
          (C * t ^ (-1 / 2 : ℝ) * Real.exp w) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hF (Real.exp_nonneg _))
          (mul_nonneg hp (Real.exp_nonneg _))
      _ = M * C * t ^ (-1 / 2 : ℝ) *
            Real.exp (c / r ^ (3 : ℕ) + -(r ^ (2 : ℕ)) / t + w) := by
        rw [Real.exp_add, Real.exp_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
        (mul_nonneg (mul_nonneg hM hC) (Real.rpow_nonneg ht.le _))
  change _ ≤ M * C * t ^ (-1 / 2 : ℝ) * Real.exp (-c * t ^ (-3 / 5 : ℝ))
  by_cases h : r ^ (5 : ℕ) ≤ t
  · apply hmain (hK₁ h)
    have h₁ := mul_le_mul_of_nonneg_left (small_radius_rate hr h) hc
    have h₂ : c + c ≤ k := by
      have := min_le_left (k / 2) (1 / 2)
      change c ≤ k / 2 at this
      linarith
    have h₃ := div_le_div_of_nonneg_right h₂ hx.le
    rw [add_div] at h₃
    simp only [div_eq_mul_inv] at *
    linarith
  · apply hmain (w := 0) (by simpa using hK₀)
    obtain ⟨h₁, h₂⟩ := short_duration_rate hr ht (le_of_not_ge h)
    have h₃ := mul_le_mul_of_nonneg_left h₁ hc
    have h₄ := mul_le_mul_of_nonneg_left h₂ (show 0 ≤ c + c by linarith)
    have h₅ : c + c ≤ 1 := by
      have := min_le_right (k / 2) (1 / 2)
      change c ≤ 1 / 2 at this
      linarith
    have h₆ := mul_le_mul_of_nonneg_right h₅ hy
    simp only [div_eq_mul_inv, one_mul, add_mul, add_zero] at *
    linarith

/-- The normal Dirac radial multiplier after the quartic measure change. -/
def spinMultiplier (ν b r : ℝ) : ℝ := ν / r ^ (4 : ℕ) - b * r

/-- The derivative entering the two chiral scalar potentials. -/
theorem spinMultiplier_hasDerivAt (ν b : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (spinMultiplier ν b) (-4 * ν / r ^ (5 : ℕ) - b) r := by
  have hd := ((hasDerivAt_const r ν).div ((hasDerivAt_id r).pow 4) (pow_ne_zero _ hr)).sub
    ((hasDerivAt_id r).const_mul b)
  convert hd using 1
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSubDiff, mul_one]
  field_simp
  ring

/-- The lower potential bound is uniform in the normal angular mode and in chirality. -/
theorem spin_gap_potential_bound {δ : ℝ} (hδ : 0 < δ) (b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν s r : ℝ), δ ≤ |ν| → |s| ≤ 1 → r ∈ Ioc 0 1 →
      ν ^ (2 : ℕ) / (8 * r ^ (8 : ℕ)) + ν ^ (2 : ℕ) / 8 - C ≤
        (spinMultiplier ν b r) ^ (2 : ℕ) + s * (-4 * ν / r ^ (5 : ℕ) - b) := by
  let R := min 1 (δ / 16)
  have hR : 0 < R := lt_min zero_lt_one (by linarith)
  let A := 4 / R ^ (5 : ℕ)
  refine ⟨b ^ (2 : ℕ) + A ^ (2 : ℕ) + |b|, by positivity, ?_⟩
  intro ν s r hν hs hr
  have h4 : 0 < r ^ (4 : ℕ) := pow_pos hr.1 _
  have h5 : 0 < r ^ (5 : ℕ) := pow_pos hr.1 _
  have h8 : 0 < r ^ (8 : ℕ) := pow_pos hr.1 _
  have hν0 : 0 ≤ |ν| := abs_nonneg _
  have hpow (n : ℕ) : r ^ n ≤ 1 := pow_le_one₀ hr.1.le hr.2
  have hW : ν ^ (2 : ℕ) / (2 * r ^ (8 : ℕ)) - b ^ (2 : ℕ) ≤
      (spinMultiplier ν b r) ^ (2 : ℕ) := by
    have h₁ := mul_le_mul_of_nonneg_left (hpow 2) (sq_nonneg b)
    have h₂ := sq_nonneg (ν / r ^ (4 : ℕ) / 2 - b * r)
    have h₃ : (ν / r ^ (4 : ℕ)) ^ (2 : ℕ) / 2 = ν ^ (2 : ℕ) / (2 * r ^ (8 : ℕ)) := by
      rw [div_pow]
      ring
    unfold spinMultiplier
    rw [← h₃]
    nlinarith
  have hD : 4 * |ν| / r ^ (5 : ℕ) ≤ ν ^ (2 : ℕ) / (4 * r ^ (8 : ℕ)) +
      A ^ (2 : ℕ) := by
    by_cases hrR : r ≤ R
    · have hRδ : R ≤ δ / 16 := min_le_right _ _
      have hr3 : r ^ (3 : ℕ) ≤ r := by
        calc
          r ^ (3 : ℕ) = r * r ^ (2 : ℕ) := by ring
          _ ≤ r * 1 := mul_le_mul_of_nonneg_left (hpow 2) hr.1.le
          _ = r := mul_one _
      have hl : 16 * r ^ (3 : ℕ) ≤ |ν| := by linarith
      have hz := mul_le_mul_of_nonneg_right hl hν0
      rw [abs_mul_abs_self] at hz
      have hw : 4 * |ν| / r ^ (5 : ℕ) ≤ ν ^ (2 : ℕ) / (4 * r ^ (8 : ℕ)) := by
        apply (div_le_div_iff₀ h5 (by positivity : 0 < 4 * r ^ (8 : ℕ))).mpr
        convert mul_le_mul_of_nonneg_right hz h5.le using 1 <;> ring
      linarith [sq_nonneg A]
    · have hR5 : R ^ (5 : ℕ) ≤ r ^ (5 : ℕ) :=
        pow_le_pow_left₀ hR.le (le_of_lt (lt_of_not_ge hrR)) _
      have hA : 4 / r ^ (5 : ℕ) ≤ A := div_le_div_of_nonneg_left (by norm_num) (by positivity) hR5
      have hAν := mul_le_mul_of_nonneg_right hA hν0
      have hsquare := sq_nonneg (|ν| / 2 - A)
      have hsquare' : A * |ν| ≤ ν ^ (2 : ℕ) / 4 + A ^ (2 : ℕ) := by
        rw [← sq_abs ν]
        nlinarith
      have hf : ν ^ (2 : ℕ) / 4 ≤ ν ^ (2 : ℕ) / (4 * r ^ (8 : ℕ)) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith [hpow 8])
      have hmul : 4 / r ^ (5 : ℕ) * |ν| = 4 * |ν| / r ^ (5 : ℕ) := by ring
      rw [hmul] at hAν
      linarith
  have hS : -(4 * |ν| / r ^ (5 : ℕ) + |b|) ≤ s * (-4 * ν / r ^ (5 : ℕ) - b) := by
    refine (neg_le_neg ?_).trans (neg_abs_le _)
    rw [abs_mul]
    calc
      |s| * |(-4 : ℝ) * ν / r ^ (5 : ℕ) - b| ≤
          1 * |(-4 : ℝ) * ν / r ^ (5 : ℕ) - b| :=
        mul_le_mul_of_nonneg_right hs (abs_nonneg _)
      _ ≤ 4 * |ν| / r ^ (5 : ℕ) + |b| := by
        rw [one_mul]
        have h := abs_sub_le ((-4 : ℝ) * ν / r ^ (5 : ℕ)) 0 b
        rw [sub_zero, zero_sub, abs_neg, abs_div, abs_mul, abs_of_pos h5] at h
        simpa using h
  have hsplit : ν ^ (2 : ℕ) / 8 ≤ ν ^ (2 : ℕ) / (8 * r ^ (8 : ℕ)) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith [hpow 8])
  have hrel : ν ^ (2 : ℕ) / (2 * r ^ (8 : ℕ)) =
      ν ^ (2 : ℕ) / (4 * r ^ (8 : ℕ)) + 2 * (ν ^ (2 : ℕ) / (8 * r ^ (8 : ℕ))) := by ring
  linarith

/-- A stretched exponential absorbs any power, uniformly on a bounded time interval. -/
theorem stretched_exponential_absorbs_power {a d T : ℝ}
    (ha : 0 < a) (hd : 0 < d) (p : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Ioc 0 T, t ^ (-p) * Real.exp (-d * t ^ (-a)) ≤ A := by
  by_cases hT : 0 ≤ T
  swap
  · exact ⟨0, le_rfl, fun t ht => False.elim (hT (ht.1.le.trans ht.2))⟩
  obtain ⟨n, hn⟩ := exists_nat_ge (p / a)
  have hp := (div_le_iff₀ ha).mp hn
  let B : ℝ := (n.factorial : ℝ) / d ^ n
  have hB : 0 ≤ B := by positivity
  have hpa : 0 ≤ a * (n : ℝ) - p := by nlinarith
  refine ⟨B * T ^ (a * (n : ℝ) - p), ?_, ?_⟩
  · exact mul_nonneg hB (Real.rpow_nonneg hT _)
  intro t ht
  have hx : 0 < d * t ^ (-a) := mul_pos hd (Real.rpow_pos_of_pos ht.1 _)
  have hcmp : Real.exp (-d * t ^ (-a)) ≤ B * t ^ (a * (n : ℝ)) := by
    calc
      _ = (Real.exp (d * t ^ (-a)))⁻¹ := by rw [neg_mul, Real.exp_neg]
      _ ≤ (((d * t ^ (-a)) ^ n) / (n.factorial : ℝ))⁻¹ :=
        inv_anti₀ (by positivity) (Real.pow_div_factorial_le_exp _ hx.le n)
      _ = _ := by
        rw [inv_div, mul_pow, ← Real.rpow_mul_natCast ht.1.le, neg_mul, Real.rpow_neg ht.1.le]
        unfold B
        field_simp [pow_ne_zero n hd.ne', (Real.rpow_pos_of_pos ht.1 (a * (n : ℝ))).ne']
  calc
    _ ≤ t ^ (-p) * (B * t ^ (a * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hcmp (Real.rpow_nonneg ht.1.le _)
    _ = B * t ^ (a * (n : ℝ) - p) := by
      rw [sub_eq_add_neg, Real.rpow_add ht.1]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.1.le ht.2 hpa) hB

/-- The stretched-exponential time majorant is integrable with arbitrary power weights. -/
theorem stretched_exponential_integrableOn {a d T : ℝ} (ha : 0 < a) (hd : 0 < d) (p : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ (-p) * Real.exp (-d * t ^ (-a))) (Ioc 0 T) := by
  obtain ⟨A, -, hbound⟩ := stretched_exponential_absorbs_power (T := T) ha hd p
  have hmeas : Measurable (fun t : ℝ => t ^ (-p) * Real.exp (-d * t ^ (-a))) := by fun_prop
  apply (integrableOn_const (C := A) (by simp [Real.volume_Ioc])).mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.exp_nonneg _))]
  exact hbound t ht

/-- Positive radial trace integrand for one shared readout. -/
def collarReadout (F : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ r in Ioc 0 1, F r * Real.exp (-(r ^ (2 : ℕ)) / t) * K t r

set_option maxHeartbeats 600000 in
/-- The scalar diagonal bounds imply integrability of the shared-readout trace. -/
theorem joint_collar_trace_integrableOn {F : ℝ → ℝ} {K : ℝ → ℝ → ℝ} {C M k T : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hk : 0 < k)
    (hFmeas : Measurable F) (hKmeas : Measurable (Function.uncurry K))
    (hF0 : ∀ r ∈ Ioc 0 1, 0 ≤ F r)
    (hF : ∀ r ∈ Ioc 0 1, F r ≤ M * Real.exp (min (k / 2) (1 / 2) / r ^ (3 : ℕ)))
    (hK0 : ∀ t ∈ Ioc 0 T, ∀ r ∈ Ioc 0 1, 0 ≤ K t r)
    (hK₀ : ∀ t ∈ Ioc 0 T, ∀ r ∈ Ioc 0 1, K t r ≤ C * t ^ (-1 / 2 : ℝ))
    (hK₁ : ∀ t ∈ Ioc 0 T, ∀ r ∈ Ioc 0 1, r < 1 / 4 → r ^ (5 : ℕ) ≤ t →
      K t r ≤ C * t ^ (-1 / 2 : ℝ) * Real.exp (-k / r ^ (3 : ℕ))) :
    IntegrableOn (fun t : ℝ => collarReadout F K t / (2 * Real.pi * t)) (Ioc 0 T) := by
  let C' := C * Real.exp (64 * k)
  let c : ℝ := min (k / 2) (1 / 2)
  have hc : 0 < c := lt_min (by linarith) (by norm_num)
  have hCC' : C ≤ C' := by
    have he := Real.one_le_exp_iff.mpr (by positivity : 0 ≤ 64 * k)
    simpa [C'] using mul_le_mul_of_nonneg_left he hC
  have hC' : 0 ≤ C' := hC.trans hCC'
  have hpoint (t : ℝ) (ht : t ∈ Ioc 0 T) (r : ℝ) (hr : r ∈ Ioc 0 1) :
      F r * Real.exp (-(r ^ (2 : ℕ)) / t) * K t r ≤
        M * C' * t ^ (-1 / 2 : ℝ) * Real.exp (-c * t ^ (-3 / 5 : ℝ)) := by
    have hfree : K t r ≤ C' * t ^ (-1 / 2 : ℝ) :=
      (hK₀ t ht r hr).trans (mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg ht.1.le _))
    apply joint_collar_pointwise_bound hC' hM hk hr.1 ht.1 (hF0 r hr) (hF r hr) hfree
    intro hrt
    by_cases hsmall : r < 1 / 4
    · exact (hK₁ t ht r hr hsmall hrt).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg ht.1.le _)) (Real.exp_nonneg _))
    · have hrf : (1 / 4 : ℝ) ≤ r := le_of_not_gt hsmall
      have hpow : (1 / 64 : ℝ) ≤ r ^ (3 : ℕ) := by
        convert pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 / 4 by norm_num) hrf 3 using 1
        norm_num
      have harg : 0 ≤ 64 * k + -k / r ^ (3 : ℕ) := by
        have hdiv : k / r ^ (3 : ℕ) ≤ 64 * k :=
          (div_le_iff₀ (pow_pos hr.1 _)).mpr (by nlinarith [mul_le_mul_of_nonneg_left hpow hk.le])
        rw [neg_div]
        linarith
      calc
        _ ≤ C * t ^ (-1 / 2 : ℝ) := hK₀ t ht r hr
        _ ≤ C * t ^ (-1 / 2 : ℝ) * Real.exp (64 * k + -k / r ^ (3 : ℕ)) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr harg)
            (mul_nonneg hC (Real.rpow_nonneg ht.1.le _))
        _ = _ := by rw [Real.exp_add]; unfold C'; ring
  have hIK : Measurable (fun z : ℝ × ℝ =>
      F z.2 * Real.exp (-(z.2 ^ (2 : ℕ)) / z.1) * K z.1 z.2) :=
    ((hFmeas.comp measurable_snd).mul (by fun_prop)).mul hKmeas
  have hread : Measurable (collarReadout F K) :=
    (hIK.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 1))).measurable
  have hweighted : Measurable (fun t : ℝ => collarReadout F K t / (2 * Real.pi * t)) := by fun_prop
  have htime := ((stretched_exponential_integrableOn (a := 3 / 5) (T := T)
    (by norm_num) hc (3 / 2)).const_mul (M * C' / (2 * Real.pi)))
  apply htime.mono' hweighted.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := ht.1
  have hne : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioc 0 1)]
      fun r => F r * Real.exp (-(r ^ (2 : ℕ)) / t) * K t r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact mul_nonneg (mul_nonneg (hF0 r hr) (Real.exp_nonneg _)) (hK0 t ht r hr)
  have hA : 0 ≤ collarReadout F K t := integral_nonneg_of_ae hne
  have hbound : collarReadout F K t ≤
      M * C' * t ^ (-1 / 2 : ℝ) * Real.exp (-c * t ^ (-3 / 5 : ℝ)) := by
    unfold collarReadout
    refine (integral_mono_of_nonneg hne
      (integrableOn_const (C := M * C' * t ^ (-1 / 2 : ℝ) *
        Real.exp (-c * t ^ (-3 / 5 : ℝ))) (by simp [Real.volume_Ioc])) ?_).trans_eq ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hpoint t ht r hr
    · rw [setIntegral_const, Real.volume_real_Ioc]
      norm_num
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hA (by positivity))]
  simp only [show (-(3 / 5) : ℝ) = -3 / 5 by norm_num]
  change _ ≤ M * C' / (2 * Real.pi) *
    (t ^ (-(3 / 2) : ℝ) * Real.exp (-c * t ^ (-3 / 5 : ℝ)))
  calc
    _ ≤ (M * C' * t ^ (-1 / 2 : ℝ) * Real.exp (-c * t ^ (-3 / 5 : ℝ))) /
        (2 * Real.pi * t) := div_le_div_of_nonneg_right hbound (by positivity)
    _ = _ := by
      rw [show (-(3 / 2) : ℝ) = -1 / 2 - 1 by norm_num, Real.rpow_sub_one ht.1.ne']
      ring

/-- The small-gap vacuum lower bound forces divergence under a power-law density. -/
theorem averaged_spin_vacuum_not_integrableOn {ρ V : ℝ → ℝ} {d m T : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hT : 0 < T) (q : ℝ)
    (hρ : ∀ x ∈ Ioc 0 T, m * x ^ q ≤ ρ x)
    (hV : ∀ x ∈ Ioc 0 T,
      Real.exp (d * x ^ (-2 / 3 : ℝ) * (1 + |Real.log x|) ^ (4 : ℕ)) ≤ V x) :
    ¬ IntegrableOn (fun x => ρ x * V x) (Ioc 0 T) := by
  intro hfin
  obtain ⟨A, hA, hbound⟩ := stretched_exponential_absorbs_power (a := 2 / 3) (T := T)
    (by norm_num) hd (q + 1)
  have hbad : IntegrableOn (fun x : ℝ => x⁻¹) (Ioc 0 T) := by
    apply (hfin.const_mul (A / m)).mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    let X := x ^ (-2 / 3 : ℝ)
    have hX : 0 ≤ X := Real.rpow_nonneg hx.1.le _
    have he : Real.exp (d * X) ≤ V x := by
      refine (Real.exp_le_exp.mpr ?_).trans (hV x hx)
      have hl : (1 : ℝ) ≤ 1 + |Real.log x| := by linarith [abs_nonneg (Real.log x)]
      simpa only [one_mul, one_pow, mul_one] using
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ zero_le_one hl 4) (mul_nonneg hd.le hX)
    have hpow : x ^ (-(q + 1)) ≤ A * Real.exp (d * X) := by
      have h := hbound x hx
      rw [show (-(2 / 3) : ℝ) = -2 / 3 by norm_num, neg_mul, Real.exp_neg,
        ← div_eq_mul_inv] at h
      exact (div_le_iff₀ (Real.exp_pos _)).mp h
    have hrenorm : x⁻¹ = x ^ q * x ^ (-(q + 1)) := by
      rw [← Real.rpow_add hx0, show q + -(q + 1) = -1 by ring, Real.rpow_neg_one]
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hx0.le)]
    have hρ0 := (mul_nonneg hm.le (Real.rpow_nonneg hx0.le q)).trans (hρ x hx)
    calc
      x⁻¹ = x ^ q * x ^ (-(q + 1)) := hrenorm
      _ ≤ x ^ q * (A * Real.exp (d * X)) :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hx0.le _)
      _ = (A / m) * (m * x ^ q * Real.exp (d * X)) := by field_simp
      _ ≤ (A / m) * (ρ x * V x) := mul_le_mul_of_nonneg_left
        (mul_le_mul (hρ x hx) he (Real.exp_nonneg _) hρ0) (div_nonneg hA hm.le)
  have hbad' := hbad.mono_set Ioo_subset_Ioc_self
  simp only [← Real.rpow_neg_one] at hbad'
  exact (lt_irrefl (-1 : ℝ)) ((intervalIntegral.integrableOn_Ioo_rpow_iff hT).mp hbad')

/-- A half-integer normal shift and trivial holonomy give the precise angular gap. -/
theorem trivial_holonomy_bounding_spin_gap :
    IsLeast (range (fun n : ℤ => |(n : ℝ) + 1 / 2|)) (1 / 2 : ℝ) := by
  constructor
  · exact ⟨0, by norm_num⟩
  · rintro _ ⟨n, rfl⟩
    change (1 / 2 : ℝ) ≤ |(n : ℝ) + 1 / 2|
    by_cases hn : 0 ≤ n
    · have hnr : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      rw [abs_of_nonneg (by linarith : 0 ≤ (n : ℝ) + 1 / 2)]
      linarith
    · have hn' : n ≤ -1 := by omega
      have hnr : (n : ℝ) ≤ -1 := by exact_mod_cast hn'
      rw [abs_of_nonpos (by linarith : (n : ℝ) + 1 / 2 ≤ 0)]
      linarith

end UV.FurtherBoundaryCollar
