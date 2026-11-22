import UV.FurtherBoundaryEnvelope
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Endpoint and confined-path estimates in the charged normal heat comparison. -/

noncomputable section

open Real Set MeasureTheory
open scoped ENNReal

namespace UV.ResumeCollarHeat

/-- Free normal kernel for the generator `∂ᵣ²`, at a displacement on the line. -/
def freeNormalKernel (s x : ℝ) : ℝ :=
  (Real.sqrt (4 * Real.pi * s))⁻¹ * Real.exp (-(x ^ (2 : ℕ)) / (4 * s))

/-- Exact normalization and the Gaussian upper tail used in the excursion estimate. -/
theorem free_normal_endpoint_tail {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s) :
    (∫ x in Ici r, freeNormalKernel s x) ≤
      Real.exp (-(r ^ (2 : ℕ)) / (4 * s)) / 2 := by
  let b : ℝ := (4 * s)⁻¹
  let f := fun x : ℝ => Real.exp (-b * x ^ (2 : ℕ))
  let F := fun x : ℝ => Real.exp (-b * r ^ (2 : ℕ)) * f (x - r)
  let C := (Real.sqrt (4 * Real.pi * s))⁻¹
  have hb : 0 < b := by positivity
  have hC : 0 ≤ C := by positivity
  have hf : Integrable f := integrable_exp_neg_mul_sq hb
  have hmeas : Measurable f := by dsimp [f]; fun_prop
  have hmp := measurePreserving_add_right (volume : Measure ℝ) (-r)
  have hF : Integrable F := by
    apply Integrable.const_mul
    simpa only [Function.comp_def, ← sub_eq_add_neg] using
      (hmp.integrable_comp hmeas.aestronglyMeasurable).mpr hf
  have hchange : (∫ x in Ici r, f (x - r)) = ∫ x in Ici 0, f x := by
    have h := setIntegral_map (μ := (volume : Measure ℝ)) (f := f)
      (s := Ici (0 : ℝ)) measurableSet_Ici hmeas.aestronglyMeasurable
      hmp.measurable.aemeasurable
    rw [hmp.map_eq] at h
    have hpre : (fun x : ℝ => x + -r) ⁻¹' Ici (0 : ℝ) = Ici r := by
      ext x
      simp
    rw [hpre] at h
    simpa only [← sub_eq_add_neg] using h.symm
  have hcomp : ∀ x ∈ Ici r, f x ≤ F x := by
    intro x hx
    have hx' : r ≤ x := hx
    unfold f F
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (mul_nonneg hb.le hr) (sub_nonneg.mpr hx')]
  have hi : (∫ x in Ici r, f x) ≤ ∫ x in Ici r, F x :=
    setIntegral_mono_on hf.integrableOn hF.integrableOn measurableSet_Ici hcomp
  have hsrc (x : ℝ) : freeNormalKernel s x = C * f x := by
    unfold freeNormalKernel f C b
    congr 1
    congr 1
    ring
  simp_rw [hsrc]
  rw [integral_const_mul]
  calc
    _ ≤ C * ∫ x in Ici r, F x := mul_le_mul_of_nonneg_left hi hC
    _ = _ := by
      unfold F
      rw [integral_const_mul, hchange, integral_Ici_eq_integral_Ioi]
      change C * (Real.exp (-b * r ^ (2 : ℕ)) * (∫ x in Ioi 0, Real.exp (-b * x ^ (2 : ℕ)))) = _
      rw [integral_gaussian_Ioi]
      have hroot : Real.sqrt (Real.pi / b) = Real.sqrt (4 * Real.pi * s) := by
        congr 1
        unfold b
        rw [div_inv_eq_mul]
        ring
      rw [hroot, show -b * r ^ (2 : ℕ) = -(r ^ (2 : ℕ)) / (4 * s) by unfold b; ring]
      unfold C
      field_simp [Real.sqrt_ne_zero'.mpr (by positivity : 0 < 4 * Real.pi * s)]

/-- Positive radial potential for the quartic normal collar. -/
def chargedPotential (j r : ℝ) : ℝ := 2 / r ^ (2 : ℕ) + j ^ (2 : ℕ) / r ^ (8 : ℕ)

/-- Each surviving confined path pays the prescribed short-time potential-integral cost. -/
theorem confined_path_potential_cost {r : ℝ} (hr : 0 < r) (j : ℝ) (x : ℝ → ℝ)
    (hx : ∀ᵐ u ∂(volume : Measure ℝ).restrict (Ioc 0 (r ^ (5 : ℕ))),
      0 < x u ∧ x u ≤ 2 * r) :
    ENNReal.ofReal (j ^ (2 : ℕ) * r ^ (5 : ℕ) / (2 * r) ^ (8 : ℕ)) ≤
      ∫⁻ u in Ioc 0 (r ^ (5 : ℕ)), ENNReal.ofReal (chargedPotential j (x u)) := by
  have h := lintegral_mono_ae (μ := (volume : Measure ℝ).restrict (Ioc 0 (r ^ (5 : ℕ))))
    (f := fun _ => ENNReal.ofReal (j ^ (2 : ℕ) / (2 * r) ^ (8 : ℕ)))
    (g := fun u => ENNReal.ofReal (chargedPotential j (x u))) (by
      filter_upwards [hx] with u hu
      apply ENNReal.ofReal_le_ofReal
      unfold chargedPotential
      have hm := div_le_div_of_nonneg_left (sq_nonneg j) (pow_pos hu.1 8)
        (pow_le_pow_left₀ hu.1.le hu.2 8)
      have hp : 0 ≤ 2 / (x u) ^ (2 : ℕ) := by positivity
      linarith)
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
    ← ENNReal.ofReal_mul (by positivity)] at h
  convert h using 2
  ring

/-- The Feynman–Kac split and endpoint reflection comparison imply the tip diagonal bound. -/
theorem short_tip_diagonal_from_reflection {r t j K P C : ℝ}
    (hr : 0 < r) (ht : 0 < t) (hj : j ≠ 0) (hC : 0 ≤ C)
    (hReflect : P ≤ 2 * ∫ x in Ici r, freeNormalKernel (r ^ (5 : ℕ)) x)
    (hSplit : K ≤ C * t ^ (-1 / 2 : ℝ) *
      (Real.exp (-(j ^ (2 : ℕ) * r ^ (5 : ℕ) / (2 * r) ^ (8 : ℕ))) + P)) :
    0 < min (j ^ (2 : ℕ) / 256) (1 / 4) ∧
      K ≤ (2 * C) * t ^ (-1 / 2 : ℝ) *
        Real.exp (-min (j ^ (2 : ℕ) / 256) (1 / 4) / r ^ (3 : ℕ)) := by
  let k : ℝ := min (j ^ (2 : ℕ) / 256) (1 / 4)
  have hk : 0 < k := lt_min (by positivity) (by norm_num)
  refine ⟨hk, ?_⟩
  have hcost : j ^ (2 : ℕ) * r ^ (5 : ℕ) / (2 * r) ^ (8 : ℕ) =
      (j ^ (2 : ℕ) / 256) / r ^ (3 : ℕ) := by
    field_simp
    ring
  have hrate : r ^ (2 : ℕ) / (4 * r ^ (5 : ℕ)) = (1 / 4) / r ^ (3 : ℕ) := by
    field_simp
  have hb1 : Real.exp (-(j ^ (2 : ℕ) * r ^ (5 : ℕ) / (2 * r) ^ (8 : ℕ))) ≤
      Real.exp (-k / r ^ (3 : ℕ)) := by
    rw [hcost, ← neg_div]
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg (min_le_left _ _)) (by positivity))
  have hb2 : P ≤ Real.exp (-k / r ^ (3 : ℕ)) := by
    have ht' := free_normal_endpoint_tail hr.le (pow_pos hr 5)
    have hp := hReflect.trans (mul_le_mul_of_nonneg_left ht' zero_le_two)
    rw [mul_div_cancel₀ _ (by norm_num), neg_div, hrate] at hp
    apply hp.trans
    rw [neg_div]
    exact Real.exp_le_exp.mpr (neg_le_neg
      (div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)))
  calc
    _ ≤ C * t ^ (-1 / 2 : ℝ) *
        (Real.exp (-(j ^ (2 : ℕ) * r ^ (5 : ℕ) / (2 * r) ^ (8 : ℕ))) + P) := hSplit
    _ ≤ C * t ^ (-1 / 2 : ℝ) * (2 * Real.exp (-k / r ^ (3 : ℕ))) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC (Real.rpow_nonneg ht.le _))
    _ = _ := by ring

/-- The source split and reflected endpoint bound transfer to the scalar joint trace. -/
theorem joint_collar_trace_from_reflection {F P : ℝ → ℝ} {K : ℝ → ℝ → ℝ}
    {C A N j T : ℝ} (hC : 0 ≤ C) (hj : j ≠ 0)
    (hFmeas : Measurable F) (hKmeas : Measurable (Function.uncurry K))
    (hF0 : ∀ r ∈ Ioc 0 1, 0 ≤ F r)
    (hF : ∀ r ∈ Ioc 0 1, F r ≤ Real.exp (UV.FurtherBoundaryEnvelope.logEnvelope A N r))
    (hK0 : ∀ t ∈ Ioc 0 T, ∀ r ∈ Ioc 0 1, 0 ≤ K t r)
    (hFree : ∀ t ∈ Ioc 0 T, ∀ r ∈ Ioc 0 1, K t r ≤ C * t ^ (-1 / 2 : ℝ))
    (hReflect : ∀ r ∈ Ioc 0 1, r < 1 / 4 →
      P r ≤ 2 * ∫ x in Ici r, freeNormalKernel (r ^ (5 : ℕ)) x)
    (hSplit : ∀ t ∈ Ioc 0 T, ∀ r ∈ Ioc 0 1, r < 1 / 4 → r ^ (5 : ℕ) ≤ t →
      K t r ≤ C * t ^ (-1 / 2 : ℝ) *
        (Real.exp (-(j ^ (2 : ℕ) * r ^ (5 : ℕ) / (2 * r) ^ (8 : ℕ))) + P r)) :
    IntegrableOn (fun t : ℝ =>
      UV.FurtherBoundaryCollar.collarReadout F K t / (2 * Real.pi * t)) (Ioc 0 T) := by
  have hC' : 0 ≤ 2 * C := by positivity
  have hk : 0 < min (j ^ (2 : ℕ) / 256) (1 / 4) := lt_min (by positivity) (by norm_num)
  apply UV.FurtherBoundaryEnvelope.logarithmic_envelope_joint_collar_trace
    hC' hk hFmeas hKmeas hF0 hF hK0
  · intro t ht r hr
    exact (hFree t ht r hr).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg ht.1.le _))
  · intro t ht r hr htip hrt
    exact (short_tip_diagonal_from_reflection hr.1 ht.1 hj hC (hReflect r hr htip)
      (hSplit t ht r hr htip hrt)).2

end UV.ResumeCollarHeat
