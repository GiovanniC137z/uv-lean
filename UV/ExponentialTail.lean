import UV.DepthAsymptotics
import UV.SelectedTail

noncomputable section
open MeasureTheory Set Real

namespace UV

/-- The standard real upper incomplete Gamma integral in its admitted domain. -/
def upperIncompleteGamma (s x : ℝ) : ℝ :=
  ∫ t in Ioi x, t ^ (s - 1) * Real.exp (-t)

def oneLineTail (d a M m R : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-4 : ℤ) *
    ∫ q : ScalarMomentum in {q | R < ‖q‖}, oneLineIntegrand d a M m q

theorem upperIncompleteGamma_exponential_bound {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    upperIncompleteGamma s x ≤ Real.exp (-(x / 2)) * (2 ^ s * Real.Gamma s) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ (s - 1) * Real.exp (-t)) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_one_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1) (b := 1)
        (by linarith) (by norm_num) (by norm_num))
  have hh : IntegrableOn (fun t : ℝ => t ^ (s - 1) * Real.exp (-((1 / 2 : ℝ) * t)))
      (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1) (b := 1 / 2)
        (by linarith) (by norm_num) (by norm_num))
  let g (t : ℝ) := Real.exp (-(x / 2)) *
    (t ^ (s - 1) * Real.exp (-((1 / 2 : ℝ) * t)))
  have hg : IntegrableOn g (Ioi 0) := hh.const_mul _
  have hsub : Ioi x ⊆ Ioi (0 : ℝ) := fun _ h => hx.trans_lt h
  unfold upperIncompleteGamma
  calc
    _ ≤ ∫ t in Ioi x, g t := by
      apply setIntegral_mono_on (hi.mono_set hsub) (hg.mono_set hsub) measurableSet_Ioi
      intro t ht
      dsimp [g]
      rw [mul_left_comm]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (hx.trans ht.le) _)
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hxt : x < t := ht
      linarith
    _ ≤ ∫ t in Ioi 0, g t := by
      apply setIntegral_mono_set hg _ (Filter.Eventually.of_forall hsub)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      dsimp [g]
      exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg
        (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
    _ = _ := by
      dsimp [g]
      rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hs (by norm_num)]
      norm_num

theorem oneLineTail_radial (d a M m : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    oneLineTail d a M m R = (8 * Real.pi ^ 2)⁻¹ *
      ∫ r in Ioi R, oneLineRadial d a M m r := by
  have htail : MeasurableSet {q : ScalarMomentum | R < ‖q‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  let f (r : ℝ) := if R < r then r ^ d * kernel a M (r ^ 2) / (r ^ 2 + m ^ 2) else 0
  have he : (fun q : ScalarMomentum =>
      {q : ScalarMomentum | R < ‖q‖}.indicator (oneLineIntegrand d a M m) q) =
      (fun q : ScalarMomentum => f ‖q‖) := by
    funext q
    simp [f, oneLineIntegrand, Set.indicator_apply, mul_div_assoc]
  unfold oneLineTail
  rw [← integral_indicator htail, he, integral_fun_norm_addHaar (E := ScalarMomentum) volume f]
  have hrad : (∫ r in Ioi 0, r ^ (Module.finrank ℝ ScalarMomentum - 1) • f r) =
      ∫ r in Ioi R, oneLineRadial d a M m r := by
    have hi : (∫ r in Ioi 0, r ^ (Module.finrank ℝ ScalarMomentum - 1) • f r) =
        ∫ r in Ioi 0, (Ioi R).indicator (oneLineRadial d a M m) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp [f]
      by_cases h : R < r
      · rw [Set.indicator_of_mem (show r ∈ Ioi R from h)]
        simp only [h, if_pos]
        simpa only [smul_eq_mul] using oneLine_radial_density d a M m hr
      · simp [h]
    rw [hi, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
    have hI : Ioi R ∩ Ioi (0 : ℝ) = Ioi R :=
      Set.inter_eq_left.mpr (fun _ h => hR.trans_lt h)
    rw [hI]
  rw [hrad, fourDimensional_unitBall_volume]
  simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
  rw [zpow_neg, zpow_ofNat]
  field_simp
  ring

theorem radial_exponential_tail_gamma {d a : ℝ} (ha : 0 < a) {R : ℝ} (hR : 0 ≤ R) :
    (∫ r in Ioi R, r ^ (d + 1) * Real.exp (-(a * r))) =
      a ^ (-(d + 2)) * upperIncompleteGamma (d + 2) (a * R) := by
  have hc := integral_comp_mul_left_Ioi
    (fun t : ℝ => t ^ (d + 1) * Real.exp (-t)) R ha
  have he : (∫ r in Ioi R, (a * r) ^ (d + 1) * Real.exp (-(a * r))) =
      a ^ (d + 1) * ∫ r in Ioi R, r ^ (d + 1) * Real.exp (-(a * r)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [Real.mul_rpow ha.le (hR.trans hr.le)]
    ring
  change (∫ r in Ioi R, (a * r) ^ (d + 1) * Real.exp (-(a * r))) = _ at hc
  rw [he] at hc
  unfold upperIncompleteGamma
  simp only [smul_eq_mul] at hc
  have hs : d + 2 - 1 = d + 1 := by ring
  rw [hs]
  have hp : a ^ (d + 1) * a ^ (-(d + 2)) = a⁻¹ := by
    rw [← Real.rpow_add ha]
    convert Real.rpow_neg_one a using 1
    ring
  apply mul_left_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos ha (d + 1)))
  rw [hc, ← mul_assoc, hp]

/-- Source exponential tail with its exact Fourier and incomplete-Gamma
constant. Mass zero is admitted because the omitted region avoids the origin. -/
theorem oqed_exponential_line_tail {d a M m R : ℝ}
    (hd : 0 ≤ d) (ha : 0 < a) (hR : 0 < R) :
    oneLineTail d a M m R ≤ Real.exp (a * M) /
      (8 * Real.pi ^ 2 * a ^ (d + 2)) * upperIncompleteGamma (d + 2) (a * R) := by
  have he := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := 1) (s := d + 1) (b := a) (by linarith) (by norm_num) ha
  simp only [Real.rpow_one, neg_mul] at he
  have hsub : Ioi R ⊆ Ioi (0 : ℝ) := fun _ h => hR.trans h
  have he' : IntegrableOn (fun r : ℝ => Real.exp (a * M) *
      (r ^ (d + 1) * Real.exp (-(a * r)))) (Ioi 0) := he.const_mul _
  have hi := oneLineRadial_integrable hd ha M m
  rw [oneLineTail_radial d a M m hR.le]
  calc
    _ ≤ (8 * Real.pi ^ 2)⁻¹ * ∫ r in Ioi R,
        Real.exp (a * M) * (r ^ (d + 1) * Real.exp (-(a * r))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply setIntegral_mono_on (hi.mono_set hsub) (he'.mono_set hsub) measurableSet_Ioi
      intro r hr
      simpa only [neg_mul] using oneLineRadial_bound ha.le d M m (hR.trans hr)
    _ = _ := by
      rw [integral_const_mul, radial_exponential_tail_gamma ha hR.le]
      rw [Real.rpow_neg ha.le]
      field_simp

end UV
