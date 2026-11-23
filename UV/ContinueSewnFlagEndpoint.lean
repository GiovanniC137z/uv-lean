import UV.ContinueNetworkSchwinger
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The logarithmic and negative-power displacement costs in an
individual Schwinger scale on the original positive time axis. -/

noncomputable section
open Real MeasureTheory Filter Set
open scoped ENNReal Topology
namespace UV.SewnFlags

def ratioHeat (a lam r : ℝ) := r ^ (a - 1) * exp (-lam/r)

def ratioCost (a lam : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioo (0:ℝ) 1, ENNReal.ofReal (ratioHeat a lam r)

def displacementCost (a x : ℝ) : ℝ≥0∞ :=
  if 0 < a then 1
  else if x = 0 then ⊤
  else if a = 0 then ENNReal.ofReal (1 + max 0 (log (1/x)))
  else ENNReal.ofReal (1 + x ^ (2*a))

theorem one_le_displacementCost (a : ℝ) {x : ℝ} (hx : 0 ≤ x) : 1 ≤ displacementCost a x := by
  unfold displacementCost
  split_ifs with h hx₀ ha₀
  · exact le_rfl
  · exact le_top
  · exact ENNReal.ofReal_one ▸ ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (le_max_left _ _))
  · exact ENNReal.ofReal_one ▸ ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (rpow_nonneg hx _))

private theorem ratioHeat_nonneg (a lam : ℝ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ ratioHeat a lam r :=
  mul_nonneg (rpow_nonneg hr _) (exp_pos _).le

theorem ratioHeat_at_zero_displacement (a : ℝ) :
    ratioCost a 0 = directionalEndpointMass a 1 := by
  simp [ratioCost, ratioHeat, directionalEndpointMass]

private theorem ratioHeat_comp_inv (a lam : ℝ) {r : ℝ} (hr : 0 < r) :
    (|(-1:ℝ)| * r ^ ((-1:ℝ)-1)) • ((r ^ (-1:ℝ)) ^ (-a-1) * exp (-(lam*r ^ (-1:ℝ)))) =
      ratioHeat a lam r := by
  rw [smul_eq_mul, abs_neg, abs_one, one_mul, ← mul_assoc, ← rpow_mul hr.le, ← rpow_add hr,
    rpow_neg_one, ratioHeat, div_eq_mul_inv]
  congr 2 <;> ring

/-- At a strictly negative face the Gamma integral on the full half-line
gives the exact power of the displacement scale. -/
theorem ratioHeat_negative {a lam : ℝ} (ha : a < 0) (hlam : 0 < lam) :
    IntegrableOn (ratioHeat a lam) (Ioi 0) ∧
      (∫ r in Ioi (0:ℝ), ratioHeat a lam r) = lam ^ a * Gamma (-a) := by
  let f := fun t : ℝ => t ^ (-a-1) * exp (-(lam*t))
  have hG : IntegrableOn (fun t : ℝ => exp (-t) * t ^ (-a-1)) (Ioi 0) :=
    GammaIntegral_convergent (by linarith)
  have hF₀ := (integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ => exp (-t) * t ^ (-a-1)) 0 hlam).2
    (by simpa using hG)
  have hF : IntegrableOn f (Ioi 0) := by
    refine (integrableOn_congr_fun (g := f) ?_ measurableSet_Ioi).1 (hF₀.const_mul ((lam ^ (-a-1))⁻¹))
    intro t ht
    change (lam ^ (-a-1))⁻¹ * (exp (-(lam*t))*(lam*t)^(-a-1)) = f t
    rw [mul_rpow hlam.le ht.le]
    dsimp only [f]
    field_simp [(rpow_pos_of_pos hlam (-a-1)).ne']
  have h := (integrableOn_Ioi_comp_rpow_iff f (by norm_num : (-1:ℝ) ≠ 0)).2 hF
  refine ⟨h.congr_fun (fun r hr => ratioHeat_comp_inv a lam hr) measurableSet_Ioi, ?_⟩
  calc
    _ = ∫ r in Ioi (0:ℝ), (|(-1:ℝ)| * r^((-1:ℝ)-1)) • f (r ^ (-1:ℝ)) := by
      exact setIntegral_congr_fun measurableSet_Ioi (fun r hr => (ratioHeat_comp_inv a lam hr).symm)
    _ = ∫ r in Ioi (0:ℝ), f r := integral_comp_rpow_Ioi f (by norm_num)
    _ = lam ^ a * Gamma (-a) := by
      rw [show (∫ r in Ioi (0:ℝ), f r) = _ from integral_rpow_mul_exp_neg_mul_Ioi (by linarith : 0 < -a) hlam]
      rw [one_div, inv_rpow hlam.le, ← rpow_neg hlam.le, neg_neg]

private theorem ratioHeat_log_small {lam : ℝ} (hlam : 0 < lam) (r : ℝ) :
    ratioHeat 0 lam r ≤ lam⁻¹ := by
  have h : lam/r ≤ exp (lam/r) := by
    have := add_one_le_exp (lam/r)
    linarith
  unfold ratioHeat
  rw [zero_sub, rpow_neg_one, neg_div, exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (exp_pos (lam/r))).2
  apply (le_inv_mul_iff₀' hlam).2
  simpa [div_eq_mul_inv] using h

private theorem ratioHeat_log_large {lam : ℝ} (hlam : 0 ≤ lam) {r : ℝ} (hr : 0 < r) :
    ratioHeat 0 lam r ≤ 1/r := by
  unfold ratioHeat
  rw [zero_sub, rpow_neg_one, neg_div, one_div]
  exact (mul_le_mul_of_nonneg_left (exp_le_one_iff.2 (neg_nonpos.mpr (div_nonneg hlam hr.le)))
    (inv_nonneg.2 hr.le)).trans_eq (mul_one _)

/-- The marginal face has a logarithmic upper bound with the precise
scale dependence, including finiteness for every positive displacement. -/
theorem ratioCost_log {lam : ℝ} (hlam : 0 < lam) :
    ratioCost 0 lam ≤ ENNReal.ofReal (1 + max 0 (log (1/lam))) := by
  let b := min lam 1
  have hb₀ : 0 < b := lt_min hlam zero_lt_one
  have hb₁ : b ≤ 1 := min_le_right _ _
  have hsplit : Ioo (0:ℝ) 1 ⊆ Ioo 0 b ∪ Icc b 1 := by
    intro r hr
    by_cases H : r < b
    · exact Or.inl ⟨hr.1,H⟩
    · exact Or.inr ⟨le_of_not_gt H,hr.2.le⟩
  have hn : Disjoint (Ioo (0:ℝ) b) (Icc b 1) := by
    refine Set.disjoint_left.mpr ?_
    intro t h₁ h₂
    exact (not_lt_of_ge h₂.1) h₁.2
  have hsmall : (∫⁻ r in Ioo (0:ℝ) b, ENNReal.ofReal (ratioHeat 0 lam r)) ≤ 1 := by
    calc
      _ ≤ ∫⁻ _ in Ioo (0:ℝ) b, ENNReal.ofReal lam⁻¹ :=
        lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioo).mono (fun r hr => ENNReal.ofReal_le_ofReal (ratioHeat_log_small hlam r)))
      _ = ENNReal.ofReal (lam⁻¹ * b) := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo,
          sub_zero, ENNReal.ofReal_mul (by positivity)]
      _ ≤ 1 := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal ((inv_mul_le_one₀ hlam).2 (min_le_left _ _))
  have hlarge : (∫⁻ r in Icc b 1, ENNReal.ofReal (ratioHeat 0 lam r)) ≤ ENNReal.ofReal (max 0 (log (1/lam))) := by
    calc
      _ ≤ ∫⁻ r in Icc b 1, ENNReal.ofReal (1/r) :=
        lintegral_mono_ae ((ae_restrict_mem measurableSet_Icc).mono (fun r hr => ENNReal.ofReal_le_ofReal (ratioHeat_log_large hlam.le (hb₀.trans_le hr.1))))
      _ = ENNReal.ofReal (log (1/b)) := by
        have hC : ContinuousOn (fun r : ℝ => 1/r) (Icc b 1) :=
          continuousOn_const.div continuousOn_id (fun x hx => (hb₀.trans_le hx.1).ne')
        have hI : IntegrableOn (fun r : ℝ => 1/r) (Icc b 1) := hC.integrableOn_compact isCompact_Icc
        rw [← ofReal_integral_eq_lintegral_ofReal hI
          ((ae_restrict_mem measurableSet_Icc).mono fun r hr => one_div_nonneg.mpr (hb₀.le.trans hr.1)),
          integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb₁, integral_one_div_of_pos hb₀ zero_lt_one]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rcases le_or_gt lam 1 with h | h
        · simp [b, min_eq_left h]
        · simp [b, min_eq_right h.le]
  unfold ratioCost
  apply (lintegral_mono_set hsplit).trans
  rw [lintegral_union measurableSet_Icc hn, ENNReal.ofReal_add zero_le_one (le_max_left _ _), ENNReal.ofReal_one]
  exact add_le_add hsmall hlarge

end UV.SewnFlags
