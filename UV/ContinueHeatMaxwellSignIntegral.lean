import UV.ContinueHeatMaxwellSign
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The strictly positive radial one-loop coefficient at every positive mass. -/

noncomputable section

namespace UV.HeatMaxwell

open MeasureTheory Set Filter
open scoped Topology

/-- The signed radial expression with x = (ma)². -/
def heatRadialIntegrand (x u : ℝ) : ℝ :=
  (heatRadius u / (x + heatRadius u)) ^ 2 * signPolynomial u / u

/-- The radial Maxwell coefficient of the unit-width link. -/
def heatMaxwellCoefficient (x : ℝ) : ℝ :=
  (24 * Real.pi ^ 2)⁻¹ * ∫ u in Ioi 0, heatRadialIntegrand x u

private theorem heat_exp_monomial_integrable (n : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ n * Real.exp (-4 * u)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := 4)
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by norm_num) (by norm_num)
  simpa [Real.rpow_natCast, Real.rpow_one] using h

private theorem heatRadialIntegrand_expanded (x : ℝ) {u : ℝ} (hu : 0 < u) :
    heatRadialIntegrand x u = (u * signPolynomial u * Real.exp (-4 * u)) /
      (x + heatRadius u) ^ 2 := by
  have he : Real.exp (-4 * u) = Real.exp (-2 * u) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heatRadialIntegrand, he, div_pow]
  generalize (x + heatRadius u) ^ 2 = d
  rw [heatRadius]
  field_simp [hu.ne']

theorem heatRadialIntegrand_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (heatRadialIntegrand x) (Ioi 0) := by
  have hpoly : IntegrableOn (fun u : ℝ => u * signPolynomial u * Real.exp (-4 * u))
      (Ioi 0) := by
    have h := ((((heat_exp_monomial_integrable 4).const_mul 2).sub
      ((heat_exp_monomial_integrable 3).const_mul 7)).add
      ((heat_exp_monomial_integrable 2).const_mul 2)).add
      ((heat_exp_monomial_integrable 1).const_mul 2)
    apply h.congr
    refine Eventually.of_forall fun u => ?_
    change 2 * (u ^ 4 * Real.exp (-4 * u)) - 7 * (u ^ 3 * Real.exp (-4 * u)) +
      2 * (u ^ 2 * Real.exp (-4 * u)) + 2 * (u ^ 1 * Real.exp (-4 * u)) =
        u * signPolynomial u * Real.exp (-4 * u)
    unfold signPolynomial
    ring
  have hm : Measurable (heatRadialIntegrand x) := by
    unfold heatRadialIntegrand heatRadius signPolynomial
    fun_prop
  apply (hpoly.norm.const_mul (x ^ 2)⁻¹).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with u hu
  have hy := heatRadius_pos hu
  have hs : x ^ 2 ≤ (x + heatRadius u) ^ 2 :=
    pow_le_pow_left₀ hx.le (le_add_of_nonneg_right hy.le) 2
  rw [heatRadialIntegrand_expanded _ hu, norm_div, Real.norm_of_nonneg (sq_nonneg _), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) hs) (norm_nonneg _)

private def lowerBranchIntegrand (x y : ℝ) : ℝ :=
  (y / (x + y)) ^ 2 * signPolynomial (heatLowerRadius y) / (y * (1 - 2 * heatLowerRadius y))

private def upperBranchIntegrand (x y : ℝ) : ℝ :=
  (y / (x + y)) ^ 2 * signPolynomial (heatUpperRadius y) / (y * (2 * heatUpperRadius y - 1))

private theorem heatLower_jacobian (x : ℝ) {u : ℝ} (hu : u ∈ Ioo 0 (1 / 2)) :
    (Real.exp (-2 * u) * (1 - 2 * u)) * lowerBranchIntegrand x (heatRadius u) =
      heatRadialIntegrand x u := by
  have hsign : 0 < 1 - 2 * u := by linarith [hu.2]
  have hpos : 0 < u := hu.1
  unfold lowerBranchIntegrand heatRadialIntegrand
  rw [heatLowerRadius_heatRadius hu]
  generalize ((heatRadius u / (x + heatRadius u)) ^ 2) = z
  rw [heatRadius]
  field_simp [hsign.ne', hpos.ne', (Real.exp_pos _).ne']

private theorem heatUpper_jacobian (x : ℝ) {u : ℝ} (hu : u ∈ Ioi (1 / 2)) :
    -(Real.exp (-2 * u) * (1 - 2 * u)) * upperBranchIntegrand x (heatRadius u) =
      heatRadialIntegrand x u := by
  have hsign : 0 < 2 * u - 1 := by linarith [show (1 : ℝ) / 2 < u from hu]
  have hpos : 0 < u := (by norm_num : (0 : ℝ) < 1 / 2).trans hu
  unfold upperBranchIntegrand heatRadialIntegrand
  rw [heatUpperRadius_heatRadius hu]
  generalize ((heatRadius u / (x + heatRadius u)) ^ 2) = z
  rw [heatRadius]
  field_simp [hsign.ne', hpos.ne', (Real.exp_pos _).ne']
  ring

private theorem heatLower_change (x : ℝ) :
    (∫ u in Ioo 0 (1 / 2), heatRadialIntegrand x u) =
      ∫ y in Ioo 0 heatPeak, lowerBranchIntegrand x y := by
  rw [← heatRadius_lower_image,
    integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Ioo
      (fun u _ => (heatRadius_hasDerivAt u).hasDerivWithinAt)
      (heatRadius_increasing.monotoneOn.mono Ioo_subset_Icc_self)]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  exact (heatLower_jacobian x hu).symm

private theorem heatUpper_change (x : ℝ) :
    (∫ u in Ioi (1 / 2), heatRadialIntegrand x u) =
      ∫ y in Ioo 0 heatPeak, upperBranchIntegrand x y := by
  rw [← heatRadius_upper_image,
    integral_image_eq_integral_deriv_smul_of_antitone measurableSet_Ioi
      (fun u _ => (heatRadius_hasDerivAt u).hasDerivWithinAt)
      (heatRadius_decreasing.antitoneOn.mono Ioi_subset_Ici_self)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  exact (heatUpper_jacobian x hu).symm

private theorem lowerBranch_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (lowerBranchIntegrand x) (Ioo 0 heatPeak) := by
  rw [← heatRadius_lower_image,
    integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn measurableSet_Ioo
      (fun u _ => (heatRadius_hasDerivAt u).hasDerivWithinAt)
      (heatRadius_increasing.monotoneOn.mono Ioo_subset_Icc_self)]
  apply ((heatRadialIntegrand_integrable hx).mono_set Ioo_subset_Ioi_self).congr_fun
    _ measurableSet_Ioo
  intro u hu
  exact (heatLower_jacobian x hu).symm

private theorem upperBranch_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (upperBranchIntegrand x) (Ioo 0 heatPeak) := by
  rw [← heatRadius_upper_image,
    integrableOn_image_iff_integrableOn_deriv_smul_of_antitoneOn measurableSet_Ioi
      (fun u _ => (heatRadius_hasDerivAt u).hasDerivWithinAt)
      (heatRadius_decreasing.antitoneOn.mono Ioi_subset_Ici_self)]
  apply ((heatRadialIntegrand_integrable hx).mono_set
    (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1 / 2))).congr_fun _ measurableSet_Ioi
  intro u hu
  exact (heatUpper_jacobian x hu).symm

/-- The exact positive density, with the four-dimensional coefficient included. -/
def heatMaxwellDensity (y : ℝ) : ℝ := (24 * Real.pi ^ 2)⁻¹ * (y * heatBranchFactor y)

theorem heatMaxwellDensity_pos {y : ℝ} (hy : y ∈ Ioo 0 heatPeak) :
    0 < heatMaxwellDensity y := by
  have hB := heatBranchFactor_pos hy
  have hY : 0 < y := hy.1
  unfold heatMaxwellDensity
  positivity

private theorem heatBranch_sum {x y : ℝ} (hx : 0 < x) (hy : y ∈ Ioo 0 heatPeak) :
    (24 * Real.pi ^ 2)⁻¹ * (lowerBranchIntegrand x y + upperBranchIntegrand x y) =
      heatMaxwellDensity y / (x + y) ^ 2 := by
  obtain ⟨hl, _⟩ := heatLowerRadius_spec hy
  obtain ⟨hb, _⟩ := heatUpperRadius_spec hy
  have hl' : 0 < 1 - 2 * heatLowerRadius y := by linarith [hl.2]
  have hb' : 0 < 2 * heatUpperRadius y - 1 := by
    linarith [show (1 : ℝ) / 2 < heatUpperRadius y from hb]
  have hy' : 0 < y := hy.1
  unfold heatMaxwellDensity heatBranchFactor lowerBranchIntegrand upperBranchIntegrand
  field_simp [hy'.ne', hl'.ne', hb'.ne']

theorem heatMaxwellDensity_kernel_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun y => heatMaxwellDensity y / (x + y) ^ 2) (Ioo 0 heatPeak) :=
  (((lowerBranch_integrable hx).add (upperBranch_integrable hx)).const_mul
    ((24 * Real.pi ^ 2)⁻¹)).congr
      ((ae_restrict_mem measurableSet_Ioo).mono fun _ hy => heatBranch_sum hx hy)

/-- Exact two-branch change of variables for the radial coefficient. -/
theorem heatMaxwellCoefficient_positive_density {x : ℝ} (hx : 0 < x) :
    heatMaxwellCoefficient x = ∫ y in Ioo 0 heatPeak, heatMaxwellDensity y / (x + y) ^ 2 := by
  have hs : Ioo (0 : ℝ) (1 / 2) ∪ Ici (1 / 2) = Ioi 0 := by
    ext u
    simp only [mem_union, mem_Ioo, mem_Ici, mem_Ioi]
    constructor
    · rintro (⟨hu, _⟩ | hu)
      · exact hu
      · linarith
    · intro hu
      rcases lt_or_ge u (1 / 2) with h | h
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr h
  have hd : Disjoint (Ioo (0 : ℝ) (1 / 2)) (Ici (1 / 2)) :=
    Set.disjoint_left.mpr fun _ hu hv => not_le_of_gt hu.2 hv
  have hi := heatRadialIntegrand_integrable hx
  have hleft : IntegrableOn (heatRadialIntegrand x) (Ioo 0 (1 / 2)) :=
    hi.mono_set Ioo_subset_Ioi_self
  have hright := hi.mono_set (show Ici (1 / 2 : ℝ) ⊆ Ioi 0 from fun _ h =>
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le h)
  unfold heatMaxwellCoefficient
  rw [← hs, setIntegral_union hd measurableSet_Ici hleft hright, integral_Ici_eq_integral_Ioi,
    heatLower_change, heatUpper_change, ← integral_add (lowerBranch_integrable hx) (upperBranch_integrable hx),
    ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioo (fun _ hy => heatBranch_sum hx hy)

theorem heatPeak_integral_pos {f : ℝ → ℝ} (hi : IntegrableOn f (Ioo 0 heatPeak))
    (hp : ∀ y ∈ Ioo 0 heatPeak, 0 < f y) : 0 < ∫ y in Ioo 0 heatPeak, f y := by
  let s := Ioo (0 : ℝ) heatPeak
  let μ := (volume : Measure ℝ).restrict s
  have ha : 0 ≤ᵐ[μ] f := (ae_restrict_mem measurableSet_Ioo).mono fun y hy => (hp y hy).le
  refine (integral_pos_iff_support_of_nonneg_ae ha hi).2 ?_
  have hsupp : s ⊆ Function.support f := fun y hy => (hp y hy).ne'
  exact lt_of_lt_of_le
    (by rw [Measure.restrict_apply measurableSet_Ioo, Set.inter_self]; exact
      (Measure.measure_Ioo_pos (volume : Measure ℝ)).2 heatPeak_pos)
    (measure_mono hsupp)

/-- The radial Maxwell coefficient is strictly positive for every positive
squared dimensionless mass. -/
theorem heatMaxwellCoefficient_pos {x : ℝ} (hx : 0 < x) :
    0 < heatMaxwellCoefficient x := by
  rw [heatMaxwellCoefficient_positive_density hx]
  apply heatPeak_integral_pos (heatMaxwellDensity_kernel_integrable hx)
  intro y hy
  exact div_pos (heatMaxwellDensity_pos hy) (sq_pos_of_pos (add_pos hx hy.1))

/-- The positive density makes the Maxwell coefficient strictly decrease
with the positive squared dimensionless mass. -/
theorem heatMaxwellCoefficient_strictAntiOn :
    StrictAntiOn heatMaxwellCoefficient (Ioi 0) := by
  intro x hx x' hx' h
  rw [heatMaxwellCoefficient_positive_density hx, heatMaxwellCoefficient_positive_density hx']
  apply sub_pos.mp
  rw [← integral_sub (heatMaxwellDensity_kernel_integrable hx) (heatMaxwellDensity_kernel_integrable hx')]
  apply heatPeak_integral_pos ((heatMaxwellDensity_kernel_integrable hx).sub
    (heatMaxwellDensity_kernel_integrable hx'))
  intro y hy
  apply sub_pos.mpr
  exact div_lt_div_of_pos_left (heatMaxwellDensity_pos hy) (sq_pos_of_pos (add_pos hx hy.1))
    (pow_lt_pow_left₀ (add_lt_add_right h y) (add_pos hx hy.1).le (by decide))

theorem heatMaxwellCoefficient_mass_width_pos {m a : ℝ} (hm : 0 < m) (ha : 0 < a) :
    0 < heatMaxwellCoefficient ((m * a) ^ 2) :=
  heatMaxwellCoefficient_pos (sq_pos_of_pos (mul_pos hm ha))

end UV.HeatMaxwell
