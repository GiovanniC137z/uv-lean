import UV.ContinueRestThresholdReadout
import UV.ContinueRestThresholdCauchy

/-! The near factors of the degenerate threshold retain the actual
vectorial pole sides when tested in the real axial slot. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology NNReal UV.SectorPlane

variable {E : Type*} [NormedAddCommGroup E]

/-- Reversal of the evolution label on a fixed sector. -/
def restThresholdReverse : Evolution → Evolution
  | .ascending => .descending
  | .descending => .ascending

theorem Plane.rest_threshold_reverse_eta (diamond : Plane E) (ε : Evolution) :
    diamond.eta (restThresholdReverse ε) = -diamond.eta ε := by
  cases ε <;> simp [restThresholdReverse, Plane.eta, evolutionSign]

def Plane.restThresholdAxialHeight (diamond : Plane E) (ε : Evolution) (h : Height)
    {m : ℝ} (hm : 0 < m) (r : ℝ) : Height :=
  ⟨(h : ℝ) / (2 * (diamond.restThresholdRoot ε h m r).re),
    div_pos h.property (mul_pos two_pos (diamond.rest_threshold_root_re_pos ε h hm r))⟩

theorem Plane.rest_threshold_axial_height_le (diamond : Plane E) (ε : Evolution)
    (h : Height) {m : ℝ} (hm : 0 < m) (r : ℝ) :
    (diamond.restThresholdAxialHeight ε h hm r : ℝ) ≤ (h : ℝ) / (2 * m) := by
  apply div_le_div_of_nonneg_left h.property.le (mul_pos two_pos hm)
  gcongr
  exact (rest_threshold_mass_le_radius_root hm r).trans (diamond.rest_threshold_root_re_lower ε h m r)

theorem Plane.rest_threshold_axial_height_small (diamond : Plane E) (ε : Evolution)
    {m : ℝ} (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ h : Height in poleBoundaryHeights, ∀ r, (diamond.restThresholdAxialHeight ε h hm r : ℝ) < δ := by
  have ht := pole_height_tendsto_zero (eventually_lt_nhds (mul_pos (mul_pos two_pos hm) hδ))
  filter_upwards [ht] with h hh r
  apply (diamond.rest_threshold_axial_height_le ε h hm r).trans_lt
  exact (div_lt_iff₀ (mul_pos two_pos hm)).mpr (by simpa [mul_comm] using hh)

theorem Plane.rest_threshold_axial_height_tendsto (diamond : Plane E) (ε : Evolution)
    {m : ℝ} (hm : 0 < m) (r : ℝ) :
    Tendsto (fun h => diamond.restThresholdAxialHeight ε h hm r)
      poleBoundaryHeights poleBoundaryHeights := by
  apply tendsto_comap_iff.mpr
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall fun h => (diamond.restThresholdAxialHeight ε h hm r).property⟩
  have hhi : Tendsto (fun h : Height => (h : ℝ) / (2 * m)) poleBoundaryHeights (𝓝 0) := by
    simpa only [zero_div] using pole_height_tendsto_zero.div_const (2 * m)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hhi
    (Eventually.of_forall fun h => (diamond.restThresholdAxialHeight ε h hm r).property.le)
    (Eventually.of_forall fun h => diamond.rest_threshold_axial_height_le ε h hm r)

theorem Plane.rest_threshold_axial_height_eventually (diamond : Plane E) (ε : Evolution)
    {m : ℝ} (hm : 0 < m) {P : Height → Prop} (hP : ∀ᶠ k : Height in poleBoundaryHeights, P k) :
    ∀ᶠ h : Height in poleBoundaryHeights, ∀ r, P (diamond.restThresholdAxialHeight ε h hm r) := by
  have hP' : {k : Height | P k} ∈ poleBoundaryHeights := hP
  obtain ⟨s, hs, hsub⟩ := Filter.mem_comap.mp hP'
  have hs' : s ∈ 𝓝[Set.Ioi (0 : ℝ)] 0 := hs
  obtain ⟨δ, hδ, hI⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hs'
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hδ
  filter_upwards [diamond.rest_threshold_axial_height_small ε hm hd] with h hh r
  let k := diamond.restThresholdAxialHeight ε h hm r
  apply hsub
  change (k : ℝ) ∈ s
  apply hI
  refine ⟨hball ?_, k.property⟩
  simpa [Metric.mem_ball, Real.dist_eq, abs_of_nonneg k.property.le] using hh r

theorem Plane.rest_threshold_near_plus_cauchy (diamond : Plane E) (ε : Evolution)
    (h : Height) {m : ℝ} (hm : 0 < m) (x r : ℝ) :
    ((x : ℂ) - diamond.restThresholdNearPlus ε h m r)⁻¹ =
      diamond.poleCoefficient ε (diamond.restThresholdAxialHeight ε h hm r)
        (x - (diamond.restThresholdNearPlus ε h m r).re) := by
  rw [diamond.pole_coefficient_eq_inv, Plane.shiftedShellCoefficient]
  congr 1
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  · simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add,
      zero_sub, Plane.restThresholdNearPlus, sub_zero, Plane.restThresholdAxialHeight]
    rw [diamond.rest_threshold_root_im ε h hm r, neg_div, neg_neg, mul_div_assoc]

theorem Plane.rest_threshold_near_minus_cauchy (diamond : Plane E) (ε : Evolution)
    (h : Height) {m : ℝ} (hm : 0 < m) (x r : ℝ) :
    ((x : ℂ) - diamond.restThresholdNearMinus ε h m r)⁻¹ =
      diamond.poleCoefficient (restThresholdReverse ε) (diamond.restThresholdAxialHeight ε h hm r)
        (x - (diamond.restThresholdNearMinus ε h m r).re) := by
  rw [diamond.pole_coefficient_eq_inv, Plane.shiftedShellCoefficient]
  congr 1
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  · simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add,
      zero_sub, Plane.restThresholdNearMinus, Plane.restThresholdAxialHeight, neg_neg]
    rw [diamond.rest_threshold_root_im ε h hm r, diamond.rest_threshold_reverse_eta,
      neg_mul, neg_div, mul_div_assoc]

theorem rest_threshold_integral_shift_center (P F : ℝ → ℂ) (a : ℝ) :
    (∫ x, P (x - a) * F x) = ∫ x, P x * F (x + a) := by
  rw [← integral_add_right_eq_self (fun x => P (x - a) * F x) a]
  simp only [add_sub_cancel_right]

end UV.SectorPlane
