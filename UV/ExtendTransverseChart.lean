import UV.NextShellResponse
import UV.NextShellMultiplier
import Mathlib.MeasureTheory.Integral.Prod

/-! Fubini and test regularity in a regular shell chart. The invariant
coordinate is D and the transverse slot is Spatial. The chart Jacobian
and any fixed test density are included in the tested function. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Transverse integration on a compact shell chart, with its finite
transverse measure. -/
def transverseTest (ν : Measure Spatial) (f : ℝ × Spatial → V) (D : ℝ) : V :=
  ∫ p, f (D, p) ∂ν

theorem transverse_test_norm_le (ν : Measure Spatial) [IsFiniteMeasure ν]
    {f : ℝ × Spatial → V} {D A : ℝ} (hA : ∀ p, ‖f (D, p)‖ ≤ A) :
    ‖transverseTest ν f D‖ ≤ ν.real univ * A := by
  simpa only [transverseTest, mul_comm] using
    (norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall hA))

theorem transverse_test_support (ν : Measure Spatial)
    {f : ℝ × Spatial → V} {r : ℝ} (hs : ∀ D p, r < |D| → f (D, p) = 0) :
    HasCompactSupport (transverseTest ν f) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -r) (b := r))
  intro D hD
  refine abs_le.mp (le_of_not_gt fun ht => hD ?_)
  simp only [transverseTest, hs D _ ht, integral_zero]

omit [NormedSpace ℝ V] in
theorem exists_normal_support_bound {f : ℝ × Spatial → V} (hs : HasCompactSupport f) :
    ∃ r > 0, ∀ D p, r < |D| → f (D, p) = 0 := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn continuous_fst.continuousOn
  refine ⟨max 1 C, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro D p hr
  by_contra h
  have hb := hC (D, p) (subset_tsupport f h)
  exact (not_le_of_gt hr) (hb.trans (le_max_right _ _))

theorem transverse_test_lipschitz [CompleteSpace V] (ν : Measure Spatial) [IsFiniteMeasure ν]
    {f : ℝ × Spatial → V} (hf : Continuous f) {A : ℝ}
    (hA : ∀ x, ‖f x‖ ≤ A) {L : ℝ≥0}
    (hL : ∀ p, LipschitzWith L (fun D => f (D, p))) :
    LipschitzWith (⟨ν.real univ, measureReal_nonneg⟩ * L) (transverseTest ν f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hi (D : ℝ) : Integrable (fun p => f (D, p)) ν :=
    Integrable.of_bound (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      A (Eventually.of_forall fun p => hA (D, p))
  rw [dist_eq_norm, dist_eq_norm, transverseTest, transverseTest, ← integral_sub (hi x) (hi y)]
  simpa only [NNReal.coe_mul, NNReal.coe_mk, mul_assoc, mul_comm, mul_left_comm] using
    (norm_integral_le_of_norm_le_const (μ := ν) (f := fun p => f (x, p) - f (y, p))
      (Eventually.of_forall fun p => (hL p).norm_sub_le x y))

/-- Differentiation of the averaged normal-coordinate test. The
domination is supplied by the compact transverse chart. -/
theorem transverse_test_hasDerivAt (ν : Measure Spatial) [IsFiniteMeasure ν]
    {f f' : ℝ × Spatial → V} (hf : Continuous f) (hf' : Continuous f')
    {A B : ℝ} (hA : ∀ x, ‖f x‖ ≤ A) (hB : ∀ x, ‖f' x‖ ≤ B)
    (hd : ∀ D p, HasDerivAt (fun x => f (x, p)) (f' (D, p)) D) (D : ℝ) :
    HasDerivAt (transverseTest ν f) (transverseTest ν f' D) D := by
  have hfc (x : ℝ) : Continuous (fun p => f (x, p)) :=
    hf.comp (continuous_const.prodMk continuous_id)
  have hf'D : Continuous (fun p => f' (D, p)) :=
    hf'.comp (continuous_const.prodMk continuous_id)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (x₀ := D) (ε := 1) zero_lt_one
    (Eventually.of_forall fun x => (hfc x).aestronglyMeasurable)
    (Integrable.of_bound (hfc D).aestronglyMeasurable A
      (Eventually.of_forall fun p => hA (D, p)))
    hf'D.aestronglyMeasurable
    (Eventually.of_forall fun p x _ => hB (x, p)) (integrable_const B)
    (Eventually.of_forall fun p x _ => hd x p)).2

/-- Integrability before Fubini for any continuous normal multiplier at
fixed positive height. Compact support is needed only in the normal
coordinate because the transverse chart measure is finite. -/
theorem chart_integrable_smul (ν : Measure Spatial) [IsFiniteMeasure ν]
    {f : ℝ × Spatial → V} (hf : Continuous f) {A r : ℝ}
    (hA : ∀ x, ‖f x‖ ≤ A) (hs : ∀ D p, r < |D| → f (D, p) = 0)
    {k : ℝ → ℝ} (hk : Continuous k) :
    Integrable (fun x : ℝ × Spatial => k x.1 • f x) (volume.prod ν) := by
  let box := Icc (-r) r
  have hi : Integrable (box.indicator (fun D : ℝ => |k D| * A)) volume :=
    ((hk.abs.mul continuous_const).continuousOn.integrableOn_compact
      (μ := volume) (isCompact_Icc (a := -r) (b := r))).integrable_indicator measurableSet_Icc
  refine (hi.comp_fst ν).mono' ((hk.comp continuous_fst).smul hf).aestronglyMeasurable ?_
  refine Eventually.of_forall fun x => ?_
  change ‖k x.1 • f x‖ ≤ box.indicator (fun D => |k D| * A) x.1
  by_cases hx : x.1 ∈ box
  · rw [indicator_of_mem hx, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hA x) (abs_nonneg _)
  · have hfar : r < |x.1| := lt_of_not_ge (fun h => hx (abs_le.mp h))
    simp [indicator_of_notMem hx, hs _ _ hfar]

theorem chart_integral_smul [CompleteSpace V] (ν : Measure Spatial) [IsFiniteMeasure ν]
    {f : ℝ × Spatial → V} (hf : Continuous f) {A r : ℝ}
    (hA : ∀ x, ‖f x‖ ≤ A) (hs : ∀ D p, r < |D| → f (D, p) = 0)
    {k : ℝ → ℝ} (hk : Continuous k) :
    (∫ x : ℝ × Spatial, k x.1 • f x ∂(volume.prod ν)) =
      ∫ D : ℝ, k D • transverseTest ν f D := by
  rw [integral_prod _ (chart_integrable_smul ν hf hA hs hk)]
  simp_rw [integral_smul, transverseTest]

theorem chart_integrable_mul (ν : Measure Spatial) [IsFiniteMeasure ν]
    {f : ℝ × Spatial → ℂ} (hf : Continuous f) {A r : ℝ}
    (hA : ∀ x, ‖f x‖ ≤ A) (hs : ∀ D p, r < |D| → f (D, p) = 0)
    {k : ℝ → ℂ} (hk : Continuous k) :
    Integrable (fun x : ℝ × Spatial => k x.1 * f x) (volume.prod ν) := by
  let box := Icc (-r) r
  have hi : Integrable (box.indicator (fun D : ℝ => ‖k D‖ * A)) volume :=
    ((hk.norm.mul continuous_const).continuousOn.integrableOn_compact
      (μ := volume) (isCompact_Icc (a := -r) (b := r))).integrable_indicator measurableSet_Icc
  refine (hi.comp_fst ν).mono' ((hk.comp continuous_fst).mul hf).aestronglyMeasurable ?_
  refine Eventually.of_forall fun x => ?_
  change ‖k x.1 * f x‖ ≤ box.indicator (fun D => ‖k D‖ * A) x.1
  by_cases hx : x.1 ∈ box
  · rw [indicator_of_mem hx, norm_mul]
    exact mul_le_mul_of_nonneg_left (hA x) (norm_nonneg _)
  · have hfar : r < |x.1| := lt_of_not_ge (fun h => hx (abs_le.mp h))
    simp [indicator_of_notMem hx, hs _ _ hfar]

theorem chart_integral_mul (ν : Measure Spatial) [IsFiniteMeasure ν]
    {f : ℝ × Spatial → ℂ} (hf : Continuous f) {A r : ℝ}
    (hA : ∀ x, ‖f x‖ ≤ A) (hs : ∀ D p, r < |D| → f (D, p) = 0)
    {k : ℝ → ℂ} (hk : Continuous k) :
    (∫ x : ℝ × Spatial, k x.1 * f x ∂(volume.prod ν)) =
      ∫ D : ℝ, k D * transverseTest ν f D := by
  rw [integral_prod _ (chart_integrable_mul ν hf hA hs hk)]
  simp_rw [integral_const_mul, transverseTest]

end UV.SectorPlane
