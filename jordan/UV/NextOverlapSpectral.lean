import UV.NextOverlapPVM
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-! Construction of the weak integral of a bounded multiplier against the
actual displacement PVM. The only approximations here are bounded simple
functions of the displacement variable. -/

noncomputable section

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal InnerProductSpace BigOperators

namespace UV.ContinuationBoundary

variable {E H : Type*} [MeasurableSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def overlapIntegral (ν : ComplexMeasure E) (f : E → ℂ) : ℂ :=
  (∫ x, f x ∂ν.re.toJordanDecomposition.posPart) -
  (∫ x, f x ∂ν.re.toJordanDecomposition.negPart) +
  Complex.I * ((∫ x, f x ∂ν.im.toJordanDecomposition.posPart) -
  (∫ x, f x ∂ν.im.toJordanDecomposition.negPart))

private theorem complex_measure_jordan_apply (ν : ComplexMeasure E)
    {s : Set E} (hs : MeasurableSet s) :
    ν s = ((ν.re.toJordanDecomposition.posPart.real s -
      ν.re.toJordanDecomposition.negPart.real s : ℝ) : ℂ) +
      Complex.I * ((ν.im.toJordanDecomposition.posPart.real s -
      ν.im.toJordanDecomposition.negPart.real s : ℝ) : ℂ) := by
  have hre : (ν s).re = ν.re.toJordanDecomposition.posPart.real s -
      ν.re.toJordanDecomposition.negPart.real s := by
    change ν.re s = _
    conv_lhs => rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition ν.re]
    exact Measure.toSignedMeasure_sub_apply hs
  have him : (ν s).im = ν.im.toJordanDecomposition.posPart.real s -
      ν.im.toJordanDecomposition.negPart.real s := by
    change ν.im s = _
    conv_lhs => rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition ν.im]
    exact Measure.toSignedMeasure_sub_apply hs
  apply Complex.ext <;> simp [hre, him, Complex.mul_re, Complex.mul_im]

private theorem bounded_integrable {f : E → ℂ} (hf : Measurable f)
    {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) (μ : Measure E) [IsFiniteMeasure μ] :
    Integrable f μ :=
  (integrable_const C).mono' hf.aestronglyMeasurable (Eventually.of_forall hb)

private theorem simple_integrable (g : SimpleFunc E ℂ) (μ : Measure E) [IsFiniteMeasure μ] :
    Integrable g μ := by
  obtain ⟨C, hC⟩ := (g.map norm).exists_forall_le
  exact bounded_integrable g.measurable hC μ

theorem overlap_integral_simple (ν : ComplexMeasure E) (g : SimpleFunc E ℂ) :
    overlapIntegral ν g = ∑ z ∈ g.range, z * ν (g ⁻¹' {z}) := by
  classical
  unfold overlapIntegral
  simp_rw [SimpleFunc.integral_eq_sum _ (simple_integrable _ _)]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  rw [complex_measure_jordan_apply ν (g.measurable (measurableSet_singleton _))]
  push_cast
  simp only [Complex.real_smul]
  ring

def simpleDisplacementIntegral (P : DisplacementPVM E H)
    (g : SimpleFunc E ℂ) : H →L[ℂ] H := by
  classical
  exact ∑ z ∈ g.range, z • P.projection (g ⁻¹' {z})

theorem simple_displacement_integral_readout (P : DisplacementPVM E H)
    (g : SimpleFunc E ℂ) (y x : H) :
    ⟪y, simpleDisplacementIntegral P g x⟫_ℂ = overlapIntegral (overlapMeasure P y x) g := by
  classical
  rw [overlap_integral_simple]
  simp only [simpleDisplacementIntegral, sum_apply, inner_sum,
    smul_apply, inner_smul_right]
  apply Finset.sum_congr rfl
  intro z _
  rw [overlapMeasure_apply P y x (g.measurable (measurableSet_singleton _))]

private theorem overlap_integral_simple_bound (P : DisplacementPVM E H)
    (g : SimpleFunc E ℂ) (y x : H) {C : ℝ} (hC : 0 ≤ C) (hg : ∀ u, ‖g u‖ ≤ C) :
    ‖overlapIntegral (overlapMeasure P y x) g‖ ≤ C * (‖y‖ * ‖x‖) := by
  classical
  rw [overlap_integral_simple]
  have hn (z : ℂ) (hz : z ∈ g.range) : ‖z‖ ≤ C := by
    obtain ⟨u, rfl⟩ := SimpleFunc.mem_range.mp hz
    exact hg u
  have hd : ∀ i ∈ g.range, ∀ j ∈ g.range, i ≠ j →
      Disjoint (g ⁻¹' {i}) (g ⁻¹' {j}) := by
    intro i _ j _ hij
    exact disjoint_singleton.mpr hij |>.preimage g
  refine (norm_sum_le _ _).trans ?_
  simp_rw [norm_mul]
  calc
    ∑ z ∈ g.range, ‖z‖ * ‖overlapMeasure P y x (g ⁻¹' {z})‖
        ≤ ∑ z ∈ g.range, C * ‖overlapMeasure P y x (g ⁻¹' {z})‖ :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hn i hi) (norm_nonneg _)
    _ ≤ C * (‖y‖ * ‖x‖) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (overlap_variation_bound P g.range (fun z => g ⁻¹' {z})
          (fun z _ => g.measurable (measurableSet_singleton z)) hd x y) hC

private def displacementApprox (f : E → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (n : ℕ) : SimpleFunc E ℂ :=
  SimpleFunc.approxOn f hf (Metric.closedBall 0 C) 0 (Metric.mem_closedBall_self hC) n

private theorem displacementApprox_bound (f : E → ℂ) (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (n : ℕ) (x : E) : ‖displacementApprox f hf C hC n x‖ ≤ C := by
  have hm := SimpleFunc.approxOn_mem hf (Metric.mem_closedBall_self (x := (0 : ℂ)) hC) n x
  simpa only [displacementApprox, Metric.mem_closedBall, dist_zero_right] using hm

private theorem displacementApprox_tendsto_integral (f : E → ℂ) (hf : Measurable f) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C) (μ : Measure E) [IsFiniteMeasure μ] :
    Tendsto (fun n => ∫ x, displacementApprox f hf C hC n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hi := bounded_integrable hf hb μ
  have ht := tendsto_integral_approxOn_of_measurable (μ := μ) hi hf
    (s := Metric.closedBall (0 : ℂ) C)
    (Filter.Eventually.of_forall (fun x => subset_closure (by simpa using hb x)))
    (Metric.mem_closedBall_self hC) (integrable_zero E ℂ μ)
  change Tendsto (fun n => (displacementApprox f hf C hC n).integral μ)
    atTop (𝓝 (∫ x, f x ∂μ)) at ht
  simpa only [SimpleFunc.integral_eq_integral _ (simple_integrable _ μ)] using ht

private theorem tendsto_overlap_integral (ν : ComplexMeasure E) (f : E → ℂ) (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun n => overlapIntegral ν (displacementApprox f hf C hC n)) atTop
      (𝓝 (overlapIntegral ν f)) := by
  unfold overlapIntegral
  exact ((displacementApprox_tendsto_integral f hf hC hb _).sub
      (displacementApprox_tendsto_integral f hf hC hb _)).add
    (((displacementApprox_tendsto_integral f hf hC hb _).sub
      (displacementApprox_tendsto_integral f hf hC hb _)).const_mul Complex.I)

variable (P : DisplacementPVM E H) (f : E → ℂ) (hf : Measurable f)
  {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C)

include hf hC hb in
private theorem weakIntegral_bound (y x : H) :
    ‖overlapIntegral (overlapMeasure P y x) f‖ ≤ C * (‖y‖ * ‖x‖) :=
  le_of_tendsto' (tendsto_overlap_integral (overlapMeasure P y x) f hf hC hb).norm
    fun n => overlap_integral_simple_bound P _ y x hC (displacementApprox_bound f hf hC n)

include hb in
private theorem simple_readout_tendsto (y x : H) :
    Tendsto (fun n => ⟪y, simpleDisplacementIntegral P (displacementApprox f hf C hC n) x⟫_ℂ)
      atTop (𝓝 (overlapIntegral (overlapMeasure P y x) f)) := by
  simp_rw [simple_displacement_integral_readout]
  exact tendsto_overlap_integral (overlapMeasure P y x) f hf hC hb

private def weakIntegralDual (x : H) : H →L[ℂ] ℂ := by
  let u := fun y : H => star (overlapIntegral (overlapMeasure P y x) f)
  have ht (y : H) : Tendsto (fun n =>
      ⟪simpleDisplacementIntegral P (displacementApprox f hf C hC n) x, y⟫_ℂ) atTop (𝓝 (u y)) := by
    have hs := (continuous_star (R := ℂ)).continuousAt.tendsto.comp
      (simple_readout_tendsto P f hf hC hb y x)
    have he : (star ∘ fun n => ⟪y, simpleDisplacementIntegral P
        (displacementApprox f hf C hC n) x⟫_ℂ) =
        fun n => ⟪simpleDisplacementIntegral P (displacementApprox f hf C hC n) x, y⟫_ℂ :=
      funext fun _ => inner_conj_symm _ _
    rw [he] at hs
    exact hs
  let A : H →ₗ[ℂ] ℂ :=
    { toFun := u
      map_add' := fun y z => tendsto_nhds_unique (ht (y + z)) (by
        simpa only [inner_add_right] using (ht y).add (ht z))
      map_smul' := fun c y => tendsto_nhds_unique (ht (c • y)) (by
        simpa only [inner_smul_right, smul_eq_mul, RingHom.id_apply] using (ht y).const_mul c) }
  exact A.mkContinuous (C * ‖x‖) (fun y => by
    change ‖star (overlapIntegral (overlapMeasure P y x) f)‖ ≤ _
    rw [norm_star, mul_assoc, mul_comm ‖x‖ ‖y‖]
    exact weakIntegral_bound P f hf hC hb y x)

private def weakIntegralVector (x : H) : H :=
  (InnerProductSpace.toDual ℂ H).symm (weakIntegralDual P f hf hC hb x)

private theorem weakIntegralVector_inner (y x : H) :
    ⟪y, weakIntegralVector P f hf hC hb x⟫_ℂ =
      overlapIntegral (overlapMeasure P y x) f := by
  rw [← inner_conj_symm, weakIntegralVector, InnerProductSpace.toDual_symm_apply]
  change star (star (overlapIntegral (overlapMeasure P y x) f)) = _
  exact star_star _

/-- The bounded PVM integral is obtained by Riesz representation of its
scalar readouts. Its bound is the bound of the actual multiplier. -/
def weakDisplacementIntegral : H →L[ℂ] H := by
  let A : H →ₗ[ℂ] H :=
    { toFun := weakIntegralVector P f hf hC hb
      map_add' := fun x z => by
        apply ext_inner_left ℂ
        intro y
        simp only [inner_add_right, weakIntegralVector_inner]
        exact tendsto_nhds_unique (simple_readout_tendsto P f hf hC hb y (x + z)) (by
          simpa only [map_add, inner_add_right] using
            (simple_readout_tendsto P f hf hC hb y x).add
              (simple_readout_tendsto P f hf hC hb y z))
      map_smul' := fun c x => by
        apply ext_inner_left ℂ
        intro y
        simp only [RingHom.id_apply, inner_smul_right, weakIntegralVector_inner]
        exact tendsto_nhds_unique (simple_readout_tendsto P f hf hC hb y (c • x)) (by
          simpa only [map_smul, inner_smul_right, smul_eq_mul] using
            (simple_readout_tendsto P f hf hC hb y x).const_mul c) }
  exact A.mkContinuous C (fun x => by
    let y := weakIntegralVector P f hf hC hb x
    change ‖y‖ ≤ _
    have hh := weakIntegral_bound P f hf hC hb y x
    rw [← weakIntegralVector_inner P f hf hC hb y x, inner_self_eq_norm_sq_to_K,
      norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)] at hh
    by_cases hy : ‖y‖ = 0
    · rw [hy]
      positivity
    · have hp := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy)
      exact le_of_mul_le_mul_left (by simpa only [pow_two, mul_left_comm C ‖y‖ ‖x‖] using hh) hp)

theorem weak_displacement_integral_readout (y x : H) :
    ⟪y, weakDisplacementIntegral P f hf hC hb x⟫_ℂ =
      overlapIntegral (overlapMeasure P y x) f :=
  weakIntegralVector_inner P f hf hC hb y x

theorem weak_displacement_integral_norm :
    ‖weakDisplacementIntegral P f hf hC hb‖ ≤ C := by
  unfold weakDisplacementIntegral
  exact LinearMap.mkContinuous_norm_le _ hC _

end UV.ContinuationBoundary
