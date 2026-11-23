import UV.ContinueOSQuarticKernels

/-! Uniform product integrability at a fixed depth follows from the eighth
point moment and the second moment of the insertion. -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace UV

variable {Y Ω ι : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]

theorem osWick_eighth_point {μ : Measure Ω} {F : ι → Ω → ℝ} {K : ι → ι → ℝ}
    (hW : OSWickMoments μ F K) (i : ι) :
    Integrable (fun ω => (F i ω)^8) μ ∧ (∫ ω, (F i ω)^8 ∂μ) = 105 * K i i ^ 4 := by
  let xs := [i,i,i,i,i,i,i,i]
  have he (ω : Ω) : osMonomial F xs ω = (F i ω)^8 := by simp [xs, osMonomial]; ring
  have hm := hW.moment 4 xs (by simp [xs])
  rw [show osWickMoment K 4 xs = 105 * K i i ^ 4 by
    simp [xs, osWickMoment, List.zipIdx, List.eraseIdx]; ring] at hm
  exact ⟨(hW.integrable xs).congr (Eventually.of_forall he), by simpa only [he] using hm⟩

/-- A uniform second moment of a spatial field and an L² insertion give
spacetime product integrability on the support of an integrable switch. -/
theorem osSpatialProduct_second_moments {ν : Measure Y} [SFinite ν]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Y → Ω → ℝ} {A : Ω → ℝ}
    {ζ : Y → ℝ} {C : ℝ} (hZ : Measurable (Function.uncurry Z))
    (hA : AEStronglyMeasurable A μ) (hA2 : Integrable (fun ω => A ω ^ 2) μ)
    (hζ : Integrable ζ ν) (h2 : ∀ x, Integrable (fun ω => Z x ω ^ 2) μ)
    (h2b : ∀ x, (∫ ω, Z x ω ^ 2 ∂μ) ≤ C) :
    Integrable (fun p : Y × Ω => A p.2 * (ζ p.1 * Z p.1 p.2)) (ν.prod μ) := by
  have hmeas : AEStronglyMeasurable (fun p : Y × Ω => A p.2 * (ζ p.1 * Z p.1 p.2)) (ν.prod μ) :=
    hA.comp_snd.mul (hζ.1.comp_fst.mul hZ.aestronglyMeasurable)
  have hpoint (x : Y) (ω : Ω) : ‖A ω * (ζ x * Z x ω)‖ ≤ ‖ζ x‖ * (A ω ^ 2 + Z x ω ^ 2) := by
    simp only [Real.norm_eq_abs, abs_mul]
    rw [mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    nlinarith [sq_nonneg (|A ω| - |Z x ω|), sq_abs (A ω), sq_abs (Z x ω),
      mul_nonneg (abs_nonneg (A ω)) (abs_nonneg (Z x ω))]
  have hI (x : Y) : Integrable (fun ω => A ω * (ζ x * Z x ω)) μ := by
    apply ((hA2.add (h2 x)).const_mul ‖ζ x‖).mono' ?_ (Eventually.of_forall (hpoint x))
    exact hA.mul (aestronglyMeasurable_const.mul
      (hZ.comp ((measurable_const (a := x)).prodMk measurable_id)).aestronglyMeasurable)
  apply (integrable_prod_iff hmeas).mpr
  refine ⟨Eventually.of_forall hI, ?_⟩
  apply (hζ.norm.mul_const ((∫ ω, A ω^2 ∂μ) + C)).mono' hmeas.norm.integral_prod_right' ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  calc
    _ ≤ ∫ ω, ‖ζ x‖ * (A ω ^ 2 + Z x ω ^ 2) ∂μ :=
      integral_mono (hI x).norm ((hA2.add (h2 x)).const_mul _) (hpoint x)
    _ ≤ _ := by
      rw [integral_const_mul, integral_add hA2 (h2 x)]
      exact mul_le_mul_of_nonneg_left (add_le_add_left (h2b x) _) (norm_nonneg _)

/-- Uniform point eighth moments and an L² insertion suffice for the
spacetime Fubini bound, with no probabilistic independence at different
spatial positions. -/
theorem osQuartic_product_integrable {ν : Measure Y} [SFinite ν]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Y → Ω → ℝ} {A : Ω → ℝ}
    {ζ : Y → ℝ} {C : ℝ} (hZ : Measurable (Function.uncurry Z))
    (hA : AEStronglyMeasurable A μ) (hA2 : Integrable (fun ω => A ω ^ 2) μ)
    (hζ : Integrable ζ ν) (h8 : ∀ x, Integrable (fun ω => Z x ω ^ 8) μ)
    (h8b : ∀ x, (∫ ω, Z x ω ^ 8 ∂μ) ≤ C) :
    Integrable (fun p : Y × Ω => A p.2 * (ζ p.1 * Z p.1 p.2 ^ 4 / 24)) (ν.prod μ) := by
  have hZ4 : Measurable (Function.uncurry (fun x ω => Z x ω ^ 4)) := hZ.pow_const 4
  have he (x : Y) (ω : Ω) : (Z x ω^4)^2 = Z x ω^8 := by ring
  have hi := osSpatialProduct_second_moments (A := A) (ζ := ζ) (C := C) hZ4 hA hA2 hζ
    (fun x => (h8 x).congr (Eventually.of_forall fun ω => (he x ω).symm))
    (fun x => by simpa only [he] using h8b x)
  exact (hi.div_const 24).congr (Eventually.of_forall fun p => by dsimp; ring)

theorem osWick_raw_product_integrable {ν : Measure Y} [SFinite ν] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : ι → Ω → ℝ} {K : ι → ι → ℝ} (hW : OSWickMoments μ F K)
    (a b : ι) (y : Y → ι) {ζ : Y → ℝ} (hζ : Integrable ζ ν)
    (hZ : Measurable (fun p : Y × Ω => F (y p.1) p.2)) {v : ℝ}
    (hv : ∀ x, K (y x) (y x) = v) :
    Integrable (fun p : Y × Ω => F a p.2 * F b p.2 * (ζ p.1 * F (y p.1) p.2 ^ 4 / 24))
      (ν.prod μ) := by
  have hA : Integrable (fun ω => F a ω * F b ω) μ := by
    exact (hW.integrable [a,b]).congr (Eventually.of_forall fun ω => by simp [osMonomial])
  have he (ω : Ω) : osMonomial F [a,b,a,b] ω = (F a ω * F b ω)^2 := by
    simp [osMonomial]; ring
  have hA2 : Integrable (fun ω => (F a ω * F b ω)^2) μ := by
    exact (hW.integrable [a,b,a,b]).congr (Eventually.of_forall he)
  exact osQuartic_product_integrable (A := fun ω => F a ω * F b ω) (Z := fun x ω => F (y x) ω)
    (C := 105 * v^4) hZ hA.1 hA2 hζ
    (fun x => (osWick_eighth_point hW (y x)).1) (fun x => by
      rw [(osWick_eighth_point hW _).2, hv])

end UV
