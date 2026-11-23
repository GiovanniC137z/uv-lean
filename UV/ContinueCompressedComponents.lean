import UV.ContinueCompressedComplete
import UV.ContinueCompressedModesExhaustion

/-! Finite disjoint products of graph components and independently tested free
spectator lines. Each component can have its own number of circle modes and
its own momentum measure. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Matrix.Norms.L2Operator ENNReal
namespace UV

theorem compressed_components_absolute {C : Type*} [Fintype C] {J X : C → Type*}
    [∀ c, Countable (J c)] [∀ c, MeasurableSpace (J c)] [∀ c, MeasurableSingletonClass (J c)]
    [∀ c, MeasurableSpace (X c)] (σ : (c : C) → Measure (X c)) [∀ c, SigmaFinite (σ c)]
    (F : (c : C) → J c → X c → ℂ) (hi : ∀ c j, Integrable (F c j) (σ c))
    (hs : ∀ c, Summable (fun j => ∫ x, ‖F c j x‖ ∂σ c)) :
    let A := fun (j : (c : C) → J c) (x : (c : C) → X c) => ∏ c, F c (j c) (x c)
    (∀ j, Integrable (A j) (Measure.pi σ)) ∧ Summable (fun j => ∫ x, ‖A j x‖ ∂Measure.pi σ) := by
  classical
  let g := fun (c : C) (j : J c) => ∫ x, ‖F c j x‖ ∂σ c
  have hg c (j : J c) : 0 ≤ g c j := integral_nonneg fun _ => norm_nonneg _
  have hcount : Measure.pi (fun c : C => (Measure.count : Measure (J c))) = Measure.count := by
    apply Measure.ext_of_singleton
    intro j
    rw [←Set.univ_pi_singleton j,Measure.pi_pi,Set.univ_pi_singleton]
    simp
  have hgc (c : C) : Integrable (g c) Measure.count := by
    apply integrable_count_iff.mpr
    simpa only [Real.norm_of_nonneg (hg c _)] using hs c
  have h := Integrable.fintype_prod_dep hgc
  rw [hcount,integrable_count_iff] at h
  refine ⟨fun j => Integrable.fintype_prod_dep (fun c => hi c (j c)),?_⟩
  have he (j : (c : C) → J c) : (∫ x : (c : C) → X c, ‖∏ c,F c (j c) (x c)‖ ∂Measure.pi σ) = ∏ c,g c (j c) := by
    simp only [norm_prod]
    exact integral_fintype_prod_eq_prod (μ := σ) (fun c x => ‖F c (j c) x‖)
  simp_rw [he]
  simpa only [Real.norm_of_nonneg (Finset.prod_nonneg fun c _ => hg c _)] using h

/-- A free component has no transverse insertion. Two normal-mode and
carrier L² endpoint packets already control its massive inverse. -/
theorem compressed_free_endpoint_test {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    {m : ℝ} (hm : 0 < m) (p : Z → OSFourSpace) (j : Z → ℤ) (L θ : ℝ)
    (φ ψ : Z → WilsonPacketSpinor) (hφ : MemLp φ 2 μ) (hψ : MemLp ψ 2 μ)
    (F : Z → ℂ) (hF : AEStronglyMeasurable F μ)
    (h : ∀ z, F z = inner ℂ (φ z) (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℂ)
      (normalDiracFrequency m (p z) (normalLegFrequency L θ (j z))) (ψ z))) :
    Integrable F μ := by
  have hiφ := (memLp_two_iff_integrable_sq_norm hφ.aestronglyMeasurable).mp hφ
  have hiψ := (memLp_two_iff_integrable_sq_norm hψ.aestronglyMeasurable).mp hψ
  apply ((hiφ.add hiψ).const_mul (m⁻¹/2)).mono' hF
  refine Eventually.of_forall fun z => ?_
  rw [h z]
  apply (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
  apply (mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mulVec _ (ψ z)) (norm_nonneg _)).trans
  calc _ ≤ ‖φ z‖*(m⁻¹*‖ψ z‖) := by
         apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
         exact mul_le_mul_of_nonneg_right (normal_frequency_mass_bound hm _ _) (norm_nonneg _)
       _ ≤ _ := by
         change _ ≤ m⁻¹/2*(‖φ z‖^2+‖ψ z‖^2)
         nlinarith only [mul_nonneg (inv_nonneg.mpr hm.le) (sq_nonneg (‖φ z‖-‖ψ z‖))]

end UV
