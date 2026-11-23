import UV.ContinueWilsonEuclideanTwoPoint

/-! Absolute convergence certificates for the limiting coefficient.
These cover the individual chord and displacement integrals and the sum
of absolute displacement integrals with their determinant weights. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter UV.SectorPlane
open scoped Topology BigOperators

namespace UV

variable {V C D ι : Type*} [Fintype V] [DecidableEq V] [Fintype C] [Fintype D] [Fintype ι]

omit [Fintype V] [DecidableEq V] in
theorem WilsonCurrentGraph.coefficient_chords_integrable (G : WilsonCurrentGraph V C D) {L : ℝ} (hL : 0 < L)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (P : V → WilsonClosedPolygon) (b : OSFourSpace → D → OSFourSpace)
    (a : D → C → ℝ) (u v w : UnitVector OSFourSpace) :
    Integrable (fun q => (P G.first).softCoefficient u v * (P G.second).softCoefficient (wilsonOppositeDirection u) w *
      G.kernel (wilsonShellPhotonForm L T) P b a 0 q) (Measure.pi (fun _ : C => volume)) :=
  (wilson_routed_photons_integrable hL T _ _ (fun j => (wilson_affine_transfer_continuous (b 0 j) (a j)).measurable)).const_mul _

theorem WilsonCurrentGraph.coefficient_absolute (G : WilsonCurrentGraph V C D) {L lam : ℝ} (hL : 0 < L)
    (hlam : 0 ≤ lam) (hl : 2*lam < 1) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (b : OSFourSpace → D → OSFourSpace) (hb : ∀ e, ContinuousAt (b · e) 0)
    (a : D → C → ℝ) (ha : ∀ e, ∃ j, a e j ≠ 0) (u v w : UnitVector OSFourSpace) :
    let χ := wilsonShellPhotonForm L T
    let F := fun (n : V → ℕ) (d : WilsonGraphDisplacements n) => wilsonGraphReturnWeight L T d *
      G.coefficient χ (fun j => wilsonReturnPolygon (d j)) b a u v w
    (∀ n, Integrable (F n) (wilsonGraphReturnMeasure L T n)) ∧ Summable (fun n : V → ℕ =>
      ‖wilsonDetWeight lam n‖ * ∫ d, ‖F n d‖ ∂wilsonGraphReturnMeasure L T n) := by
  let χ := wilsonShellPhotonForm L T
  let F := fun (n : V → ℕ) (d : WilsonGraphDisplacements n) => wilsonGraphReturnWeight L T d *
    G.coefficient χ (fun j => wilsonReturnPolygon (d j)) b a u v w
  let f := fun (n : V → ℕ) r (d : WilsonGraphDisplacements n) => wilsonGraphReturnWeight L T d *
    G.twoPoint χ (fun j => wilsonReturnPolygon (d j)) b a u v w r
  have H (n : V → ℕ) (d : WilsonGraphDisplacements n) : Tendsto (fun r => f n r d) (𝓝[≠] 0) (𝓝 (F n d)) :=
    (G.twoPoint_tendsto hL T _ b hb a ha u v w).const_mul _
  have hm (n : V → ℕ) : Measurable (F n) := measurable_of_tendsto_metrizable' (𝓝[≠] (0:ℝ))
    (fun r => (wilson_graph_return_weight_continuous hL T n).measurable.mul
      (G.twoPoint_measurable (wilson_shell_form_continuous L T) n b a u v w r))
    (tendsto_pi_nhds.mpr (H n))
  have hB (n : V → ℕ) (d : WilsonGraphDisplacements n) : ‖F n d‖ ≤ G.envelope L T d :=
    le_of_tendsto (H n d).norm (Eventually.of_forall (fun r => G.envelope_bound hL T d b a u v w r))
  have hInt (n : V → ℕ) : Integrable (F n) (wilsonGraphReturnMeasure L T n) :=
    (G.envelope_integrable hL T n).mono' (hm n).aestronglyMeasurable (Eventually.of_forall (hB n))
  refine ⟨hInt,?_⟩
  let g := fun (j : V) (k : ℕ) => lam^(k+1)*wilsonMomentIntegral L T (G.degree j) k
  have hs : Summable (fun n : V → ℕ => wilsonChordBudget C L T * ∏ j, g j (n j)) :=
    (wilson_summable_independent_lengths (fun j k => mul_nonneg (pow_nonneg hlam _) (wilson_moment_integral_nonneg _ _ _ _))
      (fun j => wilson_return_all_lengths hL hlam hl T (G.degree j))).mul_left _
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)) _ hs
  intro n
  have hle := integral_mono (hInt n).norm (G.envelope_integrable hL T n) (hB n)
  apply (mul_le_mul (wilson_det_weight_bound hlam n) hle (integral_nonneg (fun _ => norm_nonneg _))
    (Finset.prod_nonneg fun _ _ => pow_nonneg hlam _)).trans_eq
  rw [G.envelope_integral]
  simp only [g,Finset.prod_mul_distrib]
  ring

end UV
