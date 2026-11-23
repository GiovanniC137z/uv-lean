import UV.ContinueWilsonPolygonAveraging

/-! The directional transverse two-point coefficient for the sum of the
closed Wilson polygons of a fixed contracted graph. The logarithmic
determinant weight includes the actual cyclic factor 1/N at every vertex. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Real UV.SectorPlane
open scoped Topology BigOperators

namespace UV

variable {V C D ι : Type*} [Fintype V] [DecidableEq V] [Fintype C] [Fintype D] [Fintype ι]

def wilsonDetWeight (lam : ℝ) (n : V → ℕ) : ℝ := ∏ j, lam^(n j+1) / (n j+1:ℝ)

omit [DecidableEq V] in
theorem wilson_det_weight_bound {lam : ℝ} (hlam : 0 ≤ lam) (n : V → ℕ) :
    ‖wilsonDetWeight lam n‖ ≤ ∏ j, lam^(n j+1) := by
  rw [wilsonDetWeight,norm_prod]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro j _
  rw [Real.norm_of_nonneg (by positivity)]
  exact div_le_self (pow_nonneg hlam _) (le_add_of_nonneg_left (Nat.cast_nonneg _))

def WilsonCurrentGraph.summedRadial (G : WilsonCurrentGraph V C D) (L lam : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (b : OSFourSpace → D → OSFourSpace) (a : D → C → ℝ) (u v w : UnitVector OSFourSpace) (r : ℝ) : ℂ :=
  ∑' n : V → ℕ, (wilsonDetWeight lam n : ℂ) *
    ∫ d, wilsonGraphReturnWeight L T d * G.twoPoint (wilsonShellPhotonForm L T) (fun j => wilsonReturnPolygon (d j)) b a u v w r
      ∂wilsonGraphReturnMeasure L T n

def WilsonCurrentGraph.summedCoefficient (G : WilsonCurrentGraph V C D) (L lam : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (b : OSFourSpace → D → OSFourSpace) (a : D → C → ℝ) (u v w : UnitVector OSFourSpace) : ℂ :=
  ∑' n : V → ℕ, (wilsonDetWeight lam n : ℂ) *
    ∫ d, wilsonGraphReturnWeight L T d * G.coefficient (wilsonShellPhotonForm L T) (fun j => wilsonReturnPolygon (d j)) b a u v w
      ∂wilsonGraphReturnMeasure L T n

/-- A single summable majorant controls all external radial transfers
and every independent polygon length, including all self-sewings. -/
theorem WilsonCurrentGraph.summed_twoPoint_limit (G : WilsonCurrentGraph V C D) {L lam : ℝ} (hL : 0 < L)
    (hlam : 0 ≤ lam) (hl : 2*lam < 1) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (b : OSFourSpace → D → OSFourSpace) (hb : ∀ e, ContinuousAt (b · e) 0)
    (a : D → C → ℝ) (ha : ∀ e, ∃ j, a e j ≠ 0) (u v w : UnitVector OSFourSpace) :
    Tendsto (G.summedRadial L lam T b a u v w) (𝓝[≠] 0) (𝓝 (G.summedCoefficient L lam T b a u v w)) := by
  let χ := wilsonShellPhotonForm L T
  let F := fun r (n : V → ℕ) => (wilsonDetWeight lam n : ℂ) * ∫ d, wilsonGraphReturnWeight L T d *
    G.twoPoint χ (fun j => wilsonReturnPolygon (d j)) b a u v w r ∂wilsonGraphReturnMeasure L T n
  let g := fun (j : V) (k : ℕ) => lam^(k+1)*wilsonMomentIntegral L T (G.degree j) k
  let K := wilsonChordBudget C L T
  have hs : Summable (fun n : V → ℕ => K * ∏ j, g j (n j)) :=
    (wilson_summable_independent_lengths (fun j k => mul_nonneg (pow_nonneg hlam _) (wilson_moment_integral_nonneg _ _ _ _))
      (fun j => wilson_return_all_lengths hL hlam hl T (G.degree j))).mul_left K
  have hbound (r : ℝ) (n : V → ℕ) : ‖F r n‖ ≤ K * ∏ j, g j (n j) := by
    dsimp only [F]
    rw [norm_mul,Complex.norm_real]
    have hi := (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun _ => norm_nonneg _) (G.envelope_integrable hL T n)
      (Eventually.of_forall fun d => G.envelope_bound hL T d b a u v w r))
    apply (mul_le_mul (wilson_det_weight_bound hlam n) hi (norm_nonneg _)
      (Finset.prod_nonneg fun _ _ => pow_nonneg hlam _)).trans_eq
    rw [G.envelope_integral]
    simp only [g,Finset.prod_mul_distrib,K]
    ring
  change Tendsto (fun r => ∑' n, F r n) _ _
  apply tendsto_tsum_of_dominated_convergence hs
  · intro n
    exact (G.averaged_twoPoint_limit hL T n b hb a ha u v w).const_mul _
  · exact Eventually.of_forall hbound

end UV
