import UV.VerifyCurvatureRouting

/-! Absolute graph bounds for the routed Wick incidences. The literal
Haar vertex and only fixed external factors enter the coefficient; the
internal two-transfer lines are the same ones in the sector tail theorem. -/

noncomputable section

open MeasureTheory Filter Real
open scoped BigOperators Topology

namespace UV.VerifyCurvatureGraphBounds

open UV.NextCurvatureLaw UV.AdvanceCurvatureVertex UV.VerifyCurvatureExpansion
open UV.VerifyCurvatureRouting UV.FurtherCurvatureGraph UV.NextCurvatureFull
open UV.FurtherCurvatureLine UV.FurtherCurvatureShell UV.FurtherCurvatureDeterminant

private theorem externalLine_measurable {n r p I J : ℕ} (g : Incidence r p I J)
    (probes : Fin p → ModeSlot n) (j : Fin J) : Measurable (fun ℓ => externalLine g probes ℓ j) := by
  unfold externalLine
  cases isInteraction (g.ends (.inr j, 0)) <;> cases isInteraction (g.ends (.inr j, 1)) <;>
    unfold occurrenceLine curvatureLine curvatureCovariance <;> fun_prop

private theorem vertexProduct_norm_le {n r p I J : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (g : Incidence r p I J) (probes : Fin p → ModeSlot n) (a : Fin I → MeanZeroMode)
    (colors : EdgeColors n I) (outputs : Fin r → Fin n) {D : ℝ} (hD : 0 ≤ D)
    (hB : ∀ v, ‖vertexCoefficient B v‖ ≤ D) :
    ‖vertexProduct B g probes a colors outputs‖ ≤ D^r := by
  unfold vertexProduct
  split
  · rw [norm_prod]
    exact (Finset.prod_le_prod (fun _ _ => norm_nonneg _ ) (fun v _ => hB _)).trans_eq (by simp)
  · simp only [norm_zero]
    positivity

private def vertexSum {n r p I J : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (g : Incidence r p I J) (probes : Fin p → ModeSlot n) (a : Fin I → MeanZeroMode) : ℝ :=
  ∑ colors : EdgeColors n I, ∑ outputs : Fin r → Fin n, vertexProduct B g probes a colors outputs

/-- The residual coefficient is the actual color sum with the bounded
fixed-probe lines. It has no internal propagator or cutoff dependence. -/
def routedCoefficient {n r p I J : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (g : Incidence r p I J) (probes : Fin p → ModeSlot n) (ℓ : ℝ) (a : Assignment I) : ℝ := by
  classical
  exact if ha : ∀ i, a i ≠ 0 then
    if 0 ≤ ℓ then vertexSum B g probes (fun i => ⟨a i,ha i⟩) * ∏ j, externalLine g probes ℓ j
    else 0
  else 0

theorem routedCoefficient_measurable {n r p I J : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (g : Incidence r p I J) (probes : Fin p → ModeSlot n) (a : Assignment I) :
    Measurable (fun ℓ => routedCoefficient B g probes ℓ a) := by
  classical
  by_cases ha : ∀ i, a i ≠ 0
  · simp only [routedCoefficient, dif_pos ha]
    apply Measurable.ite measurableSet_Ici _ measurable_const
    exact (Finset.measurable_prod _ fun j _ => externalLine_measurable g probes j).const_mul _
  · simp only [routedCoefficient, dif_neg ha]
    exact measurable_const

/-- The same uniform bound covers every admitted momentum and depth. It
uses only the finite colors, the |Haar vertex| bound, and fixed probe lines. -/
theorem routedCoefficient_uniformly_bounded {n r p I J : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (g : Incidence r p I J) (probes : Fin p → ModeSlot n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ℓ a, |routedCoefficient B g probes ℓ a| ≤ A := by
  obtain ⟨D,hD,hB⟩ := curvatureVertexFactor_uniformly_bounded B
  let A := (Fintype.card (EdgeColors n I) : ℝ) * (Fintype.card (Fin r → Fin n) : ℝ) * (D/2)^r
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A,hA,fun ℓ a => ?_⟩
  rw [← Real.norm_eq_abs]
  unfold routedCoefficient
  split
  · rename_i ha
    split
    · rename_i hℓ
      have hP : ‖∏ j, externalLine g probes ℓ j‖ ≤ 1 := by
        rw [norm_prod]
        simpa only [Finset.prod_const_one] using
          (Finset.prod_le_prod (s := (Finset.univ : Finset (Fin J)))
            (f := fun j => ‖externalLine g probes ℓ j‖) (g := fun _ => (1 : ℝ))
            (fun _ _ => norm_nonneg _) (fun j _ =>
              noninternal_line_norm_le ℓ hℓ _ _ _ (external_not_internal g j)))
      rw [norm_mul]
      apply (mul_le_of_le_one_right (norm_nonneg _) hP).trans
      have hV (v : VertexChoice n) : ‖vertexCoefficient B v‖ ≤ D/2 := by
        rw [vertexCoefficient, norm_mul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1/2)]
        exact (mul_le_mul_of_nonneg_left (hB _ _ _) (by positivity)).trans_eq (by ring)
      unfold vertexSum
      calc
        _ ≤ ∑ colors : EdgeColors n I, ∑ outputs : Fin r → Fin n, (D/2)^r :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun colors _ =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun outputs _ =>
              vertexProduct_norm_le B g probes (fun i => ⟨a i,ha i⟩) colors outputs (by positivity) hV))
        _ = A := by unfold A; simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    · simpa only [norm_zero] using hA
  · simpa only [norm_zero] using hA

/-- The determinant-weighted spherical graph built by its literal vertices,
paired positions, and independent internal modes. -/
def routedSphericalGraph {n r p I J : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (g : Incidence r p I J) (probes : Fin p → ModeSlot n) (Λ ℓ : ℝ) : ℝ := by
  classical
  exact sphericalDeterminant n Λ ℓ *
    ∑ a ∈ Fintype.piFinset (fun _ : Fin I => sphericalModes Λ),
      if ha : ∀ i, a i ≠ 0 then
        ∑ colors : EdgeColors n I, ∑ outputs : Fin r → Fin n,
          routedWickTerm B g probes ℓ (fun i => ⟨a i,ha i⟩) colors outputs else 0

/-- The literal spherical graph equals the input of the existing
finite internal contraction theorem, including all color multiplicities. -/
theorem routedSphericalGraph_eq {n r p I J : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (g : Incidence r p I J) (probes : Fin p → ModeSlot n) (Λ ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    routedSphericalGraph B g probes Λ ℓ = sphericalGraphSum n Λ ℓ (routedCoefficient B g probes ℓ) := by
  classical
  change sphericalDeterminant n Λ ℓ * _ = sphericalDeterminant n Λ ℓ *
    (∑ a ∈ Fintype.piFinset (fun _ : Fin I => sphericalModes Λ),
      routedCoefficient B g probes ℓ a * ∏ i, curvatureLine ℓ (a i))
  apply congrArg (sphericalDeterminant n Λ ℓ * ·)
  refine Finset.sum_congr rfl fun a hA => ?_
  have ha (i : Fin I) : a i ≠ 0 := (mem_sphericalModes.mp (Fintype.mem_piFinset.mp hA i)).1
  simp only [dif_pos ha, routedCoefficient, if_pos hℓ, routedWickTerm_factor, vertexSum,
    Finset.sum_mul]

/-- The spherical graphs on one determinant-weighted finite depth law
converge to their actual absolutely summable full-mode graph. -/
theorem integrated_routedGraph_limit {n r p I J : ℕ} (hn : 0 < n)
    (B : Fin n → Fin n → Fin n → ℝ) (g : Incidence r p I J) (probes : Fin p → ModeSlot n)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ) :
    Integrable (fun ℓ => fullGraphSum n ℓ (routedCoefficient B g probes ℓ)) μ ∧
    Tendsto (fun Λ : ℝ => ∫ ℓ, routedSphericalGraph B g probes Λ ℓ ∂μ) atTop
      (𝓝 (∫ ℓ, fullGraphSum n ℓ (routedCoefficient B g probes ℓ) ∂μ)) := by
  obtain ⟨A,_,hA⟩ := routedCoefficient_uniformly_bounded B g probes
  have h := integrated_full_graph_limit hn μ hμ (routedCoefficient B g probes)
    (routedCoefficient_measurable B g probes) hA
  refine ⟨h.1, h.2.congr' (Eventually.of_forall fun Λ => ?_)⟩
  apply integral_congr_ae
  exact hμ.mono fun ℓ hℓ => (routedSphericalGraph_eq B g probes Λ ℓ hℓ).symm

/-- The absolute momentum tail of the arbitrary routed graph has the
original integrated bound at every prescribed power. -/
theorem integrated_routedGraph_absolute_tail {n r p I J : ℕ} (hn : 0 < n)
    (B : Fin n → Fin n → Fin n → ℝ) (g : Incidence r p I J) (probes : Fin p → ModeSlot n)
    {s : ℝ} (hs : 0 ≤ s) (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {M : ℝ}, 0 < M →
      Integrable (fun ℓ => fullAbsoluteTail n ℓ M (routedCoefficient B g probes ℓ)) μ ∧
      (∫ ℓ, fullAbsoluteTail n ℓ M (routedCoefficient B g probes ℓ) ∂μ) ≤ C * M^(-s) ∧
      Tendsto (fun Λ : ℝ => ∫ ℓ, sphericalTail n Λ ℓ M (routedCoefficient B g probes ℓ) ∂μ) atTop
        (𝓝 (∫ ℓ, fullAbsoluteTail n ℓ M (routedCoefficient B g probes ℓ) ∂μ)) := by
  obtain ⟨A,hA,hB⟩ := routedCoefficient_uniformly_bounded B g probes
  obtain ⟨K,hK,h⟩ := integrated_full_absolute_tail (I := I) hn hs
  refine ⟨(μ Set.univ).toReal * K * A, by positivity, fun {M} hM => ?_⟩
  have hh := h hM μ hμ (routedCoefficient B g probes) (routedCoefficient_measurable B g probes) hB
  refine ⟨hh.1, ?_, hh.2.2⟩
  exact hh.2.1.trans_eq (by ring)

/-- The integrated absolute bound is uniform in the literal spherical
cutoff, for the same complete graph coefficient. -/
theorem integrated_routedSphericalGraph_tail_uniform {n r p I J : ℕ} (hn : 0 < n)
    (B : Fin n → Fin n → Fin n → ℝ) (g : Incidence r p I J) (probes : Fin p → ModeSlot n)
    {s : ℝ} (hs : 0 ≤ s) (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ M : ℝ}, 0 ≤ Λ → 0 < M →
      Integrable (fun ℓ => sphericalTail n Λ ℓ M (routedCoefficient B g probes ℓ)) μ ∧
      (∫ ℓ, sphericalTail n Λ ℓ M (routedCoefficient B g probes ℓ) ∂μ) ≤ C * M^(-s) := by
  obtain ⟨A,hA,hB⟩ := routedCoefficient_uniformly_bounded B g probes
  obtain ⟨K,hK,h⟩ := integrated_spherical_tail_uniform (I := I) hn hs
  refine ⟨(μ Set.univ).toReal * K * A, by positivity, fun {Λ M} hΛ hM => ?_⟩
  have hh := h hΛ hM μ hμ (routedCoefficient B g probes) (routedCoefficient_measurable B g probes) hB
  exact ⟨hh.1, hh.2.trans_eq (by ring)⟩

end UV.VerifyCurvatureGraphBounds
