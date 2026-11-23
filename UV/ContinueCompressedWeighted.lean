import UV.ContinueCompressedEndpoint

/-! Absolute graph bounds with the external transfer of each tested open
path retained. Independent transfers can be integrated against the endpoint
packets themselves. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure UV.SectorPlane
namespace UV
variable {ι V Z : Type*} [Fintype ι] [Fintype V] [MeasurableSpace Z]

theorem compressed_weighted_graph {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (θ : ℝ) (σ : Measure OSFourSpace) [SigmaFinite σ] (hc : CompressedLoopBounds m L T σ) (hi : Integrable normalPacketWeight σ)
    (P : V → CompressedPiece) (hp : ∀ v, (P v).schwartzEndpoints) (s : (V → ℤ) → (v : V) → Z → Fin (P v).length → OSFourSpace)
    (hs : ∀ j v i, Measurable (s j v · i)) (Δ : V → Z → OSFourSpace) (hΔ : ∀ v, Measurable (Δ v))
    (μ : Measure Z) [SFinite μ] (W : Z → ℂ) (hW : Measurable W)
    (hiW : Integrable (fun z => ‖W z‖*∏ v,(P v).transferWeight (Δ v z)) μ) :
    CompressedGraphAbsolute σ μ m L θ T P s Δ W := by
  classical
  choose B hB hb using fun v => (P v).decaying_budget hm hL T σ hc hi ((P v).schwartz_decay (hp v))
  let g := fun v (j : ℤ) => B v*normalPhotonWeight 2 (normalLegFrequency L θ j)
  apply momentum_weighted_joint_windings (fun _ : V => σ) μ hW
    (fun j v => (P v).measurable_value hm L T _ (hs j v) (hΔ v))
    (fun j v z => (hb v _ (s j v z) (Δ v z)).1) _ hiW g
    (fun v j => mul_nonneg (hB v) (by unfold normalPhotonWeight; positivity))
    (fun v => (normal_shifted_frequency_summable hL θ).mul_left _)
  intro j v z
  simpa only [g,mul_comm ((P v).transferWeight _)] using (hb v (normalLegFrequency L θ (j v)) (s j v z) (Δ v z)).2

end UV
