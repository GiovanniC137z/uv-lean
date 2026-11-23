import UV.ContinueWilsonMixedGraph

/-! The hard A4 Maxwell integral for a finite family of open and closed
charged pieces. The local inverse identities occupy a separate set of
tested endpoints and carry no positive hop length. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure UV.SectorPlane

namespace UV

variable {V J C D ι : Type*} [Fintype V] [DecidableEq V] [Fintype J] [Fintype C] [Fintype D] [Fintype ι]

/-- All photon momenta, path fractions and endpoint tests are integrated
together in the absolute norm, including the endpoint tests of the empty
open words. Only dependent tree photon factors use the hard infrared
convention. Each positive-length component has its own hopping sum. -/
theorem wilson_hard_mixed_graph_sum {L lam ρ : ℝ} (hL : 0 < L) (hρ : 0 < ρ) (hlam : 0 ≤ lam) (hl : 2*lam < 1)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (P : V → WilsonChargedPiece) {a : V → ℕ}
    (u : (v : V) → Fin (a v) → UnitVector OSFourSpace)
    (chord : C → WilsonPhotonPolarizations) (tree : D → WilsonPhotonPolarizations)
    (route : (C → OSFourSpace) → D → OSFourSpace) (hr : ∀ e, Measurable (route · e))
    (k : (v : V) → (C → OSFourSpace) → Fin (a v) → OSFourSpace) (hk : ∀ v i, Measurable (k v · i))
    (Δ : V → WilsonPhotonPaths a C → OSFourSpace) (hΔ : ∀ v, Measurable (Δ v))
    (φ ψ : J → WilsonPacket) (δ : J → WilsonPhotonPaths a C → OSFourSpace) (hδ : ∀ j, Measurable (δ j)) :
    let μ := (volume : Measure (WilsonPathFractions a)).prod (Measure.pi (fun _ : C => (volume : Measure OSFourSpace)))
    let ν := μ.prod (Measure.pi (fun _ : J => (volume : Measure OSFourSpace)))
    let W := wilsonJointTraces (wilsonHardPathWeight a L ρ T chord tree route)
      (fun j z p => wilsonPacketPair (φ j) (ψ j) p (δ j z) 1)
    let F := fun (n : V → ℕ) (f : WilsonMarkAllocation a n) =>
      wilsonMixedWord P W L T u f
        (fun v z => wilsonVisitShift (f v) (fun i => z.1.1 ⟨v,i⟩) (k v z.1.2)) (fun v z => Δ v z.1)
    (∀ n f, Integrable (F n f) (ν.prod (Measure.pi (fun _ : V => volume)))) ∧
      Summable (fun n : V → ℕ => (∏ v, lam^(n v+1)) * ∑ f : WilsonMarkAllocation a n,
        ∫ t, ‖F n f t‖ ∂ν.prod (Measure.pi (fun _ : V => volume))) := by
  dsimp only
  let μ := (volume : Measure (WilsonPathFractions a)).prod (Measure.pi (fun _ : C => (volume : Measure OSFourSpace)))
  haveI : SFinite μ := Measure.prod.instSFinite (μ := (volume : Measure (WilsonPathFractions a)))
    (ν := Measure.pi (fun _ : C => (volume : Measure OSFourSpace)))
  let ν := μ.prod (Measure.pi (fun _ : J => (volume : Measure OSFourSpace)))
  haveI : SFinite ν := Measure.prod.instSFinite (μ := μ) (ν := Measure.pi (fun _ : J => (volume : Measure OSFourSpace)))
  obtain ⟨hm,hi⟩ := wilson_hard_path_weight a hL hρ T chord tree route hr
  obtain ⟨hmW,hiW,_⟩ := wilson_local_identities_weight φ ψ hδ μ hm hi
  let q := fun (n : V → ℕ) (f : WilsonMarkAllocation a n) v (z : WilsonPhotonPaths a C × (J → OSFourSpace)) =>
    wilsonVisitShift (f v) (fun i => z.1.1 ⟨v,i⟩) (k v z.1.2)
  have hq (n f v j) : Measurable (q n f v · j) :=
    (wilson_path_shifts_measurable k hk n f v j).comp measurable_fst
  have hd (v : V) : Measurable (fun z : WilsonPhotonPaths a C × (J → OSFourSpace) => Δ v z.1) := (hΔ v).comp measurable_fst
  exact ⟨fun n f => (wilson_mixed_words_bound P hL T u f (hq n f) hd ν hmW hiW).1,
    wilson_mixed_lengths_summable P hL hlam hl T u q hq hd ν hmW hiW⟩

end UV
