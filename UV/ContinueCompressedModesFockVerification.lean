import UV.ContinueCompressedModesFockCutoff

/-! From an actual term of the complete normal-ordered source transfer
to its individually convergent signed spinor graph and removal of
carrier-momentum cutoffs at every vertex. -/

noncomputable section
open MeasureTheory Filter Set UV.SectorPlane
open scoped Topology ENNReal SchwartzMap Matrix.Norms.L2Operator

namespace UV.FermionWick

variable {ν ι V T : Type*} [Fintype ν] [Fintype ι] [Nonempty ι] [DecidableEq ι]
  [NormedAddCommGroup V] [MeasurableSpace T]

omit [Fintype ν] [Fintype ι] [Nonempty ι] in
theorem finite_time_contractions (band : ι→Bool) (mom : ι→Spatial) (m : ℝ) (t : ν→ℝ)
    {vs : List ν} (times : vs.Pairwise (fun i j => t j<t i)) (a b : ν→ι)
    (es : List (Edge (Slot ν ι))) (n : ℕ) (he : es∈matchings n (sourceWord vs a b))
    (hn : amplitude (seaCovariance band (fun i=>FurtherOptical.energy m (mom i)) t) es≠0) :
    amplitude (seaCovariance band (fun i=>FurtherOptical.energy m (mom i)) t) es =
      timeFactor es t m (fun i => mom (a i)) := by
  have ord := matching_edges_ordered _ n _ (ordered_source t a b times) he
  have perm := matching_uses_all _ _ _ he
  unfold amplitude timeFactor
  congr 1
  apply List.map_congr_left
  intro e hem
  have h := nonzero_edge band _ t es hn e hem
  obtain ⟨hm,hx,hy⟩ := h
  have hf := (slot_mem_source (perm.mem_iff.mp (show e.first∈endpoints es from
    List.mem_flatMap.mpr ⟨e,hem,by simp⟩))).2
  have hg := (slot_mem_source (perm.mem_iff.mp (show e.second∈endpoints es from
    List.mem_flatMap.mpr ⟨e,hem,by simp⟩))).2
  rw [edgeWeight,seaCovariance,if_pos ⟨hm,hx,hy⟩,abs_of_pos (sub_pos.mpr (ord e hem))]
  have heq : e.first.orbital=a (select true e).vertex := by
    cases hc : e.first.create
    · have hb : band e.first.orbital=true := by
        have hne : false ≠ band e.first.orbital := hc ▸ hx
        cases h : band e.first.orbital
        · exact (hne h.symm).elim
        · rfl
      have hg' : e.second.create=true := hy.trans hb
      simpa [select,hc,hg'] using hm.trans hg
    · simpa [select,hc] using hf
  rw [heq]

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
theorem rimProduct_vertices (diamond : Plane V) (σ : Equiv.Perm ν) (bands : ν→Bool)
    (offset : ν→Spatial) (k : Cycle σ→Spatial) (m ℓ : ℝ) (N : ℕ) :
    (∏ c : Cycle σ, rimOnCycle diamond σ bands c offset m ℓ N (k c)) =
      ∏ i : ν, seaRimMark diamond (signedRim diamond (bands i)) (bands (σ.symm i) != bands i) m ℓ N
        (k (cycleClass σ (σ.symm i))+offset (σ.symm i)) (k (cycleClass σ i)+offset i) := by
  classical
  let F := fun i => seaRimMark diamond (signedRim diamond (bands i)) (bands (σ.symm i) != bands i) m ℓ N
    (k (cycleClass σ (σ.symm i))+offset (σ.symm i)) (k (cycleClass σ i)+offset i)
  have split (c : Cycle σ) : rimOnCycle diamond σ bands c offset m ℓ N (k c) =
      ∏ i : CycleVertex σ c,F i.val := by
    unfold rimOnCycle seaComplexLoopReadout
    apply Finset.prod_congr rfl
    intro i _
    dsimp only [F]
    have hs : cycleClass σ (σ.symm i.val)=c := ((cycleStep σ c).symm i).property
    rw [hs,i.property]
    rfl
  simp_rw [split]
  let eqv : (Σc:Cycle σ,CycleVertex σ c) ≃ ν := Equiv.sigmaFiberEquiv (cycleClass σ)
  have H := eqv.prod_comp F
  simpa only [Fintype.prod_sigma] using H

/-- The placement and fusion into circles are outputs of the Fock
calculation. N≥2 and positive mass and mean normal distance supply the
integrability margin. The finite time measure may include an ordered
slab simplex. -/
theorem verified_source_term (diamond : Plane V) {m ℓ : ℝ} (hm : 0<m) (hℓ : 0<ℓ)
    {N : ℕ} (hN : 2≤N) (isDensity : ν→Bool) (u : ν→UnitVector Spatial)
    (band : ι→Bool) (mom : ι→Spatial) (row : ι→Fin 4) (t : ν→ℝ)
    (vs : List ν) (nd : vs.Nodup) (covers : ∀i:ν,i∈vs) (times : vs.Pairwise (fun i j => t j<t i))
    (p : ℂ × List (Block (Slot ν ι))) (es : List (Edge (Slot ν ι)))
    (hp : p∈placements (physicalSource diamond m ℓ N isDensity u band mom row) vs)
    (he : es∈matchings (slots p.2).length p.2)
    (hne : amplitude (seaCovariance band (fun j => FurtherOptical.energy m (mom j)) t) es≠0)
    (tm : T→ν→ℝ) (ht : ∀i, Measurable (fun z=>tm z i)) (μ : Measure T) [IsFiniteMeasure μ]
    {d : ℕ} (χ : 𝓢(EuclideanSpace ℝ (Fin d),ℂ)) (offset : ν→Spatial)
    (L : ν→EuclideanSpace ℝ (Fin d)→L[ℝ] Spatial) :
    ∃ (a b : ν→ι) (σ : Equiv.Perm ν), p.2=sourceWord vs a b ∧
      (∀i, b (σ i)=a i ∧ (if band (a i) then t i<t (σ i) else t (σ i)<t i) ∧ σ i≠i) ∧
      p.1*amplitude (seaCovariance band (fun j=>FurtherOptical.energy m (mom j)) t) es =
        spinTime σ es t m (mom ∘ a) isDensity u (band ∘ a) (row ∘ a) *
        ∏i,seaRimMark diamond (signedRim diamond (band (a i))) (band (a (σ.symm i)) != band (a i)) m ℓ N
          (mom (a (σ.symm i))) (mom (a i)) ∧
      let F := bareGraph diamond σ es tm χ offset L isDensity u (band ∘ a) (row ∘ a) m ℓ N
      let graphMeasure := μ.prod (volume.prod volume)
      Integrable F graphMeasure ∧
      Tendsto (fun R:ℕ => ∫z in sectionBound σ offset L R,F z ∂graphMeasure) atTop (𝓝 (∫z,F z ∂graphMeasure)) ∧
      Tendsto (fun R:ℕ => ∫z in sectionBound σ offset L R,‖F z‖ ∂graphMeasure) atTop (𝓝 (∫z,‖F z‖ ∂graphMeasure)) := by
  obtain ⟨a,b,σ,hl,H,hw⟩ := physical_placement_factor diamond m ℓ N isDensity u band mom row t vs nd covers times p es hp he hne
  let F := bareGraph diamond σ es tm χ offset L isDensity u (band ∘ a) (row ∘ a) m ℓ N
  have hi : Integrable F (μ.prod (volume.prod volume)) := bareGraph_integrable diamond σ es
    (matching_signs _ _ _ he) tm ht μ χ offset L isDensity u (band ∘ a) (row ∘ a) t (fun i => (H i).2.1) hm hℓ hN
  refine ⟨a,b,σ,hl,H,?_,hi,remove_sections σ offset L hi,remove_sections σ offset L hi.norm⟩
  have hword := he
  rw [hl] at hword
  rw [hw,finite_time_contractions band mom m t times a b es _ hword hne,spinTime]
  dsimp [physicalSpin,Function.comp_def]
  ring

end UV.FermionWick
