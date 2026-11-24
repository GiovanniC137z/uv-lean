import UV.ContinueOrderedEnvelopeChart

/-! Mixed transverse and instantaneous lines in a conserved chord routing.
The first real coordinate is the carrier coordinate of the sector. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped BigOperators

namespace UV

open SectorPlane

variable {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ} {A : E → Fin n → ℝ}

/-- At fixed scattering data the bound is independent of every tree offset.
Loops, parallel photons and arbitrary choices of line kind are allowed. -/
theorem WilsonIncidenceBasis.ordered_product_bound (B : WilsonIncidenceBasis A)
    (kind : E → OrderedPhotonKind) {a : ℝ} (ha : 0 ≤ a) (b : Fin n → OSFourSpace)
    (q : B.Chord → OSFourSpace) :
    (∏ e, (kind e).envelope a (B.flow b q e)) ≤ ∏ c : B.Chord, (kind c).envelope a (q c) := by
  classical
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun e => e ∈ B.tree)]
  rw [show Subtype.fintype (fun e => e ∈ B.tree) = Finset.Subtype.fintype B.tree from Subsingleton.elim _ _]
  simp only [B.tree_flow,B.chord_flow]
  apply mul_le_of_le_one_left (Finset.prod_nonneg fun (c : B.Chord) _ => (kind c).nonneg _ _)
  exact Finset.prod_le_one (fun (j : B.tree) _ => (kind j).nonneg _ _) (fun (j : B.tree) _ => (kind j).le_one ha _)

theorem WilsonIncidenceBasis.measurable_flow (B : WilsonIncidenceBasis A)
    (b : Fin n → OSFourSpace) (e : E) : Measurable (fun q => B.flow b q e) := by
  by_cases he : e ∈ B.tree
  · simp only [WilsonIncidenceBasis.flow, dif_pos he,WilsonIncidenceBasis.onTree]
    exact (wilson_affine_transfer_continuous _ _).measurable
  · simp only [WilsonIncidenceBasis.flow, dif_neg he]
    exact measurable_pi_apply _

/-- Absolute Lebesgue convergence of the actual product over every labelled
edge in the incidence solution. Each free chord carries its own L¹ line. -/
theorem WilsonIncidenceBasis.ordered_product_integrable (B : WilsonIncidenceBasis A)
    (kind : E → OrderedPhotonKind) {a : ℝ} (ha : 0 < a) (b : Fin n → OSFourSpace) :
    Integrable (fun q => ∏ e, (kind e).envelope a (B.flow b q e))
      (Measure.pi (fun _ : B.Chord => volume)) := by
  apply (Integrable.fintype_prod (fun c : B.Chord => (kind c).integrable ha)).mono'
  · exact (Finset.measurable_prod _ fun e _ => ((kind e).measurable _).comp (B.measurable_flow b e)).aestronglyMeasurable
  · apply ae_of_all
    intro q
    rw [Real.norm_of_nonneg (Finset.prod_nonneg fun e _ => (kind e).nonneg _ _)]
    exact B.ordered_product_bound kind ha.le b q

/-- A nonzero free coefficient makes the vanishing *spatial* projection of
a routed line null in the full independent four-momentum variables. -/
theorem ordered_affine_spatial_ne_zero {C : Type*} [Fintype C]
    (b : OSFourSpace) {v : C → ℝ} (hv : ∃ i, v i ≠ 0) :
    ∀ᵐ q ∂Measure.pi (fun _ : C => (volume : Measure OSFourSpace)),
      (orderedPhotonChart (wilsonAffineTransfer b v q)).2 ≠ 0 := by
  classical
  obtain ⟨j,hj⟩ := hv
  let F := (EuclideanSpace.proj (1 : Fin 4) : OSFourSpace →L[ℝ] ℝ).toLinearMap.comp (wilsonRouteLinear v)
  let S := (affineSpan ℝ ({-b 1} : Set ℝ)).comap F.toAffineMap
  have hmem (q : C → OSFourSpace) : q ∈ S ↔ F q = -b 1 := AffineSubspace.mem_affineSpan_singleton ℝ _
  have hproper : S ≠ ⊤ := by
    intro h
    have hall (q : C → OSFourSpace) : F q = -b 1 := (hmem q).mp (h ▸ AffineSubspace.mem_top ℝ _ _)
    have hb := (hall 0).symm.trans (map_zero F)
    have hx := (hall (Pi.single j (osAxis 1).val)).trans hb
    change (wilsonRouteLinear v (Pi.single j (osAxis 1).val)) 1 = 0 at hx
    rw [wilson_route_linear_apply, Finset.sum_eq_single j] at hx
    · simp [Pi.single_eq_same,osAxis,EuclideanSpace.single_apply] at hx
      exact hj hx
    · intro i _ hij
      simp [Pi.single_eq_of_ne hij]
    · simp
  have hout : ∀ᵐ q ∂Measure.pi (fun _ : C => (volume : Measure OSFourSpace)), q ∉ S := by
    rw [ae_iff]
    simpa using addHaar_affineSubspace volume S hproper
  filter_upwards [hout] with q hq hz
  apply hq
  apply (hmem q).mpr
  have hcoord := congrArg (fun x : Spatial => x 0) hz
  change (orderedPhotonChart (wilsonAffineTransfer b v q)).2 0 = 0 at hcoord
  rw [ordered_photon_chart_space] at hcoord
  change b 1 + F q = 0 at hcoord
  linarith

/-- For a proper routed graph the exceptional spatial axes are simultaneously
null. The deletion graph only uses surviving labelled internal edges. -/
theorem WilsonIncidenceBasis.ordered_flow_spatial_ne_zero (src dst : E → Option (Fin n))
    (B : WilsonIncidenceBasis (groundedNetworkIncidence src dst).row)
    (Gdel : B.tree → SimpleGraph (Option (Fin n))) (hc : ∀ j, (Gdel j).Connected)
    (hcover : ∀ j : B.tree, NetworkOrientationCovers (Gdel j)
      (fun e : {e : E // e ≠ j.val} => src e) (fun e => dst e))
    (b : Fin n → OSFourSpace) :
    ∀ᵐ q ∂Measure.pi (fun _ : B.Chord => (volume : Measure OSFourSpace)), ∀ e,
      (orderedPhotonChart (B.flow b q e)).2 ≠ 0 := by
  classical
  apply ae_all_iff.mpr
  intro e
  by_cases he : e ∈ B.tree
  · let j : B.tree := ⟨e,he⟩
    change ∀ᵐ q ∂_, (orderedPhotonChart (B.flow b q j)).2 ≠ 0
    simp only [B.tree_flow, WilsonIncidenceBasis.onTree]
    exact ordered_affine_spatial_ne_zero _ (B.active_of_deletion j
      (wilson_incidence_nonbridge src dst j (Gdel j) (hc j) (hcover j)))
  · let c : B.Chord := ⟨e,he⟩
    change ∀ᵐ q ∂_, (orderedPhotonChart (B.flow b q c)).2 ≠ 0
    simp only [B.chord_flow]
    let v := fun i : B.Chord => if i = c then (1:ℝ) else 0
    have h := ordered_affine_spatial_ne_zero (0 : OSFourSpace) (v := v) ⟨c,by simp [v]⟩
    simpa [wilsonAffineTransfer,wilson_route_linear_apply,v,ite_smul] using h

end UV
