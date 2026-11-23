import UV.ContinueWilsonGraphHopSum

/-! The open ordered Wilson word tested against arbitrary measurable
square-integrable four-spinor packets. Momentum transfer may translate
the outgoing packet and every marked matrix. The empty word includes
the source's local identity. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter UV.SectorPlane
open scoped Matrix.Norms.L2Operator

namespace UV

abbrev WilsonPacketSpinor := EuclideanSpace ℂ (Fin 4)

structure WilsonPacket where
  value : OSFourSpace → WilsonPacketSpinor
  measurable : Measurable value
  square : MemLp value 2 volume

def WilsonPacket.cost (ψ : WilsonPacket) : ℝ := ∫ p, ‖ψ.value p‖^2

theorem WilsonPacket.square_integrable (ψ : WilsonPacket) : Integrable (fun p => ‖ψ.value p‖^2) :=
  (memLp_two_iff_integrable_sq_norm ψ.measurable.aestronglyMeasurable).mp ψ.square

theorem WilsonPacket.cost_nonneg (ψ : WilsonPacket) : 0 ≤ ψ.cost := integral_nonneg fun _ => sq_nonneg _

def wilsonPacketPair (φ ψ : WilsonPacket) (p Δ : OSFourSpace) (A : DiracMatrix) : ℂ :=
  inner ℂ (φ.value (p+Δ)) (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℂ) A (ψ.value p))

theorem wilson_packet_pair_bound (φ ψ : WilsonPacket) (p Δ : OSFourSpace) (A : DiracMatrix) :
    ‖wilsonPacketPair φ ψ p Δ A‖ ≤ ‖A‖ * ((‖φ.value (p+Δ)‖^2 + ‖ψ.value p‖^2)/2) := by
  apply (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
  have hA := Matrix.l2_opNorm_mulVec A (ψ.value p)
  have hc := (mul_le_mul_of_nonneg_left hA (norm_nonneg (φ.value (p+Δ))))
  apply hc.trans
  calc _ = ‖A‖ * (‖φ.value (p+Δ)‖ * ‖ψ.value p‖) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (‖φ.value (p+Δ)‖-‖ψ.value p‖)]) (norm_nonneg _)

local instance : MeasurableSpace DiracMatrix := borel _
local instance : BorelSpace DiracMatrix := ⟨rfl⟩

theorem wilson_packet_pair_measurable {Z : Type*} [MeasurableSpace Z] (φ ψ : WilsonPacket)
    {p Δ : Z → OSFourSpace} (hp : Measurable p) (hΔ : Measurable Δ) {A : Z → DiracMatrix} (hA : Measurable A) :
    Measurable (fun z => wilsonPacketPair φ ψ (p z) (Δ z) (A z)) := by
  have hm : Measurable (fun z => (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℂ) (A z))) :=
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional.measurable.comp hA
  have happ : Measurable (fun z => Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℂ) (A z) (ψ.value (p z))) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp (hm.prodMk (ψ.measurable.comp hp))
  exact (continuous_fst.inner (𝕜 := ℂ) continuous_snd).measurable.comp ((φ.measurable.comp (hp.add hΔ)).prodMk happ)

theorem wilson_packet_budget (φ ψ : WilsonPacket) (Δ : OSFourSpace) :
    let F := fun p => (‖φ.value (p+Δ)‖^2 + ‖ψ.value p‖^2)/2
    Integrable F ∧ (∫ p, F p) = (φ.cost+ψ.cost)/2 := by
  let mp := measurePreserving_add_right (volume : Measure OSFourSpace) Δ
  have h : Integrable (fun p : OSFourSpace => ‖φ.value (p+Δ)‖^2) := (mp.integrable_comp_emb (Homeomorph.addRight Δ).measurableEmbedding).mpr φ.square_integrable
  dsimp only
  refine ⟨(h.add ψ.square_integrable).div_const 2,?_⟩
  rw [integral_div,integral_add h ψ.square_integrable,mp.integral_comp (Homeomorph.addRight Δ).measurableEmbedding (fun p => ‖φ.value p‖^2)]
  rfl

theorem wilson_open_word_integral (φ ψ : WilsonPacket) {A : OSFourSpace → DiracMatrix} (hA : Measurable A)
    (Δ : OSFourSpace) {M : ℝ} (hb : ∀ p, ‖A p‖ ≤ M) :
    let f := fun p => wilsonPacketPair φ ψ p Δ (A p)
    Integrable f ∧ (∫ p, ‖f p‖) ≤ M*((φ.cost+ψ.cost)/2) := by
  let F := fun p => (‖φ.value (p+Δ)‖^2 + ‖ψ.value p‖^2)/2
  have h := wilson_packet_budget φ ψ Δ
  have hle (p) : ‖wilsonPacketPair φ ψ p Δ (A p)‖ ≤ M*F p :=
    (wilson_packet_pair_bound _ _ _ _ _).trans (mul_le_mul_of_nonneg_right (hb p) (by positivity))
  have hi := (h.1.const_mul M).mono' (wilson_packet_pair_measurable φ ψ measurable_id measurable_const hA).aestronglyMeasurable
    (Eventually.of_forall hle)
  exact ⟨hi,(integral_mono hi.norm (h.1.const_mul M) hle).trans_eq (by rw [integral_const_mul,h.2])⟩

variable {ι : Type*} [Fintype ι]

/-- Each nonempty open word has the same geometric hopping factor as
the untraced operator product, with a shift-independent packet budget. -/
theorem wilson_open_assigned_bound {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    {a n : ℕ} (u : Fin a → UnitVector OSFourSpace) (f : Fin a → Fin (n+1)) (q : Fin (n+1) → OSFourSpace)
    (φ ψ : WilsonPacket) (Δ : OSFourSpace) :
    let hs := wilsonAssignedHop u f q 0 :: wilsonAssignedTail u f q
    let F := fun p => wilsonPacketPair φ ψ p Δ (wilsonCirculationWord L T hs p)
    Integrable F ∧ (∫ p, ‖F p‖) ≤ (2^(n+1) * (2*L)^a)*((φ.cost+ψ.cost)/2) := by
  let hs := wilsonAssignedHop u f q 0 :: wilsonAssignedTail u f q
  have hm (l : List WilsonCirculationHop) : Measurable (wilsonCirculationWord L T l) := by
    induction l with
    | nil => exact measurable_const
    | cons h hs ih => exact ((wilson_spin_hop_measurable L T h.marks).comp (measurable_add_const _)).mul ih
  have he : wilsonCirculationCost L hs = 2^(n+1)*(2*L)^a := by
    rw [wilson_circulation_cost]
    simp only [hs,List.length_cons,List.map_cons,List.sum_cons,wilson_assigned_mark_count]
    simp [wilsonAssignedTail]
  exact wilson_open_word_integral φ ψ (hm hs) Δ (fun p => (wilson_circulation_uniform hL T hs p).trans_eq he)

theorem wilson_open_identity (φ ψ : WilsonPacket) (Δ : OSFourSpace) :
    Integrable (fun p => wilsonPacketPair φ ψ p Δ 1) ∧
      (∫ p, ‖wilsonPacketPair φ ψ p Δ 1‖) ≤ (φ.cost+ψ.cost)/2 := by
  simpa only [one_mul] using wilson_open_word_integral φ ψ measurable_const Δ (fun _ => (norm_one (α := DiracMatrix)).le)

end UV
