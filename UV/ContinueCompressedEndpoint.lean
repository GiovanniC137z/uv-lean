import UV.ContinueCompressedRouted
import UV.ContinueMomentumRoutingWeighted

/-! Decay in the external charged transfer survives integration of its
endpoint momentum. This estimate keeps the two packet norms separate. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter UV.SectorPlane
open scoped Matrix.Norms.L2Operator SchwartzMap
namespace UV
variable {ι : Type*} [Fintype ι]

def CompressedPiece.transferWeight (P : CompressedPiece) (Δ : OSFourSpace) : ℝ :=
  match P with
  | .loop .. => 1
  | .path .. => normalPacketWeight Δ

theorem CompressedPiece.transferWeight_pos (P : CompressedPiece) (Δ : OSFourSpace) : 0 < P.transferWeight Δ := by
  cases P <;> dsimp [transferWeight,normalPacketWeight] <;> positivity

theorem CompressedPiece.transferWeight_continuous (P : CompressedPiece) : Continuous P.transferWeight := by
  cases P with
  | loop => exact continuous_const
  | path => exact ((continuous_const.add continuous_norm).pow 6).inv₀ (fun x => by positivity)

def CompressedPiece.packetDecay : CompressedPiece → Prop
  | .loop .. => True
  | .path _ _ φ ψ => ∃ B : ℝ, 0 ≤ B ∧ ∀ k Δ,
      ‖φ.value (k+Δ)‖*‖ψ.value k‖ ≤ B*normalPacketWeight Δ*normalPacketWeight k

theorem CompressedPiece.schwartz_decay (P : CompressedPiece) (h : P.schwartzEndpoints) : P.packetDecay := by
  cases P with
  | loop => trivial
  | path n u φ ψ =>
    obtain ⟨f,g,rfl,rfl⟩ := h
    exact momentum_schwartz_overlap f g

theorem CompressedPiece.decaying_budget {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (σ : Measure OSFourSpace) (hc : CompressedLoopBounds m L T σ) (hw : Integrable normalPacketWeight σ)
    (P : CompressedPiece) (hp : P.packetDecay) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ s Δ, Integrable (P.value m L T ξ s Δ) σ ∧
      (∫ k, ‖P.value m L T ξ s Δ k‖ ∂σ) ≤ P.transferWeight Δ*(B*normalPhotonWeight 2 ξ) := by
  cases P with
  | loop n u =>
    obtain ⟨B,hB,h⟩ := hc n u
    exact ⟨B,hB,fun ξ s _ => by simpa [transferWeight,value] using h ξ s⟩
  | path n u φ ψ =>
    obtain ⟨C,hC,hp⟩ := hp
    obtain ⟨B,hB,hf⟩ := compressed_endpoint_form_bound hL T
    let M := B*m⁻¹^(n+2)
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hwpos (k : OSFourSpace) : 0 ≤ normalPacketWeight k := by dsimp [normalPacketWeight]; positivity
    refine ⟨M*C*(∫ k, normalPacketWeight k ∂σ),mul_nonneg (mul_nonneg hM hC) (integral_nonneg hwpos),fun ξ s Δ => ?_⟩
    let A := fun k => compressedOpenWord m L T ξ u (fun j => k+s j)
    have hA (k) : ‖A k‖ ≤ M*normalPhotonWeight 2 ξ :=
      (compressed_open_marked_bound hm L T ξ u _).trans ((mul_le_mul_of_nonneg_right (hf ξ _) (by positivity)).trans_eq (by dsimp [M]; ring))
    let F := fun k => wilsonPacketPair φ ψ k Δ (A k)
    let D := M*normalPhotonWeight 2 ξ*C*normalPacketWeight Δ
    have hW : 0 ≤ normalPhotonWeight 2 ξ := by dsimp [normalPhotonWeight]; positivity
    have hle (k) : ‖F k‖ ≤ D*normalPacketWeight k := by
      apply (momentum_packet_pair_product ..).trans
      apply (mul_le_mul (hA k) (hp k Δ) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg hM hW)).trans_eq
      dsimp [D]; ring
    have hAf := compressed_open_measurable hm L T ξ u (fun j => measurable_id.add_const (s j))
    have hi := hw.const_mul D
    have hF := hi.mono' (wilson_packet_pair_measurable φ ψ measurable_id measurable_const hAf).aestronglyMeasurable (Eventually.of_forall hle)
    refine ⟨hF,(integral_mono hF.norm hi hle).trans_eq ?_⟩
    rw [integral_const_mul]
    dsimp [transferWeight,D]; ring

end UV
