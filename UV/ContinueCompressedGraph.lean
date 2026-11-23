import UV.ContinueCompressedOpen
import UV.ContinueCompressedModes
import UV.ContinueNormalRankGraph

/-! Mixed graphs of the affine three-compression model at fixed positive
electric order. Integer indices are circle Fourier modes. A closed word
has one freely circulating five-momentum even when it is a tadpole. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter UV.SectorPlane
open scoped Matrix.Norms.L2Operator SchwartzMap

namespace UV
variable {ι V Z : Type*} [Fintype ι] [Fintype V] [MeasurableSpace Z]

inductive CompressedPiece where
  | loop (n : ℕ) (u : Fin (n+1) → UnitVector OSFourSpace)
  | path (n : ℕ) (u : Fin (n+1) → UnitVector OSFourSpace) (φ ψ : WilsonPacket)

def CompressedPiece.length : CompressedPiece → ℕ
  | .loop n _ => n+1
  | .path n .. => n+2

def CompressedPiece.value (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ) (P : CompressedPiece) :
    (Fin P.length → OSFourSpace) → OSFourSpace → OSFourSpace → ℂ :=
  match P with
  | .loop _ u => fun s _ k => compressedLoopTrace m L T ξ u (fun j => k+s j)
  | .path _ u φ ψ => fun s Δ k => wilsonPacketPair φ ψ k Δ (compressedOpenWord m L T ξ u (fun j => k+s j))

def CompressedPiece.endpointBound (σ : Measure OSFourSpace) : CompressedPiece → Prop
  | .loop .. => True
  | .path _ _ φ ψ => ∃ B : ℝ, 0 ≤ B ∧ ∀ Δ : OSFourSpace,
    let g := fun k => (‖φ.value (k+Δ)‖^2+‖ψ.value k‖^2)/2
    Integrable g σ ∧ (∫ k, g k ∂σ) ≤ B

theorem CompressedPiece.volume_endpoints (P : CompressedPiece) : P.endpointBound volume := by
  cases P with
  | loop => trivial
  | path n u φ ψ =>
    exact ⟨_,div_nonneg (add_nonneg φ.cost_nonneg ψ.cost_nonneg) (by norm_num),fun Δ =>
      ⟨(wilson_packet_budget φ ψ Δ).1,(wilson_packet_budget φ ψ Δ).2.le⟩⟩

def CompressedPiece.schwartzEndpoints : CompressedPiece → Prop
  | .loop .. => True
  | .path _ _ φ ψ => ∃ f g : 𝓢(OSFourSpace,WilsonPacketSpinor), φ = normalSchwartzPacket f ∧ ψ = normalSchwartzPacket g

theorem CompressedPiece.lattice_endpoints (b : NormalReciprocalBasis) (P : CompressedPiece) (h : P.schwartzEndpoints) :
    P.endpointBound (normalLatticeMeasure b) := by
  cases P with
  | loop => trivial
  | path n u φ ψ =>
    let o : Icc (0:ℝ) 1 := ⟨0,by simp⟩
    exact NormalChargedSector.lattice_endpoint_bound b (.line (n+1) u φ ψ o o) h

local instance : MeasurableSpace DiracMatrix := borel _
local instance : BorelSpace DiracMatrix := ⟨rfl⟩

theorem CompressedPiece.measurable_value {m : ℝ} (hm : 0 < m) (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (ξ : ℝ) (P : CompressedPiece) {s : Z → Fin P.length → OSFourSpace} (hs : ∀ j, Measurable (s · j))
    {Δ : Z → OSFourSpace} (hΔ : Measurable Δ) : Measurable (fun t : Z × OSFourSpace => P.value m L T ξ (s t.1) (Δ t.1) t.2) := by
  cases P with
  | loop n u => exact compressed_loop_measurable hm L T ξ u (fun j => measurable_snd.add ((hs j).comp measurable_fst))
  | path n u φ ψ =>
    exact wilson_packet_pair_measurable φ ψ measurable_snd (hΔ.comp measurable_fst)
      (compressed_open_measurable hm L T ξ u (fun j => measurable_snd.add ((hs j).comp measurable_fst)))

def CompressedLoopBounds (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (σ : Measure OSFourSpace) : Prop :=
  ∀ (n : ℕ) (u : Fin (n+1) → UnitVector OSFourSpace), ∃ B : ℝ, 0 ≤ B ∧ ∀ (ξ : ℝ) (s : Fin (n+1) → OSFourSpace),
    let F := fun k => compressedLoopTrace m L T ξ u (fun j => k+s j)
    Integrable F σ ∧ (∫ k, ‖F k‖ ∂σ) ≤ B*normalPhotonWeight 2 ξ

theorem CompressedPiece.integral_bound {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (σ : Measure OSFourSpace) (hc : CompressedLoopBounds m L T σ) (P : CompressedPiece) (ht : P.endpointBound σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ s Δ, Integrable (P.value m L T ξ s Δ) σ ∧ (∫ k, ‖P.value m L T ξ s Δ k‖ ∂σ) ≤ B*normalPhotonWeight 2 ξ := by
  cases P with
  | loop n u =>
    obtain ⟨B,hB,h⟩ := hc n u
    exact ⟨B,hB,fun ξ s _ => h ξ s⟩
  | path n u φ ψ =>
    obtain ⟨M,hM,he⟩ := ht
    obtain ⟨B,hB,hf⟩ := compressed_endpoint_form_bound hL T
    let K := B*m⁻¹^(n+2)
    have hK : 0 ≤ K := by dsimp [K]; positivity
    refine ⟨K*M,by positivity,fun ξ s Δ => ?_⟩
    let A := fun k => compressedOpenWord m L T ξ u (fun j => k+s j)
    let Y := fun k => (‖φ.value (k+Δ)‖^2+‖ψ.value k‖^2)/2
    have hA : Measurable A := compressed_open_measurable hm L T ξ u (fun j => measurable_id.add_const (s j))
    have hle (k) : ‖wilsonPacketPair φ ψ k Δ (A k)‖ ≤ (K*normalPhotonWeight 2 ξ)*Y k := by
      apply (wilson_packet_pair_bound ..).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      apply (compressed_open_marked_bound hm L T ξ u _).trans
      exact (mul_le_mul_of_nonneg_right (hf ξ _) (by positivity)).trans_eq (by dsimp [K]; ring)
    have hi := (he Δ).1.const_mul (K*normalPhotonWeight 2 ξ)
    have hI := hi.mono' (wilson_packet_pair_measurable φ ψ measurable_id measurable_const hA).aestronglyMeasurable (Eventually.of_forall hle)
    refine ⟨hI,(integral_mono hI.norm hi hle).trans ?_⟩
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left (he Δ).2 (by dsimp [normalPhotonWeight]; positivity)).trans_eq (by ring)

def CompressedGraphAbsolute (σ : Measure OSFourSpace) (μ : Measure Z) (m L θ : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (P : V → CompressedPiece) (s : (V → ℤ) → (v : V) → Z → Fin (P v).length → OSFourSpace)
    (Δ : V → Z → OSFourSpace) (W : Z → ℂ) : Prop :=
  let F := fun (j : V → ℤ) => wilsonJointFactors W (fun v z => (P v).value m L T (normalLegFrequency L θ (j v)) (s j v z) (Δ v z))
  let ν := μ.prod (Measure.pi (fun _ : V => σ))
  (∀ j, Integrable (F j) ν) ∧ Summable (fun j => ∫ x, ‖F j x‖ ∂ν)

theorem compressed_graph_integral {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (θ : ℝ) (σ : Measure OSFourSpace) [SigmaFinite σ] (hc : CompressedLoopBounds m L T σ) (P : V → CompressedPiece)
    (ht : ∀ v, (P v).endpointBound σ) (s : (V → ℤ) → (v : V) → Z → Fin (P v).length → OSFourSpace)
    (hs : ∀ j v i, Measurable (s j v · i)) (Δ : V → Z → OSFourSpace) (hΔ : ∀ v, Measurable (Δ v))
    (μ : Measure Z) [SFinite μ] (W : Z → ℂ) (hW : Measurable W) (hiW : Integrable W μ) :
    CompressedGraphAbsolute σ μ m L θ T P s Δ W := by
  classical
  choose B hB hb using fun v => (P v).integral_bound hm hL T σ hc (ht v)
  let g := fun (v : V) (j : ℤ) => B v*normalPhotonWeight 2 (normalLegFrequency L θ j)
  have hg (v j) : 0 ≤ g v j := mul_nonneg (hB v) (by unfold normalPhotonWeight; positivity)
  have hsum (v) : Summable (g v) := (normal_shifted_frequency_summable hL θ).mul_left _
  have h (j : V → ℤ) := wilson_joint_factors_measure (fun _ : V => σ) μ hW hiW
    (fun v => (P v).measurable_value hm L T (normalLegFrequency L θ (j v)) (hs j v) (hΔ v))
    (fun v z => (hb v _ (s j v z) (Δ v z)).1) (fun v => g v (j v)) (fun v z => (hb v _ (s j v z) (Δ v z)).2)
  exact ⟨fun j => (h j).1,Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun j => (h j).2) ((wilson_summable_product hg hsum).mul_left _)⟩

end UV
