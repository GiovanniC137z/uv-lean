import UV.ContinueWilsonOpenChain
import UV.ContinueWilsonPathRouting

/-! Simultaneous integration of closed circulations and open charged
chains tested at both ends, with shared photons and straight-link fractions. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter UV.SectorPlane
open scoped Matrix.Norms.L2Operator

namespace UV

variable {ι V Z : Type*} [Fintype ι] [Fintype V] [MeasurableSpace Z]

inductive WilsonChargedPiece where
  | loop
  | line (outgoing incoming : WilsonPacket)

def WilsonChargedPiece.value (P : WilsonChargedPiece) {a n : ℕ} (L : ℝ)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (u : Fin a → UnitVector OSFourSpace)
    (f : Fin a → Fin (n+1)) (q : Fin (n+1) → OSFourSpace) (Δ p : OSFourSpace) : ℂ :=
  match P with
  | .loop => wilsonAllocatedTrace L T u f q p
  | .line φ ψ => wilsonPacketPair φ ψ p Δ
      (wilsonCirculationWord L T (wilsonAssignedHop u f q 0 :: wilsonAssignedTail u f q) p)

def WilsonChargedPiece.budget (P : WilsonChargedPiece) {a : ℕ} (L : ℝ)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (u : Fin a → UnitVector OSFourSpace) : ℝ :=
  match P with
  | .loop => wilsonTraceBudget L T u
  | .line φ ψ => 2 * (2*L)^a * ((φ.cost+ψ.cost)/2)

theorem WilsonChargedPiece.budget_nonneg (P : WilsonChargedPiece) {a : ℕ} {L : ℝ} (hL : 0 < L)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (u : Fin a → UnitVector OSFourSpace) : 0 ≤ P.budget L T u := by
  cases P with
  | loop => exact wilson_trace_budget_nonneg _ _ _
  | line φ ψ => dsimp [budget]; have := φ.cost_nonneg; have := ψ.cost_nonneg; positivity

theorem WilsonChargedPiece.value_measurable (P : WilsonChargedPiece) {a n : ℕ} (L : ℝ)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (u : Fin a → UnitVector OSFourSpace) (f : Fin a → Fin (n+1))
    {q : Z → Fin (n+1) → OSFourSpace} (hq : ∀ j, Measurable (q · j)) {Δ p : Z → OSFourSpace}
    (hΔ : Measurable Δ) (hp : Measurable p) : Measurable (fun z => P.value L T u f (q z) (Δ z) (p z)) := by
  cases P with
  | loop => exact wilson_allocated_trace_measurable _ _ _ _ hq hp
  | line φ ψ => exact wilson_packet_pair_measurable φ ψ hp hΔ (wilson_allocated_word_measurable _ _ _ _ hq hp)

theorem WilsonChargedPiece.integral_bound (P : WilsonChargedPiece) {a n : ℕ} {L : ℝ} (hL : 0 < L)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (u : Fin a → UnitVector OSFourSpace)
    (f : Fin a → Fin (n+1)) (q : Fin (n+1) → OSFourSpace) (Δ : OSFourSpace) :
    Integrable (P.value L T u f q Δ) ∧ (∫ p, ‖P.value L T u f q Δ p‖) ≤ P.budget L T u * 2^n := by
  cases P with
  | loop => exact ⟨(wilson_charged_trace_absolute_bound hL T _ _).1,wilson_allocated_trace_bound hL T u f q⟩
  | line φ ψ =>
    have h := wilson_open_assigned_bound hL T u f q φ ψ Δ
    refine ⟨h.1,h.2.trans_eq ?_⟩
    dsimp only [budget]
    rw [pow_succ]
    ring

def wilsonMixedWord (P : V → WilsonChargedPiece) (w : Z → ℂ) (L : ℝ)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) {a n : V → ℕ} (u : (v : V) → Fin (a v) → UnitVector OSFourSpace)
    (f : WilsonMarkAllocation a n) (q : (v : V) → Z → Fin (n v+1) → OSFourSpace)
    (Δ : V → Z → OSFourSpace) : Z × (V → OSFourSpace) → ℂ :=
  wilsonJointTraces w (fun v z => (P v).value L T (u v) (f v) (q v z) (Δ v z))

theorem wilson_mixed_words_bound (P : V → WilsonChargedPiece) {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    {a n : V → ℕ} (u : (v : V) → Fin (a v) → UnitVector OSFourSpace) (f : WilsonMarkAllocation a n)
    {q : (v : V) → Z → Fin (n v+1) → OSFourSpace} (hq : ∀ v j, Measurable (q v · j))
    {Δ : V → Z → OSFourSpace} (hΔ : ∀ v, Measurable (Δ v)) (μ : Measure Z) [SFinite μ]
    {w : Z → ℂ} (hmw : Measurable w) (hw : Integrable w μ) :
    let ν := Measure.pi (fun _ : V => (volume : Measure OSFourSpace))
    Integrable (wilsonMixedWord P w L T u f q Δ) (μ.prod ν) ∧
      (∫ t, ‖wilsonMixedWord P w L T u f q Δ t‖ ∂μ.prod ν) ≤
        (∫ z, ‖w z‖ ∂μ) * ∏ v, (P v).budget L T (u v)*2^(n v) := by
  apply wilson_joint_traces_bound μ hmw hw
  · exact fun v => (P v).value_measurable L T (u v) (f v) (fun j => (hq v j).comp measurable_fst)
      ((hΔ v).comp measurable_fst) measurable_snd
  · exact fun v z => ((P v).integral_bound hL T (u v) (f v) (q v z) (Δ v z)).1
  · exact fun v z => ((P v).integral_bound hL T (u v) (f v) (q v z) (Δ v z)).2

theorem wilson_mixed_lengths_summable [DecidableEq V] (P : V → WilsonChargedPiece) {L lam : ℝ} (hL : 0 < L)
    (hlam : 0 ≤ lam) (hl : 2*lam < 1) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) {a : V → ℕ}
    (u : (v : V) → Fin (a v) → UnitVector OSFourSpace)
    (q : (n : V → ℕ) → WilsonMarkAllocation a n → (v : V) → Z → Fin (n v+1) → OSFourSpace)
    (hq : ∀ n f v j, Measurable (q n f v · j)) {Δ : V → Z → OSFourSpace} (hΔ : ∀ v, Measurable (Δ v))
    (μ : Measure Z) [SFinite μ] {w : Z → ℂ} (hmw : Measurable w) (hw : Integrable w μ) :
    Summable (fun n : V → ℕ => (∏ v, lam^(n v+1)) * ∑ f : WilsonMarkAllocation a n,
      ∫ t, ‖wilsonMixedWord P w L T u f (q n f) Δ t‖ ∂μ.prod (Measure.pi (fun _ : V => volume))) :=
  wilson_allocation_majorant_summable hlam hl (fun v => (P v).budget_nonneg hL T (u v)) _ _
    (fun _ _ => integral_nonneg fun _ => norm_nonneg _)
    (fun n f => (wilson_mixed_words_bound P hL T u f (hq n f) hΔ μ hmw hw).2)

/-- Insert any finite collection of unmarked local inverse identities
without introducing a hopping power or an untested circulation. The
resulting integrable outer weight can be used in the mixed-word bound. -/
theorem wilson_local_identities_weight {J : Type*} [Fintype J] (φ ψ : J → WilsonPacket) {Δ : J → Z → OSFourSpace}
    (hΔ : ∀ j, Measurable (Δ j)) (μ : Measure Z) [SFinite μ] {w : Z → ℂ} (hmw : Measurable w) (hw : Integrable w μ) :
    let F := fun j z p => wilsonPacketPair (φ j) (ψ j) p (Δ j z) 1
    let ν := Measure.pi (fun _ : J => (volume : Measure OSFourSpace))
    Measurable (wilsonJointTraces w F) ∧ Integrable (wilsonJointTraces w F) (μ.prod ν) ∧
      (∫ t, ‖wilsonJointTraces w F t‖ ∂μ.prod ν) ≤ (∫ z, ‖w z‖ ∂μ) * ∏ j, ((φ j).cost+(ψ j).cost)/2 := by
  dsimp only
  have hm (j : J) : Measurable (fun t : Z × OSFourSpace => wilsonPacketPair (φ j) (ψ j) t.2 (Δ j t.1) 1) :=
    wilson_packet_pair_measurable _ _ measurable_snd ((hΔ j).comp measurable_fst) measurable_const
  let F := fun j z p => wilsonPacketPair (φ j) (ψ j) p (Δ j z) 1
  refine ⟨wilson_joint_measurable (F := F) hmw hm,?_⟩
  exact wilson_joint_traces_bound (F := F) μ hmw hw hm
    (fun j z => (wilson_open_identity (φ j) (ψ j) (Δ j z)).1) (fun j => ((φ j).cost+(ψ j).cost)/2)
    (fun j z => (wilson_open_identity (φ j) (ψ j) (Δ j z)).2)

end UV
