import UV.ContinueNormalCoverFourier
import UV.ContinueWilsonOpenChain

/-! Normal-circle open lines with square-integrable carrier endpoint
packets in a joint hard photon graph. All normal windings are summed. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter UV.SectorPlane

namespace UV

abbrev NormalOpenVariables (r : ℕ) := (Fin r → ℝ) × OSFourSpace

def normalPacketWord {r : ℕ} (m D : ℝ) (u : Fin r → UnitVector OSFourSpace) (φ ψ : WilsonPacket)
    (Δ : OSFourSpace) (p : NormalOpenVariables r → Fin (r+1) → OSFourSpace) (t : NormalOpenVariables r) : ℂ :=
  wilsonPacketPair φ ψ t.2 Δ (normalOpenDiracWord normalCoverGamma5 m D u (p t) t.1)

theorem normal_packet_word_measure {r : ℕ} {m : ℝ} (hm : 0 < m) (D : ℝ) (u : Fin r → UnitVector OSFourSpace)
    (φ ψ : WilsonPacket) (Δ : OSFourSpace) (p : NormalOpenVariables r → Fin (r+1) → OSFourSpace)
    (hp : ∀ j, Measurable (p · j)) (σ : Measure OSFourSpace) [SFinite σ] (B : ℝ)
    (hB : let Y := fun k : OSFourSpace => (‖φ.value (k+Δ)‖^2+‖ψ.value k‖^2)/2
      Integrable Y σ ∧ (∫ k, Y k ∂σ) ≤ B) :
    let F := normalPacketWord m D u φ ψ Δ p
    Integrable F (volume.prod σ) ∧ (∫ t, ‖F t‖ ∂volume.prod σ) ≤ (2^(r+1)*Real.exp (-(m/2)*|D|)*(4/m)^r)*B := by
  let M := (2:ℝ)^(r+1)*Real.exp (-(m/2)*|D|)
  let g := fun t : ℝ => Real.exp (-(m/2)*|t|)
  let X := fun x : Fin r → ℝ => M*∏ j, g (x j)
  let Y := fun k : OSFourSpace => (‖φ.value (k+Δ)‖^2+‖ψ.value k‖^2)/2
  have hg := normal_open_laplace_mass hm
  have hX : Integrable X := (Integrable.fintype_prod (fun _ : Fin r => hg.1)).const_mul M
  have hXY : Integrable (fun t : NormalOpenVariables r => X t.1*Y t.2) (volume.prod σ) := hX.mul_prod hB.1
  have hF : Measurable (normalPacketWord m D u φ ψ Δ p) := wilson_packet_pair_measurable _ _ measurable_snd measurable_const
    (normal_open_word_args_measurable normalCoverGamma5 m D u hp (fun i => (measurable_pi_apply i).comp measurable_fst))
  have hb (t : NormalOpenVariables r) : ‖normalPacketWord m D u φ ψ Δ p t‖ ≤ X t.1*Y t.2 :=
    (wilson_packet_pair_bound _ _ _ _ _).trans (mul_le_mul_of_nonneg_right
      (normal_open_dirac_majorant normalCoverGamma5 normal_cover_gamma_norm hm D u (p t) t.1) (by positivity))
  have hi := hXY.mono' hF.aestronglyMeasurable (Eventually.of_forall hb)
  refine ⟨hi,(integral_mono hi.norm hXY hb).trans ?_⟩
  rw [integral_prod_mul X Y]
  dsimp only [X]
  rw [integral_const_mul,integral_fintype_prod_volume_eq_pow g]
  simp only [Fintype.card_fin,g,hg.2,M]
  exact mul_le_mul_of_nonneg_left hB.2 (by positivity)

theorem normal_packet_word_bound {r : ℕ} {m : ℝ} (hm : 0 < m) (D : ℝ) (u : Fin r → UnitVector OSFourSpace)
    (φ ψ : WilsonPacket) (Δ : OSFourSpace) (p : NormalOpenVariables r → Fin (r+1) → OSFourSpace)
    (hp : ∀ j, Measurable (p · j)) :
    let F := normalPacketWord m D u φ ψ Δ p
    Integrable F ∧ (∫ t, ‖F t‖) ≤ (2^(r+1)*Real.exp (-(m/2)*|D|)*(4/m)^r)*((φ.cost+ψ.cost)/2) :=
  normal_packet_word_measure hm D u φ ψ Δ p hp volume _ ⟨(wilson_packet_budget φ ψ Δ).1,(wilson_packet_budget φ ψ Δ).2.le⟩

variable {V Z : Type*} [Fintype V] [MeasurableSpace Z]

/-- A different open line at each vertex, with its own two packets, number
of normal increments and integer winding. Photon variables may jointly
shift every endpoint and every segment momentum. -/
theorem normal_open_graph_integral {m L : ℝ} (hm : 0 < m) (hL : 0 < L)
    (r : V → ℕ) (u : (v : V) → Fin (r v) → UnitVector OSFourSpace) (φ ψ : V → WilsonPacket)
    (z z' : V → ℝ) (hz : ∀ v, z v ∈ Icc 0 L) (hz' : ∀ v, z' v ∈ Icc 0 L)
    (Δ : V → Z → OSFourSpace) (hΔ : ∀ v, Measurable (Δ v))
    (p : (v : V) → ℤ → Z → NormalOpenVariables (r v) → Fin (r v+1) → OSFourSpace)
    (hp : ∀ v w j, Measurable (fun t : Z × NormalOpenVariables (r v) => p v w t.1 t.2 j))
    (μ : Measure Z) [SFinite μ] {W : Z → ℂ} (hW : Measurable W) (hiW : Integrable W μ) :
    let ν := Measure.pi (fun v => (volume : Measure (NormalOpenVariables (r v))))
    let F := fun (w : V → ℤ) => wilsonJointFactors W (fun v q =>
      normalPacketWord m (z' v-z v+(w v:ℝ)*L) (u v) (φ v) (ψ v) (Δ v q) (p v (w v) q))
    (∀ w, Integrable (F w) (μ.prod ν)) ∧ Summable (fun w : V → ℤ => ∫ t, ‖F w t‖ ∂μ.prod ν) := by
  let D := fun (v : V) (w : ℤ) => z' v-z v+(w:ℝ)*L
  let K := fun v => ((2:ℝ)^(r v+1)*(4/m)^(r v))*(((φ v).cost+(ψ v).cost)/2)
  let g := fun w : ℤ => Real.exp (m*L/2)*Real.exp (-(m*L/2)*|(w:ℝ)|)
  have hK (v) : 0 ≤ K v := by dsimp [K]; have := (φ v).cost_nonneg; have := (ψ v).cost_nonneg; positivity
  have hg (w) : 0 ≤ g w := by dsimp [g]; positivity
  obtain ⟨hsg,hw⟩ := normal_winding_majorant hm hL
  have hd (v : V) : |z' v-z v| ≤ L := abs_le.mpr ⟨by linarith [(hz v).2,(hz' v).1],by linarith [(hz v).1,(hz' v).2]⟩
  let F := fun (w : V → ℤ) v q => normalPacketWord m (D v (w v)) (u v) (φ v) (ψ v) (Δ v q) (p v (w v) q)
  have hB (w : V → ℤ) := wilson_joint_factors_bound (F := F w) μ hW hiW
    (fun v => wilson_packet_pair_measurable _ _ (measurable_snd.comp measurable_snd) ((hΔ v).comp measurable_fst)
      (normal_open_word_args_measurable normalCoverGamma5 m (D v (w v)) (u v) (hp v (w v))
      (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd))))
    (fun v q => (normal_packet_word_bound hm (D v (w v)) (u v) (φ v) (ψ v) (Δ v q) (p v (w v) q)
      (fun j => (hp v (w v) j).comp (measurable_const.prodMk measurable_id))).1)
    (fun v => K v * g (w v)) (fun v q => by
      apply (normal_packet_word_bound hm (D v (w v)) (u v) (φ v) (ψ v) (Δ v q) (p v (w v) q)
        (fun j => (hp v (w v) j).comp (measurable_const.prodMk measurable_id))).2.trans
      calc _ = K v * Real.exp (-(m/2)*|D v (w v)|) := by dsimp [K]; ring
           _ ≤ _ := mul_le_mul_of_nonneg_left (hw _ (hd v) _) (hK v))
  have hs := wilson_summable_product (fun v k => mul_nonneg (hK v) (hg k)) (fun v => hsg.mul_left (K v))
  exact ⟨fun w => (hB w).1,Summable.of_nonneg_of_le (fun w => integral_nonneg fun _ => norm_nonneg _)
    (fun w => (hB w).2) (hs.mul_left _)⟩

/-- In the four-dimensional isometric readout, ordinary hard A4 Maxwell
photons can be sewn among any finite number of open normal lines. Each
carrier propagator takes the tested momentum plus its routed transfer.
The cutoff acts only on the dependent tree factors. -/
theorem normal_hard_open_graph {C D ι : Type*} [Fintype C] [Fintype D] [Fintype ι]
    {m L ρ : ℝ} (hm : 0 < m) (hL : 0 < L) (hρ : 0 < ρ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (chord : C → WilsonPhotonPolarizations) (tree : D → WilsonPhotonPolarizations)
    (route : (C → OSFourSpace) → D → OSFourSpace) (hr : ∀ i, Measurable (route · i))
    (r : V → ℕ) (u : (v : V) → Fin (r v) → UnitVector OSFourSpace) (φ ψ : V → WilsonPacket)
    (z z' : V → ℝ) (hz : ∀ v, z v ∈ Icc 0 L) (hz' : ∀ v, z' v ∈ Icc 0 L)
    (Δ : V → (C → OSFourSpace) → OSFourSpace) (hΔ : ∀ v, Measurable (Δ v))
    (shift : (v : V) → (C → OSFourSpace) → Fin (r v+1) → OSFourSpace) (hs : ∀ v j, Measurable (shift v · j)) :
    let μ := Measure.pi (fun _ : C => (volume : Measure OSFourSpace))
    let ν := Measure.pi (fun v => (volume : Measure (NormalOpenVariables (r v))))
    let W := fun q => (wilsonHardPhotonProduct ρ (wilsonShellPhotonForm L T) chord tree route q : ℂ)
    let F := fun (w : V → ℤ) => wilsonJointFactors W (fun v q =>
      normalPacketWord m (z' v-z v+(w v:ℝ)*L) (u v) (φ v) (ψ v) (Δ v q) (fun t j => t.2+shift v q j))
    (∀ w, Integrable (F w) (μ.prod ν)) ∧ Summable (fun w : V → ℤ => ∫ t, ‖F w t‖ ∂μ.prod ν) :=
  normal_open_graph_integral hm hL r u φ ψ z z' hz hz' Δ hΔ (fun v _ q t j => t.2+shift v q j)
    (fun v _ j => (measurable_snd.comp measurable_snd).add ((hs v j).comp measurable_fst)) _
    (Complex.continuous_ofReal.measurable.comp (wilson_hard_product_measurable ρ (wilson_shell_form_continuous L T) chord tree hr))
    ((wilson_hard_product_integrable hL hρ T chord tree hr).ofReal (𝕜 := ℂ))

end UV
