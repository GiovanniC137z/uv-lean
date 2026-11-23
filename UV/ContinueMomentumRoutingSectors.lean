import UV.ContinueMomentumRoutingWeighted

/-! Keep the external transfer of every independently tested open line
in the normal-circle graph estimate, also after summing all windings. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter

namespace UV

variable {L m : ℝ}

def NormalChargedSector.externalWeight (P : NormalChargedSector L) (Δ : OSFourSpace) : ℝ :=
  match P with
  | .line .. => normalPacketWeight Δ
  | _ => 1

theorem NormalChargedSector.externalWeight_pos (P : NormalChargedSector L) (Δ : OSFourSpace) : 0 < P.externalWeight Δ := by
  cases P <;> first | exact zero_lt_one | exact momentum_packet_weight_pos Δ

theorem NormalChargedSector.externalWeight_measurable (P : NormalChargedSector L) : Measurable P.externalWeight := by
  cases P <;> first | exact measurable_const | exact ((measurable_const.add measurable_norm).pow_const 6).inv

def NormalChargedSector.uniformBudget (P : NormalChargedSector L) (m : ℝ) (σ : Measure OSFourSpace) : Prop :=
  ∃ g : ℤ → ℝ, (∀ w, 0 ≤ g w) ∧ Summable g ∧ ∀ w Δ s,
    Integrable (P.amplitude m w Δ s) (P.measure σ) ∧ (∫ t, ‖P.amplitude m w Δ s t‖ ∂P.measure σ) ≤ g w

theorem NormalChargedSector.external_budget (hm : 0 < m) (hL : 0 < L) (σ : Measure OSFourSpace) [SigmaFinite σ]
    (hσ : Integrable normalPacketWeight σ) (P : NormalChargedSector L) (ht : P.schwartzEndpoints) (hU : P.uniformBudget m σ) :
    ∃ g : ℤ → ℝ, (∀ w, 0 ≤ g w) ∧ Summable g ∧ ∀ w Δ s,
      Integrable (P.amplitude m w Δ s) (P.measure σ) ∧
        (∫ t, ‖P.amplitude m w Δ s t‖ ∂P.measure σ) ≤ g w*P.externalWeight Δ := by
  cases P with
  | winding | zero => simpa only [externalWeight,mul_one,uniformBudget] using hU
  | line r u φ ψ z z' =>
    obtain ⟨f,g,rfl,rfl⟩ := ht
    obtain ⟨C,hC,h⟩ := momentum_open_word_decay hm u σ hσ f g
    obtain ⟨hg,hw⟩ := normal_winding_majorant hm hL
    refine ⟨fun w => C*(Real.exp (m*L/2)*Real.exp (-(m*L/2)*|(w:ℝ)|)),fun w => by positivity,hg.mul_left C,?_⟩
    intro w Δ s
    have h' := h (z'.val-z.val+(w:ℝ)*L) Δ (fun t j => t.2+s j) (fun j => measurable_snd.add_const (s j))
    have hd : |z'.val-z.val| ≤ L := abs_le.mpr ⟨by linarith [z.property.2,z'.property.1],by linarith [z.property.1,z'.property.2]⟩
    exact ⟨h'.1,h'.2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hw _ hd w) hC) (momentum_packet_weight_pos Δ).le)⟩

variable {V Z : Type*} [Fintype V] [MeasurableSpace Z]

theorem momentum_sector_tested_graph (hm : 0 < m) (hL : 0 < L) (σ : Measure OSFourSpace) [SigmaFinite σ]
    (hσ : Integrable normalPacketWeight σ) (P : V → NormalChargedSector L) (ht : ∀ v, (P v).schwartzEndpoints)
    (hU : ∀ v, (P v).uniformBudget m σ)
    (s : (V → ℤ) → (v : V) → Z → Fin (P v).segments → OSFourSpace) (hs : ∀ w v j, Measurable (s w v · j))
    (Δ : V → Z → OSFourSpace) (hd : ∀ v, Measurable (Δ v)) (μ : Measure Z) [SFinite μ] (W : Z → ℂ) (hW : Measurable W)
    (hJ : Integrable (fun z => ‖W z‖*∏ v,(P v).externalWeight (Δ v z)) μ) :
    NormalGraphAbsolute σ μ m P s Δ W := by
  classical
  choose g hg hsum h using fun v => (P v).external_budget hm hL σ hσ (ht v) (hU v)
  exact momentum_weighted_joint_windings (fun v => (P v).measure σ) μ hW
    (fun w v => (P v).amplitude_measurable m (w v) (hs w v) (hd v))
    (fun w v z => (h v (w v) (Δ v z) (s w v z)).1) _ hJ g hg hsum
    (fun w v z => (h v (w v) (Δ v z) (s w v z)).2)

theorem NormalChargedSector.volume_uniformBudget (hm : 0 < m) (hL : 0 < L) (P : NormalChargedSector L) : P.uniformBudget m volume := by
  simpa [uniformBudget,P.measure_volume] using P.amplitude_budget hm hL

theorem NormalChargedSector.lattice_uniformBudget (b : NormalReciprocalBasis) (hm : 0 < m) (hL : 0 < L)
    (P : NormalChargedSector L) (ht : P.schwartzEndpoints) : P.uniformBudget m (normalLatticeMeasure b) :=
  P.amplitude_measure_budget hm hL _ (fun _ ha => normal_lattice_exponential_shifts b ha)
    (fun _ hr => normal_lattice_power_shifts b hm hr) (P.lattice_endpoint_bound b ht)

end UV
