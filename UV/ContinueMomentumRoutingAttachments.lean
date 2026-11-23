import UV.ContinueMomentumRoutingTestedGraph

/-! Attach each exterior photon at its charged mark and each signed
endpoint difference at its unique open path. Overall conservation and
the integrability of the actual product of tests follow in these coordinates. -/

noncomputable section

open Classical Finset MeasureTheory MeasureTheory.Measure UV.SectorPlane
open scoped SchwartzMap

namespace UV

variable {V E J A : Type*} [Fintype V] [Fintype E] [Fintype J] [AddCommGroup A]
variable {L : ℝ} {P : V → NormalChargedSector L} {G : MomentumNetwork V E}

def NormalChargedSector.isOpen : NormalChargedSector L → Prop
  | .line .. => True
  | _ => False

abbrev MomentumOpen (P : V → NormalChargedSector L) := {v : V // (P v).isOpen}

theorem momentum_open_endpoint (P : NormalChargedSector L) (a : A) :
    P.endpointTransfer a = if P.isOpen then a else 0 := by
  cases P <;> simp [NormalChargedSector.endpointTransfer,NormalChargedSector.isOpen]

theorem momentum_open_weight (P : NormalChargedSector L) (k : OSFourSpace) :
    P.externalWeight k = if P.isOpen then normalPacketWeight k else 1 := by
  cases P <;> simp [NormalChargedSector.externalWeight,NormalChargedSector.isOpen]

structure MomentumExteriorAttachments (P : V → NormalChargedSector L) (J : Type*) (n : ℕ) where
  index : J ⊕ MomentumOpen P ≃ Fin (n+1)
  mark : J → ((v : V) × Fin (P v).markCount)
  photon : J → 𝓢(OSFourSpace,ℂ)

variable {n : ℕ} (B : MomentumExteriorAttachments P J n)

def MomentumExteriorAttachments.transfers (x : Fin n → A) (j : J ⊕ MomentumOpen P) := momentumExteriorTransfers x (B.index j)

def MomentumExteriorAttachments.marked (M : MomentumMarks G (fun v => (P v).markCount)) : NormalMarkedGraph G P (Fin n → A) A where
  marks := M
  external x v i := ∑ j : J, if B.mark j = ⟨v,i⟩ then B.transfers x (.inl j) else 0
  endpoint x v := if h : (P v).isOpen then -B.transfers x (.inr ⟨v,h⟩) else 0

omit [Fintype V] [Fintype E] [Fintype J] in
theorem MomentumExteriorAttachments.conserved_transfer (x : Fin n → A) [Fintype (J ⊕ MomentumOpen P)] : ∑ j,B.transfers x j = 0 :=
  (B.index.sum_comp (momentumExteriorTransfers x)).trans (momentum_exterior_conserved x)

private theorem momentum_open_sum {H : V → Prop} (f : Subtype H → A) :
    (∑ v, if h : H v then f ⟨v,h⟩ else 0) = ∑ v : Subtype H,f v := by
  classical
  have hn (v : {v // ¬ H v}) : (if h : H v.val then f ⟨v,h⟩ else (0:A)) = 0 := dif_neg v.property
  rw [←Fintype.sum_subtype_add_sum_subtype H]
  simp only [dif_pos (Subtype.property _),hn,Finset.sum_const_zero,add_zero]

private theorem momentum_open_prod {H : V → Prop} (f : Subtype H → ℝ) :
    (∏ v, if h : H v then f ⟨v,h⟩ else 1) = ∏ v : Subtype H,f v := by
  classical
  have hn (v : {v // ¬ H v}) : (if h : H v.val then f ⟨v,h⟩ else (1:ℝ)) = 1 := dif_neg v.property
  rw [←Fintype.prod_subtype_mul_prod_subtype H]
  simp only [dif_pos (Subtype.property _),hn,Finset.prod_const_one,mul_one]

omit [Fintype E] in
theorem MomentumExteriorAttachments.conserved (M : MomentumMarks G (fun v => (P v).markCount)) (x : Fin n → A) :
    ∑ v,(B.marked M).injection x v = 0 := by
  let F := fun (t : (v : V) × Fin (P v).markCount) => ∑ j : J, if B.mark j = t then B.transfers x (.inl j) else 0
  have h₁ : (∑ v, ∑ i, F ⟨v,i⟩) = ∑ j : J,B.transfers x (.inl j) := by
    rw [←Fintype.sum_sigma,Finset.sum_comm]
    simp
  have h₂ (v) : (P v).endpointTransfer ((B.marked M).endpoint x v) =
      if h : (P v).isOpen then -B.transfers x (.inr ⟨v,h⟩) else 0 := by
    rw [momentum_open_endpoint]
    by_cases h : (P v).isOpen <;> simp [marked,h]
  change ∑ v, ((∑ i, F ⟨v,i⟩) - (P v).endpointTransfer ((B.marked M).endpoint x v)) = 0
  rw [Finset.sum_sub_distrib,h₁]
  simp_rw [h₂]
  rw [momentum_open_sum (fun v : MomentumOpen P => -B.transfers x (.inr v)),Finset.sum_neg_distrib,sub_neg_eq_add]
  simpa only [Fintype.sum_sum_type] using B.conserved_transfer x

omit [Fintype V] [Fintype E] [Fintype J] in
theorem MomentumExteriorAttachments.transfer_measurable [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSub₂ A]
    (j : J ⊕ MomentumOpen P) : Measurable (fun x : Fin n → A => B.transfers x j) := by
  let i := B.index j
  change Measurable (fun x : Fin n → A => momentumExteriorTransfers x i)
  refine Fin.cases ?_ (fun t => ?_) i
  · exact measurable_const.sub (Finset.measurable_sum _ fun s _ => measurable_pi_apply s)
  · exact measurable_pi_apply t

omit [Fintype V] [Fintype E] in
theorem MomentumExteriorAttachments.external_measurable [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSub₂ A]
    (M : MomentumMarks G (fun v => (P v).markCount)) (v : V) (i : Fin (P v).markCount) : Measurable (fun x : Fin n → A => (B.marked M).external x v i) := by
  apply Finset.measurable_sum _ (fun j _ => ?_)
  by_cases h : B.mark j = ⟨v,i⟩ <;> simp only [h,ite_true,ite_false]
  · exact B.transfer_measurable (.inl j)
  · exact measurable_const

omit [Fintype V] [Fintype E] in
theorem MomentumExteriorAttachments.endpoint_measurable [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSub₂ A] [MeasurableNeg A]
    (M : MomentumMarks G (fun v => (P v).markCount)) (v : V) : Measurable (fun x : Fin n → A => (B.marked M).endpoint x v) := by
  by_cases h : (P v).isOpen
  · simpa only [marked,dif_pos h] using (B.transfer_measurable (A := A) (.inr ⟨v,h⟩)).neg
  · simp [marked,h]

def MomentumExteriorAttachments.scalar (j : A →+ OSFourSpace) (x : Fin n → A) : ℂ :=
  ∏ i, B.photon i (j (B.transfers x (.inl i)))

omit [Fintype V] [Fintype E] in
theorem MomentumExteriorAttachments.scalar_measurable [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSub₂ A]
    (j : A →+ OSFourSpace) (hj : Measurable j) : Measurable (B.scalar j) :=
  Finset.measurable_prod _ (fun i _ => (B.photon i).continuous.measurable.comp (hj.comp (B.transfer_measurable (.inl i))))

omit [Fintype E] in
theorem MomentumExteriorAttachments.test_weight (M : MomentumMarks G (fun v => (P v).markCount)) (j : A →+ OSFourSpace) (x : Fin n → A) :
    ‖B.scalar j x‖*(B.marked M).externalWeight j x =
      ∏ i, (Sum.elim (fun k => MomentumExternalTest.photon (B.photon k)) (fun _ : MomentumOpen P => .charged)
        (B.index.symm i)).weight (j (momentumExteriorTransfers x i)) := by
  classical
  let t := fun y : J ⊕ MomentumOpen P => Sum.elim (fun k => MomentumExternalTest.photon (B.photon k)) (fun _ : MomentumOpen P => .charged) y
  let f := fun i => (t (B.index.symm i)).weight (j (momentumExteriorTransfers x i))
  have he (v) : (P v).externalWeight (j ((P v).endpointTransfer ((B.marked M).endpoint x v))) =
      if h : (P v).isOpen then normalPacketWeight (j (B.transfers x (.inr ⟨v,h⟩))) else 1 := by
    rw [momentum_open_weight,momentum_open_endpoint]
    by_cases h : (P v).isOpen <;> simp [marked,h,normalPacketWeight]
  change ‖B.scalar j x‖ * ∏ v, (P v).externalWeight (j ((P v).endpointTransfer ((B.marked M).endpoint x v))) = ∏ i,f i
  simp_rw [he]
  rw [momentum_open_prod (fun v : MomentumOpen P => normalPacketWeight (j (B.transfers x (.inr v)))),← B.index.prod_comp f,Fintype.prod_sum_type]
  simp [scalar,f,t,transfers,MomentumExternalTest.weight,norm_prod]

omit [Fintype E] in
theorem MomentumExteriorAttachments.test_integrable [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSub₂ A]
    (M : MomentumMarks G (fun v => (P v).markCount)) (j : A →+ OSFourSpace) (hj : Measurable j)
    (σ : Measure A) [SigmaFinite σ] (hσ : Integrable (fun k => normalPacketWeight (j k)) σ) :
    Integrable (fun x : Fin n → A => ‖B.scalar j x‖*(B.marked M).externalWeight j x) (Measure.pi fun _ => σ) := by
  simp_rw [B.test_weight M]
  exact momentum_exterior_absolute j hj σ hσ _

end UV
