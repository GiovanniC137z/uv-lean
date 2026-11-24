import UV.ContinueFourierHoppingLoop
import UV.ContinueOrderedEnvelopeSewing

/-! Each instantaneous photon has two allocated scalar marks, at opposite
sector frequencies. Their decay completes the original instantaneous
spatial factor. The transverse factor already contains its full denominator. -/

noncomputable section

open MeasureTheory

namespace UV.SectorPlane

def OrderedPhotonKind.softLine (kind : OrderedPhotonKind) (a : ℝ) (q : OSFourSpace) : ℝ :=
  let p := (orderedPhotonChart q).2
  match kind with
  | .transverse => orderedTransverseEnvelope a (orderedPhotonChart q)
  | .coulomb => Real.exp (-(2*a*‖p‖))*(min 1 ‖p‖)^2 / ‖p‖^2

def OrderedPhotonKind.carrierWeight (kind : OrderedPhotonKind) (q : OSFourSpace) : ℝ :=
  match kind with
  | .transverse => 1
  | .coulomb => ((1+|q 0|)⁻¹)^2

theorem OrderedPhotonKind.measurable_softLine (kind : OrderedPhotonKind) (a : ℝ) :
    Measurable (kind.softLine a) := by
  cases kind
  · exact (measurable_orderedTransverseEnvelope a).comp orderedPhotonChart.measurable
  · exact (show Measurable (fun p : Spatial => Real.exp (-(2*a*‖p‖))*(min 1 ‖p‖)^2 / ‖p‖^2) by
      fun_prop).comp (measurable_snd.comp orderedPhotonChart.measurable)

theorem OrderedPhotonKind.softLine_nonneg (kind : OrderedPhotonKind) (a : ℝ) (q : OSFourSpace) :
    0 ≤ kind.softLine a q := by
  cases kind
  · exact (ordered_envelopes_nonneg a _).1
  · unfold softLine
    positivity

theorem OrderedPhotonKind.softLine_carrierWeight (kind : OrderedPhotonKind) (a : ℝ) (q : OSFourSpace) :
    kind.softLine a q * kind.carrierWeight q = kind.envelope a q := by
  cases kind
  · exact mul_one _
  · simp only [softLine,carrierWeight,envelope,orderedCoulombEnvelope,ordered_photon_chart_time]
    simp [div_eq_mul_inv,mul_assoc,mul_comm]

/-- Individual matrix component of the transverse projector or identity in
the instantaneous channel. Unit basis directions are fixed in the sector. -/
def OrderedPhotonKind.projector (kind : OrderedPhotonKind) (i j : Fin 3) (q : OSFourSpace) : ℝ :=
  match kind with
  | .transverse => orderedSpatialProjector i j (orderedPhotonChart q).2
  | .coulomb => 1

theorem OrderedPhotonKind.measurable_projector (kind : OrderedPhotonKind) (i j : Fin 3) :
    Measurable (kind.projector i j) := by
  cases kind
  · exact (measurable_orderedSpatialProjector i j).comp (measurable_snd.comp orderedPhotonChart.measurable)
  · exact measurable_const

theorem OrderedPhotonKind.projector_bound (kind : OrderedPhotonKind) (i j : Fin 3) (q : OSFourSpace) :
    |kind.projector i j q| ≤ 1 := by
  cases kind
  · exact ordered_spatial_projector_bound _ _ _
  · exact (abs_one : |(1:ℝ)|=1).le

variable {V E : Type*} [Fintype V] [Fintype E] {N : V → ℕ}

abbrev HoppingFourierMark (L : (v : V) → HoppingFourierLoop (N v)) :=
  (v : V) × (j : Fin (N v+2)) × Fin ((L v).time j).marks.length

abbrev HoppingScalarEnd (kind : E → OrderedPhotonKind) := {e : E // kind e = .coulomb} × Bool

def hoppingScalarFrequency (kind : E → OrderedPhotonKind) (q : E → OSFourSpace) (k : HoppingScalarEnd kind) : ℝ :=
  if k.2 then q k.1 0 else -(q k.1 0)

theorem hopping_weight_by_index (xs : List ℝ) :
    hoppingWeight xs = ∏ i : Fin xs.length, (1+|xs.get i|)⁻¹ := by
  unfold hoppingWeight
  conv_lhs => rw [←List.ofFn_get xs]
  simp only [List.map_ofFn,List.prod_ofFn,Function.comp_def]

/-- A bijection from the actual scalar positions to the two endpoint labels
of every instantaneous edge allows arbitrary allocation among carrier slots.
Both orientations have the same absolute-frequency weight. -/
theorem hopping_fourier_routed_weights (L : (v : V) → HoppingFourierLoop (N v))
    (kind : E → OrderedPhotonKind) (q : E → OSFourSpace)
    (R : HoppingFourierMark L ≃ HoppingScalarEnd kind)
    (hr : ∀ i : HoppingFourierMark L, ((L i.1).time i.2.1).marks.get i.2.2 = hoppingScalarFrequency kind q (R i)) :
    (∏ v, (L v).weight) = ∏ e, (kind e).carrierWeight (q e) := by
  classical
  let w := fun i : HoppingScalarEnd kind => (1+|hoppingScalarFrequency kind q i|)⁻¹
  have h : (∏ v, (L v).weight) = ∏ i : HoppingScalarEnd kind, w i := by
    rw [←R.prod_comp w]
    simp only [HoppingFourierLoop.weight,HoppingCarrierSlot.weight,hopping_weight_by_index,Fintype.prod_sigma]
    exact Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun j _ =>
      Finset.prod_congr rfl fun i _ => by simp only [w,hr ⟨v,j,i⟩]
  rw [h,Fintype.prod_prod_type,← Fintype.prod_subtype_mul_prod_subtype (fun e => kind e = .coulomb)]
  have hrest : (∏ e : {e : E // ¬kind e=.coulomb}, (kind e).carrierWeight (q e))=1 := by
    apply Finset.prod_eq_one
    rintro ⟨e,he⟩ _
    cases hk : kind e
    · rfl
    · exact (he hk).elim
  rw [hrest,mul_one]
  apply Finset.prod_congr rfl
  intro e _
  simp [w,hoppingScalarFrequency,e.property,OrderedPhotonKind.carrierWeight,sq]

end UV.SectorPlane
