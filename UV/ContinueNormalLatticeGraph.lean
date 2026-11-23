import UV.ContinueNormalLatticePackets
import UV.ContinueNormalProtectedGraph

/-! Joint reciprocal-lattice integrals for mixed charged components.
An open line uses the values of smooth carrier spinor tests at the modes.
The normal increments and normal-cover frequency stay continuous. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter
open scoped SchwartzMap

namespace UV

variable {L : ℝ}

def NormalChargedSector.schwartzEndpoints : NormalChargedSector L → Prop
  | .winding .. | .zero .. => True
  | .line _ _ φ ψ _ _ => ∃ f g : 𝓢(OSFourSpace,WilsonPacketSpinor), φ = normalSchwartzPacket f ∧ ψ = normalSchwartzPacket g

theorem NormalChargedSector.lattice_endpoint_bound (b : NormalReciprocalBasis) (P : NormalChargedSector L)
    (ht : P.schwartzEndpoints) : P.endpointBound (normalLatticeMeasure b) := by
  cases P with
  | winding | zero => trivial
  | line r u φ ψ z z' =>
    obtain ⟨f,g,rfl,rfl⟩ := ht
    obtain ⟨A,hA,hf⟩ := normal_schwartz_lattice_shifts b f
    obtain ⟨B,hB,hg⟩ := normal_schwartz_lattice_shifts b g
    have hg' : Integrable (fun k => ‖g k‖^2) (normalLatticeMeasure b) ∧ (∫ k, ‖g k‖^2 ∂normalLatticeMeasure b) ≤ B := by
      simpa only [add_zero] using hg 0
    refine ⟨(A+B)/2,by positivity,fun Δ => ⟨((hf Δ).1.add hg'.1).div_const 2,?_⟩⟩
    change (∫ k, (‖f (k+Δ)‖^2+‖g k‖^2)/2 ∂normalLatticeMeasure b) ≤ (A+B)/2
    rw [integral_div,integral_add (hf Δ).1 hg'.1]
    linarith [(hf Δ).2,hg'.2]

/-- The absolute winding sum and the joint charged integrations on a
finite torus for any absolutely integrable routed outer photon weight. -/
theorem normal_lattice_protected_graph_integral {V Z : Type*} [Fintype V] [MeasurableSpace Z]
    (b : NormalReciprocalBasis) {m : ℝ} (hm : 0 < m) (hL : 0 < L) (P : V → NormalChargedSector L)
    (hP : ∀ v, (P v).schwartzEndpoints)
    (s : (V → ℤ) → (v : V) → Z → Fin (P v).segments → OSFourSpace)
    (hs : ∀ w v j, Measurable (s w v · j)) (Δ : V → Z → OSFourSpace) (hΔ : ∀ v, Measurable (Δ v))
    (μ : Measure Z) [SFinite μ] {W : Z → ℂ} (hW : Measurable W) (hiW : Integrable W μ) :
    let ν := Measure.pi (fun v => (P v).measure (normalLatticeMeasure b))
    let F := fun w : V → ℤ => wilsonJointFactors W (fun v q => (P v).amplitude m (w v) (Δ v q) (s w v q))
    (∀ w, Integrable (F w) (μ.prod ν)) ∧ Summable (fun w => ∫ t, ‖F w t‖ ∂μ.prod ν) :=
  normal_measured_graph_integral (normalLatticeMeasure b) P (fun v => (P v).amplitude_measure_budget hm hL _
    (fun _ ha => normal_lattice_exponential_shifts b ha) (fun _ hr => normal_lattice_power_shifts b hm hr)
    ((P v).lattice_endpoint_bound b (hP v))) s hs Δ hΔ μ hW hiW

end UV
