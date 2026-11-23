import UV.ContinueCayleyMatrix
import UV.ContinueCayleySlot

/-! The genuine finite family of signed-energy Borel measures from a single
self-adjoint dilation. All entries are polarized compact spectral measures
pushed by the same real-valued inverse Cayley coordinate. -/

noncomputable section
open MeasureTheory Set Filter ContinuousLinearMap Matrix
open scoped Topology InnerProductSpace ComplexConjugate ComplexOrder ENNReal Matrix
namespace UV.SectorPlane

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private abbrev rep (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) :=
  cfcHom (R:=ℂ) (closing_cayley_normal K hK)

private def energyCoord (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K)
    (t : spectrum ℂ (closingCayley K hK)) : ℝ := closingCayleyEnergy t

private theorem energy_measurable (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) :
    Measurable (energyCoord K hK) := by unfold energyCoord closingCayleyEnergy; fun_prop

/-- The Cayley law of a domain vector also equals the ordinary compact
state of that same vector pushed forward to the signed energy line. The
weighted state of (K+i)x is identified before this pushforward. -/
theorem closing_domain_slot_pushforward (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (x : K.domain) :
    closingDomainSlotLaw K hK x =
      (closingCompactState (rep K hK) (x:H)).map (energyCoord K hK) := by
  let X := spectrum ℂ (closingCayley K hK)
  let w (t : X) := ENNReal.ofReal (closingCayleyWeight t)
  let ν := closingCompactState (rep K hK) (K x+Complex.I • (x:H))
  let μ := ν.withDensity w
  have hμ : IsFiniteMeasure μ := by
    constructor
    have h := measure_lt_top (closingDomainSlotLaw K hK x) univ
    change (μ.map (energyCoord K hK)) univ < ⊤ at h
    simpa only [Measure.map_apply (energy_measurable K hK) MeasurableSet.univ,preimage_univ] using h
  change μ.map _ = _
  congr 1
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let g : C(X,ℂ) := ⟨fun t => (f t:ℂ),Complex.continuous_ofReal.comp f.continuous⟩
  have hw : Measurable w := by dsimp only [w,closingCayleyWeight]; fun_prop
  have he : (∫ t, g t ∂μ) = ∫ t, g t ∂closingCompactState (rep K hK) (x:H) := by
    rw [show μ=ν.withDensity w from rfl,integral_withDensity_eq_integral_toReal_smul hw (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    have hn (t : X) : 0 ≤ closingCayleyWeight t := by unfold closingCayleyWeight; positivity
    simp only [w,ENNReal.toReal_ofReal (hn _),Complex.real_smul]
    rw [closing_compact_state_integral]
    exact closing_domain_weighted_compact_test K hK x g
  apply Complex.ofReal_injective
  rw [←integral_complex_ofReal, ←integral_complex_ofReal]
  exact he

variable {ι : Type*} [Fintype ι]

def closingDomainMatrixMeasure (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (x : ι → K.domain) :
    Matrix ι ι (ComplexMeasure ℝ) := fun i j =>
  (closingCompactPolar (rep K hK) (x i:H) (x j:H)).val.1.map (energyCoord K hK)

theorem closing_domain_matrix_quadratic (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (x : ι → K.domain)
    (v : ι → ℂ) (s : Set ℝ) (hs : MeasurableSet s) :
    (∑ i, ∑ j, (conj (v i)*v j)*closingDomainMatrixMeasure K hK x i j s) =
      ((closingDomainSlotLaw K hK (∑ i,v i • x i)).real s:ℂ) := by
  let p (i : ι) := (x i:H)
  let t := energyCoord K hK ⁻¹' s
  have hm : MeasurableSet t := energy_measurable K hK hs
  have h := closing_polar_quadratic_set (fun y => closingPositivePairing (closingCompactState (rep K hK) y))
    (fun f => rep K hK f) (fun y f => closing_compact_state_integral (rep K hK) y f) p v t
  unfold closingDomainMatrixMeasure
  simp_rw [VectorMeasure.map_apply _ (energy_measurable K hK) hs]
  rw [closing_domain_slot_pushforward, map_measureReal_apply (energy_measurable K hK) hs]
  apply h.trans
  change (closingCompactState (rep K hK) (∑ i,v i • p i)).toSignedMeasure.toComplexMeasure 0 t = _
  simp only [SignedMeasure.toComplexMeasure_apply,Measure.toSignedMeasure_apply_measurable hm,
    VectorMeasure.zero_apply,Submodule.coe_sum,Submodule.coe_smul_of_tower]
  rfl

theorem closing_domain_matrix_positive (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (x : ι → K.domain)
    (s : Set ℝ) (hs : MeasurableSet s) :
    Matrix.PosSemidef (fun i j => closingDomainMatrixMeasure K hK x i j s) := by
  apply closing_matrix_positive_of_quadratic
  exact fun v => ⟨_,measureReal_nonneg,closing_domain_matrix_quadratic K hK x v s hs⟩

end UV.SectorPlane
