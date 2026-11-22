import UV.ContinuationVectorialPole
import UV.ContinuationCarrierReadout

/-! The branch action unit on a locked diamond and the corresponding
fixed carrier coefficient in the literal quotient. -/

noncomputable section

namespace UV.SectorPlane

open UV.Carrier

def branchActionCoefficient (ε : Evolution) : QuotientCarrier :=
  (evolutionSign ε : ℂ) • poleRoot

theorem branch_action_square (ε : Evolution) :
    branchActionCoefficient ε * branchActionCoefficient ε = 1 := by
  apply quotientCharacterEquiv.injective
  cases ε <;> simp [branchActionCoefficient, evolutionSign, poleRoot, generator]

/-- The fixed branch unit is constant for the scalar coefficient part of
a BRST operation whose action on the fixed carrier is zero. -/
theorem branch_action_BV_constant (ε : Evolution) (BR : QuotientCarrier →ₗ[ℂ] QuotientCarrier)
    (hcarrier : BR poleRoot = 0) : BR (branchActionCoefficient ε) = 0 := by
  simp [branchActionCoefficient, hcarrier]

theorem branch_action_scalar_recovered (ε : Evolution) (S_sc : QuotientCarrier) :
    branchActionCoefficient ε * (branchActionCoefficient ε * S_sc) = S_sc := by
  rw [← mul_assoc, branch_action_square, one_mul]

end UV.SectorPlane
