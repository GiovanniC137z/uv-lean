import UV.FormalBRST
import Mathlib.RingTheory.PowerSeries.PiTopology

/-! The formal coefficient completion carries its actual product topology.
Continuity of coefficientwise BRST maps is derived from the coefficient
map, and does not impose a Banach norm on canonical functional derivatives. -/

noncomputable section
open scoped PowerSeries.WithPiTopology

namespace UV

theorem formalLinearMap_continuous
    {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    [TopologicalSpace A] [TopologicalSpace B]
    (L : A →ₗ[ℚ] B) (hL : Continuous L) : Continuous (formalLinearMap L) := by
  apply continuous_pi
  intro d
  change Continuous (fun f : PowerSeries A => L (f (Finsupp.single () (d ()))))
  exact hL.comp (continuous_apply _)

theorem formalGradedDerivative_continuous
    {A : Type*} [Ring A] [Algebra ℚ A] [TopologicalSpace A]
    {σ : GradingInvolution A} {odd : Bool} (D : GradedDerivative σ odd)
    (hD : Continuous D.d) : Continuous (formalGradedDerivative D).d :=
  formalLinearMap_continuous D.d hD

theorem formalGrading_continuous
    {A : Type*} [Ring A] [Algebra ℚ A] [TopologicalSpace A]
    (σ : GradingInvolution A) (hσ : Continuous σ.parity) : Continuous (formalGrading σ).parity := by
  apply continuous_pi
  intro d
  change Continuous (fun f : PowerSeries A => σ.parity (f d))
  exact hσ.comp (continuous_apply _)

end UV
