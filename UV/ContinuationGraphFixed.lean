import UV.ContinuationGraphOrders
import UV.ContinuationSectorPlane

/-! The completed action, locked geometry and prescribed evolution branch are
fixed at the type of the generated graph family. -/

noncomputable section
open MeasureTheory Set Real

namespace UV.ContinuationGraph

/-- A declaration for one completed action on one labelled sector copy.
Its Euclidean chart is the intrinsic four-dimensional one used by the graph
criteria. Neither the unit carrier nor the evolution branch is read off
from Euclidean loop momenta. -/
structure GraphDeclaration (E Action Support Infrared : Type) [NormedAddCommGroup E] where
  plane : SectorPlane.Plane E
  evolution : SectorPlane.Evolution
  completedAction : Action
  support : Support
  infrared : Infrared
  depth : ℝ
  depth_pos : 0 < depth

def GraphDeclaration.poleUnit {E Action Support Infrared : Type} [NormedAddCommGroup E]
    (D : GraphDeclaration E Action Support Infrared) : SectorPlane.UnitVector E :=
  D.plane.poleUnit

theorem GraphDeclaration.poleUnit_eq_carrier {E Action Support Infrared : Type} [NormedAddCommGroup E]
    (D : GraphDeclaration E Action Support Infrared) : D.poleUnit = D.plane.Ghat := rfl

theorem GraphDeclaration.poleUnit_norm {E Action Support Infrared : Type} [NormedAddCommGroup E]
    (D : GraphDeclaration E Action Support Infrared) : ‖(D.poleUnit : E)‖ = 1 :=
  D.poleUnit.property

/-- All finite orders of the declared action within the selected support,
plane, and evolution branch. The `Generated` family contains the graphs
of that declaration. A criterion presentation is supplied for each graph. -/
theorem fixed_sector_all_finite_orders
    {E Action Support Infrared P : Type} [NormedAddCommGroup E]
    (D : GraphDeclaration E Action Support Infrared)
    (Generated : GraphDeclaration E Action Support Infrared → ℕ → Type)
    (graph : ∀ n, Generated D n → ExpandedSourceGraph P) :
    ∀ n g, ∃ B : ℝ, 0 ≤ B ∧ ∀ p,
      Integrable ((graph n g).integrand p) (graph n g).measure ∧
      (∫ x, ‖(graph n g).integrand p x‖ ∂(graph n g).measure) ≤ B :=
  expanded_all_finite_orders graph

end UV.ContinuationGraph
