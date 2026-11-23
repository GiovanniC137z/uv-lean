import UV.MarkedPhotonSewing
import Mathlib.MeasureTheory.Integral.Pi

/-! Every completed Wick pairing has one independent photon variable per
edge and two labelled ends per edge. Marking either end extracts that
edge's variable and leaves the other variables in their original order.
A change of labeling includes crossed and nested pairings. -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators

namespace UV.MarkedPhoton

variable {X P : Type*} [MeasurableSpace X]

/-- A matching identifies the labelled ports with oriented edge ends.
Choosing their enumeration does not restrict the matching. -/
def markedPairLift {n : ℕ} (pairing : P ≃ Fin (n+1) × Fin 2) (i : P) :
    X × (Fin n → X) ≃ᵐ (Fin (n+1) → X) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) (pairing i).1).symm

theorem markedPairLift_apply {n : ℕ} (pairing : P ≃ Fin (n+1) × Fin 2) (i : P) (x : X) (y : Fin n → X) :
    (markedPairLift pairing i (x,y)) ((pairing i).1) = x ∧
    ∀ j, (markedPairLift pairing i (x,y)) ((pairing i).1.succAbove j) = y j := by
  change (pairing i).1.insertNth (α := fun _ => X) x y (pairing i).1 = x ∧ ∀ j, (pairing i).1.insertNth (α := fun _ => X) x y ((pairing i).1.succAbove j) = y j
  simp

theorem markedPairLift_preserving {n : ℕ} (pairing : P ≃ Fin (n+1) × Fin 2) (i : P)
    (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (markedPairLift pairing i) (μ.prod (Measure.pi (fun _ : Fin n => μ)))
      (Measure.pi (fun _ : Fin (n+1) => μ)) :=
  (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) (pairing i).1).symm

/-- Evaluate the signed symmetric kernel on its actual paired fields.
The map v supplies both oriented legs (including momentum inversion,
polarization factors or discrete component tests) from each independent
edge variable. -/
def wickParent {n : ℕ} (pairing : P ≃ Fin (n+1) × Fin 2) (kernel : (P → X) → ℝ)
    (v : Fin 2 → X → X) (covariance : X → ℝ) (p : Fin (n+1) → X) : ℝ :=
  kernel (fun i => v (pairing i).2 (p (pairing i).1)) * ∏ j, covariance (p j)

/-- The integrated measured mark leaves one edge variable open. Actual
complete-pair integrability implies integrability after taking the absolute
value of this signed marginal, for either end. -/
theorem marked_wick_parent_sewing {n : ℕ} (pairing : P ≃ Fin (n+1) × Fin 2)
    (kernel : (P → X) → ℝ) (v : Fin 2 → X → X) (covariance : X → ℝ)
    (μ : Measure X) [SigmaFinite μ] (i : P)
    (hParent : Integrable (wickParent pairing kernel v covariance) (Measure.pi (fun _ => μ))) :
    let mark := fun x : X => ∫ y, wickParent pairing kernel v covariance (markedPairLift pairing i (x,y))
      ∂Measure.pi (fun _ : Fin n => μ)
    Integrable mark μ ∧ (∫ x, ‖mark x‖ ∂μ) ≤ ∫ p, ‖wickParent pairing kernel v covariance p‖ ∂Measure.pi (fun _ => μ) := by
  let e := markedPairLift (X := X) pairing i
  let A := wickParent pairing kernel v covariance
  have he := markedPairLift_preserving pairing i μ
  have h := he.integrable_comp_of_integrable hParent
  refine ⟨h.integral_prod_left,?_⟩
  have hm := integral_mono h.integral_prod_left.norm h.integral_norm_prod_left
    (fun x => norm_integral_le_integral_norm (fun y => A (e (x,y))))
  have ht := he.integral_comp' (fun p => ‖A p‖)
  have hInt : Integrable (fun z : X × (Fin n → X) => ‖A (e z)‖) (μ.prod (Measure.pi (fun _ : Fin n => μ))) := h.norm
  rw [integral_prod _ hInt] at ht
  exact hm.trans_eq ht

/-- Sum over all physical pairings and over both labelled ends. This
constructs all measure-preserving marking charts from the pairings. -/
theorem marked_wick_continuum_trace {J : Type*} {n : ℕ} (s : Finset J)
    (pairing : J → Fin (2*(n+1)) ≃ Fin (n+1) × Fin 2)
    (kernel : J → (Fin (2*(n+1)) → X) → ℝ) (v : Fin 2 → X → X) (covariance : X → ℝ)
    (μ : Measure X) [SigmaFinite μ]
    (hParent : ∀ j ∈ s, Integrable (wickParent (pairing j) (kernel j) v covariance) (Measure.pi (fun _ => μ))) :
    let A := fun j => wickParent (pairing j) (kernel j) v covariance
    let ν := Measure.pi (fun _ : Fin n => μ)
    let M := fun x : X => ∑ j ∈ s, ∑ i : Fin (2*(n+1)), ∫ y, A j (markedPairLift (pairing j) i (x,y)) ∂ν
    Integrable M μ ∧ (∫ x, ‖M x‖ ∂μ) ≤ ∑ j ∈ s, (2*(n+1):ℕ) * ∫ p, ‖A j p‖ ∂Measure.pi (fun _ => μ) := by
  exact marked_sewing_absolute s (fun _ => 2*(n+1)) _ (fun j i => markedPairLift (pairing j) i)
    μ _ _ (fun j _ i => markedPairLift_preserving (pairing j) i μ) hParent

end UV.MarkedPhoton
