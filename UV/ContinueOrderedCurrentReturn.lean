import UV.ContinueOrderedCurrentPlane
import UV.ContinueOrderedHopPaths

/-! The currents entering the ordered-source estimate on the original
Gaussian hop and carrier-duration integration variables. -/

noncomputable section

open MeasureTheory Finset
open scoped RealInnerProductSpace

namespace UV.SectorPlane.OrderedTwoBandPath

variable {n : ℕ}

private def returnStep (d : Fin n → OrderedHopStep) (j : ℕ) : OrderedHopStep :=
  if h : j < n+1 then (Fin.cons (orderedHopClosingStep d) d : Fin (n+1) → OrderedHopStep) ⟨j,h⟩ else 0

private theorem return_step_fin (d : Fin n → OrderedHopStep) (j : Fin (n+1)) :
    returnStep d j = (Fin.cons (orderedHopClosingStep d) d : Fin (n+1) → OrderedHopStep) j := by simp [returnStep,j.isLt]

private def returnVertex (d : Fin n → OrderedHopStep) (j : ℕ) : OrderedHopStep :=
  ∑ i ∈ range j, returnStep d i

private theorem return_vertex_closes (d : Fin n → OrderedHopStep) :
    returnVertex d (n+1) = returnVertex d 0 := by
  simp only [returnVertex,range_zero,sum_empty,←Fin.sum_univ_eq_sum_range,return_step_fin]
  exact orderedHop_path_closes d

/-- Take partial sums of the integration variables, with the determined
closing step placed first, following the same cyclic ordering as the density. -/
def returnPath (d : Fin n → OrderedHopStep) : OrderedTwoBandPath where
  hops := n+1
  time j := (returnVertex d j).1
  position j := (returnVertex d j).2
  time_closed := congrArg Prod.fst (return_vertex_closes d)
  space_closed := congrArg Prod.snd (return_vertex_closes d)

theorem return_path_length (d : Fin n → OrderedHopStep) :
    (returnPath d).length = orderedHopPathLength d := by
  have he (j : ℕ) : (returnPath d).duration j = (returnStep d j).1 ∧
      (returnPath d).step j = (returnStep d j).2 := by
    simp [duration,step,returnPath,returnVertex,sum_range_succ]
  change (∑ j ∈ range (n+1), (|(returnPath d).duration j|+‖(returnPath d).step j‖)) = _
  have ht := fun j => (he j).1
  have hx := fun j => (he j).2
  simp only [ht,hx,←Fin.sum_univ_eq_sum_range,return_step_fin]
  rw [Fin.sum_univ_succ]
  rfl

private theorem continuous_return_step (j : ℕ) :
    Continuous (fun d : Fin n → OrderedHopStep => returnStep d j) := by
  by_cases h : j < n+1
  · simp only [returnStep,dif_pos h]
    generalize (⟨j,h⟩ : Fin (n+1)) = i
    cases i using Fin.cases with
    | zero => exact continuous_orderedHopClosingStep
    | succ k => exact continuous_apply k
  · simp only [returnStep,dif_neg h]
    exact continuous_const

private theorem continuous_return_vertex (j : ℕ) :
    Continuous (fun d : Fin n → OrderedHopStep => returnVertex d j) :=
  continuous_finset_sum _ fun k _ => continuous_return_step k

theorem continuous_return_time (j : ℕ) :
    Continuous (fun d : Fin n → OrderedHopStep => (returnPath d).time j) :=
  continuous_fst.comp (continuous_return_vertex j)

theorem continuous_return_position (j : ℕ) :
    Continuous (fun d : Fin n → OrderedHopStep => (returnPath d).position j) :=
  continuous_snd.comp (continuous_return_vertex j)

theorem continuous_return_density :
    Continuous (fun z : (Fin n → OrderedHopStep) × (ℝ × Spatial) =>
      (returnPath z.1).density z.2.1 z.2.2) :=
  continuous_density_vertices (P := fun z : (Fin n → OrderedHopStep) × (ℝ × Spatial) => returnPath z.1) (N := n+1) (fun _ => rfl) (fun j => (continuous_return_time j).comp continuous_fst)
    (fun j => (continuous_return_position j).comp continuous_fst) (continuous_fst.comp continuous_snd)
    (continuous_snd.comp continuous_snd)

theorem continuous_return_spatialCurrent (e : Spatial) :
    Continuous (fun z : (Fin n → OrderedHopStep) × (ℝ × Spatial) =>
      (returnPath z.1).spatialCurrent z.2.1 z.2.2 e) :=
  continuous_spatialCurrent_vertices (P := fun z : (Fin n → OrderedHopStep) × (ℝ × Spatial) => returnPath z.1) (N := n+1) (fun _ => rfl) (fun j => (continuous_return_time j).comp continuous_fst)
    (fun j => (continuous_return_position j).comp continuous_fst) (continuous_fst.comp continuous_snd)
    (continuous_snd.comp continuous_snd) continuous_const

end UV.SectorPlane.OrderedTwoBandPath
