import UV.ContinueWilsonCurrentPlacements
import UV.ContinueWilsonRoutedSoftLimit

/-! The current obtained by summing the marked spin-word placements
is the polarized geometric current on the very same closed polygon. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Finset UV.SectorPlane
open scoped RealInnerProductSpace BigOperators

namespace UV

variable {n N : ℕ}

def wilsonExtendSteps (d : Fin N → OSFourSpace) (k : ℕ) : OSFourSpace := if h : k < N then d ⟨k,h⟩ else 0

@[simp] theorem wilson_extend_step (d : Fin N → OSFourSpace) (j : Fin N) : wilsonExtendSteps d j = d j := by
  simp [wilsonExtendSteps,j.isLt]

theorem wilson_finite_start_eq (d : Fin N → OSFourSpace) (j : Fin N) :
    wilsonFiniteStart d j = wilsonPolygonStart (wilsonExtendSteps d) j := by
  let g := fun k : ℕ => if k < j.val then wilsonExtendSteps d k else 0
  have h : (∑ k : Fin N, g k) = wilsonFiniteStart d j := by
    simp only [g,wilson_extend_step,wilsonFiniteStart,Fin.lt_def]
  rw [←h,Fin.sum_univ_eq_sum_range]
  have hs := Finset.sum_subset (f := g) (Finset.range_mono j.isLt.le)
    (fun k _ hk => if_neg (show ¬k < j.val from fun h => hk (Finset.mem_range.mpr h)))
  rw [←hs]
  exact Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk))

def wilsonReturnPolygon (d : Fin n → OSFourSpace) : WilsonClosedPolygon where
  displacement := wilsonExtendSteps (wilsonReturnSteps d)
  hops := n+1
  closed := by
    rw [wilsonPolygonStart,←Fin.sum_univ_eq_sum_range]
    simpa only [wilson_extend_step] using (wilson_return_closed d)

theorem wilson_return_polygon_perimeter (d : Fin n → OSFourSpace) :
    (wilsonReturnPolygon d).perimeter = wilsonReturnPerimeter d := by
  simp only [WilsonClosedPolygon.perimeter,wilsonPerimeter,wilsonReturnPolygon,←Fin.sum_univ_eq_sum_range,
    wilson_extend_step,wilsonReturnPerimeter]

theorem wilson_polarized_inclusion (u : UnitVector OSFourSpace) (x : OSFourSpace) :
    inner ℂ (wilsonCarrierInclusion u.val) (wilsonCarrierInclusion x) = (⟪u.val,x⟫:ℝ) := by
  simp [wilsonCarrierInclusion,complexifyMomentum,PiLp.inner_apply,RCLike.inner_apply]

theorem wilson_return_polarized_mark (d : Fin n → OSFourSpace) (u : UnitVector OSFourSpace) (p : OSFourSpace) :
    wilsonFiniteMark (wilsonReturnSteps d) u p = (wilsonReturnPolygon d).polarized u p := by
  simp only [wilsonFiniteMark,WilsonClosedPolygon.polarized,wilsonPolygonCurrent,wilsonReturnPolygon,
    inner_sum,inner_smul_right,wilson_polarized_inclusion,←Fin.sum_univ_eq_sum_range,wilson_extend_step,
    wilson_finite_start_eq]

theorem wilson_polarized_current_from_placements {a : ℕ} {ι : Type*} [Fintype ι] (L : ℝ)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (u : Fin a → UnitVector OSFourSpace)
    (k : Fin a → OSFourSpace) (d : Fin n → OSFourSpace) :
    (∑ f : Fin a → Fin (n+1), ∫ s : Fin a → unitInterval, wilsonMarkedReturn L T
      (fun j => (wilsonAssignedHop u f (wilsonVisitShift f s k) j).marks) (wilsonVisitShift f s k) d) =
      wilsonReturnWeight L T d * ∏ i, (wilsonReturnPolygon d).polarized (u i) (k i) := by
  simpa only [wilson_return_polarized_mark] using wilson_polygon_all_placements L T u k d

end UV
