import UV.ContinueWilsonTraceClosure
import UV.ContinueWilsonPathRouting

/-! On each closed charged polygon, summing all labelled photon
placements and integrating every straight-link fraction gives the
product of its geometric currents, including coincident link choices. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter UV.SectorPlane
open scoped RealInnerProductSpace unitInterval BigOperators

namespace UV

variable {a n N : ℕ} {ι : Type*} [Fintype ι]

def wilsonFiniteStart (d : Fin N → OSFourSpace) (j : Fin N) := ∑ k, if k < j then d k else 0

def wilsonFiniteMark (d : Fin N → OSFourSpace) (u : UnitVector OSFourSpace) (p : OSFourSpace) : ℂ :=
  ∑ j, wilsonEdgeWave p (wilsonFiniteStart d j) (d j) * (⟪u.val,d j⟫:ℝ)

private theorem wilson_visit_weight_list (us : WilsonDirections) (x : OSFourSpace) :
    wilsonDirectionWeight us x = (us.map (fun u => ((⟪u.val,x⟫:ℝ):ℂ))).prod := by
  induction us with
  | nil => rfl
  | cons u us ih => simp only [wilsonDirectionWeight,ih,List.map_cons,List.prod_cons]

theorem wilson_all_visit_weights (u : Fin a → UnitVector OSFourSpace) (f : Fin a → Fin (n+1))
    (q d : Fin (n+1) → OSFourSpace) :
    (∏ j, wilsonDirectionWeight (wilsonAssignedHop u f q j).marks (d j)) = ((∏ i, ⟪(u i).val,d (f i)⟫:ℝ) : ℂ) := by
  rw [Complex.ofReal_prod,←Finset.prod_fiberwise Finset.univ f]
  apply Finset.prod_congr rfl
  intro j _
  simp only [wilsonAssignedHop,wilson_visit_weight_list,List.map_map,Finset.prod_map_toList,Function.comp_apply]
  exact Finset.prod_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])

theorem wilson_all_visit_waves (f : Fin a → Fin (n+1)) (s : Fin a → I)
    (k : Fin a → OSFourSpace) (d : Fin (n+1) → OSFourSpace) :
    (∏ j, thinPlaneWave (wilsonVisitShift f s k j) (d j)) = ∏ i, thinPlaneWave (k i) (wilsonVisitPosition f s d i) := by
  simp only [thinPlaneWave,←Complex.exp_sum,←Finset.mul_sum,←Complex.ofReal_sum,wilson_visit_phase]

theorem wilson_marked_return_allocation (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (u : Fin a → UnitVector OSFourSpace) (f : Fin a → Fin (n+1)) (s : Fin a → I) (k : Fin a → OSFourSpace)
    (d : Fin n → OSFourSpace) :
    let q := wilsonVisitShift f s k
    wilsonMarkedReturn L T (fun j => (wilsonAssignedHop u f q j).marks) q d =
      wilsonReturnWeight L T d * ∏ i, thinPlaneWave (k i) (wilsonVisitPosition f s (wilsonReturnSteps d) i) *
        (⟪(u i).val,wilsonReturnSteps d (f i)⟫:ℝ) := by
  dsimp only
  rw [wilsonMarkedReturn,Finset.prod_mul_distrib,Finset.prod_mul_distrib,wilson_all_visit_waves,wilson_all_visit_weights,Complex.ofReal_prod]

theorem wilson_unit_fraction_integral (p x d : OSFourSpace) :
    (∫ s : I, thinPlaneWave p (x+(s:ℝ) • d)) = wilsonEdgeWave p x d := by
  rw [integral_subtype measurableSet_Icc (fun r : ℝ => thinPlaneWave p (x+r • d)),
    integral_Icc_eq_integral_Ioc,wilsonEdgeWave,intervalIntegral.integral_of_le zero_le_one]

theorem wilson_polygon_all_placements (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (u : Fin a → UnitVector OSFourSpace) (k : Fin a → OSFourSpace) (d : Fin n → OSFourSpace) :
    (∑ f : Fin a → Fin (n+1), ∫ s : Fin a → I, wilsonMarkedReturn L T
      (fun j => (wilsonAssignedHop u f (wilsonVisitShift f s k) j).marks) (wilsonVisitShift f s k) d) =
      wilsonReturnWeight L T d * ∏ i, wilsonFiniteMark (wilsonReturnSteps d) (u i) (k i) := by
  let D := wilsonReturnSteps d
  have he (f : Fin a → Fin (n+1)) : (∫ s : Fin a → I, wilsonMarkedReturn L T
      (fun j => (wilsonAssignedHop u f (wilsonVisitShift f s k) j).marks) (wilsonVisitShift f s k) d) =
      wilsonReturnWeight L T d * ∏ i, wilsonEdgeWave (k i) (wilsonFiniteStart D (f i)) (D (f i)) *
        (⟪(u i).val,D (f i)⟫:ℝ) := by
    simp_rw [wilson_marked_return_allocation,integral_const_mul]
    change _ * (∫ s : Fin a → I, ∏ i, thinPlaneWave (k i) (wilsonFiniteStart D (f i)+(s i:ℝ) • D (f i)) *
      (⟪(u i).val,D (f i)⟫:ℝ)) = _
    rw [integral_fintype_prod_volume_eq_prod (fun i (r : I) => thinPlaneWave (k i)
      (wilsonFiniteStart D (f i)+(r:ℝ) • D (f i)) * (⟪(u i).val,D (f i)⟫:ℝ))]
    simp_rw [integral_mul_const,wilson_unit_fraction_integral]
  simp only [he,←Finset.mul_sum,wilsonFiniteMark,Fintype.prod_sum,D]

end UV
