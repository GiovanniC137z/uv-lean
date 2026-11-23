import UV.ContinueWilsonSpinRotation
import UV.ContinueWilsonAbsoluteTwoPoint

/-! Orthogonal transport of unit polarizations, closed paths, their
ordered spin traces, the two projected external currents, and the
transverse Maxwell sewing on the Euclidean carrier four-plane. -/

noncomputable section

open MeasureTheory Filter UV.SectorPlane
open scoped Topology RealInnerProductSpace ComplexConjugate

namespace UV

def wilsonRotateUnit (R : OSFourSpace ≃ₗᵢ[ℝ] OSFourSpace) (u : UnitVector OSFourSpace) : UnitVector OSFourSpace :=
  ⟨R u.val,(R.norm_map _).trans u.property⟩

def WilsonClosedPolygon.rotate (P : WilsonClosedPolygon) (R : OSFourSpace ≃ₗᵢ[ℝ] OSFourSpace) : WilsonClosedPolygon where
  displacement := fun j => R (P.displacement j)
  hops := P.hops
  closed := by simp only [wilsonPolygonStart,←map_sum]; exact (congrArg R P.closed).trans (map_zero R)

theorem wilson_return_steps_rotate (R : OSFourSpace ≃ₗᵢ[ℝ] OSFourSpace) {n : ℕ} (d : Fin n → OSFourSpace) (j : Fin (n+1)) :
    wilsonReturnSteps (fun k => R (d k)) j = R (wilsonReturnSteps d j) := by
  cases j using Fin.cases with
  | zero => simp [wilsonReturnSteps]
  | succ j => rfl

theorem wilson_return_polygon_rotate (R : OSFourSpace ≃ₗᵢ[ℝ] OSFourSpace) {n : ℕ} (d : Fin n → OSFourSpace) :
    wilsonReturnPolygon (fun k => R (d k)) = (wilsonReturnPolygon d).rotate R := by
  have he : wilsonExtendSteps (wilsonReturnSteps (fun k => R (d k))) =
      fun j => R (wilsonExtendSteps (wilsonReturnSteps d) j) := by
    funext j
    by_cases h : j < n+1 <;> simp [wilsonExtendSteps,h,wilson_return_steps_rotate]
  exact WilsonClosedPolygon.mk.injEq .. |>.mpr ⟨he,rfl⟩

theorem wilson_return_weight_rotate {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (R : OSFourSpace ≃ₗᵢ[ℝ] OSFourSpace) {n : ℕ} (d : Fin n → OSFourSpace) :
    wilsonReturnWeight L T (fun j => R (d j)) = wilsonReturnWeight L T d := by
  have hs := wilson_spin_trace_orthogonal L R (List.ofFn (wilsonReturnSteps d))
  simp only [List.map_ofFn] at hs
  simp only [wilsonReturnWeight,←map_sum,←map_neg,wilson_continuous_density_orthogonal hL T,
    wilsonReturnSpin,wilson_return_steps_rotate]
  exact congrArg (_ * ·) hs

theorem wilson_rotated_edge_wave (R : OSFourSpace ≃ₗᵢ[ℝ] OSFourSpace) (p x d : OSFourSpace) :
    wilsonEdgeWave (R p) (R x) (R d) = wilsonEdgeWave p x d := by
  simp only [wilsonEdgeWave,thinPlaneWave,←map_smul,←map_add,R.inner_map_map]

private theorem wilson_inner_inclusion (x y : OSFourSpace) :
    inner ℂ (wilsonCarrierInclusion x) (wilsonCarrierInclusion y) = (⟪x,y⟫:ℝ) := by
  simp [wilsonCarrierInclusion,complexifyMomentum,PiLp.inner_apply,RCLike.inner_apply]

theorem WilsonClosedPolygon.polarized_rotate (P : WilsonClosedPolygon) (R : OSFourSpace ≃ₗᵢ[ℝ] OSFourSpace)
    (u : UnitVector OSFourSpace) (p : OSFourSpace) : (P.rotate R).polarized (wilsonRotateUnit R u) (R p) = P.polarized u p := by
  simp only [polarized,rotate,wilsonRotateUnit,wilsonPolygonCurrent,wilsonPolygonStart,←map_sum,
    wilson_rotated_edge_wave,inner_sum,inner_smul_right,wilson_inner_inclusion,R.inner_map_map]

theorem wilson_rotate_sewing (P Q : WilsonClosedPolygon) (R : OSFourSpace ≃ₗᵢ[ℝ] OSFourSpace)
    {χ : OSFourSpace → ℂ} (hχ : ∀ p, χ (R p) = χ p) (p : OSFourSpace) :
    (WilsonPolygonEdge.mk (P.rotate R) (Q.rotate R)).sewing χ (R p) = (WilsonPolygonEdge.mk P Q).sewing χ p := by
  simp only [WilsonPolygonEdge.formula,hχ,R.norm_map,WilsonClosedPolygon.rotate,wilsonPolygonCurrent,
    wilsonPolygonStart,←map_sum,wilson_rotated_edge_wave,inner_sum,sum_inner,inner_smul_left,
    inner_smul_right,wilson_inner_inclusion,R.inner_map_map]

theorem wilson_orthogonal_unit_pair (u v u' v' : UnitVector OSFourSpace) (huv : ⟪u.val,v.val⟫ = 0) (h' : ⟪u'.val,v'.val⟫ = 0) :
    ∃ R : OSFourSpace ≃ₗᵢ[ℝ] OSFourSpace, wilsonRotateUnit R u = u' ∧ wilsonRotateUnit R v = v' := by
  let S := (ℝ ∙ (u.val-u'.val))ᗮ.reflection
  have hs : S u.val = u'.val := Submodule.reflection_sub (u.property.trans u'.property.symm)
  let H := (ℝ ∙ (S v.val-v'.val))ᗮ.reflection
  have ht : H (S v.val) = v'.val := Submodule.reflection_sub (by rw [S.norm_map,v.property,v'.property])
  have ho : ⟪S v.val,u'.val⟫ = 0 := by rw [real_inner_comm,←hs,S.inner_map_map,huv]
  have hrev : ⟪v'.val,u'.val⟫ = 0 := (real_inner_comm _ _).trans h'
  have hu : H u'.val = u'.val := Submodule.reflection_mem_subspace_eq_self (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (by
    rw [inner_sub_left,ho,hrev,sub_self]))
  exact ⟨S.trans H,Subtype.ext ((congrArg H hs).trans hu),Subtype.ext ht⟩

end UV
