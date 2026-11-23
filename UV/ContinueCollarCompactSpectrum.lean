import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Operator.Compact

/-! Real compact symmetric operators have a complete system of orthogonal
eigenspaces. This includes compact Green operators on radial L². -/

noncomputable section

open Set Metric
open scoped InnerProductSpace

namespace UV.CollarEigenmode

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Norm attainment for a compact symmetric operator, with a nonzero
eigenvector of either sign. The extremum is taken on its compact image. -/
theorem compact_symmetric_eigenvector (T : H →L[ℝ] H) (hc : IsCompactOperator T)
    (hs : T.toLinearMap.IsSymmetric) (hn : T ≠ 0) :
    ∃ η : ℝ,|η|=‖T‖ ∧ ∃ v : H,v ≠ 0 ∧ T v=η • v := by
  let K := closure (T '' closedBall (0:H) 1)
  have hK : IsCompact K := hc.isCompact_closure_image_closedBall 1
  have hzero : 0 ∈ K := subset_closure ⟨0,by simp,by simp⟩
  obtain ⟨y,hy,hmax⟩ := hK.exists_isMaxOn ⟨0,hzero⟩ continuous_norm.continuousOn
  have ht : ‖T‖ ≤ ‖y‖ := ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _) fun v hv =>
    hmax (subset_closure ⟨v,by simp [mem_closedBall,dist_zero_right,hv],rfl⟩)
  have hball : K ⊆ closedBall (0:H) ‖T‖ := by
    apply closure_minimal _ isClosed_closedBall
    rintro _ ⟨x,hx,rfl⟩
    simp only [mem_closedBall,dist_zero_right] at hx ⊢
    exact (T.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg _) hx)
  have ha : ‖y‖=‖T‖ := (show ‖y‖ ≤ ‖T‖ by simpa using hball hy).antisymm ht
  have hp : 0 < ‖T‖ := norm_pos_iff.mpr hn
  have hyne : y ≠ 0 := norm_pos_iff.mp (ha ▸ hp)
  have hlin : K ⊆ {z : H | ⟪z,y⟫_ℝ ≤ ‖T y‖} := by
    apply closure_minimal _ (isClosed_le (by fun_prop) continuous_const)
    rintro _ ⟨x,hx,rfl⟩
    have hh : ⟪T x,y⟫_ℝ=⟪x,T y⟫_ℝ := hs x y
    change ⟪T x,y⟫_ℝ ≤ _
    rw [hh]
    exact (real_inner_le_norm x (T y)).trans (mul_le_of_le_one_left (norm_nonneg _) (by simpa using hx))
  have hnorm : ‖T y‖=‖T‖^2 := by
    have hlow := hlin hy
    change ⟪y,y⟫_ℝ ≤ ‖T y‖ at hlow
    rw [real_inner_self_eq_norm_sq,ha] at hlow
    exact (show ‖T y‖ ≤ ‖T‖^2 by simpa only [ha,pow_two] using T.le_opNorm y).antisymm hlow
  have hdouble : T (T y)= (‖T‖^2) • y := by
    have hn2 := norm_sub_sq_real (T (T y)) ((‖T‖^2) • y)
    have hyy : ⟪T (T y),y⟫_ℝ=‖T y‖^2 := (hs (T y) y).trans (real_inner_self_eq_norm_sq _)
    rw [real_inner_smul_right,hyy,norm_smul,Real.norm_of_nonneg (sq_nonneg _),hnorm,ha] at hn2
    have hu := T.le_opNorm (T y)
    rw [hnorm] at hu
    have hpow := pow_le_pow_left₀ (norm_nonneg _) hu 2
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    nlinarith only [hn2,hpow,sq_nonneg ‖T (T y)-(‖T‖^2) • y‖]
  by_cases h : T y+‖T‖ • y=0
  · exact ⟨-‖T‖,by simp, y,hyne,by simpa using eq_neg_of_add_eq_zero_left h⟩
  · refine ⟨‖T‖,abs_of_nonneg (norm_nonneg _),T y+‖T‖ • y,h,?_⟩
    rw [map_add,map_smul,hdouble,smul_add,smul_smul,pow_two,add_comm]

/-- The eigenspaces of an arbitrary compact symmetric operator have
dense span in a real Hilbert space. -/
theorem compact_symmetric_dense_eigenspaces [CompleteSpace H] (T : H →L[ℝ] H) (hc : IsCompactOperator T)
    (hs : T.toLinearMap.IsSymmetric) :
    (⨆ e : ℝ,Module.End.eigenspace T.toLinearMap e).topologicalClosure = ⊤ := by
  let C := ⨆ e : ℝ,Module.End.eigenspace T.toLinearMap e
  let W := Cᗮ
  have hW : ∀ v ∈ W,T.toLinearMap v ∈ W := hs.orthogonalComplement_iSup_eigenspaces_invariant
  let L := T.toLinearMap.restrict hW
  let S := L.mkContinuous ‖T‖ (fun x => T.le_opNorm x.val)
  have hSW : IsCompactOperator S := IsCompactOperator.restrict (f := T.toLinearMap) hc hW C.isClosed_orthogonal
  have hsym : S.toLinearMap.IsSymmetric := hs.restrict_invariant hW
  have vanish (e : ℝ) (z : W) (hz : S z=e • z) : z=0 := by
    have hz' : z ∈ Module.End.eigenspace L e := Module.End.mem_eigenspace_iff.mpr hz
    rw [show Module.End.eigenspace L e=⊥ from hs.orthogonalComplement_iSup_eigenspaces e] at hz'
    exact hz'
  have hbot : W=⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    let z : W := ⟨x,hx⟩
    by_cases h : S=0
    · have hz := vanish 0 z (by simp [h])
      exact congrArg Subtype.val hz
    · obtain ⟨e,_,y,hy,hS⟩ := compact_symmetric_eigenvector S hSW hsym h
      exact (hy (vanish e y hS)).elim
  change C.topologicalClosure=⊤
  rw [← C.orthogonal_orthogonal_eq_closure,show Cᗮ=⊥ from hbot,Submodule.bot_orthogonal_eq_top]

end UV.CollarEigenmode
