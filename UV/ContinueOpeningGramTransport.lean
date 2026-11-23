import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic

/-! Unitary identification from the full complex Gram kernel on any
indexed total family. Finite dependencies and repeated labels are allowed. -/

noncomputable section
open scoped InnerProductSpace
open Set

namespace UV

/-- Two total families with the same complex Gram kernel determine a unitary
that takes every named vector to the vector with the same label. -/
theorem opening_gram_transport {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (v : ι → E) (w : ι → F)
    (hv : Dense (Submodule.span ℂ (range v) : Set E))
    (hw : Dense (Submodule.span ℂ (range w) : Set F))
    (hGram : ∀ i j, ⟪v i,v j⟫_ℂ = ⟪w i,w j⟫_ℂ) :
    ∃ U : E ≃ₗᵢ[ℂ] F, ∀ i, U (v i) = w i := by
  classical
  let V := Finsupp.linearCombination ℂ v
  let W := Finsupp.linearCombination ℂ w
  have hn (a : ι →₀ ℂ) : ‖V a‖ = ‖W a‖ := by
    have h : ⟪V a,V a⟫_ℂ = ⟪W a,W a⟫_ℂ := by
      simp only [V,W,Finsupp.linearCombination_apply,Finsupp.sum,sum_inner,inner_sum,
        inner_smul_left,inner_smul_right,hGram]
    have hh := congrArg Complex.re h
    change RCLike.re ⟪V a,V a⟫_ℂ = RCLike.re ⟪W a,W a⟫_ℂ at hh
    simp only [inner_self_eq_norm_sq] at hh
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hh
  have hker : LinearMap.ker V ≤ LinearMap.ker W := by
    intro c hc
    apply norm_eq_zero.mp
    rw [←hn,LinearMap.mem_ker.mp hc,norm_zero]
  let T := ((LinearMap.ker V).liftQ W hker).comp V.quotKerEquivRange.symm.toLinearMap
  have hT (a : ι →₀ ℂ) : T (V.rangeRestrict a) = W a := by
    change (LinearMap.ker V).liftQ W hker (V.quotKerEquivRange.symm ⟨V a,_⟩) = W a
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let I : LinearMap.range V →ₗᵢ[ℂ] F :=
    { toLinearMap := T
      norm_map' := fun u => by
        obtain ⟨a,rfl⟩ := V.surjective_rangeRestrict u
        rw [hT]
        exact (hn a).symm }
  have hd : DenseRange (LinearMap.range V).subtypeL := by
    change Dense (range ((↑) : LinearMap.range V → E))
    have h : Dense (LinearMap.range V : Set E) := by simpa only [V,Finsupp.range_linearCombination] using hv
    exact h.mono (fun x hx => ⟨⟨x,hx⟩,rfl⟩)
  let J := I.toContinuousLinearMap.extend (LinearMap.range V).subtypeL hd isUniformEmbedding_subtype_val.isUniformInducing
  have he (u : LinearMap.range V) : J (u:E) = I u :=
    ContinuousLinearMap.extend_eq _ _ _ _ u
  let U : E →ₗᵢ[ℂ] F :=
    { toLinearMap := J.toLinearMap
      norm_map' := fun x => by
        refine hd.induction_on (p := fun y => ‖J y‖ = ‖y‖) x (isClosed_eq J.continuous.norm continuous_norm) ?_
        intro u
        change ‖J (u:E)‖ = ‖(u:E)‖
        rw [he]
        exact I.norm_map u }
  have hUw i : U (v i) = w i := by
    let c := Finsupp.single i (1:ℂ)
    have hv' : V c = v i := by simp [V,c]
    have hw' : W c = w i := by simp [W,c]
    rw [←hv',←hw']
    exact (he (V.rangeRestrict c)).trans (hT c)
  have hspan : Submodule.span ℂ (range w) ≤ LinearMap.range U.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨v i,hUw i⟩
  have hs : Function.Surjective U := by
    intro y
    have hi : IsClosed (range U) := U.isometry.isClosedEmbedding.isClosed_range
    exact (closure_minimal hspan hi) (hw y)
  exact ⟨LinearIsometryEquiv.ofSurjective U hs,hUw⟩

/-- The dense source family also fixes the unitary uniquely. -/
theorem opening_gram_transport_unique {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (v : ι → E)
    (hv : Dense (Submodule.span ℂ (range v) : Set E)) (U V : E ≃ₗᵢ[ℂ] F)
    (h : ∀ i, U (v i) = V (v i)) : U = V := by
  have he : U.toContinuousLinearEquiv.toContinuousLinearMap = V.toContinuousLinearEquiv.toContinuousLinearMap :=
    ContinuousLinearMap.ext_on hv (fun _ ⟨i,hi⟩ => hi ▸ h i)
  ext x
  exact congrArg (fun f : E →L[ℂ] F => f x) he

end UV
