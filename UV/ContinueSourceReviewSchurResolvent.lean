import UV.ContinueSourceReviewSchur
import Mathlib.Analysis.Normed.Operator.Banach

/-! Existence of the nonreal resolvent of a densely defined self-adjoint
partial linear map, proved from its graph and Hilbert adjoint. -/

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace ComplexConjugate NNReal
namespace UV.SectorPlane

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem closing_nonreal_lower_bound (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K)
    (z : ℂ) (x : K.domain) :
    |z.im| *‖(x:H)‖ ≤ ‖z • (x:H)+K x‖ := by
  let w := z • (x:H)+K x
  have hreal : (⟪(x:H),K x⟫_ℂ).im=0 := by
    have h : starRingEnd ℂ ⟪(x:H),K x⟫_ℂ = ⟪(x:H),K x⟫_ℂ := by
      rw [inner_conj_symm]; exact closing_symmetric_of_selfAdjoint K hK x x
    have h' := congrArg Complex.im h
    simp only [Complex.conj_im] at h'
    linarith
  have hself : ⟪(x:H),(x:H)⟫_ℂ = (‖(x:H)‖^2:ℝ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hIm : (⟪(x:H),w⟫_ℂ).im=z.im * ‖(x:H)‖^2 := by
    rw [show w=z • (x:H)+K x from rfl,inner_add_right,inner_smul_right,hself,Complex.add_im,hreal,
      add_zero,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,mul_zero,zero_add]
  have h := (Complex.abs_im_le_norm ⟪(x:H),w⟫_ℂ).trans (norm_inner_le_norm _ _)
  rw [hIm,abs_mul,abs_of_nonneg (sq_nonneg ‖(x:H)‖)] at h
  by_cases hx : (x:H)=0
  · simp [hx]
  · apply le_of_mul_le_mul_right _ (norm_pos_iff.mpr hx)
    simpa [pow_two,mul_assoc,mul_comm ‖(x:H)‖ ‖w‖] using h

def closingGraphShift (K : H →ₗ.[ℂ] H) (z : ℂ) : K.graph →L[ℂ] H :=
  (z • ContinuousLinearMap.fst ℂ H H + ContinuousLinearMap.snd ℂ H H).comp K.graph.subtypeL

private theorem closing_graph_bound (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (z : ℂ)
    (hz : z.im ≠ 0) :
    ∃ c : ℝ≥0, AntilipschitzWith c (closingGraphShift K z) := by
  have hic : 0 < |z.im| := abs_pos.mpr hz
  let c := |z.im|⁻¹
  have hc : 0 < c := inv_pos.mpr hic
  let b := c+1+‖z‖*c
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  refine ⟨⟨b,hb⟩,ContinuousLinearMap.antilipschitz_of_bound _ (fun p => ?_)⟩
  obtain ⟨x,h₁,h₂⟩ := (K.mem_graph_iff.mp p.property)
  let w := z • (x:H)+K x
  have hlow := closing_nonreal_lower_bound K hK z x
  have hx : ‖(x:H)‖ ≤ c*‖w‖ := (le_inv_mul_iff₀ hic).mpr hlow
  have hKx : ‖K x‖ ≤ ‖w‖+‖z‖*‖(x:H)‖ := by
    calc _ = ‖w-z • (x:H)‖ := by simp [w]
         _ ≤ ‖w‖ + ‖z • (x:H)‖ := norm_sub_le _ _
         _ = _ := by rw [norm_smul]
  change max ‖p.val.1‖ ‖p.val.2‖ ≤ b*‖z • p.val.1+p.val.2‖
  rw [←h₁,←h₂]
  change max ‖(x:H)‖ ‖K x‖ ≤ b*‖w‖
  apply max_le
  · dsimp only [b]; nlinarith [norm_nonneg w,mul_nonneg (mul_nonneg (norm_nonneg z) hc.le) (norm_nonneg w)]
  · dsimp only [b]; nlinarith [mul_le_mul_of_nonneg_left hx (norm_nonneg z),mul_nonneg hc.le (norm_nonneg w)]

private theorem closing_graph_range_top (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (z : ℂ)
    (hz : z.im ≠ 0) : LinearMap.range (closingGraphShift K z) = ⊤ := by
  letI : CompleteSpace K.graph := IsClosed.completeSpace_coe (hs:=hK.isClosed)
  let f := closingGraphShift K z
  obtain ⟨c,hc⟩ := closing_graph_bound K hK z hz
  have hclosed : IsClosed (LinearMap.range f : Set H) := hc.isClosed_range f.uniformContinuous
  change LinearMap.range f=⊤
  rw [←hclosed.submodule_topologicalClosure_eq]
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply eq_bot_iff.mpr
  intro y hy
  have horth := (Submodule.mem_orthogonal (LinearMap.range f) y).mp hy
  have hrep (x : K.domain) : ⟪-starRingEnd ℂ z • y,(x:H)⟫_ℂ = ⟪y,K x⟫_ℂ := by
    let p : K.graph := ⟨((x:H),K x),K.mem_graph x⟩
    have h := horth (f p) ⟨p,rfl⟩
    have hs : ⟪y,z • (x:H) + K x⟫_ℂ=0 := by rw [←inner_conj_symm]; simpa [f,p,closingGraphShift] using congrArg (starRingEnd ℂ) h
    rw [inner_add_right,inner_smul_right] at hs
    rw [inner_smul_left,map_neg]
    simp only [Complex.conj_conj,neg_mul]
    linear_combination -hs
  have had : y∈K.adjoint.domain := LinearPMap.mem_adjoint_domain_of_exists y ⟨_,hrep⟩
  have hdom : y∈K.domain := (LinearPMap.isSelfAdjoint_def.mp hK) ▸ had
  have hval := LinearPMap.adjoint_apply_eq hK.dense_domain ⟨y,had⟩ hrep
  have he : K ⟨y,hdom⟩ = -starRingEnd ℂ z • y := by
    have hle : K.adjoint ≤ K := le_of_eq (LinearPMap.isSelfAdjoint_def.mp hK)
    exact (hle.2 (x:=⟨y,had⟩) (y:=⟨y,hdom⟩) rfl).symm.trans hval
  have hlow := closing_nonreal_lower_bound K hK (starRingEnd ℂ z) ⟨y,hdom⟩
  simp only [he,neg_smul,add_neg_cancel,norm_zero,Complex.conj_im,abs_neg] at hlow
  change y=0
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg y,abs_pos.mpr hz])

structure ClosingUnboundedResolvent (K : H →ₗ.[ℂ] H) (z : ℂ) where
  map : H →L[ℂ] H
  inDomain : ∀ x, map x ∈ K.domain
  rightInverse : ∀ x, z • map x+K ⟨map x,inDomain x⟩ = x
  leftInverse : ∀ x : K.domain, map (z • (x:H)+K x) = (x:H)

/-- Actual bounded nonreal inverse, including its domain and both inverse
identities. No assumption about the spectrum or surjectivity is needed. -/
def closingNonrealResolvent (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (z : ℂ)
    (hz : z.im ≠ 0) : ClosingUnboundedResolvent K z := by
  letI : CompleteSpace K.graph := IsClosed.completeSpace_coe (hs:=hK.isClosed)
  let f := closingGraphShift K z
  have hinj := (closing_graph_bound K hK z hz).choose_spec.injective
  let U := ContinuousLinearEquiv.ofBijective f (LinearMap.ker_eq_bot.mpr hinj) (closing_graph_range_top K hK z hz)
  let G := ((ContinuousLinearMap.fst ℂ H H).comp K.graph.subtypeL).comp U.symm.toContinuousLinearMap
  have hd y : G y ∈ K.domain := LinearPMap.mem_domain_of_mem_graph (U.symm y).property
  refine ⟨G,hd,?_,?_⟩
  · intro y
    have hs := K.mem_graph_iff.mp (U.symm y).property
    obtain ⟨x,h₁,h₂⟩ := hs
    have he : K ⟨G y,hd y⟩=(U.symm y).val.2 :=
      (congrArg K (Subtype.ext h₁.symm)).trans h₂
    rw [he]
    exact U.apply_symm_apply y
  · intro x
    let p : K.graph := ⟨((x:H),K x),K.mem_graph x⟩
    change (U.symm (U p)).val.1 = (x:H)
    rw [U.symm_apply_apply]

end UV.SectorPlane
