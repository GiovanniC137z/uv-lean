import UV.ContinueCayleyForward
import UV.ContinueNaimarkSchur
import UV.ContinueSourceReviewSchurHamiltonian

/-! Forward spectral measure of the literal finite charged slots coupled to an
arbitrary self-adjoint boundary. Together with the inverse construction this
gives the signed measure and Schur descriptions of the same two-point data. -/
noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
namespace UV.SectorPlane

variable {ι S H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem closing_boundary_matrix_measure [FiniteDimensional ℂ S] (b : OrthonormalBasis ι ℂ S)
    (A : S →L[ℂ] S) (hA : IsSelfAdjoint A) (T : S →L[ℂ] H)
    (B : H →ₗ.[ℂ] H) (hB : IsSelfAdjoint B) :
    ∃ M : Matrix ι ι (ComplexMeasure ℝ), ClosingPositiveMatrixMeasure M ∧ ClosingNormalizedMatrixMeasure M ∧
      Integrable (fun E : ℝ => E^2) (closingTraceLaw M) ∧
      (∀ (z : ℂ) (hz : z.im≠0) (i j : ι), closingMeasureEntryIntegral M (fun E : ℝ => (z+(E:ℂ))⁻¹) i j =
        ⟪b i,Ring.inverse (closingInverseSlot A T (closingNonrealResolvent B hB z hz).map z) (b j)⟫_ℂ) ∧
      (∀ i j : ι, closingMeasureEntryIntegral M (fun E : ℝ => (E:ℂ)) i j = ⟪b i,A (b j)⟫_ℂ) ∧
      (∀ i j : ι, closingMeasureEntryIntegral M (fun E : ℝ => (E:ℂ)^2) i j =
        ⟪b i,(A*A+T.adjoint.comp T) (b j)⟫_ℂ) := by
  let K := closingPartialBlock A T B
  let F := closingSlotInclusion (S:=S) (H:=H)
  let J : S →ₗᵢ[ℂ] ClosingSlots S H :=
    { F.toLinearMap with norm_map' := fun v => by simp [F,WithLp.norm_toLp_fst] }
  have hJ (v : S) : J v ∈ K.domain := B.domain.zero_mem
  have hK := closing_partial_block_selfAdjoint A hA T B hB
  obtain ⟨M,hp,hn,h₂,hr,h₁,h₂'⟩ := closing_cayley_forward K hK J b hJ
  let x := fun i => (⟨J (b i),hJ (b i)⟩ : K.domain)
  have hact (i : ι) : K (x i) = WithLp.toLp 2 (A (b i),T (b i)) := by
    simpa using closing_partial_block_action A T B (b i) (0:B.domain)
  refine ⟨M,hp,hn,h₂,?_,?_,?_⟩
  · intro z hz i j
    rw [hr z hz i j]
    have h := closing_partial_block_compressed_resolvent A hA T B hB z hz
    rw [←h]
    change ⟪F (b i),_⟫_ℂ = ⟪b i,F.adjoint _⟫_ℂ
    rw [adjoint_inner_right]
    rfl
  · intro i j
    rw [h₁]
    change ⟪WithLp.toLp 2 (b i,(0:H)),K (x j)⟫_ℂ = _
    simp [hact]
  · intro i j
    rw [h₂']
    change ⟪K (x i),K (x j)⟫_ℂ = _
    simp only [hact,WithLp.prod_inner_apply,WithLp.ofLp_toLp,add_apply,mul_apply,coe_comp',Function.comp_apply,
      inner_add_right,adjoint_inner_right]
    have hs : A.adjoint=A := hA.star_eq
    rw [←adjoint_inner_right A,hs]

/-- Exact common temporal insertion before any soft limit. Both solved
boundary variables belong to the domain of the same unbounded generator. -/
theorem closing_unbounded_temporal_insertion (A : S →L[ℂ] S) (T : S →L[ℂ] H)
    (B : H →ₗ.[ℂ] H) (hB : IsSelfAdjoint B) (q : ℝ) (a z z' : ℂ)
    (hz : z.im≠0) (hz' : z'.im≠0) (v v' : S) :
    let R := closingNonrealResolvent B hB z hz
    let R' := closingNonrealResolvent B hB z' hz'
    let u : B.domain := ⟨R.map (-T v),R.inDomain _⟩
    let u' : B.domain := ⟨R'.map (-(T v'+(a*(q:ℂ)) • (u:H))),R'.inDomain _⟩
    T v + (z • (u:H)+B u) = 0 ∧
      (T v'+(a*(q:ℂ)) • (u:H)) + (z' • (u':H)+B u') = 0 ∧
      closingShift A z' v'+T.adjoint (u':H)+(a*(q:ℂ)) • v =
        closingInverseSlot A T R'.map z' v' + a • closingTemporalMark T q R'.map R.map v := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · rw [ClosingUnboundedResolvent.rightInverse,add_neg_cancel]
  · rw [ClosingUnboundedResolvent.rightInverse,add_neg_cancel]
  · simp only [closingShift,closingInverseSlot,closingTemporalMark,closing_sandwich_apply,
      add_apply,sub_apply,smul_apply,one_apply,mul_apply,map_neg,map_add,map_smul]
    module

end UV.SectorPlane
