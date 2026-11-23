import UV.ContinueSourceReviewSchurWard

/-! The converse block construction starts from a prescribed self-adjoint
boundary B and arbitrary bounded slot and hopping blocks A,T. -/

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace ComplexConjugate
namespace UV.SectorPlane

variable {S H : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] [CompleteSpace S] in
def closingPartialDiagonal (B : H →ₗ.[ℂ] H) : ClosingSlots S H →ₗ.[ℂ] ClosingSlots S H :=
  let E := (WithLp.prodContinuousLinearEquiv 2 ℂ S H).toLinearEquiv
  let p := (LinearMap.snd ℂ S H).comp E.toLinearMap
  let P := B.domain.comap p
  let f := (p.comp P.subtype).codRestrict B.domain (fun x => x.property)
  ⟨P,E.symm.toLinearMap.comp ((LinearMap.inr ℂ S H).comp (B.toFun.comp f))⟩

theorem closing_partial_diagonal_selfAdjoint (B : H →ₗ.[ℂ] H) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (closingPartialDiagonal (S:=S) B) := by
  let D := closingPartialDiagonal (S:=S) B
  have hs : D.IsFormalAdjoint D := by
    intro x y
    change ⟪WithLp.toLp 2 ((0:S), B ⟨(WithLp.ofLp x.val).2,x.property⟩),y.val⟫_ℂ =
      ⟪x.val,WithLp.toLp 2 ((0:S),B ⟨(WithLp.ofLp y.val).2,y.property⟩)⟫_ℂ
    simp only [WithLp.prod_inner_apply,WithLp.ofLp_toLp,inner_zero_left,inner_zero_right,zero_add]
    exact closing_symmetric_of_selfAdjoint B hB ⟨(WithLp.ofLp x.val).2,x.property⟩ ⟨(WithLp.ofLp y.val).2,y.property⟩
  have onto (z : ℂ) (hz : z.im ≠ 0) :
      Function.Surjective (fun x : D.domain => z • (x:ClosingSlots S H)+D x) := by
    intro y
    let R := closingNonrealResolvent B hB z hz
    let s := (WithLp.ofLp y).1
    let t := (WithLp.ofLp y).2
    let x := WithLp.toLp 2 (z⁻¹ • s,R.map t)
    have hx : x∈D.domain := R.inDomain t
    refine ⟨⟨x,hx⟩,?_⟩
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change z • (z⁻¹ • s)+0=s
      rw [smul_smul,mul_inv_cancel₀ (by rintro rfl; simp at hz),one_smul,add_zero]
    · exact R.rightInverse t
  apply UV.unbounded_selfAdjoint_of_imaginary_resolvents' D hs
  · intro y; obtain ⟨x,hx⟩ := onto Complex.I (by simp) y
    exact ⟨x,(add_comm _ _).trans hx⟩
  · intro y; obtain ⟨x,hx⟩ := onto (-Complex.I) (by simp) y
    refine ⟨x,?_⟩
    change D x-Complex.I • (x:ClosingSlots S H)=y
    rw [sub_eq_neg_add,←neg_smul]; exact hx

/-- On S⊕D(B) the two entries are exactly (Au+T*w,Tu+Bw). -/
def closingPartialBlock (A : S →L[ℂ] S) (T : S →L[ℂ] H) (B : H →ₗ.[ℂ] H) :
    ClosingSlots S H →ₗ.[ℂ] ClosingSlots S H :=
  closingBoundedPerturb (closingPartialDiagonal B) (closingBlock A T 0)

theorem closing_partial_block_selfAdjoint (A : S →L[ℂ] S) (hA : IsSelfAdjoint A)
    (T : S →L[ℂ] H) (B : H →ₗ.[ℂ] H) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (closingPartialBlock A T B) :=
  closing_selfAdjoint_bounded_perturb _ (closing_partial_diagonal_selfAdjoint B hB) _
    (closing_block_selfAdjoint A T 0 hA (IsSelfAdjoint.zero _))

theorem closing_partial_block_action (A : S →L[ℂ] S) (T : S →L[ℂ] H)
    (B : H →ₗ.[ℂ] H) (v : S) (w : B.domain) :
    closingPartialBlock A T B ⟨WithLp.toLp 2 (v,(w:H)),w.property⟩ =
      WithLp.toLp 2 (A v+T.adjoint w,T v+B w) := by
  change WithLp.toLp 2 ((0:S),B w)+closingBlock A T 0 (WithLp.toLp 2 (v,(w:H)))=_
  rw [closing_block_apply]
  apply WithLp.ofLp_injective 2
  simp [add_comm]

/-- The specified unbounded block Hamiltonian, compressed to its original
finite source slots, yields the inverse Schur pencil for every nonreal z. -/
theorem closing_partial_block_compressed_resolvent [FiniteDimensional ℂ S]
    (A : S →L[ℂ] S) (hA : IsSelfAdjoint A) (T : S →L[ℂ] H)
    (B : H →ₗ.[ℂ] H) (hB : IsSelfAdjoint B) (z : ℂ) (hz : z.im ≠ 0) :
    let K := closingPartialBlock A T B
    let R := (closingNonrealResolvent K (closing_partial_block_selfAdjoint A hA T B hB) z hz).map
    let J := closingSlotInclusion (S:=S) (H:=H)
    J.adjoint.comp (R.comp J) = Ring.inverse (closingInverseSlot A T (closingNonrealResolvent B hB z hz).map z) := by
  let K := closingPartialBlock A T B
  let G := closingNonrealResolvent K (closing_partial_block_selfAdjoint A hA T B hB) z hz
  let R := closingNonrealResolvent B hB z hz
  let J := closingSlotInclusion (S:=S) (H:=H)
  let D := closingInverseSlot A T R.map z
  let F := J.adjoint.comp (G.map.comp J)
  have hgd : F*D=1 := by
    ext v
    let w : B.domain := ⟨R.map (T v),R.inDomain _⟩
    let x := WithLp.toLp 2 (v,(-w:H))
    let xd : K.domain := ⟨x,B.domain.neg_mem w.property⟩
    have heq : z • x + K xd = J (D v) := by
      have hact : K xd=WithLp.toLp 2 (A v+T.adjoint (-w:H),T v+B (-w)) :=
        closing_partial_block_action A T B v (-w)
      rw [hact]
      apply WithLp.ofLp_injective 2
      apply Prod.ext
      · change z • v+(A v+T.adjoint (-w:H)) = z • v + A v - T.adjoint (R.map (T v))
        rw [map_neg]; abel
      · change z • (-(w:H)) + (T v+B (-w))=0
        rw [smul_neg,LinearPMap.map_neg,←R.rightInverse (T v)]
        change -(z • (w:H))+(z • (w:H)+B w+-B w)=0
        abel
    change J.adjoint (G.map (J (D v)))=v
    rw [←heq,G.leftInverse xd]
    exact closing_slot_inclusion_adjoint xd.val
  have hlin : F.toLinearMap*D.toLinearMap=1 := by ext v; exact DFunLike.congr_fun hgd v
  have hdg : D*F=1 := by ext v; exact DFunLike.congr_fun (LinearMap.mul_eq_one_comm.mp hlin) v
  let u : (S →L[ℂ] S)ˣ := ⟨D,F,hdg,hgd⟩
  exact (Ring.inverse_unit u).symm

end UV.SectorPlane
