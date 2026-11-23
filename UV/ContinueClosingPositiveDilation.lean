import UV.ContinueClosingPositiveAtoms

/-! Orthogonal block elimination for a bounded positive spectral
realization. The ambient boundary channel extends its orthogonal
complement by a decoupled zero slot. -/

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace

namespace UV.SectorPlane

variable {S H : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem closing_lift_adjoint_left (J : S →ₗᵢ[ℂ] H) (v : S) :
    J.toContinuousLinearMap.adjoint (J v) = v := by
  apply ext_inner_left ℂ
  intro u
  rw [adjoint_inner_right]
  exact J.inner_map_map u v

set_option maxHeartbeats 500000 in
/-- A bounded self-adjoint dilation of a finite-slot covariance gives
a Hermitian slot block and a self-adjoint boundary Schur realization. -/
theorem closing_bounded_dilation_split [FiniteDimensional ℂ S]
    (J : S →ₗᵢ[ℂ] H) (K : H →L[ℂ] H) (hK : IsSelfAdjoint K) :
    ∃ (A : S →L[ℂ] S) (B : H →L[ℂ] H) (T : S →L[ℂ] H),
      IsSelfAdjoint A ∧ IsSelfAdjoint B ∧
      A = J.toContinuousLinearMap.adjoint.comp (K.comp J.toContinuousLinearMap) ∧
      (K.comp J.toContinuousLinearMap).adjoint.comp (K.comp J.toContinuousLinearMap) =
        A * A + T.adjoint.comp T ∧
      ∀ z : ℂ, z.im ≠ 0 →
        J.toContinuousLinearMap.adjoint.comp ((closingResolvent K z).comp J.toContinuousLinearMap) =
          Ring.inverse (closingInverseSlot A T (closingResolvent B z) z) := by
  let F := J.toContinuousLinearMap
  let P := F.comp F.adjoint
  let Q : H →L[ℂ] H := 1 - P
  let A := F.adjoint.comp (K.comp F)
  let B := Q.comp (K.comp Q)
  let T := Q.comp (K.comp F)
  have hF (v : S) : F.adjoint (F v) = v := closing_lift_adjoint_left J v
  have hP : P.adjoint = P := by simp [P]
  have hQ : Q.adjoint = Q := by
    have h1 : (1 : H →L[ℂ] H).adjoint = 1 := adjoint_id
    simp [Q, hP, h1]
  have hK' : K.adjoint = K := hK.star_eq
  have hA : IsSelfAdjoint A := by
    apply ContinuousLinearMap.isSelfAdjoint_iff'.mpr
    simp [A, hK', comp_assoc]
  have hB : IsSelfAdjoint B := by
    apply ContinuousLinearMap.isSelfAdjoint_iff'.mpr
    simp [B, hK', hQ, comp_assoc]
  have hT : T.adjoint = F.adjoint.comp (K.comp Q) := by
    simp [T, hK', hQ, comp_assoc]
  have hQF (v : S) : Q (F v) = 0 := by
    simp [Q, P, hF v]
  have hFQ (y : H) : F.adjoint (Q y) = 0 := by
    simp [Q, P, hF (F.adjoint y)]
  have hQQ (y : H) : Q (Q y) = Q y := by
    change Q y - F (F.adjoint (Q y)) = Q y
    simp [hFQ y]
  have hdecomp (y : H) : F (F.adjoint y) + Q y = y := by
    change F (F.adjoint y) + (y - F (F.adjoint y)) = y
    abel
  have hsplitMoment : (K.comp F).adjoint.comp (K.comp F) = A * A + T.adjoint.comp T := by
    apply ContinuousLinearMap.ext
    intro v
    apply ext_inner_left ℂ
    intro u
    simp only [coe_comp', Function.comp_apply, adjoint_inner_right, add_apply, mul_apply,
      inner_add_right]
    have hA' : A.adjoint = A := hA.star_eq
    have hea : ⟪u, A (A v)⟫_ℂ = ⟪A u, A v⟫_ℂ := by
      calc
        _ = ⟪u, A.adjoint (A v)⟫_ℂ := by rw [hA']
        _ = _ := adjoint_inner_right A u (A v)
    rw [hea]
    calc
      ⟪K (F u), K (F v)⟫_ℂ =
        ⟪K (F u), F (A v)⟫_ℂ + ⟪K (F u), Q (K (F v))⟫_ℂ := by
          rw [← inner_add_right]
          exact congrArg (inner ℂ (K (F u))) (hdecomp (K (F v))).symm
      _ = _ := by
        rw [← adjoint_inner_left F]
        change ⟪A u, A v⟫_ℂ + ⟪K (F u), Q (K (F v))⟫_ℂ =
          ⟪A u, A v⟫_ℂ + ⟪Q (K (F u)), Q (K (F v))⟫_ℂ
        congr 1
        calc
          _ = ⟪K (F u), Q.adjoint (Q (K (F v)))⟫_ℂ := by rw [hQ, hQQ]
          _ = _ := adjoint_inner_right Q (K (F u)) (Q (K (F v)))
  refine ⟨A, B, T, hA, hB, rfl, hsplitMoment, ?_⟩
  intro z hz
  let D := closingInverseSlot A T (closingResolvent B z) z
  let G := F.adjoint.comp ((closingResolvent K z).comp F)
  have huK := closing_shift_isUnit_of_nonreal K hK hz
  have huB := closing_shift_isUnit_of_nonreal B hB hz
  have hDG : D * G = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    let y := closingResolvent K z (F v)
    let x := F.adjoint y
    have he : closingShift K z y = F v :=
      congrArg (fun L : H →L[ℂ] H => L (F v)) (Ring.mul_inverse_cancel _ huK)
    have hlo₀ := congrArg Q he
    change Q (z • y + K y) = Q (F v) at hlo₀
    rw [hQF, map_add, map_smul] at hlo₀
    have hsplit₁ : T x + B (Q y) = Q (K y) := by
      change Q (K (F x)) + Q (K (Q (Q y))) = Q (K y)
      rw [hQQ, ← map_add, ← map_add, hdecomp]
    have hlo : T x + closingShift B z (Q y) = 0 := by
      change T x + (z • Q y + B (Q y)) = 0
      rw [add_left_comm, hsplit₁, hlo₀]
    have hlo' := congrArg (closingResolvent B z) (eq_neg_of_add_eq_zero_right hlo)
    have hR (w : H) : closingResolvent B z (closingShift B z w) = w :=
      congrArg (fun L : H →L[ℂ] H => L w) (Ring.inverse_mul_cancel _ huB)
    change closingResolvent B z (closingShift B z (Q y)) = _ at hlo'
    rw [hR, map_neg] at hlo'
    have hhi₀ := congrArg F.adjoint he
    change F.adjoint (z • y + K y) = F.adjoint (F v) at hhi₀
    rw [hF, map_add, map_smul] at hhi₀
    have hsplit₂ : A x + T.adjoint (Q y) = F.adjoint (K y) := by
      rw [hT]
      change F.adjoint (K (F x)) + F.adjoint (K (Q (Q y))) = F.adjoint (K y)
      rw [hQQ, ← map_add, ← map_add, hdecomp]
    change D x = v
    change z • x + A x - T.adjoint (closingResolvent B z (T x)) = v
    rw [sub_eq_add_neg, ← map_neg, ← hlo', add_assoc, hsplit₂]
    exact hhi₀
  have hDG' : D.toLinearMap * G.toLinearMap = 1 := by
    apply LinearMap.ext
    intro v
    exact DFunLike.congr_fun hDG v
  have hGD' := LinearMap.mul_eq_one_comm.mp hDG'
  have hGD : G * D = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L : S →ₗ[ℂ] S => L v) hGD'
  let u : (S →L[ℂ] S)ˣ := ⟨D, G, hDG, hGD⟩
  exact (Ring.inverse_unit u).symm

theorem closing_atomic_schur_realization {ι : Type*} [Fintype ι] [FiniteDimensional ℂ S]
    (E : ι → ℝ) (W : ι → S →L[ℂ] S) (hW : ∀ i, 0 ≤ W i)
    (hI : (∑ i, W i) = (1 : S →L[ℂ] S)) :
    ∃ (A : S →L[ℂ] S) (B : ClosingAtomicSpace ι S →L[ℂ] ClosingAtomicSpace ι S)
      (T : S →L[ℂ] ClosingAtomicSpace ι S),
      IsSelfAdjoint A ∧ IsSelfAdjoint B ∧ A = ∑ i, (E i : ℂ) • W i ∧
      ∀ z : ℂ, z.im ≠ 0 →
        (∑ i, (z + (E i : ℂ))⁻¹ • W i) =
          Ring.inverse (closingInverseSlot A T (closingResolvent B z) z) := by
  obtain ⟨J, K, hK, hG, hA⟩ := closing_finite_atomic_positive_realization E W hW hI
  obtain ⟨A, B, T, hA', hB, hA'', _, hS⟩ := closing_bounded_dilation_split J K hK
  exact ⟨A, B, T, hA', hB, hA''.trans hA, fun z hz => (hG z hz).symm.trans (hS z hz)⟩

end UV.SectorPlane
