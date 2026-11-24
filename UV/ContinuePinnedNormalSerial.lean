import UV.ContinuePinnedNormalNetwork
import Mathlib.Tactic.FinCases

/-! The two-serial-segment example with distinct held labels at the
same position. Its common short-time corner costs an extra normal power. -/

noncomputable section
open MeasureTheory Real Matrix
open scoped BigOperators Matrix ENNReal
namespace UV

private def serialSrc : Fin 2 → Fin 1 ⊕ Bool := ![.inr false,.inl 0]
private def serialDst : Fin 2 → Fin 1 ⊕ Bool := ![.inl 0,.inr true]

def pinnedSerialIncidence : Matrix (Fin 1) (Fin 2) ℝ := pinnedHeldIncidence serialSrc serialDst

private theorem pinnedSerialIncidence_apply (i : Fin 1) (e : Fin 2) :
    pinnedSerialIncidence i e = if e = 0 then 1 else -1 := by
  fin_cases i
  fin_cases e <;> norm_num [pinnedSerialIncidence,pinnedHeldIncidence,groundedNetworkIncidence,
    pinnedHeldEndpoint,serialSrc,serialDst]
  all_goals decide

theorem pinnedSerialDurationPolynomial_eq (t : Fin 2 → ℝ) (ht : ∀ e, 0 < t e) :
    pinnedDurationPolynomial pinnedSerialIncidence t = t 0 + t 1 := by
  unfold pinnedDurationPolynomial retainedGramDet
  rw [Matrix.det_fin_one,Fin.prod_univ_two,Matrix.mul_apply (N := pinnedSerialIncidenceᵀ),Fin.sum_univ_two]
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply,pinnedSerialIncidence_apply]
  norm_num
  field_simp [(ht 0).ne',(ht 1).ne']
  ring

private theorem pinnedSerialIncidence_mulVec {E : Type*} (s : E → Fin 2) (x : Fin 1 → ℝ) (e : E) :
    ((pinnedSerialIncidence.submatrix id s)ᵀ *ᵥ x) e =
      (if s e = 0 then 1 else -1)*x 0 := by
  simp [Matrix.mulVec,dotProduct,Matrix.submatrix_apply,pinnedSerialIncidence_apply]

private theorem pinnedSerialIncidence_restriction_injective {E : Type*} [Nonempty E] (s : E → Fin 2) :
    Function.Injective (pinnedSerialIncidence.submatrix id s)ᵀ.mulVec := by
  classical
  let e : E := Classical.choice inferInstance
  intro x y h
  have he := congrFun h e
  rw [pinnedSerialIncidence_mulVec,pinnedSerialIncidence_mulVec] at he
  have h0 : (if s e = 0 then (1:ℝ) else -1) ≠ 0 := by split_ifs <;> norm_num
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  exact hj ▸ mul_left_cancel₀ h0 he

private theorem serial_rank_nonempty (S : Finset (Fin 2)) (hS : S.Nonempty) :
    (retainedColumns pinnedSerialIncidence S).rank = 1 := by
  letI : Nonempty S := hS.to_subtype
  exact pinned_normal_rank _ (pinnedSerialIncidence_restriction_injective (Subtype.val : S → Fin 2))

theorem pinnedSerialHeatIntegral {d : ℕ} {D : ℝ} (hD : 0 < D)
    (t : Fin 2 → ℝ) (ht : ∀ i, 0 < t i) :
    (∫ y : Fin d → EuclideanSpace ℝ (Fin 1), pinnedHeldHeatProduct serialSrc serialDst D t y) =
      (4*π*D)^(-(d:ℝ)/2) * (t 0 + t 1)^(-(d:ℝ)/2) := by
  have hA : Function.Injective pinnedSerialIncidenceᵀ.mulVec :=
    pinnedSerialIncidence_restriction_injective (id : Fin 2 → Fin 2)
  simp_rw [pinnedHeldHeatProduct_incidence]
  change (∫ y : Fin d → EuclideanSpace ℝ (Fin 1), pinnedNormalHeatProduct pinnedSerialIncidence D t y) = _
  rw [pinned_normal_heat_integral _ hA hD t ht,pinnedSerialDurationPolynomial_eq t ht]
  congr 2
  ring

/-- Each isolated endpoint requires only its own positive duration
exponent. The common corner also requires their sum to exceed `d/2`. -/
theorem pinnedSerialHeatDuration_finite_iff {d : ℕ} {D : ℝ} (hD : 0 < D) (η : Fin 2 → ℝ) :
    (∫⁻ t, ENNReal.ofReal (retainedWidthDensity η t *
      (∫ y : Fin d → EuclideanSpace ℝ (Fin 1), pinnedHeldHeatProduct serialSrc serialDst D t y))
        ∂directionalSchwingerMeasure (Fin 2)) < ⊤ ↔
      0 < η 0 ∧ 0 < η 1 ∧ (d:ℝ)/2 < η 0+η 1 := by
  have hA : Function.Injective pinnedSerialIncidenceᵀ.mulVec :=
    pinnedSerialIncidence_restriction_injective (id : Fin 2 → Fin 2)
  simp_rw [pinnedHeldHeatProduct_incidence]
  change (∫⁻ t, ENNReal.ofReal (retainedWidthDensity η t *
    (∫ y : Fin d → EuclideanSpace ℝ (Fin 1), pinnedNormalHeatProduct pinnedSerialIncidence D t y))
      ∂directionalSchwingerMeasure (Fin 2)) < ⊤ ↔ _
  rw [pinned_normal_heat_duration_finite_iff _ hA hD η]
  have h (S : Finset (Fin 2)) (hS : S.Nonempty) :
      pinnedDurationNullity pinnedSerialIncidence S = S.card-1 := by
    unfold pinnedDurationNullity
    rw [serial_rank_nonempty S hS]
  have hU : (Finset.univ : Finset (Fin 2)).Nonempty := ⟨0,Finset.mem_univ _⟩
  have h0 : ({0} : Finset (Fin 2)).Nonempty := Finset.singleton_nonempty _
  have h1 : ({1} : Finset (Fin 2)).Nonempty := Finset.singleton_nonempty _
  constructor
  · intro H
    exact ⟨by simpa [h _ h0] using H {0} h0,by simpa [h _ h1] using H {1} h1,
      by simpa [h _ hU,Fin.sum_univ_two] using H Finset.univ hU⟩
  · rintro ⟨ha,hb,hab⟩ S hS
    rw [h S hS]
    by_cases hA : 0 ∈ S <;> by_cases hB : 1 ∈ S
    · have he : S = Finset.univ := by ext j; fin_cases j <;> simp [hA,hB]
      simpa [he,Fin.sum_univ_two] using hab
    · have he : S = {0} := by ext j; fin_cases j <;> simp [hA,hB]
      simpa [he] using ha
    · have he : S = {1} := by ext j; fin_cases j <;> simp [hA,hB]
      simpa [he] using hb
    · obtain ⟨j,hj⟩ := hS
      fin_cases j
      · exact (hA hj).elim
      · exact (hB hj).elim

end UV
