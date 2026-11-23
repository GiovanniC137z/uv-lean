import UV.ContinueNormalHolonomyCoefficient
import UV.ContinueNormalProtectedGraph

/-! Absolutely summable expansion of the actual periodic circle word.
The integer on each marked propagator is reindexed by total winding
and the independent integer lifts of the remaining displacements. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter UV.SectorPlane
open scoped Matrix.Norms.L2Operator

namespace UV

def normalOrderedWord {r : ℕ} (A : Fin r → DiracMatrix) := (List.ofFn A).prod

theorem normal_ordered_word_summable {r : ℕ} (A : Fin r → ℤ → DiracMatrix)
    (h : ∀ i, Summable (fun j => ‖A i j‖)) :
    Summable (fun k : Fin r → ℤ => ‖normalOrderedWord (fun i => A i (k i))‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (wilson_summable_product (fun _ _ => norm_nonneg _) h)
  intro k
  simpa only [List.map_ofFn,List.prod_ofFn,Function.comp_def] using (List.ofFn (fun i => A i (k i))).norm_prod_le

theorem normal_ordered_word_tsum {r : ℕ} (A : Fin r → ℤ → DiracMatrix) (h : ∀ i, Summable (fun j => ‖A i j‖)) :
    normalOrderedWord (fun i => ∑' j, A i j) = ∑' k : Fin r → ℤ, normalOrderedWord (fun i => A i (k i)) := by
  classical
  induction r with
  | zero => simp [normalOrderedWord,tsum_fintype]
  | succ r ih =>
    let e := Fin.consEquiv (fun _ : Fin (r+1) => ℤ)
    change (List.ofFn (fun i => ∑' j, A i j)).prod = _
    rw [List.ofFn_succ,List.prod_cons]
    change (∑' j, A 0 j)*normalOrderedWord (fun i => ∑' j, A i.succ j) = _
    rw [ih (fun i => A i.succ) (fun i => h i.succ),tsum_mul_tsum_of_summable_norm (h 0)
      (normal_ordered_word_summable _ (fun i => h i.succ)),←e.tsum_eq]
    apply tsum_congr
    rintro ⟨j,k⟩
    dsimp only [normalOrderedWord]
    conv_rhs => rw [List.ofFn_succ,List.prod_cons]
    simp only [e,Fin.consEquiv_apply,Fin.cons_zero,Fin.cons_succ]

theorem normal_ordered_word_smul {r : ℕ} (c : Fin r → ℂ) (A : Fin r → DiracMatrix) :
    normalOrderedWord (fun j => c j • A j) = (∏ j, c j) • normalOrderedWord A := by
  induction r with
  | zero => simp [normalOrderedWord]
  | succ r ih =>
    rw [Fin.prod_univ_succ,normalOrderedWord,List.ofFn_succ,List.prod_cons,normalOrderedWord,List.ofFn_succ,List.prod_cons]
    change (c 0 • A 0)*normalOrderedWord (fun i => c i.succ • A i.succ) = _
    rw [ih,smul_mul_smul]
    rfl

def normalWindingAllocation (n : ℕ) : (ℤ × (Fin n → ℤ)) ≃ (Fin (n+1) → ℤ) where
  toFun z := Fin.cons (z.1-∑ i, z.2 i) z.2
  invFun k := (∑ j, k j, fun i => k i.succ)
  left_inv z := by simp [Fin.sum_univ_succ]
  right_inv k := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.sum_univ_succ]

theorem normal_allocated_increments_offset {n : ℕ} (L δ : ℝ) (t : Fin n → ℝ) (w : ℤ) (h : Fin n → ℤ) (i : Fin (n+1)) :
    L*(normalOpenIncrements δ t i+((normalWindingAllocation n (w,h) i:ℤ):ℝ)) =
      normalOpenIncrements (L*(δ+(w:ℝ))) (fun j => L*(t j+(h j:ℝ))) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [normalOpenIncrements,normalWindingAllocation,Equiv.coe_fn_mk,Fin.cons_zero,Int.cast_sub,Int.cast_sum,
      Finset.sum_add_distrib,mul_add]
    simp_rw [←Finset.mul_sum]
    ring
  · simp only [normalOpenIncrements,normalWindingAllocation,Equiv.coe_fn_mk,Fin.cons_succ]

theorem normal_allocated_increments {n : ℕ} (L : ℝ) (t : Fin n → ℝ) (w : ℤ) (h : Fin n → ℤ) (i : Fin (n+1)) :
    L*(normalOpenIncrements 0 t i+((normalWindingAllocation n (w,h) i:ℤ):ℝ)) =
      normalOpenIncrements ((w:ℝ)*L) (fun j => L*(t j+(h j:ℝ))) i := by
  simpa only [zero_add,mul_comm L (w:ℝ)] using normal_allocated_increments_offset L 0 t w h i

theorem normal_allocated_phase_offset {n : ℕ} (θ δ : ℝ) (t : Fin n → ℝ) (w : ℤ) (h : Fin n → ℤ) :
    (∏ i, normalAngularPhase θ (normalOpenIncrements δ t i+((normalWindingAllocation n (w,h) i:ℤ):ℝ))) =
      normalAngularPhase θ (δ+(w:ℝ)) := by
  have hk : ∑ i, normalWindingAllocation n (w,h) i = w := by simp [normalWindingAllocation,Fin.sum_univ_succ]
  unfold normalAngularPhase
  rw [←Complex.exp_sum,←Finset.mul_sum,←Complex.ofReal_sum,Finset.sum_add_distrib,normal_open_increments_sum,←Int.cast_sum,hk]

theorem normal_allocated_phase {n : ℕ} (θ : ℝ) (t : Fin n → ℝ) (w : ℤ) (h : Fin n → ℤ) :
    (∏ i, normalAngularPhase θ (normalOpenIncrements 0 t i+((normalWindingAllocation n (w,h) i:ℤ):ℝ))) =
      normalAngularPhase θ (w:ℝ) := by
  simpa only [zero_add] using normal_allocated_phase_offset θ 0 t w h

def normalCircleTrace {n : ℕ} (m L θ : ℝ) (u : Fin (n+1) → UnitVector OSFourSpace) (p : Fin (n+1) → OSFourSpace)
    (t : Fin n → ℝ) : ℂ := (L:ℂ) * (normalOrderedWord (fun i => normalCircleKernel m L θ (p i)
      (normalOpenIncrements 0 t i) * diracSlash (u i).val)).trace

/-- The sign here follows the periodic gauge for ∂z+iθ/L and increments
summing to +wL. Reversing the winding orientation reverses its phase. -/
theorem normal_circle_trace_windings {n : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ)
    (u : Fin (n+1) → UnitVector OSFourSpace) (p : Fin (n+1) → OSFourSpace) (t : Fin n → ℝ) :
    let F := fun z : ℤ × (Fin n → ℤ) => normalWindingTrace m L (-θ) z.1 u p (fun j => L*(t j+(z.2 j:ℝ)))
    Summable (fun z => ‖F z‖) ∧ normalCircleTrace m L θ u p t = ∑' w : ℤ, ∑' h : Fin n → ℤ, F (w,h) := by
  let d := normalOpenIncrements 0 t
  let A := fun (i : Fin (n+1)) (j : ℤ) => normalCircleTerm m L θ (p i) (d i) j * diracSlash (u i).val
  have hA (i) : Summable (fun j => ‖A i j‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (normal_circle_term_summable hm hL θ (p i) (d i))
    intro j
    simpa only [wilson_slash_opnorm,(u i).property,mul_one] using norm_mul_le (normalCircleTerm m L θ (p i) (d i) j) (diracSlash (u i).val)
  let P := fun k : Fin (n+1) → ℤ => normalOrderedWord (fun i => A i (k i))
  let e := normalWindingAllocation n
  let tr := (Matrix.traceLinearMap (Fin 4) ℂ ℂ).toContinuousLinearMap
  let H := fun k => (L:ℂ)*tr (P k)
  have hP := normal_ordered_word_summable A hA
  have hH : Summable (fun k => ‖H k‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hP.mul_left (L*4))
    intro k
    rw [show ‖H k‖ = L*‖(P k).trace‖ by simp [H,tr,abs_of_pos hL]]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (wilson_trace_le_opnorm (P k)) hL.le
  have halloc (z : ℤ × (Fin n → ℤ)) : H (e z) =
      normalWindingTrace m L (-θ) z.1 u p (fun j => L*(t j+(z.2 j:ℝ))) := by
    rcases z with ⟨w,h⟩
    dsimp only [H,tr,P,A,normalCircleTerm,e,d]
    simp only [smul_mul_assoc,normal_allocated_increments,normal_ordered_word_smul,normal_allocated_phase,
      Matrix.traceLinearMap_apply,LinearMap.coe_toContinuousLinearMap',Matrix.trace_smul]
    change (L:ℂ) * (normalAngularPhase θ (w:ℝ) • _) = _
    have hphase : normalAngularPhase θ (w:ℝ) = Complex.exp (Complex.I*(((w:ℝ)* -θ:ℝ):ℂ)) := by
      unfold normalAngularPhase
      congr 1; push_cast; ring
    simp only [hphase,smul_eq_mul,normalWindingTrace,normalLoopPhase,normalOrderedWord,mul_assoc]
  have hS : Summable (fun z => ‖H (e z)‖) := e.summable_iff.mpr hH
  refine ⟨by simpa only [halloc] using hS,?_⟩
  refine Eq.trans (b := ∑' k, H k) ?_ ((e.tsum_eq H).symm.trans (hS.of_norm.tsum_prod.trans ?_))
  swap
  · exact tsum_congr fun w => tsum_congr fun j => halloc (w,j)
  have hj (i) : normalCircleKernel m L θ (p i) (d i)*diracSlash (u i).val = ∑' j, A i j := by
    exact ((normal_circle_term_summable hm hL θ (p i) (d i)).of_norm.tsum_mul_right _).symm
  change (L:ℂ)*tr (normalOrderedWord (fun i => normalCircleKernel m L θ (p i) (d i)*diracSlash (u i).val)) = _
  simp_rw [hj]
  rw [normal_ordered_word_tsum A hA]
  exact ((hP.of_norm.hasSum.map tr.toAddMonoidHom tr.continuous).mul_left (L:ℂ)).tsum_eq.symm

end UV
