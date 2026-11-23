import UV.ContinueRoughCurvatureAngular

/-! Finite angular compression on a closed word. All routings, including
backtracking, appear with their original cyclic order. -/

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace UV.RoughCurvature

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem frobenius_trace_mul (A B : Matrix ι ι ℝ) :
    |(A*B).trace| ≤ ‖A‖ * ‖B‖ := by
  have ht : (A*B).trace = ∑ p : ι × ι, A p.1 p.2 * B p.2 p.1 := by
    rw [Fintype.sum_prod_type]
    rfl
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1
  rw [sq_abs, ht, mul_pow, Matrix.frobenius_norm_def, Matrix.frobenius_norm_def,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)]
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
    (fun p => A p.1 p.2) (fun p => B p.2 p.1)
  rw [Fintype.sum_prod_type (f := fun p : ι × ι => A p.1 p.2 ^ 2),
    Fintype.sum_prod_type (f := fun p : ι × ι => B p.2 p.1 ^ 2), Finset.sum_comm (f := fun i j => B j i ^ 2)] at h
  exact h

private theorem frobenius_prod (A : Matrix ι ι ℝ) (B : List (Matrix ι ι ℝ)) :
    ‖(A :: B).prod‖ ≤ ((A :: B).map norm).prod := by
  induction B generalizing A with
  | nil => simp
  | cons C B ih =>
      rw [List.prod_cons, List.map_cons, List.prod_cons]
      exact (Matrix.frobenius_norm_mul _ _).trans (mul_le_mul_of_nonneg_left (ih C) (norm_nonneg _))

/-- The trace of a finite word with at least two factors has a uniform
Hilbert–Schmidt bound independent of the number of angular modes. -/
theorem frobenius_cycle_le {n : ℕ} (A : Fin (n+2) → Matrix ι ι ℝ) :
    |(List.ofFn A).prod.trace| ≤ ∏ i, ‖A i‖ := by
  rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
  calc
    _ ≤ ‖A 0‖ * ‖(List.ofFn (fun i : Fin (n+1) => A i.succ)).prod‖ := frobenius_trace_mul _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have h := frobenius_prod (A (0 : Fin (n+1)).succ) (List.ofFn (fun i : Fin n => A i.succ.succ))
      rw [List.ofFn_succ (f := fun i : Fin (n+1) => A i.succ), Fin.prod_univ_succ]
      simpa [List.map_ofFn, List.prod_ofFn] using h

private def edgePath {n : ℕ} (x : ι) (k : Fin n → ι) (y : ι) : Fin (n+2) → ι :=
  Fin.cons x (Fin.snoc k y)

omit [Fintype ι] [DecidableEq ι] in
private theorem edgePath_cons {n : ℕ} (x z : ι) (k : Fin n → ι) (y : ι) :
    edgePath x (Fin.cons z k) y = Fin.cons x (edgePath z k y) := by
  unfold edgePath
  rw [← Fin.cons_snoc_eq_snoc_cons]

private theorem matrix_path_formula {n : ℕ} (A : Fin (n+1) → Matrix ι ι ℝ) (x y : ι) :
    (List.ofFn A).prod x y =
      ∑ k : Fin n → ι, ∏ i : Fin (n+1), A i (edgePath x k y i.castSucc) (edgePath x k y i.succ) := by
  induction n generalizing x with
  | zero =>
      simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
        Fintype.sum_unique, Fin.prod_univ_succ, Fin.prod_univ_zero, edgePath, Fin.castSucc_zero,
        Fin.cons_zero, Fin.cons_succ]
      rw [show (0 : Fin 1) = Fin.last 0 by rfl, Fin.snoc_last]
  | succ n ih =>
      rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
      simp_rw [ih (fun i => A i.succ) _, Finset.mul_sum]
      rw [← Fintype.sum_prod_type (f := fun p : ι × (Fin n → ι) =>
        A 0 x p.1 * ∏ i : Fin (n+1), A i.succ (edgePath p.1 p.2 y i.castSucc) (edgePath p.1 p.2 y i.succ))]
      let e : ι × (Fin n → ι) ≃ (Fin (n+1) → ι) := Fin.consEquiv (fun _ => ι)
      apply Fintype.sum_equiv e _ _
      intro p
      rcases p with ⟨z,k⟩
      change A 0 x z *
        (∏ i : Fin (n+1), A i.succ (edgePath z k y i.castSucc) (edgePath z k y i.succ)) =
        ∏ i : Fin (n+2), A i (edgePath x (Fin.cons z k) y i.castSucc) (edgePath x (Fin.cons z k) y i.succ)
      rw [edgePath_cons]
      conv_rhs => rw [Fin.prod_univ_succ]
      simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_succ, edgePath]

/-- The finite matrix trace enumerates precisely the closed mode paths. -/
theorem cycle_trace_formula {n : ℕ} (A : Fin (n+1) → Matrix ι ι ℝ) :
    (List.ofFn A).prod.trace =
      ∑ k : Fin (n+1) → ι, ∏ i : Fin (n+1), A i (k i) (k (i+1)) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, matrix_path_formula]
  rw [← Fintype.sum_prod_type (f := fun p : ι × (Fin n → ι) =>
    ∏ i : Fin (n+1), A i (edgePath p.1 p.2 p.1 i.castSucc) (edgePath p.1 p.2 p.1 i.succ))]
  let e : ι × (Fin n → ι) ≃ (Fin (n+1) → ι) := Fin.consEquiv (fun _ => ι)
  apply Fintype.sum_equiv e _ _
  rintro ⟨x,k⟩
  apply Finset.prod_congr rfl
  intro i _
  have hpath : edgePath x k x = Fin.snoc (Fin.cons x k) x := Fin.cons_snoc_eq_snoc_cons x k x
  rw [hpath, Fin.snoc_castSucc]
  congr 1
  change @Fin.snoc (n+1) (fun _ => ι) (@Fin.cons n (fun _ => ι) x k) x i.succ = @Fin.cons n (fun _ => ι) x k (i+1)
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [show (Fin.last n).succ = Fin.last (n+1) by rfl, Fin.snoc_last]
    have he : Fin.last n + 1 = (0 : Fin (n+1)) := by
      apply Fin.ext
      simp
    rw [he, Fin.cons_zero]
  · rw [← Fin.castSucc_succ, Fin.snoc_castSucc]
    apply congrArg (@Fin.cons n (fun _ => ι) x k)
    simp

end UV.RoughCurvature
