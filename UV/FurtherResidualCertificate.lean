import UV.ResidualCoercivity

/-! The signed linear positive-basis certificate for the actual
four-component routing of the residual-coercivity proposition. -/

noncomputable section
open Set
open scoped BigOperators Matrix

namespace UV.FurtherResidual

/-- The least singular value of a real square matrix, in its variational
form on the scalar Euclidean unit sphere. -/
def leastSingular {L : ℕ} (A : Matrix (Fin L) (Fin L) ℝ) : ℝ :=
  sInf ((fun x => ‖Matrix.toEuclideanLin A x‖) '' Metric.sphere 0 1)

theorem leastSingular_spec {L : ℕ} [Nonempty (Fin L)]
    (A : Matrix (Fin L) (Fin L) ℝ) (hA : A.det ≠ 0) :
    0 < leastSingular A ∧ ∀ x, leastSingular A * ‖x‖ ≤ ‖Matrix.toEuclideanLin A x‖ := by
  let f := Matrix.toEuclideanLin A
  have hinj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr hA))
  have hker (x : EuclideanSpace ℝ (Fin L)) (hx : f x = 0) : x = 0 := by
    apply (WithLp.equiv 2 _).injective
    apply hinj
    change A.mulVec (WithLp.ofLp x) = A.mulVec 0
    rw [Matrix.mulVec_zero]
    exact congrArg WithLp.ofLp hx
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin L)) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) f.continuous_of_finiteDimensional.norm.continuousOn
  have hunorm : ‖u‖ = 1 := by simpa using hu
  have hleast : leastSingular A = ‖f u‖ := by
    apply IsLeast.csInf_eq
    refine ⟨⟨u, hu, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hmin hx
  refine ⟨?_, fun x => ?_⟩
  · rw [hleast]
    apply norm_pos_iff.mpr
    intro h
    have hz := hker u h
    simp [hz] at hunorm
  · by_cases hx : x = 0
    · simp [hx]
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let y := ‖x‖⁻¹ • x
    have hy : y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin L)) 1 := by
      simp [y, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), hn.ne']
    have hm := mul_le_mul_of_nonneg_right (hmin hy) hn.le
    simpa [hleast, f, y, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le),
      mul_right_comm _ _ ‖x‖, inv_mul_cancel₀ hn.ne'] using hm

/-- The scalar Euclidean row norm bounds the action of the corresponding
four-component routing row. -/
theorem routed_row_norm_le {I : Type*} {L : ℕ}
    (C : Matrix I (Fin L) ℝ) (i : I) (k : EuclideanSpace ℝ (Fin L × Fin 4)) :
    ‖residualRouting C i k‖ ≤ ‖(WithLp.toLp 2 (C i) : EuclideanSpace ℝ (Fin L))‖ * ‖k‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs, residualRouting_component]
  rw [Fintype.sum_prod_type, Finset.sum_comm (f := fun (j : Fin L) (ν : Fin 4) => k (j, ν) ^ 2),
    Finset.mul_sum]
  exact Finset.sum_le_sum (fun ν _ => Finset.sum_mul_sq_le_sq_mul_sq _ (C i) (fun j => k (j, ν)))

/-- Lifting a square routing minor into the four intrinsic Euclidean
coordinates preserves its scalar least singular value. -/
theorem routed_basis_norm_le_sum {I : Type*} {L : ℕ} [Nonempty (Fin L)]
    (C : Matrix I (Fin L) ℝ) (s : Fin L ↪ I)
    (hs : (C.submatrix s id).det ≠ 0) (k : EuclideanSpace ℝ (Fin L × Fin 4)) :
    leastSingular (C.submatrix s id) * ‖k‖ ≤ ∑ j, ‖residualRouting C (s j) k‖ := by
  let A := C.submatrix s id
  let x (ν : Fin 4) : EuclideanSpace ℝ (Fin L) := WithLp.toLp 2 (fun j => k (j, ν))
  obtain ⟨hσ, hscale⟩ := leastSingular_spec A hs
  have hx : ∑ ν, ‖x ν‖ ^ 2 = ‖k‖ ^ 2 := by
    simp_rw [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    rfl
  have hy : (∑ ν, ‖Matrix.toEuclideanLin A (x ν)‖ ^ 2) =
      ∑ j, ‖residualRouting C (s j) k‖ ^ 2 := by
    simp_rw [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro ν _
    rw [residualRouting_component]
    rfl
  have hsq ν := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr (hscale (x ν))
  apply (sq_le_sq₀ (by positivity) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mp
  calc
    _ = ∑ ν, (leastSingular A * ‖x ν‖) ^ 2 := by
      simp_rw [mul_pow, ← Finset.mul_sum, hx]
      rfl
    _ ≤ ∑ ν, ‖Matrix.toEuclideanLin A (x ν)‖ ^ 2 := Finset.sum_le_sum (fun ν _ => hsq ν)
    _ = ∑ j, ‖residualRouting C (s j) k‖ ^ 2 := hy
    _ ≤ _ := Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

/-- The source's signed positive-basis certificate, pointwise on the
actual Euclidean loop space. Taking a unit-sphere minimum gives exactly
the stated lower bound on the linear margin. -/
theorem signed_linear_basis_certificate {I : Type*} [Fintype I]
    {L : ℕ} [Nonempty (Fin L)] (C : Matrix I (Fin L) ℝ) (h : I → ℝ)
    (s : Fin L ↪ I) (hs : (C.submatrix s id).det ≠ 0)
    (hstar : ℝ) (hstar_pos : 0 < hstar) (hselected : ∀ j, hstar ≤ h (s j))
    (k : EuclideanSpace ℝ (Fin L × Fin 4)) :
    (hstar * leastSingular (C.submatrix s id) -
      ∑ i ∈ Finset.univ.filter (fun i => h i < 0),
        |h i| * ‖(WithLp.toLp 2 (C i) : EuclideanSpace ℝ (Fin L))‖) * ‖k‖ ≤
      ∑ i, h i * ‖residualRouting C i k‖ := by
  classical
  let S : Finset I := Finset.univ.map s
  let N : Finset I := Finset.univ.filter (fun i => h i < 0)
  let normRow i := ‖(WithLp.toLp 2 (C i) : EuclideanSpace ℝ (Fin L))‖
  let normRoute i := ‖residualRouting C i k‖
  have hbound (i : I) :
      (if i ∈ S then hstar * normRoute i else 0) -
          (if i ∈ N then |h i| * normRow i * ‖k‖ else 0) ≤ h i * normRoute i := by
    by_cases hi : i ∈ S
    · obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      have hpos := hstar_pos.trans_le (hselected j)
      have hn : s j ∉ N := by simp [N, not_lt.mpr hpos.le]
      simpa only [hi, hn, if_true, if_false, sub_zero] using
        mul_le_mul_of_nonneg_right (hselected j) (norm_nonneg (residualRouting C (s j) k))
    · by_cases hn : h i < 0
      · have hn' : i ∈ N := by simp [N, hn]
        simp only [hi, hn', if_false, if_true, zero_sub, abs_of_neg hn]
        have ht := mul_le_mul_of_nonpos_left (routed_row_norm_le C i k) hn.le
        simpa only [normRow, normRoute, neg_mul, neg_neg, mul_assoc] using ht
      · have hn' : i ∉ N := by simp [N, hn]
        simp only [hi, hn', if_false, sub_zero]
        exact mul_nonneg (le_of_not_gt hn) (norm_nonneg _)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbound i)
  rw [Finset.sum_sub_distrib, ← Finset.sum_filter, ← Finset.sum_filter] at hsum
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter] at hsum
  rw [← Finset.mul_sum, ← Finset.sum_mul] at hsum
  have hbasis : ∑ j, normRoute (s j) = ∑ i ∈ S, normRoute i := by
    rw [Finset.sum_map]
  have hp := mul_le_mul_of_nonneg_left (routed_basis_norm_le_sum C s hs k) hstar_pos.le
  rw [← hbasis] at hsum
  rw [sub_mul, mul_assoc]
  exact (sub_le_sub_right hp _).trans hsum

/-- The minimum signed residual over the intrinsic Euclidean unit sphere. -/
def linearMargin {I : Type*} [Fintype I] {L : ℕ}
    (C : Matrix I (Fin L) ℝ) (h : I → ℝ) : ℝ :=
  sInf ((fun k => ∑ i, h i * ‖residualRouting C i k‖) '' Metric.sphere 0 1)

/-- The literal minimum estimate using the smallest selected residual
and the scalar smallest singular value, as in the source. -/
theorem signed_linear_margin_basis_certificate {I : Type*} [Fintype I]
    {L : ℕ} [Nonempty (Fin L)] (C : Matrix I (Fin L) ℝ) (h : I → ℝ)
    (s : Fin L ↪ I) (hs : (C.submatrix s id).det ≠ 0) (hpos : ∀ j, 0 < h (s j)) :
    Finset.univ.inf' Finset.univ_nonempty (fun j => h (s j)) * leastSingular (C.submatrix s id) -
      ∑ i ∈ Finset.univ.filter (fun i => h i < 0),
        |h i| * ‖(WithLp.toLp 2 (C i) : EuclideanSpace ℝ (Fin L))‖ ≤ linearMargin C h := by
  classical
  apply le_csInf ((NormedSpace.sphere_nonempty.mpr zero_le_one).image _)
  rintro _ ⟨k, hk, rfl⟩
  have hstar : 0 < Finset.univ.inf' Finset.univ_nonempty (fun j => h (s j)) :=
    (Finset.lt_inf'_iff _).mpr (fun j _ => hpos j)
  have hmin (j : Fin L) : Finset.univ.inf' Finset.univ_nonempty (fun j => h (s j)) ≤ h (s j) :=
    Finset.inf'_le _ (Finset.mem_univ j)
  have hk' : ‖k‖ = 1 := by simpa using hk
  simpa only [hk', mul_one] using signed_linear_basis_certificate C h s hs _ hstar hmin k

end UV.FurtherResidual
