import UV.ContinueRetainedGaussianMass

/-! A null conditional score produces an infinite Gaussian integral with
respect to the actual Lebesgue measure in the loop slots. -/

noncomputable section

open Matrix MeasureTheory Set
open scoped Matrix BigOperators InnerProductSpace ENNReal

namespace UV

private theorem retained_lintegral_fin_prod {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] {n : ℕ} (f : Fin n → X → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : Fin n → X, ∏ i, f i (x i) ∂Measure.pi (fun _ => μ)) =
      ∏ i, ∫⁻ x, f i x ∂μ := by
  induction n with
  | zero => simp only [Finset.univ_eq_empty, Finset.prod_empty, lintegral_const,
      one_mul, Measure.pi_empty_univ]
  | succ n ih =>
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0).symm
    have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    calc
      _ = ∫⁻ p : X × (Fin n → X), f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i)
          ∂μ.prod (Measure.pi (fun _ => μ)) := by
        rw [← he.lintegral_comp_emb e.measurableEmbedding]
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
          Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = _ := by
        have htail : Measurable (fun x : Fin n → X => ∏ i : Fin n, f i.succ (x i)) :=
          Finset.measurable_prod _ fun i _ => (hf i.succ).comp (measurable_pi_apply i)
        rw [lintegral_prod_mul (hf 0).aemeasurable htail.aemeasurable,
          ih (fun i => f i.succ) (fun i => hf i.succ), Fin.prod_univ_succ]

private theorem retained_lintegral_prod {R X : Type*} [Fintype R] [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (f : R → X → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : R → X, ∏ i, f i (x i) ∂Measure.pi (fun _ => μ)) =
      ∏ i, ∫⁻ x, f i x ∂μ := by
  let e := (Fintype.equivFin R).symm
  rw [← (measurePreserving_piCongrLeft (fun _ : R => μ) e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact retained_lintegral_fin_prod μ (fun i => f (e i)) (fun i => hf (e i))

theorem retainedGaussian_lintegral_top {R : Type*} [Fintype R] [DecidableEq R]
    (A : Matrix R R ℝ) (hA : A.PosSemidef) (hSingular : ¬A.PosDef) :
    (∫⁻ x, ENNReal.ofReal (retainedGaussian A x)) = ∞ := by
  let b := hA.1.eigenvectorBasis
  let e : EuclideanSpace ℝ R ≃ᵐ (R → ℝ) := b.measurableEquiv.trans (EuclideanSpace.measurableEquiv R)
  have he : MeasurePreserving e volume volume :=
    (EuclideanSpace.volume_preserving_measurableEquiv R).comp b.measurePreserving_measurableEquiv
  let g (i : R) (x : ℝ) := ENNReal.ofReal (Real.exp (-(hA.1.eigenvalues i * x ^ 2 / 2)))
  have hg (i : R) : Measurable (g i) := by
    dsimp [g]
    fun_prop
  have hcoords (x : EuclideanSpace ℝ R) :
      ENNReal.ofReal (retainedGaussian A x) = ∏ i, g i (e x i) := by
    rw [retainedGaussian, networkBasis_quadratic A b hA.1.eigenvalues
      (networkSPD_eigenbasis_action A hA.1), Finset.sum_div, ← Finset.sum_neg_distrib, Real.exp_sum]
    rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
    rfl
  simp_rw [hcoords]
  rw [he.lintegral_comp_emb e.measurableEmbedding (fun x => ∏ i, g i (x i))]
  change (∫⁻ x : R → ℝ, ∏ i, g i (x i) ∂Measure.pi (fun _ => volume)) = _
  rw [retained_lintegral_prod _ _ hg]
  have hzero : ∃ i, hA.1.eigenvalues i = 0 := by
    by_contra! h
    exact hSingular (hA.1.posDef_iff_eigenvalues_pos.mpr (fun i =>
      lt_of_le_of_ne (hA.eigenvalues_nonneg i) (Ne.symm (h i))))
  obtain ⟨j, hj⟩ := hzero
  have htop : (∫⁻ x, g j x) = ∞ := by
    simp [g, hj]
  have hpos (i : R) : 0 < (∫⁻ x, g i x) := by
    rw [lintegral_pos_iff_support (hg i)]
    have hs : Function.support (g i) = univ := by
      ext x
      simp [Function.mem_support, g, (Real.exp_pos _).not_ge]
    rw [hs, Real.volume_univ]
    exact ENNReal.zero_lt_top
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), htop, ENNReal.top_mul]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => (hpos i).ne'

theorem retainedFourGaussian_lintegral_top {R : Type*} [Fintype R] [DecidableEq R]
    (A : Matrix R R ℝ) (hA : A.PosSemidef) (hSingular : ¬A.PosDef) :
    (∫⁻ x, ENNReal.ofReal (retainedFourGaussian A x)) = ∞ := by
  have he (x : Fin 4 → EuclideanSpace ℝ R) :
      ENNReal.ofReal (retainedFourGaussian A x) =
        ∏ i, ENNReal.ofReal (retainedGaussian A (x i)) :=
    ENNReal.ofReal_prod_of_nonneg (fun i _ =>
      show 0 ≤ retainedGaussian A (x i) from (Real.exp_pos _).le)
  simp_rw [he]
  change (∫⁻ x : Fin 4 → EuclideanSpace ℝ R,
    ∏ i, ENNReal.ofReal (retainedGaussian A (x i)) ∂Measure.pi (fun _ => volume)) = _
  have hm : Measurable (fun x => ENNReal.ofReal (retainedGaussian A x)) := by
    unfold retainedGaussian mulVec dotProduct
    fun_prop
  rw [retained_lintegral_fin_prod volume
    (fun _ : Fin 4 => fun x => ENNReal.ofReal (retainedGaussian A x)) (fun _ => hm)]
  simp [retainedGaussian_lintegral_top A hA hSingular]

theorem retainedK0_eq_top {E S L : Type*} [Fintype E] [Fintype S] [Fintype L]
    [DecidableEq E] [DecidableEq S] [DecidableEq L]
    (t : E → ℝ) (ht : ∀ e, 0 < t e) (C : Matrix S E ℝ) (J : Matrix L E ℝ)
    (hC : C.rank = Fintype.card S)
    (hM : (fromRows C J).rank ≠ Fintype.card S + Fintype.card L) :
    retainedK0 t C J = ∞ := by
  have hA := (retainedGram_posDef_iff_rank t ht C).mpr hC
  have hQ := retainedSchur_posSemidef t ht C J hC
  have hsing : ¬ (retainedSchur t C J).PosDef :=
    fun h => hM ((retainedSchur_posDef_iff_rank t ht C J hC).mp h)
  rw [retainedK0, retainedFourGaussian_lintegral_top _ hQ hsing,
    retainedSeamDensityAtZero_formula _ hA, ENNReal.mul_top]
  apply ne_of_gt
  rw [ENNReal.ofReal_pos]
  exact div_pos (inv_pos.mpr (mul_pos (by positivity) (pow_pos hA.det_pos _)))
    (by positivity)

theorem retainedK0_lt_top_iff_rank {E S L : Type*} [Fintype E] [Fintype S] [Fintype L]
    [DecidableEq E] [DecidableEq S] [DecidableEq L]
    (t : E → ℝ) (ht : ∀ e, 0 < t e) (C : Matrix S E ℝ) (J : Matrix L E ℝ)
    (hC : C.rank = Fintype.card S) :
    retainedK0 t C J < ∞ ↔ (fromRows C J).rank = Fintype.card S + Fintype.card L := by
  constructor
  · intro h
    contrapose! h
    exact (retainedK0_eq_top t ht C J hC h).ge
  · intro h
    rw [retainedK0_eq t ht C J hC h]
    exact ENNReal.ofReal_lt_top

end UV
