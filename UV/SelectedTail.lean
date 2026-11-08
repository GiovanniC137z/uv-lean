import UV.GlobalConvergence

/-! Quantitative tails in independent selected-line coordinates.  The
one-line constant is the actual four-dimensional Gamma/moment constant. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal

namespace UV

theorem norm_rpow_tail {E : Type*} [NormedAddCommGroup E]
    {R d δ : ℝ} (hR : 0 < R) (hδ : 0 ≤ δ) {q : E} (hq : R < ‖q‖) :
    ‖q‖ ^ d ≤ R ^ (-δ) * ‖q‖ ^ (d + δ) := by
  have hn : 0 < ‖q‖ := hR.trans hq
  have hr := Real.rpow_le_rpow hR.le hq.le hδ
  have hp : 0 < R ^ δ := Real.rpow_pos_of_pos hR δ
  rw [Real.rpow_add hn, Real.rpow_neg hR.le]
  have hh : 1 ≤ (R ^ δ)⁻¹ * ‖q‖ ^ δ := by
    rw [← div_eq_inv_mul, le_div_iff₀ hp]
    simpa using hr
  calc
    ‖q‖ ^ d = ‖q‖ ^ d * 1 := (mul_one _).symm
    _ ≤ ‖q‖ ^ d * ((R ^ δ)⁻¹ * ‖q‖ ^ δ) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (norm_nonneg q) d)
    _ = _ := by ring

/-- Exact source one-line tail bound, with the full Laplace transform. -/
theorem actual_selected_line_tail_le
    (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0)
    {a d δ R : ℝ} (ha : 0 < a) (hd : 0 ≤ d) (hδ : 0 < δ) (hR : 0 < R)
    (hM : inverseMoment ρ (1 + (d + δ) / 2) < ⊤) (m : ℝ) :
    (∫ q : LoopMomentum in {q | R < ‖q‖},
      ‖q‖ ^ d * laplace ρ (a ^ 2 * ‖q‖ ^ 2) / (‖q‖ ^ 2 + m ^ 2)) ≤
      R ^ (-δ) * lineMomentBound ρ a (d + δ) := by
  have hsmall : inverseMoment ρ (1 + d / 2) < ⊤ :=
    inverseMoment_lower_order_finite ρ (by linarith) (by linarith) hM
  have hi := actual_selected_line_integrable ρ hneg hzero ha hd hsmall m
  have hi' := actual_selected_line_integrable ρ hneg hzero ha (add_nonneg hd hδ.le) hM m
  have hn (q : LoopMomentum) :
      0 ≤ laplace ρ (a ^ 2 * ‖q‖ ^ 2) / (‖q‖ ^ 2 + m ^ 2) := by
    apply div_nonneg
    · exact integral_nonneg fun _ => Real.exp_nonneg _
    · positivity
  have hb : (∫ q : LoopMomentum in {q | R < ‖q‖},
      ‖q‖ ^ d * laplace ρ (a ^ 2 * ‖q‖ ^ 2) / (‖q‖ ^ 2 + m ^ 2)) ≤
      ∫ q : LoopMomentum in {q | R < ‖q‖},
        R ^ (-δ) * (‖q‖ ^ (d + δ) * laplace ρ (a ^ 2 * ‖q‖ ^ 2) /
          (‖q‖ ^ 2 + m ^ 2)) := by
    apply integral_mono_ae hi.integrableOn (hi'.const_mul _).integrableOn
    filter_upwards [ae_restrict_mem (isOpen_lt continuous_const continuous_norm).measurableSet] with q hq
    have hh := mul_le_mul_of_nonneg_right (norm_rpow_tail (d := d) hR hδ.le hq) (hn q)
    convert hh using 1 <;> ring
  calc
    _ ≤ _ := hb
    _ ≤ ∫ q : LoopMomentum,
        R ^ (-δ) * (‖q‖ ^ (d + δ) * laplace ρ (a ^ 2 * ‖q‖ ^ 2) /
          (‖q‖ ^ 2 + m ^ 2)) := by
      apply setIntegral_le_integral (hi'.const_mul _)
      apply Filter.Eventually.of_forall
      intro q
      apply mul_nonneg (Real.rpow_nonneg hR.le _)
      rw [mul_div_assoc]
      exact mul_nonneg (Real.rpow_nonneg (norm_nonneg q) _) (hn q)
    _ = R ^ (-δ) * ∫ q : LoopMomentum,
        ‖q‖ ^ (d + δ) * laplace ρ (a ^ 2 * ‖q‖ ^ 2) / (‖q‖ ^ 2 + m ^ 2) :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (actual_selected_line_integral_le ρ hneg hzero ha (add_nonneg hd hδ.le) hM m)
      (Real.rpow_nonneg hR.le _)

/-- Finite-dimensional union bound with independent selected coordinates.
The right side replaces just the omitted coordinate's factor each time. -/
theorem selected_product_union_tail
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w u : ι → LoopMomentum → ℝ)
    (hw : ∀ i, Integrable (w i)) (hu : ∀ i, Integrable (u i))
    (hwn : ∀ i q, 0 ≤ w i q) (hun : ∀ i q, 0 ≤ u i q)
    {R δ : ℝ} (hR : 0 < R)
    (ht : ∀ i q, R < ‖q‖ → w i q ≤ R ^ (-δ) * u i q) :
    (∫ ℓ : ι → LoopMomentum in {ℓ | ∃ j, R < ‖ℓ j‖},
      ∏ i, w i (ℓ i) ∂(Measure.pi fun _ : ι => volume)) ≤
      R ^ (-δ) * ∑ j, ∏ i, ∫ q, if i = j then u i q else w i q := by
  classical
  let μ := Measure.pi fun _ : ι => (volume : Measure LoopMomentum)
  let v (j i : ι) (q : LoopMomentum) := if i = j then u i q else w i q
  have hv (j i : ι) : Integrable (v j i) := by
    by_cases h : i = j <;> simp [v, h, hw, hu]
  have hvn (j i : ι) (q : LoopMomentum) : 0 ≤ v j i q := by
    dsimp [v]
    split_ifs <;> simp [hwn, hun]
  have hp (j : ι) : Integrable (fun ℓ : ι → LoopMomentum => ∏ i, v j i (ℓ i)) μ :=
    Integrable.fintype_prod (hv j)
  have hs : Integrable (fun ℓ : ι → LoopMomentum =>
      R ^ (-δ) * ∑ j, ∏ i, v j i (ℓ i)) μ :=
    (integrable_finset_sum _ fun j _ => hp j).const_mul _
  have hi : Integrable (fun ℓ : ι → LoopMomentum => ∏ i, w i (ℓ i)) μ :=
    Integrable.fintype_prod hw
  have hbound {ℓ : ι → LoopMomentum} (hℓ : ∃ j, R < ‖ℓ j‖) :
      (∏ i, w i (ℓ i)) ≤ R ^ (-δ) * ∑ j, ∏ i, v j i (ℓ i) := by
    obtain ⟨j, hj⟩ := hℓ
    have hh : (∏ i, w i (ℓ i)) ≤
        ∏ i, ((if i = j then R ^ (-δ) else 1) * v j i (ℓ i)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact hwn i _
      · intro i _
        by_cases hij : i = j
        · simpa [v, hij] using ht j (ℓ j) hj
        · simp [v, hij]
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq'] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun j => ∏ i, v j i (ℓ i))
        (fun i _ => Finset.prod_nonneg fun k _ => hvn i k (ℓ k))
        (Finset.mem_univ j)) (Real.rpow_nonneg hR.le _))
  calc
    _ ≤ ∫ ℓ : ι → LoopMomentum in {ℓ | ∃ j, R < ‖ℓ j‖},
        R ^ (-δ) * ∑ j, ∏ i, v j i (ℓ i) ∂μ := by
      apply integral_mono_ae hi.integrableOn hs.integrableOn
      have hm : MeasurableSet {ℓ : ι → LoopMomentum | ∃ j, R < ‖ℓ j‖} := by
        have he : {ℓ : ι → LoopMomentum | ∃ j, R < ‖ℓ j‖} =
            ⋃ j : ι, {ℓ : ι → LoopMomentum | R < ‖ℓ j‖} := by ext; simp
        rw [he]
        apply MeasurableSet.iUnion
        intro j
        exact (isOpen_lt continuous_const (continuous_apply j).norm).measurableSet
      filter_upwards [ae_restrict_mem hm] with ℓ hℓ
      exact hbound hℓ
    _ ≤ ∫ ℓ : ι → LoopMomentum,
        R ^ (-δ) * ∑ j, ∏ i, v j i (ℓ i) ∂μ := by
      apply setIntegral_le_integral hs
      exact Filter.Eventually.of_forall fun ℓ => mul_nonneg
        (Real.rpow_nonneg hR.le _) (Finset.sum_nonneg fun j _ =>
          Finset.prod_nonneg fun i _ => hvn j i _)
    _ = _ := by
      rw [integral_const_mul, integral_finset_sum _ fun j _ => hp j]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact integral_fintype_prod_eq_prod (v j)

def selectedTailWeight (ρ : Measure ℝ) (a m d δ : ℝ) (q : LoopMomentum) : ℝ :=
  (‖q‖ ^ δ + ‖q‖ ^ (d + δ)) * selectedLine ρ a m q

theorem selectedTailWeight_nonneg (ρ : Measure ℝ) (a m d δ : ℝ) (q : LoopMomentum) :
    0 ≤ selectedTailWeight ρ a m d δ q := by
  unfold selectedTailWeight
  exact mul_nonneg (by positivity) (selectedLine_nonneg ρ a m q)

theorem selectedTailWeight_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {a d D δ : ℝ} (ha : 0 < a) (hd : 0 ≤ d) (hdD : d ≤ D) (hδ : 0 ≤ δ)
    (hM : inverseMoment ρ (1 + (D + δ) / 2) < ⊤) (m : ℝ) :
    Integrable (selectedTailWeight ρ a m d δ) := by
  have h1 := selectedLine_integrable_of_highest_moment ρ ha hδ
    (show δ ≤ D + δ by linarith) hM m
  have h2 := selectedLine_integrable_of_highest_moment ρ ha (add_nonneg hd hδ)
    (add_le_add_right hdD δ) hM m
  convert h1.add h2 using 1
  ext q
  simp only [selectedTailWeight, add_mul, Pi.add_apply]

theorem selectedTailWeight_integral_le (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {a d D δ : ℝ} (ha : 0 < a) (hd : 0 ≤ d) (hdD : d ≤ D) (hδ : 0 ≤ δ)
    (hM : inverseMoment ρ (1 + (D + δ) / 2) < ⊤) (m : ℝ) :
    (∫ q, selectedTailWeight ρ a m d δ q) ≤
      lineMomentBound ρ a δ + lineMomentBound ρ a (d + δ) := by
  have hM1 : inverseMoment ρ (1 + δ / 2) < ⊤ :=
    inverseMoment_lower_order_finite ρ (by linarith) (by linarith) hM
  have hM2 : inverseMoment ρ (1 + (d + δ) / 2) < ⊤ :=
    inverseMoment_lower_order_finite ρ (by linarith) (by linarith) hM
  have h1 := selectedLine_weight_integrable ρ ha hδ hM1 m
  have h2 := selectedLine_weight_integrable ρ ha (add_nonneg hd hδ) hM2 m
  simp only [selectedTailWeight, add_mul]
  rw [integral_add h1 h2]
  exact add_le_add (selectedLine_integral_le ρ ha hδ hM1 m)
    (selectedLine_integral_le ρ ha (add_nonneg hd hδ) hM2 m)

theorem selectedWeight_tail_le (ρ : Measure ℝ) (a m d : ℝ)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 ≤ δ) {q : LoopMomentum} (hq : R < ‖q‖) :
    selectedWeight ρ a m d q ≤ R ^ (-δ) * selectedTailWeight ρ a m d δ q := by
  have h0 := norm_rpow_tail (d := 0) hR hδ hq
  have hd := norm_rpow_tail (d := d) hR hδ hq
  simp only [Real.rpow_zero, zero_add] at h0
  unfold selectedWeight selectedTailWeight
  have hh := mul_le_mul_of_nonneg_right (add_le_add h0 hd) (selectedLine_nonneg ρ a m q)
  convert hh using 1
  ring

/-- Explicit uniform tail for any complete finite anisotropic graph envelope.
Each summand replaces only one line's moment budget at a time. -/
theorem optimized_selected_graph_tail
    {ι A P F : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ι → Measure ℝ) [∀ j, IsFiniteMeasure (ρ j)]
    (a m D : ι → ℝ) (d : A → ι → ℝ) (c : A → ℝ)
    (ha : ∀ j, 0 < a j) (hd : ∀ α j, 0 ≤ d α j)
    (hdD : ∀ α j, d α j ≤ D j) (hD : ∀ j, 0 ≤ D j) (hc : ∀ α, 0 ≤ c α)
    {δ : ℝ} (hδ : 0 < δ)
    (hM : ∀ j, inverseMoment (ρ j) (1 + (D j + δ) / 2) < ⊤)
    (f : P → (ι → LoopMomentum) → F)
    (hf : ∀ p, AEStronglyMeasurable (f p) (Measure.pi fun _ : ι => volume))
    (hb : ∀ p ℓ, ‖f p ℓ‖ ≤ ∑ α, c α *
      ∏ j, selectedWeight (ρ j) (a j) (m j) (d α j) (ℓ j))
    {R : ℝ} (hR : 0 < R) :
    ∀ p, (∫ ℓ : ι → LoopMomentum in {ℓ | ∃ j, R < ‖ℓ j‖},
      ‖f p ℓ‖ ∂(Measure.pi fun _ : ι => volume)) ≤
      R ^ (-δ) * ∑ α, c α * ∑ j, ∏ i,
        if i = j then
          lineMomentBound (ρ i) (a i) δ + lineMomentBound (ρ i) (a i) (d α i + δ)
        else lineMomentBound (ρ i) (a i) 0 + lineMomentBound (ρ i) (a i) (d α i) := by
  classical
  let μ := Measure.pi fun _ : ι => (volume : Measure LoopMomentum)
  let w (α : A) (i : ι) := selectedWeight (ρ i) (a i) (m i) (d α i)
  let u (α : A) (i : ι) := selectedTailWeight (ρ i) (a i) (m i) (d α i) δ
  have hM0 (j : ι) : inverseMoment (ρ j) (1 + D j / 2) < ⊤ :=
    inverseMoment_lower_order_finite (ρ j) (by linarith [hD j]) (by linarith) (hM j)
  have hw (α : A) (i : ι) : Integrable (w α i) :=
    selectedWeight_integrable (ρ i) (ha i) (hd α i) (hdD α i) (hM0 i) (m i)
  have hu (α : A) (i : ι) : Integrable (u α i) :=
    selectedTailWeight_integrable (ρ i) (ha i) (hd α i) (hdD α i) hδ.le (hM i) (m i)
  have hp (α : A) : Integrable (fun ℓ : ι → LoopMomentum => ∏ i, w α i (ℓ i)) μ :=
    Integrable.fintype_prod (hw α)
  have hs : Integrable (fun ℓ : ι → LoopMomentum => ∑ α, c α * ∏ i, w α i (ℓ i)) μ :=
    integrable_finset_sum _ fun α _ => (hp α).const_mul _
  intro p
  have hfp := hs.mono' (hf p) (Filter.Eventually.of_forall (hb p))
  calc
    _ ≤ ∫ ℓ : ι → LoopMomentum in {ℓ | ∃ j, R < ‖ℓ j‖},
        ∑ α, c α * ∏ i, w α i (ℓ i) ∂μ :=
      integral_mono_ae hfp.norm.integrableOn hs.integrableOn
        (Filter.Eventually.of_forall fun ℓ => hb p ℓ)
    _ = ∑ α, c α * ∫ ℓ : ι → LoopMomentum in {ℓ | ∃ j, R < ‖ℓ j‖},
        ∏ i, w α i (ℓ i) ∂μ := by
      rw [integral_finset_sum _ fun α _ => ((hp α).const_mul _).integrableOn]
      simp only [integral_const_mul]
    _ ≤ ∑ α, c α * (R ^ (-δ) * ∑ j, ∏ i,
        ∫ q, if i = j then u α i q else w α i q) := by
      apply Finset.sum_le_sum
      intro α _
      apply mul_le_mul_of_nonneg_left _ (hc α)
      exact selected_product_union_tail (w α) (u α) (hw α) (hu α)
        (fun i => selectedWeight_nonneg _ _ _ _) (fun i => selectedTailWeight_nonneg _ _ _ _ _)
        hR (fun i q hq => selectedWeight_tail_le _ _ _ _ hR hδ.le hq)
    _ ≤ R ^ (-δ) * ∑ α, c α * ∑ j, ∏ i,
        if i = j then
          lineMomentBound (ρ i) (a i) δ + lineMomentBound (ρ i) (a i) (d α i + δ)
        else lineMomentBound (ρ i) (a i) 0 + lineMomentBound (ρ i) (a i) (d α i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro α _
      rw [mul_left_comm (c α)]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hR.le _)
      apply mul_le_mul_of_nonneg_left _ (hc α)
      apply Finset.sum_le_sum
      intro j _
      apply Finset.prod_le_prod
      · intro i _
        apply integral_nonneg
        intro q
        split_ifs
        · exact selectedTailWeight_nonneg _ _ _ _ _ _
        · exact selectedWeight_nonneg _ _ _ _ _
      · intro i _
        by_cases hij : i = j
        · simp only [hij, if_pos]
          exact selectedTailWeight_integral_le (ρ j) (ha j) (hd α j) (hdD α j)
            hδ.le (hM j) (m j)
        · simp only [hij, if_false]
          exact selectedWeight_integral_le (ρ i) (ha i) (hd α i) (hdD α i) (hM0 i) (m i)

end UV
