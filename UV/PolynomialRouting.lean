import UV.GlobalConvergence

/-! Polynomial growth is preserved by the actual inverse affine routing.
The constants below are obtained from its operator norm and a uniform bound
on the external shift, rather than supplied as routed-envelope assumptions. -/

noncomputable section
open scoped BigOperators

namespace UV

private theorem one_le_real_finset_product {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  have h := Finset.prod_le_prod (s := s) (f := fun _ => (1 : ℝ))
    (g := f) (fun _ _ => zero_le_one) hf
  simpa only [Finset.prod_const_one] using h

/-- Each coordinate factor is at least one, so their product controls the
    power of the finite-product sup norm. The empty product is also allowed. -/
theorem pi_norm_rpow_le_product {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] {D : ℝ} (hD : 0 ≤ D) (ℓ : ι → E) :
    ‖ℓ‖ ^ D ≤ ∏ j, (1 + ‖ℓ j‖ ^ D) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    letI := hi
    have hn : ‖ℓ‖ = 0 := by simp [Pi.norm_def]
    have hz : (0 : ℝ) ^ D ≤ 1 := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1) hD
    simpa only [hn, Finset.univ_eq_empty, Finset.prod_empty] using hz
  | inr hi =>
    letI := hi
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ
      Finset.univ_nonempty (fun j => ‖ℓ j‖₊)
    have hn : ‖ℓ‖ = ‖ℓ j‖ := by
      simpa only [Pi.norm_def] using congrArg (fun x : NNReal => (x : ℝ)) hj
    rw [hn]
    have hp : 1 ≤ ∏ i ∈ Finset.univ.erase j, (1 + ‖ℓ i‖ ^ D) :=
      one_le_real_finset_product _ _ (fun i _ =>
        le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg (ℓ i)) D))
    calc
      _ ≤ 1 + ‖ℓ j‖ ^ D := le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      _ = (1 + ‖ℓ j‖ ^ D) * 1 := by ring
      _ ≤ (1 + ‖ℓ j‖ ^ D) * ∏ i ∈ Finset.univ.erase j, (1 + ‖ℓ i‖ ^ D) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := Finset.mul_prod_erase Finset.univ
        (fun i => 1 + ‖ℓ i‖ ^ D) (Finset.mem_univ j)

theorem max_pi_norm_rpow_le_product {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] {D : ℝ} (hD : 0 ≤ D) (ℓ : ι → E) :
    (max 1 ‖ℓ‖) ^ D ≤ ∏ j, (1 + ‖ℓ j‖ ^ D) := by
  have hp : 1 ≤ ∏ j, (1 + ‖ℓ j‖ ^ D) :=
    one_le_real_finset_product _ _ (fun j _ =>
      le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg (ℓ j)) D))
  rw [Real.rpow_max (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg ℓ) hD,
    Real.one_rpow]
  exact max_le hp (pi_norm_rpow_le_product hD ℓ)

/-- A bounded external shift gives an explicit uniform operator-norm bound on
    the inverse routing, followed by a factorized polynomial envelope. -/
theorem inverse_affine_polynomial_bound {ι E P : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : (ι → E) ≃L[ℝ] (ι → E)) (b : P → (ι → E))
    {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) (hb : ∀ p, ‖b p‖ ≤ B)
    (p : P) (ℓ : ι → E) :
    1 + ‖e.symm (ℓ - b p)‖ ^ D ≤
      (1 + (‖e.symm.toContinuousLinearMap‖ * (1 + B)) ^ D) *
        ∏ j, (1 + ‖ℓ j‖ ^ D) := by
  let K := ‖e.symm.toContinuousLinearMap‖ * (1 + B)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hx : 0 ≤ max (1 : ℝ) ‖ℓ‖ := le_trans (by norm_num) (le_max_left _ _)
  have hshift : ‖ℓ - b p‖ ≤ (1 + B) * max 1 ‖ℓ‖ := by
    have h₁ := norm_sub_le ℓ (b p)
    have h₂ := le_max_left (1 : ℝ) ‖ℓ‖
    have h₃ := le_max_right (1 : ℝ) ‖ℓ‖
    nlinarith [hb p, mul_nonneg hB (sub_nonneg.mpr h₂)]
  have hr : ‖e.symm (ℓ - b p)‖ ≤ K * max 1 ‖ℓ‖ := by
    calc
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖ℓ - b p‖ :=
        e.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ((1 + B) * max 1 ‖ℓ‖) :=
        mul_le_mul_of_nonneg_left hshift (norm_nonneg _)
      _ = _ := by ring
  have hpower : ‖e.symm (ℓ - b p)‖ ^ D ≤
      K ^ D * ∏ j, (1 + ‖ℓ j‖ ^ D) := by
    calc
      _ ≤ (K * max 1 ‖ℓ‖) ^ D := Real.rpow_le_rpow (norm_nonneg _) hr hD
      _ = K ^ D * (max 1 ‖ℓ‖) ^ D := Real.mul_rpow hK hx
      _ ≤ _ := mul_le_mul_of_nonneg_left (max_pi_norm_rpow_le_product hD ℓ)
        (Real.rpow_nonneg hK D)
  have hp : 1 ≤ ∏ j, (1 + ‖ℓ j‖ ^ D) :=
    one_le_real_finset_product _ _ (fun j _ =>
      le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg (ℓ j)) D))
  change 1 + ‖e.symm (ℓ - b p)‖ ^ D ≤ (1 + K ^ D) * _
  nlinarith

/-- A uniform original-coordinate polynomial numerator estimate therefore
    yields the selected-coordinate product estimate required by the graph
    convergence theorem, with a constant computed from the routing. -/
theorem numerator_bound_after_affine_routing {ι E F P : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    (e : (ι → E) ≃L[ℝ] (ι → E)) (b : P → (ι → E))
    {B C D : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ p, ‖b p‖ ≤ B) (N : P → (ι → E) → F)
    (hN : ∀ p k, ‖N p k‖ ≤ C * (1 + ‖k‖ ^ D)) (p : P) (ℓ : ι → E) :
    ‖N p (e.symm (ℓ - b p))‖ ≤
      (C * (1 + (‖e.symm.toContinuousLinearMap‖ * (1 + B)) ^ D)) *
        ∏ j, (1 + ‖ℓ j‖ ^ D) := by
  calc
    _ ≤ C * (1 + ‖e.symm (ℓ - b p)‖ ^ D) := hN p _
    _ ≤ C * ((1 + (‖e.symm.toContinuousLinearMap‖ * (1 + B)) ^ D) *
        ∏ j, (1 + ‖ℓ j‖ ^ D)) :=
      mul_le_mul_of_nonneg_left (inverse_affine_polynomial_bound e b hB hD hb p ℓ) hC
    _ = _ := by ring

end UV
