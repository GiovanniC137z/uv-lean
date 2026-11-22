import UV.VerifyNetworkMarkedPolynomial

/-! Uniform polynomial bounds for displacement-marked network
coefficients in the actual shared-vertex covariance. -/

noncomputable section

open scoped BigOperators InnerProductSpace Matrix

namespace UV

variable {n : ℕ}

private theorem networkCovariance_pair_bound_of_diagonal
    (Q : NetworkVisitSpace n →L[ℝ] NetworkVisitSpace n)
    (hQ : ∀ u v, inner ℝ u (Q v) = inner ℝ v (Q u))
    {M : ℝ} (hM : 0 ≤ M)
    (hDiag : ∀ x, 0 ≤ inner ℝ x (Q x) ∧ inner ℝ x (Q x) ≤ M * ‖x‖ ^ 2)
    (u v : NetworkVisitSpace n) :
    |inner ℝ u (Q v)| ≤ M * ‖u‖ * ‖v‖ := by
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  let x := ‖u‖⁻¹ • u
  let y := ‖v‖⁻¹ • v
  have hxu : ‖x‖ = 1 := by
    simp only [x, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg u)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]
  have hyv : ‖y‖ = 1 := by
    simp only [y, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have hpol : inner ℝ (x + y) (Q (x + y)) - inner ℝ (x - y) (Q (x - y)) =
      4 * inner ℝ x (Q y) := by
    simp only [map_add, map_sub, inner_add_left, inner_sub_left, inner_add_right, inner_sub_right]
    rw [hQ y x]
    ring
  have hsum : ‖x + y‖ ≤ 2 := by
    linarith only [norm_add_le x y, hxu, hyv]
  have hsub : ‖x - y‖ ≤ 2 := by
    linarith only [norm_sub_le x y, hxu, hyv]
  have hasums := pow_le_pow_left₀ (norm_nonneg _) hsum 2
  have hasubs := pow_le_pow_left₀ (norm_nonneg _) hsub 2
  have hupp := (hDiag (x + y)).2.trans (mul_le_mul_of_nonneg_left hasums hM)
  have hlu := (hDiag (x + y)).1
  have hlow := (hDiag (x - y)).2.trans (mul_le_mul_of_nonneg_left hasubs hM)
  have hll := (hDiag (x - y)).1
  have hxy : |inner ℝ x (Q y)| ≤ M := abs_le.mpr ⟨by linarith only [hpol, hlu, hlow],
    by linarith only [hpol, hupp, hll]⟩
  have hx : (‖u‖ : ℝ) • x = u := by
    rw [show x = ‖u‖⁻¹ • u from rfl, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu), one_smul]
  have hy : (‖v‖ : ℝ) • y = v := by
    rw [show y = ‖v‖⁻¹ • v from rfl, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  have hscale : inner ℝ u (Q v) = (‖u‖ * ‖v‖) * inner ℝ x (Q y) := by
    calc
      _ = ⟪‖u‖ • x, Q (‖v‖ • y)⟫_ℝ := by rw [hx, hy]
      _ = _ := by rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
  rw [hscale, abs_mul, abs_of_nonneg (mul_nonneg (norm_nonneg u) (norm_nonneg v))]
  calc
    _ ≤ (‖u‖ * ‖v‖) * M := mul_le_mul_of_nonneg_left hxy (by positivity)
    _ = _ := by ring

/-- Every covariance pairing costs at most one power of the largest
duration, on the same inverse shared-vertex quadratic form. -/
theorem networkCovariance_pair_duration_bound {E : Type*} [Fintype E]
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (s : E → ℝ) (smin smax : ℝ),
      0 < smin → 0 < smax → (∀ e, smin ≤ s e ∧ s e ≤ smax) →
      ∀ u v : NetworkVisitSpace n,
        |inner ℝ u (networkCovariance src dst s v)| ≤ (smax / γ) * ‖u‖ * ‖v‖ := by
  obtain ⟨γ, C, hγ, hC, hbound⟩ :=
    networkSharedDamping_duration_bounds G src dst hG hcover
  refine ⟨γ, hγ, ?_⟩
  intro s smin smax hmin hmax hs u v
  have hse (e : E) := hmin.trans_le (hs e).1
  apply networkCovariance_pair_bound_of_diagonal _
    (networkCovariance_pair_symmetric G src dst s hG hcover hse) (by positivity) _ u v
  intro x
  rw [← networkSharedDamping_eq_inner]
  exact ⟨(by positivity : 0 ≤ smin / C * ‖x‖ ^ 2).trans
    (hbound s smin smax hmin hmax hs x).1, (hbound s smin smax hmin hmax hs x).2⟩

theorem NetworkMarkPolynomial.evaluate_abs_bound (P : NetworkMarkPolynomial n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : NetworkVisitSpace n →L[ℝ] NetworkVisitSpace n) (M : ℝ), 1 ≤ M →
      (∀ u v, |inner ℝ u (Q v)| ≤ M * ‖u‖ * ‖v‖) →
      ∀ q : NetworkVisitSpace n, |P.evaluate Q q| ≤ C * (M * (1 + ‖q‖)) ^ P.degree := by
  induction P with
  | constant c => exact ⟨|c|, abs_nonneg _, by simp
      [NetworkMarkPolynomial.evaluate, NetworkMarkPolynomial.degree]⟩
  | linear u =>
      refine ⟨‖u‖, norm_nonneg _, fun Q M hM hQ q => ?_⟩
      simp only [NetworkMarkPolynomial.evaluate, NetworkMarkPolynomial.degree, pow_one]
      calc
        _ ≤ M * ‖u‖ * ‖q‖ := hQ u q
        _ = ‖u‖ * (M * ‖q‖) := by ring
        _ ≤ _ := by gcongr; linarith
  | pairing u v =>
      refine ⟨‖u‖ * ‖v‖, by positivity, fun Q M hM hQ q => ?_⟩
      simp only [NetworkMarkPolynomial.evaluate, NetworkMarkPolynomial.degree, pow_one]
      calc
        _ ≤ M * ‖u‖ * ‖v‖ := hQ u v
        _ = (‖u‖ * ‖v‖) * (M * 1) := by ring
        _ ≤ _ := by gcongr; exact le_add_of_nonneg_right (norm_nonneg _)
  | add f g hf hg =>
      obtain ⟨C, hC, hf⟩ := hf
      obtain ⟨D, hD, hg⟩ := hg
      refine ⟨C + D, add_nonneg hC hD, fun Q M hM hQ q => ?_⟩
      let T := M * (1 + ‖q‖)
      have hT : 1 ≤ T := by
        unfold T
        nlinarith [mul_nonneg (zero_le_one.trans hM) (norm_nonneg q)]
      simp only [NetworkMarkPolynomial.evaluate, NetworkMarkPolynomial.degree]
      calc
        _ ≤ |f.evaluate Q q| + |g.evaluate Q q| := abs_add_le _ _
        _ ≤ C * T ^ f.degree + D * T ^ g.degree := add_le_add (hf Q M hM hQ q) (hg Q M hM hQ q)
        _ ≤ C * T ^ (max f.degree g.degree) + D * T ^ (max f.degree g.degree) :=
          add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (le_max_left _ _)) hC)
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (le_max_right _ _)) hD)
        _ = _ := by rw [add_mul]
  | mul f g hf hg =>
      obtain ⟨C, hC, hf⟩ := hf
      obtain ⟨D, hD, hg⟩ := hg
      refine ⟨C * D, mul_nonneg hC hD, fun Q M hM hQ q => ?_⟩
      simp only [NetworkMarkPolynomial.evaluate, NetworkMarkPolynomial.degree, abs_mul, pow_add]
      calc
        _ ≤ (C * (M * (1 + ‖q‖)) ^ f.degree) * (D * (M * (1 + ‖q‖)) ^ g.degree) :=
          mul_le_mul (hf Q M hM hQ q) (hg Q M hM hQ q) (abs_nonneg _) (by positivity)
        _ = _ := by ring

/-- A finite list of actual displacement marks adds at most its length
to both the duration and momentum growth exponents. -/
theorem networkMarkedFourier_norm_bound {E : Type*} [Fintype E]
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst)
    (directions : List (NetworkVisitSpace n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m z s : E → ℝ) (smin smax : ℝ),
      0 < smin → 0 < smax → (∀ e, smin ≤ s e ∧ s e ≤ smax) →
      ∀ q : NetworkVisitSpace n,
        ‖networkMarkedFourier src dst m z s directions q‖ ≤
          (C * (1 + smax) ^ directions.length * (1 + ‖q‖) ^ directions.length) *
            ‖networkSharedFourier src dst m z s q‖ := by
  obtain ⟨γ, hγ, hQ⟩ := networkCovariance_pair_duration_bound G src dst hG hcover
  obtain ⟨C, hC, hP⟩ := (networkMarkPolynomial directions).evaluate_abs_bound
  refine ⟨C * (1 + γ⁻¹) ^ directions.length, by positivity, ?_⟩
  intro m z s smin smax hmin hmax hs q
  let M := (1 + γ⁻¹) * (1 + smax)
  have hM : 1 ≤ M := by
    have hγI : 0 ≤ γ⁻¹ := inv_nonneg.mpr hγ.le
    unfold M
    nlinarith [mul_nonneg hγI hmax.le]
  have hMul : smax / γ ≤ M := by
    rw [div_eq_mul_inv]
    have hγI : 0 ≤ γ⁻¹ := inv_nonneg.mpr hγ.le
    unfold M
    nlinarith
  have hb (u v : NetworkVisitSpace n) :
      |inner ℝ u (networkCovariance src dst s v)| ≤ M * ‖u‖ * ‖v‖ := by
    apply (hQ s smin smax hmin hmax hs u v).trans
    gcongr
  have hh := hP (networkCovariance src dst s) M hM hb q
  have hhPow : 1 ≤ M * (1 + ‖q‖) := by
    nlinarith [mul_nonneg (zero_le_one.trans hM) (norm_nonneg q)]
  rw [networkMarkedFourier_eq_polynomial G src dst m z s hG hcover
    (fun e => hmin.trans_le (hs e).1), norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    _ ≤ C * (M * (1 + ‖q‖)) ^ (networkMarkPolynomial directions).degree := hh
    _ ≤ C * (M * (1 + ‖q‖)) ^ directions.length :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hhPow (networkMarkPolynomial_degree directions)) hC
    _ = _ := by unfold M; rw [mul_pow, mul_pow]; ring

end UV
