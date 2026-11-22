import UV.AdvanceNetworkRoutedBounds

/-! Momentum integration with polynomial factors and explicit duration
dependence. The positive shift factor is uniform over the bounded external
shift, and the normalization retains the actual independent loop dimension. -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Matrix InnerProductSpace

namespace UV

/-- A Gaussian weighted by a real nonnegative degree can be rescaled at
a cost bounded by a fixed power of the inverse width. -/
theorem networkGaussian_weight_scale (L : ℕ) {a t D : ℝ}
    (ha : 0 < a) (ht : 0 < t) (ht1 : t ≤ 1) (hD : 0 ≤ D) :
    (∫ k : NetworkVisitSpace L, (1 + ‖k‖ ^ D) * Real.exp (-(a * t * ‖k‖ ^ 2))) ≤
      (t⁻¹) ^ (⌈D⌉₊ + 4 * L) *
        (∫ k : NetworkVisitSpace L, (1 + ‖k‖ ^ D) * Real.exp (-(a * ‖k‖ ^ 2))) := by
  let W (u : ℝ) (k : NetworkVisitSpace L) := (1 + ‖k‖ ^ D) * Real.exp (-(a * u * ‖k‖ ^ 2))
  let N := ⌈D⌉₊
  have htInv : 1 ≤ t⁻¹ := by
    simpa only [one_div, one_mul] using (le_div_iff₀ ht).2
      (show (1 : ℝ) * t ≤ 1 from by simpa only [one_mul] using ht1)
  have ht0 : 0 ≤ t⁻¹ := zero_le_one.trans htInv
  have hScale := Measure.integral_comp_inv_smul
    (volume : Measure (NetworkVisitSpace L)) (W t) t
  rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    Nat.mul_comm L 4, abs_of_nonneg (pow_nonneg ht.le _), smul_eq_mul] at hScale
  have hi (u : ℝ) (hu : 0 < u) : Integrable (W u) :=
    integrable_real_degree_gaussian (mul_pos ha hu) hD
  have hiScale : Integrable (fun k : NetworkVisitSpace L => W t (t⁻¹ • k)) :=
    (hi t ht).comp_smul (inv_ne_zero ht.ne')
  have hdom (k : NetworkVisitSpace L) : W t (t⁻¹ • k) ≤ t⁻¹ ^ N * W 1 k := by
    have hp : t⁻¹ ^ D ≤ t⁻¹ ^ N := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le htInv (Nat.le_ceil D)
    have hbase := one_le_pow₀ htInv (n := N)
    have hw : 1 + ‖t⁻¹ • k‖ ^ D ≤ t⁻¹ ^ N * (1 + ‖k‖ ^ D) := by
      rw [norm_smul, Real.norm_of_nonneg ht0, Real.mul_rpow ht0 (norm_nonneg k), mul_add, mul_one]
      exact add_le_add hbase (mul_le_mul_of_nonneg_right hp (by positivity))
    have hsq : a * t * ‖t⁻¹ • k‖ ^ 2 = a * t⁻¹ * ‖k‖ ^ 2 := by
      rw [norm_smul, Real.norm_of_nonneg ht0]
      field_simp
    have he : Real.exp (-(a * t * ‖t⁻¹ • k‖ ^ 2)) ≤ Real.exp (-(a * 1 * ‖k‖ ^ 2)) := by
      rw [hsq]
      exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htInv ha.le) (sq_nonneg _)))
    unfold W
    calc
      _ ≤ (t⁻¹ ^ N * (1 + ‖k‖ ^ D)) * Real.exp (-(a * 1 * ‖k‖ ^ 2)) :=
        mul_le_mul hw he (by positivity) (by positivity)
      _ = _ := by ring
  suffices h : (∫ k, W t k) ≤ t⁻¹ ^ (N + 4 * L) * ∫ k, W 1 k by
    simpa only [W, N, mul_one] using h
  calc
    _ = t⁻¹ ^ (4 * L) * ∫ k, W t (t⁻¹ • k) := by
      rw [hScale, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ ht.ne', one_pow, one_mul]
    _ ≤ t⁻¹ ^ (4 * L) * ∫ k, t⁻¹ ^ N * W 1 k :=
      mul_le_mul_of_nonneg_left (integral_mono hiScale ((hi 1 zero_lt_one).const_mul _)
        hdom) (pow_nonneg ht0 _)
    _ = _ := by rw [integral_const_mul, ← mul_assoc, ← pow_add, add_comm (4 * L) N]

/-- Increasing durations weaken the shared precision. The determinant
prefactor costs at most the explicit power `smax^(2n)`. -/
theorem networkFullPrecision_normalizer_duration_bound {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s : E → ℝ) (smin smax : ℝ),
      0 < smin → 0 < smax → (∀ e, smin ≤ s e ∧ s e ≤ smax) →
      Real.sqrt ((4 * Real.pi) ^ Fintype.card (Fin n × Fin 4) /
        (networkFullPrecision src dst s).det) ≤ K * smax ^ (2 * n) := by
  obtain ⟨γ, C, hγ, hC, hbound⟩ := networkSharedEnergy_duration_bounds G src dst hG hcover
  refine ⟨(4 * Real.pi / γ) ^ (2 * n), by positivity, ?_⟩
  intro s smin smax hmin hmax hs
  let A := networkFullPrecision src dst s
  have hA : A.PosDef := networkFullPrecision_posDef G src dst s hG hcover
    (fun e => hmin.trans_le (hs e).1)
  have hLo (x : NetworkVisitSpace n) : γ / smax * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) := by
    rw [show x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) = networkSharedEnergy src dst s x from
      networkFullPrecision_quadratic src dst s x]
    exact (hbound s smin smax hmin hmax hs x).1
  have hHi (x : NetworkVisitSpace n) : x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) ≤ C / smin * ‖x‖ ^ 2 := by
    rw [show x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) = networkSharedEnergy src dst s x from
      networkFullPrecision_quadratic src dst s x]
    exact (hbound s smin smax hmin hmax hs x).2
  have hdet : (γ / smax) ^ Fintype.card (Fin n × Fin 4) ≤ A.det := by
    rw [hA.1.det_eq_prod_eigenvalues]
    simpa only [Finset.prod_const, Finset.card_univ] using
      Finset.prod_le_prod (fun _ _ => (div_pos hγ hmax).le)
        (fun i _ => (networkSPD_eigenvalue_bounds A hA hLo hHi i).1)
  change Real.sqrt ((4 * Real.pi) ^ Fintype.card (Fin n × Fin 4) / A.det) ≤ _
  calc
    _ ≤ Real.sqrt ((4 * Real.pi) ^ Fintype.card (Fin n × Fin 4) /
          (γ / smax) ^ Fintype.card (Fin n × Fin 4)) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by positivity)
        (by positivity) hdet)
    _ = _ := by
      rw [← div_pow, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
        div_div_eq_mul_div, show n * 4 = (2 * n) * 2 by omega, pow_mul, Real.sqrt_sq (by positivity)]
      have he : 4 * Real.pi * smax / γ = (4 * Real.pi / γ) * smax := by ring
      rw [he, mul_pow]

/-- The normalized integral with any fixed nonnegative real momentum
degree is bounded uniformly in the external shift by a product of
the literal edge prefactor and finite powers of the two duration scales. -/
theorem networkRoutedFourier_weighted_duration_bound {E : Type*} [Fintype E] {n L : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst)
    (B : NetworkVisitSpace L →L[ℝ] NetworkVisitSpace n)
    (hB : Function.Injective B) (R : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 < K ∧ ∀ (m z s : E → ℝ) (smin smax : ℝ),
      0 < smin → 0 < smax → (∀ e, smin ≤ s e ∧ s e ≤ smax) →
      ∀ (b : NetworkVisitSpace n), ‖b‖ ≤ R →
        Integrable (fun k => (1 + ‖k‖ ^ D) * ‖networkRoutedFourier src dst m z s B b k‖) ∧
        (1 / (2 * Real.pi) ^ (4 * L)) *
          (∫ k, (1 + ‖k‖ ^ D) * ‖networkRoutedFourier src dst m z s B b k‖) ≤
          K * networkSharedPrefactor m z s * smax ^ (2 * n) *
            (1 + smin⁻¹) ^ (⌈D⌉₊ + 4 * L) := by
  obtain ⟨a, K₁, ha, hK₁, hdom⟩ := networkRoutedGaussian_duration_envelope G src dst hG hcover B hB R
  obtain ⟨K₂, hK₂, hdet⟩ := networkFullPrecision_normalizer_duration_bound G src dst hG hcover
  let J := ∫ k : NetworkVisitSpace L, (1 + ‖k‖ ^ D) * Real.exp (-(a * ‖k‖ ^ 2))
  have hJ : 0 ≤ J := integral_nonneg (fun _ => by positivity)
  let K := (1 / (2 * Real.pi) ^ (4 * L)) * K₁ * K₂ * (1 + J)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro m z s smin smax hmin hmax hs b hb
  let t := min 1 smin
  let P := networkSharedPrefactor m z s
  let W (k : NetworkVisitSpace L) := (1 + ‖k‖ ^ D) * Real.exp (-(a * t * ‖k‖ ^ 2))
  let F (k : NetworkVisitSpace L) := (1 + ‖k‖ ^ D) * ‖networkRoutedFourier src dst m z s B b k‖
  let C := P * (K₂ * smax ^ (2 * n)) * K₁
  have ht : 0 < t := lt_min zero_lt_one hmin
  have ht1 : t ≤ 1 := min_le_left _ _
  have hse (e : E) : 0 < s e := hmin.trans_le (hs e).1
  have hP : 0 ≤ P := networkSharedPrefactor_nonneg m z s hse
  have hiW : Integrable W := integrable_real_degree_gaussian (mul_pos ha ht) hD
  have hWF (k : NetworkVisitSpace L) : F k ≤ C * W k := by
    let N := Real.sqrt ((4 * Real.pi) ^ Fintype.card (Fin n × Fin 4) /
      (networkFullPrecision src dst s).det)
    have hN : N ≤ K₂ * smax ^ (2 * n) := hdet s smin smax hmin hmax hs
    have he := hdom s smin smax hmin hmax hs b hb k
    calc
      F k = (1 + ‖k‖ ^ D) * (P * N * Real.exp (-networkSharedDamping src dst s (B k + b))) := by
        rw [show F k = (1 + ‖k‖ ^ D) * ‖networkSharedFourier src dst m z s (B k + b)‖ from rfl,
          networkSharedFourier_norm G src dst m z s hG hcover hse]
        rfl
      _ ≤ (1 + ‖k‖ ^ D) * (P * (K₂ * smax ^ (2 * n)) *
          (K₁ * Real.exp (-(a * t * ‖k‖ ^ 2)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hN hP) he (by positivity) (by positivity)
      _ = C * W k := by unfold C W; ring
  have hFm : AEStronglyMeasurable F volume := by
    simp_rw [F, networkRoutedFourier, networkSharedFourier_norm G src dst m z s hG hcover hse]
    apply Measurable.aestronglyMeasurable
    unfold dotProduct Matrix.mulVec
    fun_prop
  have hiF : Integrable F := (hiW.const_mul C).mono' hFm (Eventually.of_forall (fun k => by
    rw [Real.norm_of_nonneg (show 0 ≤ F k by unfold F; positivity)]
    exact hWF k))
  have hInv : t⁻¹ ≤ 1 + smin⁻¹ := by
    by_cases hs1 : smin ≤ 1
    · rw [show t = smin from min_eq_right hs1]
      exact le_add_of_nonneg_left zero_le_one
    · rw [show t = 1 from min_eq_left (le_of_not_ge hs1), inv_one]
      exact le_add_of_nonneg_right (inv_nonneg.mpr hmin.le)
  have hJbound : (∫ k, W k) ≤ (1 + smin⁻¹) ^ (⌈D⌉₊ + 4 * L) * (1 + J) := by
    refine (networkGaussian_weight_scale L ha ht ht1 hD).trans ?_
    exact mul_le_mul (pow_le_pow_left₀ (inv_nonneg.mpr ht.le) hInv _)
      (le_add_of_nonneg_left zero_le_one) hJ (by positivity)
  refine ⟨hiF, ?_⟩
  change (1 / (2 * Real.pi) ^ (4 * L)) * (∫ k, F k) ≤ _
  have hiUpper := integral_mono hiF (hiW.const_mul C) hWF
  rw [integral_const_mul] at hiUpper
  calc
    _ ≤ (1 / (2 * Real.pi) ^ (4 * L)) *
        (C * ((1 + smin⁻¹) ^ (⌈D⌉₊ + 4 * L) * (1 + J))) :=
      mul_le_mul_of_nonneg_left (hiUpper.trans (mul_le_mul_of_nonneg_left hJbound (by positivity)))
        (by positivity)
    _ = _ := by unfold K C P; ring

end UV
