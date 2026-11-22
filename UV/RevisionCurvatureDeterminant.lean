import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Finite-mode relative determinant of the compact curvature comparison,
with the depth kept common to the entire finite set of modes. -/

namespace UV.RevisionCurvatureDeterminant

open Filter
open scoped BigOperators Topology

/-- The literal inverse determinant power from the two copied kinetic terms. -/
noncomputable def relativeDeterminant {K : Type*} (modes : Finset K) (freq : K → ℝ)
    (depth : ℝ) (n : ℕ) : ℝ :=
  (∏ k ∈ modes, (1 + Real.exp (-2 * depth * freq k)) ^ n)⁻¹

theorem relative_determinant_bounds {K : Type*} (modes : Finset K) (freq : K → ℝ)
    (depth : ℝ) (n : ℕ) : 0 < relativeDeterminant modes freq depth n ∧
      relativeDeterminant modes freq depth n ≤ 1 := by
  have hprod : 1 ≤ ∏ k ∈ modes, (1 + Real.exp (-2 * depth * freq k)) ^ n := by
    simpa only [Finset.prod_const_one] using
      (Finset.prod_le_prod (s := modes) (f := fun _ => (1 : ℝ))
        (g := fun k => (1 + Real.exp (-2 * depth * freq k)) ^ n)
        (fun _ _ => zero_le_one)
        (fun _ _ => one_le_pow₀ (le_add_of_nonneg_right (Real.exp_nonneg _))))
  exact ⟨inv_pos.mpr (zero_lt_one.trans_le hprod), inv_le_one_of_one_le₀ hprod⟩

/-- Every retained mode inside the depth ball costs a uniform amount in
the logarithm of the same determinant. -/
theorem relative_determinant_mode_bound {K : Type*} {modes inside : Finset K}
    (hsub : inside ⊆ modes) (freq : K → ℝ) (depth : ℝ) (n : ℕ)
    (hshort : ∀ k ∈ inside, depth * freq k ≤ 1) :
    relativeDeterminant modes freq depth n ≤
      Real.exp (-((n : ℝ) * inside.card) * Real.log (1 + Real.exp (-2))) := by
  let f (k : K) := 1 + Real.exp (-2 * depth * freq k)
  have hfp (k : K) : 0 < f k := by dsimp [f]; positivity
  have hlog (k : K) : 0 ≤ Real.log (f k) := by
    apply Real.log_nonneg
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  have hs : (inside.card : ℝ) * Real.log (1 + Real.exp (-2)) ≤
      ∑ k ∈ modes, Real.log (f k) := by
    calc
      _ = ∑ _k ∈ inside, Real.log (1 + Real.exp (-2)) := by simp
      _ ≤ ∑ k ∈ inside, Real.log (f k) := by
        apply Finset.sum_le_sum
        intro k hk
        apply Real.log_le_log (by positivity)
        dsimp [f]
        apply add_le_add_left
        exact Real.exp_le_exp.mpr (by linarith [hshort k hk])
      _ ≤ ∑ k ∈ modes, Real.log (f k) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => hlog k
  have hd : relativeDeterminant modes freq depth n =
      Real.exp (-(n : ℝ) * ∑ k ∈ modes, Real.log (f k)) := by
    have hp : 0 < ∏ k ∈ modes, f k ^ n := Finset.prod_pos fun k _ => pow_pos (hfp k) _
    unfold relativeDeterminant
    change (∏ k ∈ modes, f k ^ n)⁻¹ = _
    rw [← Real.exp_log hp, ← Real.exp_neg, Real.log_prod _ _ (fun k _ => (pow_pos (hfp k) _).ne')]
    simp only [Real.log_pow, Finset.mul_sum, Finset.sum_neg_distrib, neg_mul]
  rw [hd]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n)]

/-- A count of at least (c R^4) low modes yields the quartic exponential
budget, without requiring the modes outside the depth ball to be independent. -/
theorem relative_determinant_quartic_bound {K : Type*} {modes inside : Finset K}
    (hsub : inside ⊆ modes) (freq : K → ℝ) (depth : ℝ) {n : ℕ} (hn : 0 < n)
    (hshort : ∀ k ∈ inside, depth * freq k ≤ 1) {c R : ℝ} (hc : 0 < c)
    (hcount : c * R ^ 4 ≤ (inside.card : ℝ)) :
    ∃ a > (0 : ℝ), relativeDeterminant modes freq depth n ≤ Real.exp (-a * R ^ 4) := by
  let b := Real.log (1 + Real.exp (-2))
  have hb : 0 < b := Real.log_pos (lt_add_of_pos_right 1 (Real.exp_pos _))
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  refine ⟨n * c * b, by positivity, (relative_determinant_mode_bound hsub freq depth n hshort).trans ?_⟩
  apply Real.exp_le_exp.mpr
  change -((n : ℝ) * inside.card) * b ≤ -(n * c * b) * R ^ 4
  nlinarith [mul_le_mul_of_nonneg_left hcount (show 0 ≤ (n : ℝ) * b by positivity)]

theorem relative_determinant_zero_depth {K : Type*} (modes : Finset K)
    (freq : K → ℝ) (n : ℕ) :
    relativeDeterminant modes freq 0 n = ((2 : ℝ) ^ (n * modes.card))⁻¹ := by
  unfold relativeDeterminant
  simp [pow_mul, one_add_one_eq_two]

/-- Euclidean frequency of an integer mode in the unit-period convention
where lattice momenta themselves give the frequencies. -/
noncomputable def latticeFrequency (k : Fin 4 → ℤ) : ℝ :=
  Real.sqrt (∑ i, (k i : ℝ) ^ 2)

/-- The positive orthant cube gives a quartic lower bound for any set
containing the complete nonzero four-dimensional frequency ball. -/
theorem lattice_ball_card_lower (modes : Finset (Fin 4 → ℤ)) {R : ℝ}
    (hR : 2 ≤ R)
    (hball : ∀ k : Fin 4 → ℤ, k ≠ 0 → latticeFrequency k ≤ R → k ∈ modes) :
    (R / 4) ^ 4 ≤ (modes.card : ℝ) := by
  classical
  let N := ⌊R / 2⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by norm_num; linarith)
  have hNlo : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNhi : (N : ℝ) ≤ R / 2 := Nat.floor_le (by linarith)
  have hNlt : R / 2 < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hNR : R / 4 ≤ (N : ℝ) := by linarith
  let cube (u : Fin 4 → Fin N) (i : Fin 4) : ℤ := (u i).val + 1
  have hInject : Function.Injective cube := by
    intro u v huv
    funext i
    apply Fin.ext
    have hi := congrFun huv i
    dsimp [cube] at hi
    exact_mod_cast (add_right_cancel hi)
  have hcard : N ^ 4 ≤ modes.card := by
    have hincl : Finset.univ.image cube ⊆ modes := by
      intro k hk
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hk
      have hne : cube u ≠ 0 := by
        intro he
        have h0 := congrFun he (0 : Fin 4)
        change ((u 0).val : ℤ) + 1 = 0 at h0
        omega
      apply hball _ hne
      unfold latticeFrequency
      have hsq : (∑ i : Fin 4, (cube u i : ℝ) ^ 2) ≤ 4 * (N : ℝ) ^ 2 := by
        calc
          _ ≤ ∑ _i : Fin 4, (N : ℝ) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            have hbi : (cube u i : ℝ) ≤ N := by
              have hi : (u i).val + 1 ≤ N := (u i).isLt
              dsimp [cube]
              exact_mod_cast hi
            have hai : 0 ≤ (cube u i : ℝ) := by dsimp [cube]; positivity
            exact (sq_le_sq₀ hai (by positivity)).2 hbi
          _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
      apply (Real.sqrt_le_iff).2
      refine ⟨by linarith, hsq.trans ?_⟩
      have hsqR := (sq_le_sq₀ (show 0 ≤ 2 * (N : ℝ) by positivity)
        (show 0 ≤ R by linarith)).2 (show 2 * (N : ℝ) ≤ R by linarith)
      nlinarith
    simpa [Finset.card_image_of_injective _ hInject, Fintype.card_fun] using Finset.card_le_card hincl
  have hcast : (N : ℝ) ^ 4 ≤ modes.card := by exact_mod_cast hcard
  exact (pow_le_pow_left₀ (by linarith) hNR _).trans hcast

/-- The determinant suppresses every polynomial cost of a fixed graph
even along simultaneous cutoff and zero-depth limits. -/
theorem quartic_determinant_polynomial_limit {a D : ℝ} (ha : 0 < a) (hD : 0 ≤ D) :
    Tendsto (fun R : ℝ => Real.exp (-a * R ^ 4) * (1 + R) ^ D) atTop (𝓝 0) := by
  have hupper := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero D a ha).const_mul ((2 : ℝ) ^ D)
  rw [mul_zero] at hupper
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg (by linarith) _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hR0 : 0 ≤ R := by linarith
    have hpow : R ≤ R ^ 4 := by
      calc
        R = R ^ 1 := by simp
        _ ≤ R ^ 4 := pow_le_pow_right₀ hR (by decide)
    have hde : Real.exp (-a * R ^ 4) ≤ Real.exp (-a * R) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hpow (neg_nonpos.mpr ha.le))
    have hp : (1 + R) ^ D ≤ (2 * R) ^ D :=
      Real.rpow_le_rpow (by linarith) (by linarith) hD
    calc
      _ ≤ Real.exp (-a * R) * (2 * R) ^ D :=
        mul_le_mul hde hp (Real.rpow_nonneg (by linarith) _) (Real.exp_nonneg _)
      _ = _ := by rw [Real.mul_rpow (by norm_num) hR0]; ring

theorem quartic_determinant_polynomial_uniform {a D : ℝ} (ha : 0 < a) (hD : 0 ≤ D) :
    ∃ C > (0 : ℝ), ∀ R : ℝ, 0 ≤ R → Real.exp (-a * R ^ 4) * (1 + R) ^ D ≤ C := by
  obtain ⟨B, hB⟩ := eventually_atTop.1
    ((quartic_determinant_polynomial_limit ha hD).eventually (gt_mem_nhds zero_lt_one))
  let B' := max 0 B
  refine ⟨1 + (1 + B') ^ D, by have h : 0 ≤ (1 + B') ^ D := Real.rpow_nonneg (by dsimp [B']; positivity) _; linarith, ?_⟩
  intro R hR
  by_cases hlarge : B' ≤ R
  · exact (hB R ((le_max_right (0 : ℝ) B).trans hlarge)).le.trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (by dsimp [B']; positivity) _))
  · have hp : (1 + R) ^ D ≤ (1 + B') ^ D :=
      Real.rpow_le_rpow (by linarith) (by linarith) hD
    have he : Real.exp (-a * R ^ 4) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) (by positivity))
    calc
      _ ≤ 1 * (1 + B') ^ D := mul_le_mul he hp (Real.rpow_nonneg (by linarith) _) zero_le_one
      _ ≤ _ := by linarith

end UV.RevisionCurvatureDeterminant
