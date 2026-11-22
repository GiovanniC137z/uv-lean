import UV.ResumeCollarHeat
import Mathlib.Analysis.SumIntegralComparisons

/-! The full shifted integer angular heat sum in a fixed quartic normal chart. -/

noncomputable section

open MeasureTheory Filter Set

namespace UV.ContinueCollarAngular

private theorem nat_cast_le_sq (n : ℕ) : (n : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := by
  cases n with
  | zero => norm_num
  | succ n =>
    rw [Nat.cast_succ]
    nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]

private theorem gaussian_nat_bound {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => Real.exp (-a * (n : ℝ) ^ (2 : ℕ))) ∧
      (∑' n : ℕ, Real.exp (-a * (n : ℝ) ^ (2 : ℕ))) ≤ 1 + Real.sqrt (Real.pi / a) / 2 := by
  let g := fun x : ℝ => Real.exp (-a * x ^ (2 : ℕ))
  have hgauss : Summable (fun n : ℕ => g n) := by
    apply Summable.of_nonneg_of_le (f := fun n : ℕ => (Real.exp (-a)) ^ n)
      (fun _ => Real.exp_nonneg _) _ (summable_geometric_of_lt_one (Real.exp_nonneg _)
        (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)))
    intro n
    change g n ≤ (Real.exp (-a)) ^ n
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    change -a * (n : ℝ) ^ (2 : ℕ) ≤ _
    nlinarith [mul_le_mul_of_nonneg_left (nat_cast_le_sq n) ha.le]
  refine ⟨hgauss, ?_⟩
  have htail : Summable (fun n : ℕ => g ((n + 1 : ℕ) : ℝ)) := (summable_nat_add_iff 1).2 hgauss
  have hsum : (∑' n : ℕ, g ((n + 1 : ℕ) : ℝ)) ≤ Real.sqrt (Real.pi / a) / 2 := by
    apply le_of_tendsto htail.hasSum.tendsto_sum_nat
    refine Eventually.of_forall fun N => ?_
    have gAnti : AntitoneOn g (Icc 0 (0 + (N : ℝ))) := by
      intro x hx y _ hxy
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hx.1 hxy 2) (neg_nonpos.mpr ha.le)
    have hR : 0 ≤ (N : ℝ) := by positivity
    calc
      _ ≤ ∫ x in (0 : ℝ)..N, g x := by
        simpa only [zero_add] using gAnti.sum_le_integral
      _ = ∫ x in Ioc (0 : ℝ) N, g x := intervalIntegral.integral_of_le hR
      _ ≤ ∫ x in Ioi (0 : ℝ), g x :=
        setIntegral_mono_set (integrable_exp_neg_mul_sq ha).integrableOn
          (ae_of_all _ fun _ => Real.exp_nonneg _)
          (ae_of_all _ fun _ hx => hx.1)
      _ = _ := integral_gaussian_Ioi a
  change (∑' n : ℕ, g n) ≤ _
  have hzero : g ((0 : ℕ) : ℝ) = 1 := by simp [g]
  rw [hgauss.tsum_eq_zero_add, hzero]
  exact add_le_add_left hsum 1

private def intSides : ℕ ⊕ ℕ ≃ ℤ where
  toFun := Sum.elim Int.ofNat Int.negSucc
  invFun z := match z with
    | .ofNat n => .inl n
    | .negSucc n => .inr n
  left_inv s := by cases s <;> rfl
  right_inv z := by cases z <;> rfl

set_option maxHeartbeats 700000 in
/-- The sum over every angular integer has an explicit bound uniform in the real shift. -/
theorem shifted_angular_gaussian_bound {a : ℝ} (ha : 0 < a) (θ : ℝ) :
    Summable (fun n : ℤ => Real.exp (-a * ((n : ℝ) + θ) ^ (2 : ℕ))) ∧
      (∑' n : ℤ, Real.exp (-a * ((n : ℝ) + θ) ^ (2 : ℕ))) ≤ 2 + Real.sqrt (Real.pi / a) := by
  let x := θ - (⌊θ⌋ : ℤ)
  have hx0 : 0 ≤ x := sub_nonneg.mpr (Int.floor_le θ)
  have hx1 : x ≤ 1 := by
    unfold x
    linarith [Int.lt_floor_add_one θ]
  let f := fun n : ℤ => Real.exp (-a * ((n : ℝ) + θ) ^ (2 : ℕ))
  let g := fun n : ℤ => Real.exp (-a * ((n : ℝ) + x) ^ (2 : ℕ))
  let m := fun n : ℕ => Real.exp (-a * (n : ℝ) ^ (2 : ℕ))
  obtain ⟨hm, hmt⟩ := gaussian_nat_bound ha
  have hcmp₁ (n : ℕ) : (g ∘ intSides ∘ Sum.inl) n ≤ m n := by
    apply Real.exp_le_exp.mpr
    change -a * ((n : ℝ) + x) ^ (2 : ℕ) ≤ -a * (n : ℝ) ^ (2 : ℕ)
    exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ (by positivity) (by linarith) _)
      (neg_nonpos.mpr ha.le)
  have hcmp₂ (n : ℕ) : (g ∘ intSides ∘ Sum.inr) n ≤ m n := by
    apply Real.exp_le_exp.mpr
    change -a * (((Int.negSucc n : ℤ) : ℝ) + x) ^ (2 : ℕ) ≤ _
    rw [Int.cast_negSucc, Nat.cast_add, Nat.cast_one,
      show -((n : ℝ) + 1) + x = -((n : ℝ) + (1 - x)) by ring, neg_sq]
    exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ (by positivity) (by linarith) _)
      (neg_nonpos.mpr ha.le)
  have hs₁ : Summable (g ∘ intSides ∘ Sum.inl) :=
    Summable.of_nonneg_of_le (fun _ => Real.exp_nonneg _) hcmp₁ hm
  have hs₂ : Summable (g ∘ intSides ∘ Sum.inr) :=
    Summable.of_nonneg_of_le (fun _ => Real.exp_nonneg _) hcmp₂ hm
  have hgsides := Summable.sum (g ∘ intSides) hs₁ hs₂
  have hgs : Summable g := intSides.summable_iff.mp hgsides
  have hgt : ∑' n, g n ≤ 2 + Real.sqrt (Real.pi / a) := by
    rw [← intSides.tsum_eq, Summable.tsum_sum (f := fun i => g (intSides i)) hs₁ hs₂]
    have h₁ : (∑' n : ℕ, g (intSides (Sum.inl n))) ≤ ∑' n : ℕ, m n :=
      hs₁.tsum_le_tsum hcmp₁ hm
    have h₂ : (∑' n : ℕ, g (intSides (Sum.inr n))) ≤ ∑' n : ℕ, m n :=
      hs₂.tsum_le_tsum hcmp₂ hm
    have hm' : (∑' n : ℕ, m n) ≤ 1 + Real.sqrt (Real.pi / a) / 2 := hmt
    linarith only [h₁, h₂, hm']
  let e : ℤ ≃ ℤ := Equiv.addRight (-⌊θ⌋)
  have he : f ∘ e = g := by
    funext n
    change Real.exp (-a * (((n + -⌊θ⌋ : ℤ) : ℝ) + θ) ^ (2 : ℕ)) =
      Real.exp (-a * ((n : ℝ) + (θ - (⌊θ⌋ : ℤ))) ^ (2 : ℕ))
    push_cast
    apply congrArg (fun y : ℝ => Real.exp (-a * y ^ (2 : ℕ)))
    ring
  change Summable f ∧ (∑' n, f n) ≤ _
  refine ⟨e.summable_iff.mp ?_, ?_⟩
  · rwa [he]
  · rw [← e.tsum_eq]
    exact (tsum_congr (congrFun he)).le.trans hgt

/-- For a short duration the angular Gaussian sum costs exactly one half inverse power of time. -/
theorem shifted_angular_short_time_bound {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (ht1 : t ≤ 1)
    (θ : ℝ) :
    Summable (fun n : ℤ => Real.exp (-(a * t) * ((n : ℝ) + θ) ^ (2 : ℕ))) ∧
      (∑' n : ℤ, Real.exp (-(a * t) * ((n : ℝ) + θ) ^ (2 : ℕ))) ≤
        (2 + Real.sqrt (Real.pi / a)) * t ^ (-1 / 2 : ℝ) := by
  obtain ⟨hs, hb⟩ := shifted_angular_gaussian_bound (mul_pos ha ht) θ
  refine ⟨hs, hb.trans ?_⟩
  have hroot : Real.sqrt (Real.pi / (a * t)) =
      Real.sqrt (Real.pi / a) * t ^ (-1 / 2 : ℝ) := by
    rw [div_mul_eq_div_div, div_eq_mul_inv, Real.sqrt_mul (by positivity),
      Real.sqrt_inv, Real.sqrt_eq_rpow t, show (-1 / 2 : ℝ) = -(1 / 2) by ring,
      Real.rpow_neg ht.le]
  have hone : 1 ≤ t ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_zero t]
    exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)
  rw [hroot, add_mul]
  exact add_le_add_right (by simpa using mul_le_mul_of_nonneg_left hone (by norm_num : (0 : ℝ) ≤ 2)) _

end UV.ContinueCollarAngular
