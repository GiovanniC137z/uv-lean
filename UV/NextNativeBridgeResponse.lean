import UV.NextNativeBridgeKernel
import UV.AnalyticScalar

/-! Connected cycles of quadratic insertions of the normal-profile readouts.
All cycle momenta are in the fixed intrinsic four-dimensional Euclidean chart. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace UV.NextNativeBridge

structure NormalBridge (E : Type) [NormedAddCommGroup E] where
  plane : UV.SectorPlane.Plane E
  evolution : UV.SectorPlane.Evolution
  mass : ℝ
  mass_pos : 0 < mass
  profiles : Bool → NormalProfile
  normalGap : ℝ
  normalGap_pos : 0 < normalGap
  profiles_separated : Separated (profiles false) (profiles true) normalGap

variable {E : Type} [NormedAddCommGroup E]

def euclideanOmega (B : NormalBridge E) (k : UV.ScalarMomentum) : ℝ :=
  Real.sqrt (‖k‖ ^ 2 + B.mass ^ 2)

theorem mass_le_euclideanOmega (B : NormalBridge E) (k : UV.ScalarMomentum) :
    B.mass ≤ euclideanOmega B k := by
  apply (Real.le_sqrt B.mass_pos.le (by positivity)).2
  linarith [sq_nonneg ‖k‖]

theorem norm_le_euclideanOmega (B : NormalBridge E) (k : UV.ScalarMomentum) :
    ‖k‖ ≤ euclideanOmega B k := by
  apply (Real.le_sqrt (norm_nonneg k) (by positivity)).2
  linarith [sq_nonneg B.mass]

theorem euclideanOmega_le (B : NormalBridge E) (k : UV.ScalarMomentum) :
    euclideanOmega B k ≤ ‖k‖ + B.mass := by
  apply (Real.sqrt_le_left (add_nonneg (norm_nonneg k) B.mass_pos.le)).2
  nlinarith [mul_nonneg (norm_nonneg k) B.mass_pos.le]

def bridgeCoefficient (B : NormalBridge E) (i j : Bool) (k : UV.ScalarMomentum) : ℝ :=
  normalCovariance (B.profiles i) (B.profiles j) (euclideanOmega B k)

theorem bridgeCoefficient_stronglyMeasurable (B : NormalBridge E) (i j : Bool) :
    StronglyMeasurable (bridgeCoefficient B i j) :=
  (normalCovariance_stronglyMeasurable _ _).comp_measurable
    (by unfold euclideanOmega; fun_prop)

private def profileL1 (f : NormalProfile) : ℝ := ∫ y, ‖f.profile y‖

private theorem profileL1_nonneg (f : NormalProfile) : 0 ≤ profileL1 f :=
  integral_nonneg (fun _ => norm_nonneg _)

private theorem bridge_bound_from_gap (B : NormalBridge E) (i j : Bool)
    (q k : UV.ScalarMomentum) {d : ℝ} (hd : 0 ≤ d)
    (hgap : Separated (B.profiles i) (B.profiles j) d) :
    ‖bridgeCoefficient B i j (k + q)‖ ≤
      (profileL1 (B.profiles i) * profileL1 (B.profiles j) / (2 * B.mass) *
        Real.exp (d * ‖q‖)) * Real.exp (-(d * ‖k‖)) := by
  have hm := mass_le_euclideanOmega B (k + q)
  have hω := B.mass_pos.trans_le hm
  have hC : 0 ≤ profileL1 (B.profiles i) * profileL1 (B.profiles j) :=
    mul_nonneg (profileL1_nonneg _) (profileL1_nonneg _)
  have htri : ‖k‖ ≤ ‖k + q‖ + ‖q‖ := by
    simpa only [add_sub_cancel_right, sub_eq_add_neg, norm_neg, add_neg_cancel_right]
      using norm_sub_le (k + q) q
  have hshift : ‖k‖ - ‖q‖ ≤ euclideanOmega B (k + q) :=
    (sub_le_iff_le_add.mpr htri).trans (norm_le_euclideanOmega B _)
  have he : Real.exp (-euclideanOmega B (k + q) * d) ≤
      Real.exp (d * ‖q‖ - d * ‖k‖) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hshift hd]
  calc
    _ ≤ profileL1 (B.profiles i) * profileL1 (B.profiles j) *
        Real.exp (-euclideanOmega B (k + q) * d) / (2 * euclideanOmega B (k + q)) :=
      normalCovariance_bound _ _ hω hgap
    _ ≤ profileL1 (B.profiles i) * profileL1 (B.profiles j) *
        Real.exp (d * ‖q‖ - d * ‖k‖) / (2 * B.mass) := by
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he hC)
        (by positivity)).trans
        (div_le_div_of_nonneg_left (mul_nonneg hC (Real.exp_nonneg _))
          (by linarith [B.mass_pos]) (mul_le_mul_of_nonneg_left hm (by norm_num)))
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring

private theorem bridge_uniform_bound (B : NormalBridge E) (i j : Bool)
    (q k : UV.ScalarMomentum) :
    ‖bridgeCoefficient B i j (k + q)‖ ≤
      profileL1 (B.profiles i) * profileL1 (B.profiles j) / (2 * B.mass) := by
  simpa only [zero_mul, neg_zero, Real.exp_zero, mul_one] using
    bridge_bound_from_gap B i j q k (d := 0) le_rfl (fun _ _ _ _ => abs_nonneg _)

private theorem bridge_cross_bound (B : NormalBridge E) (i j : Bool)
    (hij : i ≠ j) (q k : UV.ScalarMomentum) :
    ‖bridgeCoefficient B i j (k + q)‖ ≤
      (profileL1 (B.profiles i) * profileL1 (B.profiles j) / (2 * B.mass) *
        Real.exp (B.normalGap * ‖q‖)) * Real.exp (-(B.normalGap * ‖k‖)) := by
  apply bridge_bound_from_gap B i j q k B.normalGap_pos.le
  cases i <;> cases j
  · exact (hij rfl).elim
  · exact B.profiles_separated
  · exact separated_symm B.profiles_separated
  · exact (hij rfl).elim

def closedCycleProduct {V : Type} [Fintype V] (B : NormalBridge E)
    (next : Equiv.Perm V) (labels : V → Bool)
    (shifts : V → UV.ScalarMomentum) (k : UV.ScalarMomentum) : ℝ :=
  ∏ j, bridgeCoefficient B (labels j) (labels (next j)) (k + shifts j)

private theorem cycle_has_crossing {V : Type} (next : Equiv.Perm V) (labels : V → Bool)
    (hconn : ∀ i j : V, ∃ n : ℕ, ((next : V → V)^[n]) i = j)
    (hmixed : ∃ i j : V, labels i ≠ labels j) :
    ∃ j, labels j ≠ labels (next j) := by
  by_contra! hh
  obtain ⟨i, j, hij⟩ := hmixed
  have he (n : ℕ) : labels i = labels (((next : V → V)^[n]) i) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact hh _
  obtain ⟨n, hn⟩ := hconn i j
  exact hij (hn ▸ he n)

/-- Every mixed connected Wick cycle is absolutely integrable, for arbitrary
finite incidence count and arbitrary fixed external-momentum shifts. -/
theorem mixed_normal_cycle_integrable {V : Type} [Fintype V] (B : NormalBridge E)
    (next : Equiv.Perm V) (labels : V → Bool)
    (shifts : V → UV.ScalarMomentum)
    (hconn : ∀ i j : V, ∃ n : ℕ, ((next : V → V)^[n]) i = j)
    (hmixed : ∃ i j : V, labels i ≠ labels j) :
    Integrable (closedCycleProduct B next labels shifts) := by
  classical
  obtain ⟨j, hj⟩ := cycle_has_crossing next labels hconn hmixed
  let K := fun i : V => profileL1 (B.profiles (labels i)) *
    profileL1 (B.profiles (labels (next i))) / (2 * B.mass)
  have hK (i : V) : 0 ≤ K i :=
    div_nonneg (mul_nonneg (profileL1_nonneg _) (profileL1_nonneg _))
      (mul_nonneg zero_le_two B.mass_pos.le)
  let A := (K j * Real.exp (B.normalGap * ‖shifts j‖)) *
    ∏ i ∈ Finset.univ.erase j, K i
  have hi := (UV.integrable_norm_pow_exp (E := UV.ScalarMomentum) (μ := volume)
    B.normalGap_pos 0).const_mul A
  simp only [pow_zero, one_mul] at hi
  apply hi.mono'
  · unfold closedCycleProduct
    have hm (i : V) : AEStronglyMeasurable
        (fun k => bridgeCoefficient B (labels i) (labels (next i)) (k + shifts i)) volume :=
      ((bridgeCoefficient_stronglyMeasurable B _ _).comp_measurable
        (by fun_prop : Measurable (fun k : UV.ScalarMomentum => k + shifts i))).aestronglyMeasurable
    rw [show (fun k => ∏ j, bridgeCoefficient B (labels j) (labels (next j)) (k + shifts j)) =
        ∏ j, (fun k => bridgeCoefficient B (labels j) (labels (next j)) (k + shifts j)) by
      funext k
      rw [Finset.prod_apply]]
    exact Finset.aestronglyMeasurable_prod Finset.univ (fun i _ => hm i)
  · refine Eventually.of_forall fun k => ?_
    unfold closedCycleProduct
    rw [norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    unfold A
    rw [mul_assoc, mul_comm (∏ i ∈ Finset.univ.erase j, K i), ← mul_assoc]
    apply mul_le_mul
    · exact bridge_cross_bound B _ _ hj _ _
    · apply Finset.prod_le_prod
      · exact fun i _ => norm_nonneg _
      · exact fun i _ => bridge_uniform_bound B _ _ _ _
    · exact Finset.prod_nonneg fun i _ => norm_nonneg _
    · exact mul_nonneg (mul_nonneg (hK j) (Real.exp_nonneg _)) (Real.exp_nonneg _)

/-- Finite sums over connected Wick cycles retain absolute convergence. -/
theorem mixed_normal_coefficient_integrable {V W : Type} [Fintype V] [Fintype W]
    (B : NormalBridge E) (next : W → Equiv.Perm V) (labels : V → Bool)
    (shifts : W → V → UV.ScalarMomentum) (weights : W → ℝ)
    (hconn : ∀ w, ∀ i j : V, ∃ n : ℕ, ((next w : V → V)^[n]) i = j)
    (hmixed : ∃ i j : V, labels i ≠ labels j) :
    Integrable (fun k => ∑ w, weights w * closedCycleProduct B (next w) labels (shifts w) k) :=
  integrable_finset_sum _ (fun w _ =>
    (mixed_normal_cycle_integrable B (next w) labels (shifts w) (hconn w) hmixed).const_mul _)

end UV.NextNativeBridge
